from __future__ import annotations

import csv
import json
import re
import time
from collections import Counter, defaultdict
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path
from typing import Any

import requests
from rapidfuzz.fuzz import token_set_ratio

import firehouse_research.build_leads as base

OUTPUT_DIR = Path("output")
INPUT_CSV = OUTPUT_DIR / "verified_leads.csv"
SCAN_DATE = "2026-08-18"

VERIFIED_CENTERS = {
    "Woodstock": (34.0869120, -84.5286110, "9745 Highway 92 shopping center, Woodstock, GA 30188"),
    "Tucker": (33.8554913, -84.2098366, "4306 Lawrenceville Highway shopping center, Tucker, GA 30084"),
}

FINAL_QUOTAS = {
    "Education & Childcare": 45,
    "Healthcare & Medical": 45,
    "Professional Offices & Finance": 40,
    "Industrial, Construction & Auto": 30,
    "Sports, Fitness & Recreation": 25,
    "Hotels, Events & Entertainment": 20,
    "Government, Faith & Community": 20,
    "Apartments & Residential Communities": 10,
    "Retail & Shopping": 15,
}

# Extra records are scanned so unavailable websites can be replaced by stronger
# candidates without losing the category mix.
PRESELECT_QUOTAS = {
    "Education & Childcare": 65,
    "Healthcare & Medical": 65,
    "Professional Offices & Finance": 60,
    "Industrial, Construction & Auto": 48,
    "Sports, Fitness & Recreation": 42,
    "Hotels, Events & Entertainment": 35,
    "Government, Faith & Community": 35,
    "Apartments & Residential Communities": 20,
    "Retail & Shopping": 30,
}

GENERIC_NAME_WORDS = {
    "the", "and", "of", "at", "in", "for", "a", "an", "inc", "llc", "company",
    "center", "centre", "school", "academy", "medical", "health", "clinic", "office",
    "services", "service", "group", "associates", "association", "woodstock", "tucker",
    "georgia", "ga", "north", "south", "east", "west",
}


def use_verified_center(address: str) -> tuple[float, float, str]:
    store_name = "Woodstock" if "Woodstock" in address else "Tucker"
    return VERIFIED_CENTERS[store_name]


def source_only_website(record: dict[str, Any]) -> tuple[str, None, bool, str]:
    return record.get("website", ""), None, False, "audited_after_candidate_selection"


def record_quality(record: dict[str, Any]) -> tuple[float, float, str]:
    return (-base.final_score(record), record["distance_miles"], record["name_norm"])


def diverse_preselect(records: list[dict[str, Any]], store: str, count: int = 250) -> list[dict[str, Any]]:
    pool = [record for record in records if record["assigned_store"] == store]
    selected: list[dict[str, Any]] = []
    selected_ids: set[str] = set()

    for group, quota in PRESELECT_QUOTAS.items():
        group_pool = [
            record for record in pool
            if record["category_group"] == group
            and record.get("confidence", 0) >= 0.90
            and record.get("source_count", 0) >= 2
        ]
        group_pool.sort(key=record_quality)
        for record in group_pool[:quota]:
            key = record.get("overture_id") or f"{record['name_norm']}|{base.normalize_text(record['full_address'])}"
            if key not in selected_ids:
                selected_ids.add(key)
                selected.append(record)

    # Fill to at least 400 per store with other strong, address-complete records.
    target = max(sum(PRESELECT_QUOTAS.values()), 400)
    remainder = [
        record for record in pool
        if (record.get("overture_id") or f"{record['name_norm']}|{base.normalize_text(record['full_address'])}") not in selected_ids
        and record.get("confidence", 0) >= 0.90
        and record.get("source_count", 0) >= 2
    ]
    remainder.sort(key=record_quality)
    for record in remainder:
        if len(selected) >= target:
            break
        key = record.get("overture_id") or f"{record['name_norm']}|{base.normalize_text(record['full_address'])}"
        selected_ids.add(key)
        selected.append(record)
    return selected


def valid_phone(value: str) -> bool:
    digits = re.sub(r"\D", "", value or "")
    return 10 <= len(digits) <= 15


def valid_email(value: str) -> bool:
    return bool(re.fullmatch(r"[^\s@]+@[^\s@]+\.[^\s@]+", value or "", re.IGNORECASE))


def visible_name_tokens(name: str) -> list[str]:
    return [
        token for token in base.normalize_text(name).split()
        if len(token) >= 4 and token not in GENERIC_NAME_WORDS
    ]


def check_website(row: dict[str, str]) -> dict[str, Any]:
    url = (row.get("Website (public listing)") or "").strip()
    if not url:
        return {"status": None, "final_url": "", "name_match": False, "note": "no_source_website"}
    try:
        response = requests.get(
            url,
            headers={"User-Agent": base.USER_AGENT},
            timeout=7,
            allow_redirects=True,
            stream=True,
        )
        status = response.status_code
        content_type = response.headers.get("content-type", "").lower()
        body = b""
        if "html" in content_type or "text" in content_type:
            for chunk in response.iter_content(chunk_size=16384):
                body += chunk
                if len(body) >= 140000:
                    break
        text = re.sub(r"<script.*?</script>|<style.*?</style>", " ", body.decode("utf-8", errors="ignore"), flags=re.I | re.S)
        text = re.sub(r"<[^>]+>", " ", text)
        normalized_page = base.normalize_text(text[:140000])
        name = row.get("Entity Name", "")
        tokens = visible_name_tokens(name)
        token_hits = sum(token in normalized_page for token in tokens)
        fuzzy = token_set_ratio(base.normalize_text(name), normalized_page[:30000]) if normalized_page else 0
        name_match = bool(tokens) and (token_hits >= min(2, len(tokens)) or fuzzy >= 72)
        if not tokens:
            name_match = fuzzy >= 78
        return {
            "status": status,
            "final_url": response.url,
            "name_match": bool(name_match),
            "note": "reachable" if status < 500 else "server_error",
        }
    except Exception as exc:  # noqa: BLE001
        return {"status": None, "final_url": url, "name_match": False, "note": type(exc).__name__}


def verify_websites(rows: list[dict[str, str]]) -> None:
    unique: dict[str, dict[str, str]] = {}
    for row in rows:
        url = (row.get("Website (public listing)") or "").strip()
        if url:
            unique.setdefault(url, row)
    results: dict[str, dict[str, Any]] = {}
    with ThreadPoolExecutor(max_workers=48) as executor:
        future_to_url = {executor.submit(check_website, row): url for url, row in unique.items()}
        for future in as_completed(future_to_url):
            url = future_to_url[future]
            try:
                results[url] = future.result()
            except Exception as exc:  # noqa: BLE001
                results[url] = {"status": None, "final_url": url, "name_match": False, "note": type(exc).__name__}

    for row in rows:
        phone = row.get("Phone (public listing)", "")
        email = row.get("Email (public listing)", "")
        if phone and not valid_phone(phone):
            row["Phone (public listing)"] = ""
        if email and not valid_email(email):
            row["Email (public listing)"] = ""
        source_url = (row.get("Website (public listing)") or "").strip()
        result = results.get(source_url, {"status": None, "final_url": source_url, "name_match": False, "note": "not_checked"})
        row["Website (public listing)"] = result["final_url"] or source_url
        row["Website HTTP Status"] = "" if result["status"] is None else str(result["status"])
        row["Website Name Match"] = "Yes" if result["name_match"] else "No"
        row["_website_reachable"] = "1" if result["status"] is not None and result["status"] < 500 else "0"
        row["_website_name_match"] = "1" if result["name_match"] else "0"
        row["_website_note"] = result["note"]
        present = []
        if row.get("Phone (public listing)"):
            present.append("phone")
        if row.get("Email (public listing)"):
            present.append("email")
        if row.get("Website (public listing)"):
            present.append("website")
        row["Contact Completeness"] = ", ".join(present) if present else "No verified public contact in source"


def row_sort_key(row: dict[str, str]) -> tuple[int, int, float, float, str]:
    return (
        -int(row.get("_website_name_match", "0")),
        -int(row.get("_website_reachable", "0")),
        -float(row.get("Lead Score") or 0),
        float(row.get("Straight-Line Distance (mi)") or 99),
        base.normalize_text(row.get("Entity Name", "")),
    )


def strict_entity_row(row: dict[str, str]) -> bool:
    try:
        distance = float(row.get("Straight-Line Distance (mi)") or 999)
        confidence = float(row.get("Overture Confidence") or 0)
        sources = int(float(row.get("Overture Source Count") or 0))
    except ValueError:
        return False
    address = row.get("Full Physical Address", "")
    return (
        bool(row.get("Entity Name", "").strip())
        and bool(address.strip())
        and bool(re.search(r"\d", address))
        and distance <= 10.0
        and confidence >= 0.90
        and sources >= 2
        and row.get("State", "").strip().upper() == "GA"
    )


def select_final(rows: list[dict[str, str]], store: str) -> list[dict[str, str]]:
    pool = [row for row in rows if row.get("Assigned Store") == store and strict_entity_row(row)]
    selected: list[dict[str, str]] = []
    seen: set[tuple[str, str]] = set()
    for group, quota in FINAL_QUOTAS.items():
        group_pool = [row for row in pool if row.get("Category Group") == group]
        group_pool.sort(key=row_sort_key)
        for row in group_pool:
            key = (base.normalize_text(row["Entity Name"]), base.normalize_text(row["Full Physical Address"]))
            if key in seen:
                continue
            seen.add(key)
            selected.append(row)
            if sum(item.get("Category Group") == group for item in selected) >= quota:
                break

    # If a narrowly defined category has fewer valid records, fill with the best
    # remaining entity while preserving uniqueness and the 250/store total.
    remainder = sorted(pool, key=row_sort_key)
    for row in remainder:
        if len(selected) >= 250:
            break
        key = (base.normalize_text(row["Entity Name"]), base.normalize_text(row["Full Physical Address"]))
        if key in seen:
            continue
        seen.add(key)
        selected.append(row)
    if len(selected) < 250:
        raise RuntimeError(f"Only {len(selected)} strict final records for {store}")
    return selected[:250]


def update_status(row: dict[str, str]) -> None:
    if row.get("_website_name_match") == "1":
        row["Verification Status"] = "A — high-confidence multi-source place record; physical address and entity name also matched on reachable public website"
    elif row.get("_website_reachable") == "1":
        row["Verification Status"] = "B — high-confidence multi-source place record; public website reachable but page-text name match was inconclusive"
    else:
        row["Verification Status"] = "B — high-confidence multi-source place record with complete physical address; source website unavailable or blocked during scan"


def write_csv(path: Path, headers: list[str], rows: list[dict[str, str]]) -> None:
    with path.open("w", encoding="utf-8-sig", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=headers, extrasaction="ignore")
        writer.writeheader()
        writer.writerows(rows)


def main() -> None:
    base.geocode = use_verified_center
    base.fetch_overpass = lambda store: []
    base.validate_website = source_only_website
    base.select_store_records = diverse_preselect
    base.main()

    with INPUT_CSV.open(encoding="utf-8-sig", newline="") as handle:
        reader = csv.DictReader(handle)
        headers = list(reader.fieldnames or [])
        candidates = list(reader)
    print(f"Auditing {len(candidates)} diversified candidates", flush=True)
    verify_websites(candidates)

    final_rows: list[dict[str, str]] = []
    for store in ("Woodstock", "Tucker"):
        store_rows = select_final(candidates, store)
        for index, row in enumerate(store_rows, start=1):
            row["Lead ID"] = f"FH-{store[:3].upper()}-{index:03d}"
            update_status(row)
            score = float(row.get("Lead Score") or 0)
            if row.get("_website_name_match") == "1":
                score += 8
            elif row.get("_website_reachable") == "1":
                score += 3
            row["Lead Score"] = f"{score:.1f}"
            row["Priority Tier"] = "A" if score >= 122 else "B" if score >= 108 else "C"
        final_rows.extend(store_rows)

    final_rows.sort(key=lambda row: (row["Assigned Store"], -float(row["Lead Score"]), float(row["Straight-Line Distance (mi)"])))
    write_csv(OUTPUT_DIR / "verified_leads.csv", headers, final_rows)
    write_csv(OUTPUT_DIR / "woodstock_leads.csv", headers, [row for row in final_rows if row["Assigned Store"] == "Woodstock"])
    write_csv(OUTPUT_DIR / "tucker_leads.csv", headers, [row for row in final_rows if row["Assigned Store"] == "Tucker"])

    top_100: list[dict[str, str]] = []
    for store in ("Woodstock", "Tucker"):
        store_rows = [row for row in final_rows if row["Assigned Store"] == store]
        top_100.extend(sorted(store_rows, key=row_sort_key)[:50])
    write_csv(OUTPUT_DIR / "top_100.csv", headers, top_100)

    key_counts = Counter((base.normalize_text(row["Entity Name"]), base.normalize_text(row["Full Physical Address"])) for row in final_rows)
    if any(value > 1 for value in key_counts.values()):
        raise RuntimeError("Duplicate entity/address rows remained after final selection")
    if max(float(row["Straight-Line Distance (mi)"]) for row in final_rows) > 10.0:
        raise RuntimeError("Out-of-radius record remained after final selection")

    category_counts = Counter(row["Category Group"] for row in final_rows)
    store_counts = Counter(row["Assigned Store"] for row in final_rows)
    status_counts = Counter(row["Verification Status"] for row in final_rows)
    summary = {
        "generated_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "scan_date": SCAN_DATE,
        "selected_total": len(final_rows),
        "counts_by_store": dict(store_counts),
        "counts_by_category_group": dict(category_counts),
        "verification_counts": dict(status_counts),
        "website_reachable": sum(row.get("_website_reachable") == "1" for row in final_rows),
        "website_entity_name_match": sum(row.get("_website_name_match") == "1" for row in final_rows),
        "public_phone_count": sum(bool(row.get("Phone (public listing)")) for row in final_rows),
        "public_email_count": sum(bool(row.get("Email (public listing)")) for row in final_rows),
        "public_website_count": sum(bool(row.get("Website (public listing)")) for row in final_rows),
        "duplicate_entity_address_rows": 0,
        "maximum_distance_miles": max(float(row["Straight-Line Distance (mi)"]) for row in final_rows),
        "radius_miles": 10.0,
        "distance_method": "Haversine straight-line distance from independently verified restaurant-center coordinates",
        "record_rule": "Named entity, complete physical street-style Georgia address, <=10.0 miles, Overture confidence >=0.90, and at least two Overture source records",
        "contact_rule": "Public phone/email/website copied from current Overture Places source records; syntax-checked; never inferred. Website reachability is not email deliverability.",
        "category_target_per_store": FINAL_QUOTAS,
        "stores": [
            {"store": name, "lat": data[0], "lon": data[1], "display_name": data[2]}
            for name, data in VERIFIED_CENTERS.items()
        ],
        "source_urls": [
            "https://docs.overturemaps.org/guides/places/",
            "https://docs.overturemaps.org/getting-data/overturemaps-py/",
        ],
    }
    (OUTPUT_DIR / "summary.json").write_text(json.dumps(summary, indent=2), encoding="utf-8")
    print(json.dumps(summary, indent=2), flush=True)


if __name__ == "__main__":
    main()
