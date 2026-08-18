from __future__ import annotations

import csv
import html
import json
import math
import os
import re
import subprocess
import sys
import time
import urllib.parse
from collections import defaultdict
from concurrent.futures import ThreadPoolExecutor, as_completed
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable

import requests
from rapidfuzz.fuzz import token_set_ratio

OUTPUT_DIR = Path("output")
OUTPUT_DIR.mkdir(parents=True, exist_ok=True)

RADIUS_MILES = 10.0
RADIUS_METERS = 16093.44
EARTH_RADIUS_MILES = 3958.7613
USER_AGENT = "FirehouseSubsCateringResearch/1.0 (public-business-data validation)"

STORES = [
    {
        "store": "Woodstock",
        "address": "9745-D Highway 92, Woodstock, GA 30188",
    },
    {
        "store": "Tucker",
        "address": "4306 Lawrenceville Highway, Suite 130, Tucker, GA 30084",
    },
]

# Overture primary and alternate place categories are taxonomy slugs. These
# keyword groups intentionally cast a wide net, then priority scoring favors
# organizations most likely to place repeat group-meal orders.
GROUP_RULES: list[tuple[str, tuple[str, ...]]] = [
    ("Education & Childcare", (
        "school", "preschool", "day_care", "daycare", "childcare", "college",
        "university", "academy", "education", "tutoring", "learning_center",
        "training_center", "technical_school", "trade_school", "campus",
    )),
    ("Healthcare & Medical", (
        "hospital", "medical", "clinic", "health", "doctor", "physician",
        "dentist", "dental", "orthodont", "chiropr", "urgent_care", "dialysis",
        "rehabilitation", "nursing", "senior_care", "assisted_living", "laboratory",
        "imaging", "therapy", "pharmacy", "veterinary", "optomet", "podiatr",
    )),
    ("Sports, Fitness & Recreation", (
        "sports", "gym", "fitness", "recreation", "athletic", "martial_arts",
        "dance", "yoga", "pilates", "golf", "tennis", "soccer", "baseball",
        "basketball", "swimming", "bowling", "skating", "trampoline", "arena",
        "stadium", "sports_club", "country_club", "community_pool",
    )),
    ("Hotels, Events & Entertainment", (
        "hotel", "motel", "lodging", "event", "banquet", "wedding", "conference",
        "convention", "theater", "theatre", "cinema", "museum", "performing_arts",
        "entertainment", "amusement", "music_venue", "auditorium", "gallery",
    )),
    ("Government, Faith & Community", (
        "government", "city_hall", "courthouse", "library", "community_center",
        "church", "mosque", "synagogue", "temple", "religious", "worship",
        "non_profit", "nonprofit", "charity", "social_service", "youth_organization",
        "fire_station", "police", "post_office", "civic", "association",
    )),
    ("Professional Offices & Finance", (
        "office", "lawyer", "law_firm", "attorney", "insurance", "accounting",
        "accountant", "financial", "bank", "credit_union", "mortgage", "real_estate",
        "consulting", "employment", "staffing", "marketing", "engineering",
        "architect", "technology", "software", "coworking", "business_center",
        "corporate", "headquarters", "professional_service",
    )),
    ("Industrial, Construction & Auto", (
        "industrial", "manufacturer", "manufacturing", "factory", "warehouse",
        "distribution", "logistics", "construction", "contractor", "automotive",
        "car_dealer", "auto_dealer", "dealership", "repair_shop", "fleet",
        "equipment", "wholesale", "business_park", "storage_facility",
    )),
    ("Apartments & Residential Communities", (
        "apartment", "condominium", "residential", "property_management",
        "retirement_community", "housing_complex", "mobile_home_park",
    )),
    ("Retail & Shopping", (
        "shopping", "retail", "store", "supermarket", "grocery", "department_store",
        "hardware", "home_improvement", "furniture", "electronics", "clothing",
        "bookstore", "shopping_center", "shopping_mall", "marketplace",
    )),
]

EXCLUDE_CATEGORY_TERMS = (
    "restaurant", "fast_food", "cafe", "coffee_shop", "coffeehouse", "bar",
    "pub", "nightclub", "food_truck", "pizza_place", "burger_joint", "bakery",
    "sandwich_shop", "ice_cream", "caterer", "meal_delivery", "food_court",
)

BASE_PRIORITY = {
    "Education & Childcare": 96,
    "Healthcare & Medical": 94,
    "Hotels, Events & Entertainment": 92,
    "Professional Offices & Finance": 90,
    "Industrial, Construction & Auto": 89,
    "Government, Faith & Community": 87,
    "Sports, Fitness & Recreation": 86,
    "Apartments & Residential Communities": 81,
    "Retail & Shopping": 74,
    "Other Local Employer / Organization": 66,
}

SUGGESTED_ROLE = {
    "Education & Childcare": "Principal, office manager, PTO/PTA, athletic director, or program director",
    "Healthcare & Medical": "Practice manager, office manager, department coordinator, or administrator",
    "Sports, Fitness & Recreation": "General manager, league director, coach, tournament director, or membership manager",
    "Hotels, Events & Entertainment": "Sales manager, event coordinator, banquet manager, or general manager",
    "Government, Faith & Community": "Office administrator, facilities coordinator, ministry leader, or program director",
    "Professional Offices & Finance": "Office manager, executive assistant, HR, operations, or branch manager",
    "Industrial, Construction & Auto": "Operations manager, HR, service manager, dispatcher, or safety coordinator",
    "Apartments & Residential Communities": "Property manager, leasing manager, resident-events coordinator, or HOA manager",
    "Retail & Shopping": "Store manager, district manager, HR, or shopping-center property manager",
    "Other Local Employer / Organization": "Owner, general manager, office manager, or operations coordinator",
}

CATERING_USE = {
    "Education & Childcare": "Teacher workdays, staff meetings, parent nights, athletics, clubs, testing days, and field trips",
    "Healthcare & Medical": "Staff lunches, training, appreciation meals, vendor lunches, and extended-shift meals",
    "Sports, Fitness & Recreation": "Team meals, tournaments, camps, coach meetings, member events, and watch parties",
    "Hotels, Events & Entertainment": "Guest groups, event crews, meetings, rehearsals, conferences, and overflow catering",
    "Government, Faith & Community": "Committee meetings, volunteer meals, training, community events, and youth programs",
    "Professional Offices & Finance": "Client meetings, trainings, recruiting, staff lunches, closings, and appreciation events",
    "Industrial, Construction & Auto": "Shift meals, safety meetings, project lunches, inventory days, and employee appreciation",
    "Apartments & Residential Communities": "Resident events, leasing events, HOA meetings, move-in days, and maintenance-team meals",
    "Retail & Shopping": "Store meetings, inventory nights, seasonal teams, grand openings, and employee appreciation",
    "Other Local Employer / Organization": "Staff meetings, training, events, appreciation meals, and group orders",
}


def normalize_text(value: Any) -> str:
    value = html.unescape(str(value or "")).lower()
    value = re.sub(r"\b(the|incorporated|inc|llc|l\.l\.c|corp|corporation|company|co|ltd)\b", " ", value)
    return re.sub(r"[^a-z0-9]+", " ", value).strip()


def haversine_miles(lat1: float, lon1: float, lat2: float, lon2: float) -> float:
    p1 = math.radians(lat1)
    p2 = math.radians(lat2)
    dphi = math.radians(lat2 - lat1)
    dlambda = math.radians(lon2 - lon1)
    a = math.sin(dphi / 2) ** 2 + math.cos(p1) * math.cos(p2) * math.sin(dlambda / 2) ** 2
    return 2 * EARTH_RADIUS_MILES * math.asin(math.sqrt(a))


def bbox_for_radius(lat: float, lon: float, miles: float) -> tuple[float, float, float, float]:
    lat_delta = miles / 69.0
    lon_delta = miles / (69.172 * max(math.cos(math.radians(lat)), 0.2))
    return lon - lon_delta, lat - lat_delta, lon + lon_delta, lat + lat_delta


def geocode(address: str) -> tuple[float, float, str]:
    endpoints = [
        "https://nominatim.openstreetmap.org/search",
        "https://nominatim.openstreetmap.org/ui/search.html",  # never parsed; fallback marker
    ]
    response = requests.get(
        endpoints[0],
        params={"q": address, "format": "jsonv2", "limit": 1, "countrycodes": "us"},
        headers={"User-Agent": USER_AGENT},
        timeout=30,
    )
    response.raise_for_status()
    results = response.json()
    if not results:
        raise RuntimeError(f"Could not geocode store address: {address}")
    return float(results[0]["lat"]), float(results[0]["lon"]), results[0].get("display_name", address)


def run_overture_download(store: dict[str, Any]) -> Path:
    west, south, east, north = bbox_for_radius(store["lat"], store["lon"], 10.35)
    output = OUTPUT_DIR / f"{store['store'].lower()}_places.geojsonseq"
    cmd = [
        "overturemaps",
        "download",
        f"--bbox={west:.7f},{south:.7f},{east:.7f},{north:.7f}",
        "-f",
        "geojsonseq",
        "--type=place",
        "-o",
        str(output),
        "--connect_timeout=20",
        "--request_timeout=120",
    ]
    print("Running:", " ".join(cmd), flush=True)
    subprocess.run(cmd, check=True)
    return output


def overpass_query(lat: float, lon: float) -> str:
    tags = ["amenity", "shop", "office", "tourism", "leisure", "healthcare", "craft", "industrial"]
    clauses = "\n".join(
        f'nwr(around:{int(RADIUS_METERS + 250)},{lat:.7f},{lon:.7f})["name"]["{tag}"];'
        for tag in tags
    )
    clauses += (
        f'\nnwr(around:{int(RADIUS_METERS + 250)},{lat:.7f},{lon:.7f})["name"]["building"~"school|hospital|office|commercial|industrial|retail|hotel|church|civic|sports_centre|warehouse"];'
    )
    return f"[out:json][timeout:180];(\n{clauses}\n);out center tags qt;"


def fetch_overpass(store: dict[str, Any]) -> list[dict[str, Any]]:
    endpoints = [
        "https://overpass-api.de/api/interpreter",
        "https://overpass.kumi.systems/api/interpreter",
        "https://overpass.nchc.org.tw/api/interpreter",
    ]
    query = overpass_query(store["lat"], store["lon"])
    last_error: Exception | None = None
    for endpoint in endpoints:
        try:
            response = requests.post(
                endpoint,
                data={"data": query},
                headers={"User-Agent": USER_AGENT},
                timeout=240,
            )
            response.raise_for_status()
            payload = response.json()
            records: list[dict[str, Any]] = []
            for element in payload.get("elements", []):
                tags = element.get("tags") or {}
                name = tags.get("name")
                if not name:
                    continue
                lat_value = element.get("lat")
                lon_value = element.get("lon")
                if lat_value is None or lon_value is None:
                    center = element.get("center") or {}
                    lat_value = center.get("lat")
                    lon_value = center.get("lon")
                if lat_value is None or lon_value is None:
                    continue
                records.append(
                    {
                        "type": element.get("type"),
                        "id": element.get("id"),
                        "lat": float(lat_value),
                        "lon": float(lon_value),
                        "name": name,
                        "name_norm": normalize_text(name),
                        "tags": tags,
                    }
                )
            print(f"Overpass {store['store']}: {len(records)} named records", flush=True)
            return records
        except Exception as exc:  # noqa: BLE001
            last_error = exc
            print(f"Overpass endpoint failed: {endpoint}: {exc}", flush=True)
            time.sleep(3)
    print(f"Overpass unavailable for {store['store']}: {last_error}", flush=True)
    return []


def scalar_from(value: Any, preferred_keys: Iterable[str] = ("value", "url", "phone", "email")) -> str:
    if value is None:
        return ""
    if isinstance(value, str):
        return value.strip()
    if isinstance(value, (int, float)):
        return str(value)
    if isinstance(value, dict):
        for key in preferred_keys:
            item = value.get(key)
            if item:
                return scalar_from(item, preferred_keys)
        for item in value.values():
            candidate = scalar_from(item, preferred_keys)
            if candidate:
                return candidate
        return ""
    if isinstance(value, list):
        for item in value:
            candidate = scalar_from(item, preferred_keys)
            if candidate:
                return candidate
    return ""


def all_scalars(value: Any, preferred_keys: Iterable[str] = ("value", "url", "phone", "email")) -> list[str]:
    found: list[str] = []
    if value is None:
        return found
    if isinstance(value, str):
        if value.strip():
            found.append(value.strip())
    elif isinstance(value, dict):
        direct = False
        for key in preferred_keys:
            if key in value and value.get(key):
                found.extend(all_scalars(value.get(key), preferred_keys))
                direct = True
        if not direct:
            for item in value.values():
                found.extend(all_scalars(item, preferred_keys))
    elif isinstance(value, list):
        for item in value:
            found.extend(all_scalars(item, preferred_keys))
    elif isinstance(value, (int, float)):
        found.append(str(value))
    output: list[str] = []
    seen: set[str] = set()
    for item in found:
        key = item.lower()
        if key not in seen:
            seen.add(key)
            output.append(item)
    return output


def parse_name(properties: dict[str, Any]) -> str:
    names = properties.get("names") or {}
    if isinstance(names, dict):
        primary = names.get("primary")
        if isinstance(primary, str):
            return primary.strip()
        common = names.get("common")
        if isinstance(common, dict):
            for language in ("en", "local"):
                item = common.get(language)
                if isinstance(item, str) and item.strip():
                    return item.strip()
            for item in common.values():
                if isinstance(item, str) and item.strip():
                    return item.strip()
    return scalar_from(names, ("primary", "value"))


def parse_categories(properties: dict[str, Any]) -> tuple[str, list[str]]:
    categories = properties.get("categories") or {}
    if isinstance(categories, dict):
        primary = scalar_from(categories.get("primary"), ("value", "name"))
        alternate = all_scalars(categories.get("alternate"), ("value", "name"))
        return primary, alternate
    values = all_scalars(categories, ("value", "name"))
    return (values[0] if values else ""), values[1:]


def normalize_region(region: str) -> str:
    region = str(region or "").strip()
    if region.upper() == "GA" or region.lower() == "georgia":
        return "GA"
    return region


def choose_address(properties: dict[str, Any]) -> dict[str, str] | None:
    addresses = properties.get("addresses") or []
    if isinstance(addresses, dict):
        addresses = [addresses]
    for raw in addresses:
        if not isinstance(raw, dict):
            continue
        freeform = str(raw.get("freeform") or raw.get("address") or "").strip()
        locality = str(raw.get("locality") or raw.get("city") or "").strip()
        region = normalize_region(raw.get("region") or raw.get("state") or "")
        postcode = str(raw.get("postcode") or raw.get("postal_code") or "").strip()
        country = str(raw.get("country") or "US").strip().upper()
        if not freeform:
            continue
        lower = freeform.lower()
        if any(term in lower for term in ("p.o. box", "po box", "no physical address", "unknown road")):
            continue
        if country not in ("US", "USA", "UNITED STATES", ""):
            continue
        if region and region != "GA":
            continue
        # Reject generic locality-only values. A street-style physical address normally
        # contains a digit, a highway/route marker, or a unit number.
        street_like = bool(re.search(r"\d", freeform)) or any(
            token in lower for token in ("highway", "hwy", "route", "parkway", "pkwy", "street", "st ", "road", "rd ", "avenue", "ave ", "boulevard", "blvd", "drive", "dr ", "lane", "ln ", "way", "circle", "court")
        )
        if not street_like:
            continue
        full_parts = [freeform]
        if locality and locality.lower() not in freeform.lower():
            full_parts.append(locality)
        if region and region.lower() not in freeform.lower():
            full_parts.append(region)
        if postcode and postcode not in freeform:
            full_parts.append(postcode)
        full_address = ", ".join(part for part in full_parts if part)
        return {
            "street": freeform,
            "city": locality,
            "state": region or "GA",
            "zip": postcode[:5],
            "full_address": full_address,
        }
    return None


def category_group(primary: str, alternate: list[str]) -> str | None:
    combined = " ".join([primary, *alternate]).lower().replace("-", "_").replace(" ", "_")
    if any(term in combined for term in EXCLUDE_CATEGORY_TERMS):
        return None
    for group, terms in GROUP_RULES:
        if any(term in combined for term in terms):
            return group
    return "Other Local Employer / Organization"


def phone_is_valid(phone: str) -> bool:
    digits = re.sub(r"\D", "", phone or "")
    return 10 <= len(digits) <= 15


def email_is_valid(email: str) -> bool:
    return bool(re.fullmatch(r"[^\s@]+@[^\s@]+\.[^\s@]+", email or "", re.IGNORECASE))


def canonical_url(url: str) -> str:
    url = (url or "").strip()
    if not url:
        return ""
    if not re.match(r"^https?://", url, re.IGNORECASE):
        url = "https://" + url.lstrip("/")
    return url


def source_count(properties: dict[str, Any]) -> tuple[int, str]:
    sources = properties.get("sources") or []
    if isinstance(sources, dict):
        sources = [sources]
    datasets: set[str] = set()
    dates: list[str] = []
    for source in sources:
        if not isinstance(source, dict):
            continue
        dataset = source.get("dataset") or source.get("source") or source.get("name")
        if dataset:
            datasets.add(str(dataset))
        for key in ("update_time", "updated_at", "timestamp"):
            if source.get(key):
                dates.append(str(source[key]))
    latest = max(dates) if dates else ""
    return max(len(datasets), len(sources)), latest


def osm_grid(records: list[dict[str, Any]], cell_size: float = 0.004) -> dict[tuple[int, int], list[dict[str, Any]]]:
    grid: dict[tuple[int, int], list[dict[str, Any]]] = defaultdict(list)
    for record in records:
        key = (int(record["lat"] / cell_size), int(record["lon"] / cell_size))
        grid[key].append(record)
    return grid


def match_osm(candidate: dict[str, Any], grid: dict[tuple[int, int], list[dict[str, Any]]], cell_size: float = 0.004) -> dict[str, Any] | None:
    key = (int(candidate["lat"] / cell_size), int(candidate["lon"] / cell_size))
    best: tuple[float, dict[str, Any]] | None = None
    for dx in (-1, 0, 1):
        for dy in (-1, 0, 1):
            for record in grid.get((key[0] + dx, key[1] + dy), []):
                distance_miles = haversine_miles(candidate["lat"], candidate["lon"], record["lat"], record["lon"])
                if distance_miles > 0.20:
                    continue
                similarity = token_set_ratio(candidate["name_norm"], record["name_norm"])
                candidate_number = re.match(r"\d+", candidate.get("street", ""))
                osm_number = str(record["tags"].get("addr:housenumber") or "")
                address_bonus = 8 if candidate_number and osm_number and candidate_number.group(0) == osm_number else 0
                score = similarity + address_bonus - distance_miles * 40
                if similarity >= 72 and (best is None or score > best[0]):
                    best = (score, record)
    return best[1] if best else None


def osm_full_address(tags: dict[str, Any]) -> str:
    street = " ".join(
        str(item).strip()
        for item in (tags.get("addr:housenumber"), tags.get("addr:street"))
        if item
    )
    parts = [street, tags.get("addr:city"), tags.get("addr:state"), tags.get("addr:postcode")]
    return ", ".join(str(item).strip() for item in parts if item)


def read_overture(path: Path, stores_by_name: dict[str, dict[str, Any]], origin_store: str) -> list[dict[str, Any]]:
    candidates: list[dict[str, Any]] = []
    with path.open("r", encoding="utf-8") as handle:
        for line in handle:
            line = line.strip().lstrip("\x1e")
            if not line:
                continue
            try:
                feature = json.loads(line)
            except json.JSONDecodeError:
                continue
            geometry = feature.get("geometry") or {}
            coordinates = geometry.get("coordinates") or []
            if len(coordinates) < 2:
                continue
            lon, lat = float(coordinates[0]), float(coordinates[1])
            properties = feature.get("properties") or {}
            name = parse_name(properties)
            if not name or len(normalize_text(name)) < 3:
                continue
            address = choose_address(properties)
            if not address:
                continue
            primary_category, alternate_categories = parse_categories(properties)
            group = category_group(primary_category, alternate_categories)
            if group is None:
                continue
            distances = {
                store_name: haversine_miles(lat, lon, store["lat"], store["lon"])
                for store_name, store in stores_by_name.items()
            }
            eligible = {key: value for key, value in distances.items() if value <= RADIUS_MILES + 1e-6}
            if not eligible:
                continue
            assigned_store = min(eligible, key=eligible.get)
            distance = eligible[assigned_store]
            websites = [canonical_url(item) for item in all_scalars(properties.get("websites"), ("value", "url"))]
            websites = [item for item in websites if item]
            phones = [item for item in all_scalars(properties.get("phones"), ("value", "phone")) if phone_is_valid(item)]
            emails = [item for item in all_scalars(properties.get("emails"), ("value", "email")) if email_is_valid(item)]
            confidence_raw = properties.get("confidence")
            try:
                confidence = float(confidence_raw) if confidence_raw is not None else 0.0
            except (TypeError, ValueError):
                confidence = 0.0
            sources_n, latest_source = source_count(properties)
            candidate = {
                "overture_id": str(properties.get("id") or feature.get("id") or ""),
                "name": name.strip(),
                "name_norm": normalize_text(name),
                "category_group": group,
                "primary_category": primary_category,
                "alternate_categories": "; ".join(alternate_categories[:5]),
                **address,
                "lat": lat,
                "lon": lon,
                "assigned_store": assigned_store,
                "distance_miles": distance,
                "within_both": len(eligible) > 1,
                "phone": phones[0] if phones else "",
                "email": emails[0] if emails else "",
                "website": websites[0] if websites else "",
                "confidence": confidence,
                "source_count": sources_n,
                "latest_source_date": latest_source,
                "origin_download": origin_store,
            }
            candidates.append(candidate)
    return candidates


def preliminary_score(candidate: dict[str, Any]) -> float:
    score = float(BASE_PRIORITY.get(candidate["category_group"], 65))
    score += max(0.0, 20.0 - candidate["distance_miles"] * 2.0)
    score += 5.0 if candidate.get("phone") else 0.0
    score += 5.0 if candidate.get("website") else 0.0
    score += 7.0 if candidate.get("email") else 0.0
    score += min(candidate.get("source_count", 0), 3) * 2.0
    score += min(max(candidate.get("confidence", 0.0), 0.0), 1.0) * 8.0
    return score


def validate_website(record: dict[str, Any]) -> tuple[str, int | None, bool, str]:
    url = record.get("website") or ""
    if not url:
        return url, None, False, ""
    try:
        response = requests.get(
            url,
            headers={"User-Agent": USER_AGENT},
            timeout=8,
            allow_redirects=True,
            stream=True,
        )
        status = response.status_code
        content_type = response.headers.get("content-type", "")
        snippet = b""
        if "text/html" in content_type.lower():
            for chunk in response.iter_content(chunk_size=16384):
                snippet += chunk
                if len(snippet) >= 100000:
                    break
        text = re.sub(r"<[^>]+>", " ", snippet.decode("utf-8", errors="ignore"))
        text_norm = normalize_text(text[:100000])
        name_tokens = [token for token in record["name_norm"].split() if len(token) >= 4]
        name_match = bool(name_tokens) and sum(token in text_norm for token in name_tokens) >= max(1, min(2, len(name_tokens)))
        return response.url, status, name_match, "reachable" if status < 500 else "server_error"
    except Exception as exc:  # noqa: BLE001
        return url, None, False, type(exc).__name__


def deduplicate(candidates: list[dict[str, Any]]) -> list[dict[str, Any]]:
    # The same Overture place may appear in both overlapping downloads. Prefer the
    # record with the strongest contact and source data.
    best: dict[str, dict[str, Any]] = {}
    for candidate in candidates:
        address_key = normalize_text(candidate["street"] + " " + candidate.get("zip", ""))
        key = candidate.get("overture_id") or f"{candidate['name_norm']}|{address_key}"
        quality = preliminary_score(candidate)
        if key not in best or quality > preliminary_score(best[key]):
            best[key] = candidate
    # Secondary exact name+address dedupe catches records with duplicate IDs.
    final: dict[tuple[str, str], dict[str, Any]] = {}
    for candidate in best.values():
        key = (candidate["name_norm"], normalize_text(candidate["full_address"]))
        quality = preliminary_score(candidate)
        if key not in final or quality > preliminary_score(final[key]):
            final[key] = candidate
    return list(final.values())


def verification_status(candidate: dict[str, Any]) -> tuple[str, int]:
    if candidate.get("osm_match") and candidate.get("website_name_match"):
        return "A — cross-verified in Overture, OpenStreetMap, and official/reachable website", 3
    if candidate.get("osm_match"):
        return "A — cross-verified in Overture and OpenStreetMap", 3
    if candidate.get("website_name_match"):
        return "A — Overture record plus reachable website matching entity name", 3
    if candidate.get("confidence", 0) >= 0.90 and candidate.get("source_count", 0) >= 2:
        return "B — high-confidence Overture record with multiple source records", 2
    if candidate.get("confidence", 0) >= 0.90 and (candidate.get("phone") or candidate.get("website")):
        return "B — high-confidence Overture record with public contact data", 2
    if candidate.get("confidence", 0) >= 0.95:
        return "B — very-high-confidence Overture record with complete physical address", 2
    return "C — address-complete Overture record; manual recheck recommended", 1


def final_score(candidate: dict[str, Any]) -> float:
    score = preliminary_score(candidate)
    score += 9.0 if candidate.get("osm_match") else 0.0
    score += 8.0 if candidate.get("website_name_match") else 0.0
    score += 2.0 if candidate.get("website_status") and candidate.get("website_status") < 500 else 0.0
    score += candidate.get("verification_rank", 0) * 2.0
    return score


def select_store_records(records: list[dict[str, Any]], store: str, count: int = 250) -> list[dict[str, Any]]:
    pool = [record for record in records if record["assigned_store"] == store]
    # A/B verification first. If a store has fewer than 250, fill only from
    # very-high-confidence C records rather than inventing or using incomplete addresses.
    verified = [record for record in pool if record["verification_rank"] >= 2]
    verified.sort(key=lambda item: (-final_score(item), item["distance_miles"], item["name_norm"]))
    selected = verified[:count]
    if len(selected) < count:
        fallback = [
            record for record in pool
            if record not in selected and record.get("confidence", 0) >= 0.90
        ]
        fallback.sort(key=lambda item: (-final_score(item), item["distance_miles"], item["name_norm"]))
        selected.extend(fallback[: count - len(selected)])
    return selected


def map_url(record: dict[str, Any]) -> str:
    query = f"{record['name']}, {record['full_address']}"
    return "https://www.google.com/maps/search/?api=1&query=" + urllib.parse.quote(query)


def osm_url(match: dict[str, Any] | None) -> str:
    if not match:
        return ""
    return f"https://www.openstreetmap.org/{match['type']}/{match['id']}"


def write_outputs(selected: list[dict[str, Any]], all_candidates: list[dict[str, Any]], stores: list[dict[str, Any]]) -> None:
    selected.sort(key=lambda item: (item["assigned_store"], -final_score(item), item["distance_miles"]))
    for index, record in enumerate(selected, start=1):
        score = round(final_score(record), 1)
        record["final_score"] = score
        record["priority_tier"] = "A" if score >= 120 else "B" if score >= 105 else "C"
        record["lead_id"] = f"FH-{record['assigned_store'][:3].upper()}-{index:03d}"
        record["google_maps_url"] = map_url(record)
        record["osm_url"] = osm_url(record.get("osm_match"))
        record["contact_completeness"] = ", ".join(
            label for label, present in (
                ("phone", bool(record.get("phone"))),
                ("email", bool(record.get("email"))),
                ("website", bool(record.get("website"))),
            ) if present
        ) or "No verified public contact in source; use map/official-site research"
        record["suggested_contact_role"] = SUGGESTED_ROLE[record["category_group"]]
        record["suggested_catering_use"] = CATERING_USE[record["category_group"]]

    headers = [
        "Lead ID", "Assigned Store", "Priority Tier", "Lead Score", "Entity Name",
        "Category Group", "Primary Category", "Alternate Categories", "Full Physical Address",
        "Street Address", "City", "State", "ZIP", "Straight-Line Distance (mi)",
        "Phone (public listing)", "Email (public listing)", "Website (public listing)",
        "Website HTTP Status", "Website Name Match", "Contact Completeness",
        "Verification Status", "Overture Confidence", "Overture Source Count",
        "Latest Source Timestamp", "OSM Cross-Match", "OSM Source Link", "Overture GERS/Place ID",
        "Google Maps Search", "Latitude", "Longitude", "Within Both Service Areas",
        "Suggested Decision Maker", "Likely Catering Uses", "Outreach Status", "Last Contact",
        "Next Follow-Up", "Owner", "Quoted Amount", "Orders Won", "Revenue Won", "Notes",
    ]
    rows: list[list[Any]] = []
    for record in selected:
        rows.append([
            record["lead_id"], record["assigned_store"], record["priority_tier"], record["final_score"], record["name"],
            record["category_group"], record["primary_category"], record["alternate_categories"], record["full_address"],
            record["street"], record["city"], record["state"], record["zip"], round(record["distance_miles"], 2),
            record.get("phone", ""), record.get("email", ""), record.get("website", ""),
            record.get("website_status") or "", "Yes" if record.get("website_name_match") else "No", record["contact_completeness"],
            record["verification_status"], round(record.get("confidence", 0.0), 3), record.get("source_count", 0),
            record.get("latest_source_date", ""), "Yes" if record.get("osm_match") else "No", record["osm_url"], record.get("overture_id", ""),
            record["google_maps_url"], round(record["lat"], 7), round(record["lon"], 7), "Yes" if record.get("within_both") else "No",
            record["suggested_contact_role"], record["suggested_catering_use"], "Not contacted", "", "", "", "", 0, 0, "",
        ])
    with (OUTPUT_DIR / "verified_leads.csv").open("w", newline="", encoding="utf-8-sig") as handle:
        writer = csv.writer(handle)
        writer.writerow(headers)
        writer.writerows(rows)

    # Store-specific and top-100 CSVs make inspection and import recovery easier.
    for store in ("Woodstock", "Tucker"):
        with (OUTPUT_DIR / f"{store.lower()}_leads.csv").open("w", newline="", encoding="utf-8-sig") as handle:
            writer = csv.writer(handle)
            writer.writerow(headers)
            writer.writerows(row for row in rows if row[1] == store)
    top_rows: list[list[Any]] = []
    for store in ("Woodstock", "Tucker"):
        store_rows = [row for row in rows if row[1] == store]
        top_rows.extend(sorted(store_rows, key=lambda row: (-float(row[3]), float(row[13])))[:50])
    with (OUTPUT_DIR / "top_100.csv").open("w", newline="", encoding="utf-8-sig") as handle:
        writer = csv.writer(handle)
        writer.writerow(headers)
        writer.writerows(top_rows)

    counts_by_store = defaultdict(int)
    counts_by_group = defaultdict(int)
    verification_counts = defaultdict(int)
    contact_counts = {"phone": 0, "email": 0, "website": 0}
    for record in selected:
        counts_by_store[record["assigned_store"]] += 1
        counts_by_group[record["category_group"]] += 1
        verification_counts[record["verification_status"]] += 1
        for field in contact_counts:
            if record.get(field):
                contact_counts[field] += 1
    summary = {
        "generated_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "selected_total": len(selected),
        "candidate_total_after_address_and_radius_filters": len(all_candidates),
        "counts_by_store": dict(counts_by_store),
        "counts_by_category_group": dict(sorted(counts_by_group.items(), key=lambda item: (-item[1], item[0]))),
        "verification_counts": dict(verification_counts),
        "contact_counts": contact_counts,
        "radius_miles": RADIUS_MILES,
        "distance_method": "Haversine straight-line distance from geocoded restaurant coordinates",
        "contact_rule": "Phone/email/website copied only from Overture or matched OpenStreetMap public listing; never inferred",
        "address_rule": "Complete physical street-style address required; PO boxes and missing/generic addresses excluded",
        "source_urls": [
            "https://docs.overturemaps.org/guides/places/",
            "https://docs.overturemaps.org/getting-data/overturemaps-py/",
            "https://www.openstreetmap.org/",
            "https://nominatim.org/release-docs/latest/api/Search/",
        ],
        "stores": stores,
    }
    (OUTPUT_DIR / "summary.json").write_text(json.dumps(summary, indent=2), encoding="utf-8")


def main() -> None:
    for store in STORES:
        lat, lon, display_name = geocode(store["address"])
        store.update({"lat": lat, "lon": lon, "geocoder_display_name": display_name})
        print(f"{store['store']} geocoded to {lat:.7f}, {lon:.7f}: {display_name}", flush=True)
        time.sleep(1.1)

    stores_by_name = {store["store"]: store for store in STORES}
    overture_paths: dict[str, Path] = {}
    osm_records_by_store: dict[str, list[dict[str, Any]]] = {}
    for store in STORES:
        overture_paths[store["store"]] = run_overture_download(store)
        osm_records_by_store[store["store"]] = fetch_overpass(store)

    candidates: list[dict[str, Any]] = []
    for store_name, path in overture_paths.items():
        candidates.extend(read_overture(path, stores_by_name, store_name))
    candidates = deduplicate(candidates)
    print(f"Address-complete, in-radius, non-dining candidates: {len(candidates)}", flush=True)

    grids = {store: osm_grid(records) for store, records in osm_records_by_store.items()}
    for candidate in candidates:
        match = match_osm(candidate, grids.get(candidate["assigned_store"], {}))
        candidate["osm_match"] = match
        if match:
            tags = match.get("tags") or {}
            if not candidate.get("phone"):
                phone = tags.get("phone") or tags.get("contact:phone")
                if phone and phone_is_valid(str(phone)):
                    candidate["phone"] = str(phone)
            if not candidate.get("email"):
                email_value = tags.get("email") or tags.get("contact:email")
                if email_value and email_is_valid(str(email_value)):
                    candidate["email"] = str(email_value)
            if not candidate.get("website"):
                candidate["website"] = canonical_url(tags.get("website") or tags.get("contact:website") or "")

    # Validate public websites for the strongest candidate pool. This improves
    # verification without allowing a slow/broken site to delete an otherwise
    # cross-verified real entity.
    validation_pool: list[dict[str, Any]] = []
    for store in ("Woodstock", "Tucker"):
        store_pool = [candidate for candidate in candidates if candidate["assigned_store"] == store]
        store_pool.sort(key=lambda item: (-preliminary_score(item), item["distance_miles"]))
        validation_pool.extend([candidate for candidate in store_pool[:500] if candidate.get("website")])
    unique_by_url: dict[str, dict[str, Any]] = {}
    for candidate in validation_pool:
        unique_by_url.setdefault(candidate["website"], candidate)
    results_by_url: dict[str, tuple[str, int | None, bool, str]] = {}
    with ThreadPoolExecutor(max_workers=24) as executor:
        futures = {executor.submit(validate_website, record): url for url, record in unique_by_url.items()}
        for future in as_completed(futures):
            url = futures[future]
            try:
                results_by_url[url] = future.result()
            except Exception as exc:  # noqa: BLE001
                results_by_url[url] = (url, None, False, type(exc).__name__)
    for candidate in candidates:
        result = results_by_url.get(candidate.get("website", ""))
        if result:
            final_url, status, name_match, note = result
            candidate["website"] = final_url
            candidate["website_status"] = status
            candidate["website_name_match"] = name_match
            candidate["website_check_note"] = note
        else:
            candidate["website_status"] = None
            candidate["website_name_match"] = False
            candidate["website_check_note"] = "not_checked"
        status_text, rank = verification_status(candidate)
        candidate["verification_status"] = status_text
        candidate["verification_rank"] = rank

    woodstock = select_store_records(candidates, "Woodstock", 250)
    tucker = select_store_records(candidates, "Tucker", 250)
    selected = woodstock + tucker
    if len(woodstock) < 250 or len(tucker) < 250:
        raise RuntimeError(
            f"Not enough address-complete records after validation: Woodstock={len(woodstock)}, Tucker={len(tucker)}"
        )
    write_outputs(selected, candidates, STORES)
    print(f"Wrote {len(selected)} verified physical-address leads", flush=True)


if __name__ == "__main__":
    try:
        main()
    except Exception as exc:  # noqa: BLE001
        print(f"FATAL: {type(exc).__name__}: {exc}", file=sys.stderr, flush=True)
        raise
