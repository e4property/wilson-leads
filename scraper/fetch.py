"""
Wilson County TX Motivated Seller Lead Scraper v1.0
County: Wilson (Floresville, TX — San Antonio-adjacent)
Source: wilson.tx.publicsearch.us — FC department (Foreclosure notices)
Platform: same PublicSearch/GovOS platform as bexar-leads/nueces-leads.

v1.0 scope: NOTICE OF FORECLOSURE only. Deliberately skips the
Appointment-of-Substitute-Trustee (pre-foreclosure) source for now --
Bexar's own APPT-to-NOF conversion rate came back at 9.3% (7/75 resolved
leads), and there's no outcome-tracking yet to prove pre-fore outreach on
Bexar converts to contracts either. Not worth porting a second parallel
pipeline to a new county before that's answered. Also skips owner
enrichment via county appraisal data -- Wilson CAD's data export/API
hasn't been researched yet, same "data first, enrich after" path Nueces
itself took. Every mechanism below (URL construction, date-range handling,
wait-selector, pagination) is already proven correct against Bexar/Nueces
today -- built in from the start here instead of needing the same fixes
found the hard way later.

GHL tags: wilson_lead
"""

import json
import logging
import re
import time
import urllib.parse
from datetime import datetime, timedelta, timezone
from pathlib import Path

from selenium import webdriver
from selenium.webdriver.chrome.options import Options
from selenium.webdriver.common.by import By
from selenium.webdriver.support.ui import WebDriverWait
from selenium.webdriver.support import expected_conditions as EC

logging.basicConfig(level=logging.INFO, format="%(asctime)s [%(levelname)s] %(message)s")
log = logging.getLogger(__name__)

PUBLICSEARCH_BASE = "https://wilson.tx.publicsearch.us"
RECORDS_PATH = Path("dashboard/records.json")

TODAY = datetime.now(timezone.utc)
SCRAPE_DAYS = 365  # wide initial window for the first backfill run

# ── On-market status via HomeHarvest (free, Realtor.com, no Selenium) ──────
ON_MARKET_STATUSES     = {"FOR_SALE", "PENDING", "FOR_RENT"}
ON_MARKET_FETCH_LIMIT   = 15  # max never-checked leads to look up per run
ON_MARKET_REFRESH_DAYS  = 7   # re-check a lead's status at most this often
ON_MARKET_REFRESH_LIMIT = 10  # max already-checked leads to re-check per run

# Wilson's doc numbers are "YYYY-NNN" (e.g. "2020-38"), not the pure
# 7-10 digit numeric format Bexar/Nueces use -- confirmed live 2026-08-26.
DOC_NUM_RE = re.compile(r"^\d{4}-\d+$")
DATE_RE = re.compile(r"^\d{1,2}/\d{1,2}/\d{4}$")

# ── Owner enrichment via Wilson CAD (owner comes from the FC department's
# own results table only when a personal grantor happens to be readable
# there -- confirmed live 2026-09-13 this platform's FC table carries no
# grantor/grantee columns at all, same limitation Bexar's FC table has
# (see bexar-leads/scraper/fetch.py's own comment on this), so every
# record here starts with owner="". Wilson CAD's own eSearch portal
# (esearch.wilson-cad.org, BIS Consultants platform) supports owner-by-
# address lookup and is confirmed live to work -- see
# lookup_owner_by_address() below for the two real quirks found getting
# it to actually fire.
WILSON_CAD_URL = "https://esearch.wilson-cad.org/"

ENTITY_KEYWORDS = [
    "LLC", "LLP", "LTD", "L.L.C", "LP", "FSB", "INC", "CORP", "CORPORATION",
    "MORTGAGE", "BANK", "N.A.", "NA", "TRUST", "TRUSTEE", "SERVICES",
    "SERVICING", "FINANCIAL", "FINANCE", "ASSOCIATION", "FEDERAL",
    "SAVINGS", "SOCIETY", "HOLDINGS", "CAPITAL", "FUNDING", "FUND",
    "PARTNERS", "GROUP", "COMPANY", "CO", "PROPERTIES", "DEVELOPMENTS",
    "INVESTMENTS", "CREDIT UNION", "HOUSING",
]


def is_entity_name(name):
    if not name:
        return True
    upper = name.upper()
    return any(re.search(r"\b" + re.escape(kw) + r"\b", upper) for kw in ENTITY_KEYWORDS)


def looks_like_personal_name(name):
    if not name:
        return False
    if any(ch.isdigit() for ch in name):
        return False
    if "," in name or ":" in name:
        return False
    words = name.split()
    if len(words) < 2 or len(name) > 45:
        return False
    return True


STREET_SUFFIXES = {
    "ST", "STREET", "AVE", "AVENUE", "DR", "DRIVE", "LN", "LANE", "RD", "ROAD",
    "CT", "COURT", "BLVD", "BOULEVARD", "WAY", "CV", "COVE", "TRL", "TRAIL",
    "PL", "PLACE", "LOOP", "CIR", "CIRCLE", "PKWY", "PARKWAY", "HWY", "HIGHWAY",
    "XING", "CROSSING", "PASS", "RUN", "BND", "BEND", "PT", "POINT", "TER",
    "TERRACE", "SQ", "SQUARE", "WALK", "PATH", "ROW", "GLEN", "HOLW", "HOLLOW",
    "VLY", "VALLEY", "RIDGE", "RDG", "MDWS", "MEADOWS", "CRK", "CREEK", "GRV",
    "GROVE", "HL", "HILL", "HLS", "HILLS", "PARK", "LNDG", "LANDING", "SHRS",
    "SHORES", "ESTS", "ESTATES", "VW", "VIEW", "FRST", "FOREST", "SPGS",
    "SPRINGS", "BLF", "BLUFF", "GDNS", "GARDENS", "PLZ", "PLAZA",
}
DIRECTIONALS = {"N", "S", "E", "W", "NE", "NW", "SE", "SW"}


def parse_street_number_name(address):
    """
    Extract (street_number, street_name_no_suffix) from a raw scraped
    address cell, matching Wilson CAD's own eSearch form instruction
    ("No Prefix, suffix, or Unit Numbers"). e.g. "701 LIVE OAK DR,
    ADKINS, TEXAS, 78101" -> ("701", "LIVE OAK") -- confirmed live this
    exact parse against this exact address returns a single, correct
    CAD match.
    """
    if not address:
        return "", ""
    head = address.split(",")[0].strip().upper()
    parts = head.split()
    if not parts or not re.match(r"^\d+[A-Z]?$", parts[0]):
        return "", ""
    number = parts[0]
    rest = parts[1:]
    if rest and rest[0] in DIRECTIONALS:
        rest = rest[1:]
    if rest and rest[-1] in STREET_SUFFIXES:
        rest = rest[:-1]
    return number, " ".join(rest).strip()


def lookup_owner_by_address(driver, street_number, street_name, timeout=20):
    """
    Wilson CAD's eSearch portal (BIS Consultants platform). Two real
    quirks found getting this to actually fire, confirmed live
    2026-09-13:
    1. The Advanced-search inputs only carry the `name` attribute the
       page's own JS (getSearchCriteria()) reads once the "Advanced" tab
       link has been clicked -- setting values before that lands on
       inputs the search silently ignores.
    2. The site's executeSearch() bails out with no error and no console
       output unless a real `mousemove` event has already fired on the
       page (`if (!hasMovedMouse) { alert(...); return; }` in its own
       source) -- a plain value-set + calling AdvancedSearch() does
       nothing at all without this.
    Only accepts a match when exactly one property matched (same "no
    owner shown is better than a wrong owner shown" rule used
    elsewhere) -- common street names can return several properties.
    Returns "" on no match, ambiguous match, or any failure.
    """
    from selenium.webdriver.support.ui import WebDriverWait

    try:
        driver.get(WILSON_CAD_URL)
        time.sleep(2)
        driver.execute_script(
            "const a = Array.from(document.querySelectorAll('a'))"
            ".find(a => a.textContent.trim() === 'Advanced'); if (a) a.click();"
        )
        time.sleep(1)
        driver.execute_script(
            """
            function setVal(el, value) {
                const setter = Object.getOwnPropertyDescriptor(window.HTMLInputElement.prototype, 'value').set;
                setter.call(el, value);
                el.dispatchEvent(new Event('input', {bubbles: true}));
                el.dispatchEvent(new Event('change', {bubbles: true}));
            }
            const sn = document.querySelector('input[name="StreetNumber"]');
            const snm = document.querySelector('input[name="StreetName"]');
            if (sn) setVal(sn, arguments[0]);
            if (snm) setVal(snm, arguments[1]);
            document.dispatchEvent(new MouseEvent('mousemove', {bubbles: true, clientX: 100, clientY: 100}));
            """,
            street_number, street_name,
        )
        time.sleep(0.5)
        driver.execute_script("if (typeof AdvancedSearch === 'function') AdvancedSearch();")
        WebDriverWait(driver, timeout).until(lambda d: "/search/result" in d.current_url)
        time.sleep(1.5)
    except Exception as e:
        log.debug(f"  CAD lookup failed for {street_number} {street_name}: {e}")
        return ""

    try:
        rows = driver.execute_script(
            """
            const table = document.querySelector('table');
            if (!table) return [];
            return Array.from(table.querySelectorAll('tbody tr'))
                .filter(tr => tr.querySelectorAll('td').length > 0)
                .map(tr => Array.from(tr.querySelectorAll('td')).map(td => td.innerText.trim()));
            """
        ) or []
    except Exception:
        return ""

    if len(rows) != 1:
        return ""
    # Header confirmed live: Property ID, Year, Geo ID, Nbrhd. Code, Type,
    # Owner Name, Owner ID, Situs Address, ... -- Owner Name is index 5.
    row = rows[0]
    return row[5].strip() if len(row) > 5 else ""


def enrich_owners(records, driver):
    """
    Runs lookup_owner_by_address() for records with a real address but
    no owner (every record, currently -- see the module comment above).
    """
    candidates = [
        r for r in records
        if not (r.get("owner") or "").strip() and (r.get("address") or "").strip()
    ]
    if not candidates:
        return records

    log.info(f"Owner enrichment: {len(candidates)} candidates")
    found = 0
    for rec in candidates:
        number, name = parse_street_number_name(rec["address"])
        if not number or not name:
            continue
        owner = lookup_owner_by_address(driver, number, name)
        if owner and not is_entity_name(owner) and looks_like_personal_name(owner):
            rec["owner"] = owner.title()
            found += 1
            log.info(f"  [{rec['doc_number']}] owner: -> {rec['owner']!r}")
        elif owner:
            # A real CAD match, just not a personal name (e.g. an LLC that
            # bought the property) -- record it plainly rather than
            # silently dropping real, if uninteresting, data.
            rec["owner"] = owner.title()
        time.sleep(1)
    log.info(f"Owner enrichment: {found}/{len(candidates)} personal names found")
    return records


def get_driver():
    opts = Options()
    opts.add_argument("--headless=new")
    opts.add_argument("--no-sandbox")
    opts.add_argument("--disable-dev-shm-usage")
    opts.add_argument("--disable-gpu")
    opts.add_argument("--window-size=1280,900")
    opts.add_argument(
        "user-agent=Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
        "(KHTML, like Gecko) Chrome/128.0.0.0 Safari/537.36"
    )
    return webdriver.Chrome(options=opts)


def new_record(doc_number, lead_type, run_ts):
    return {
        "doc_number": doc_number,
        "county": "wilson",
        "type": lead_type,
        "source": "publicsearch",
        "owner": "",
        "address": "",
        "city": "",
        "zip": "",
        "date_filed": "",
        "sale_date": "",
        "days_until_sale": None,
        "legal_desc": "",
        "score": 0,
        "run_ts": run_ts,
        "is_new": True,
        "duplicate": False,
        "ghl_tag": "wilson_lead",
        "dash_phone": "",
        "dash_dispo": "new",
        "dash_notes": "",
        "ghl_pushed": False,
        "ghl_id": "",
    }


def scrape_foreclosures(known_docs, driver, run_ts, days=None):
    """
    FC department, pure listing (no searchType/searchValue) -- the ONLY
    mechanism confirmed to actually work on this platform for a
    document-type-scoped department (live-verified against Bexar and
    Nueces 2026-08-25/26: quickSearch+searchValue never matches anything
    once a department is scoped this way). instrumentDateRange has no
    "Certified through" lag the way recordedDateRange does, so the end
    bound can safely extend past today.
    """
    window = days if days is not None else SCRAPE_DAYS
    cutoff = (TODAY - timedelta(days=window)).strftime("%Y%m%d")
    # 2026-08-28: instrumentDateRange started returning inconsistent/
    # incomplete results for this department -- confirmed the identical bug
    # live in bexar-leads and nueces-leads (same PublicSearch platform).
    # Switched to recordedDateRange, the field actually proven to still
    # work. No need to extend the end date into the future anymore --
    # recorded dates are never forward-dated (unlike sale dates).
    end_str = TODAY.strftime("%Y%m%d")
    offset = 0
    consecutive_empty = 0
    new_records = []
    page_num = 0
    # 2026-09-08: ported from bexar-leads after its equivalent loop hung
    # 1.5+ hours with no absolute page cap -- this loop has the identical
    # shape (same PublicSearch platform, same heuristic-only break
    # conditions) and the same gap. Cheap insurance even though this
    # specific county hasn't hung yet.
    MAX_PAGES = 30

    log.info("Scraping FC/Foreclosures...")

    while True:
        page_num += 1
        if page_num > MAX_PAGES:
            log.warning(f"  Hit MAX_PAGES={MAX_PAGES} — stopping, rest deferred to next run")
            break
        url = (
            f"{PUBLICSEARCH_BASE}/results"
            f"?department=FC"
            f"&recordedDateRange={cutoff}%2C{end_str}"
            f"&keywordSearch=false"
            f"&limit=50"
            f"&offset={offset}"
            f"&sort=desc"
            f"&sortBy=recordedDate"
            f"&searchType=advancedSearch"
        )
        log.info(f"  offset={offset}")

        try:
            driver.get(url)
            # No-results pages render an <h1> with a build-hashed CSS class
            # (e.g. "css-z524vz", changes per deploy) -- never a stable
            # ".no-results" class name. Match on the visible text instead,
            # confirmed live 2026-08-25/26 this is why class-based waits
            # spun for the full timeout on every zero-match page.
            WebDriverWait(driver, 30).until(
                EC.presence_of_element_located(
                    (By.XPATH, "//table//tr/td | //h1[contains(text(),'No Results')]")
                )
            )
            time.sleep(2)
        except Exception as e:
            log.warning(f"  Timeout offset={offset}: {e}")
            consecutive_empty += 1
            if consecutive_empty >= 2:
                break
            time.sleep(5)
            continue

        src = driver.page_source
        # 2026-08-28: `"no results" in src.lower()` is a substring match
        # against the ENTIRE raw page source, not a scoped element check --
        # confirmed the exact same bug live in bexar-leads, silently
        # dropping real leads while reporting success. Only trust "no
        # results" if there's truly no data row AND a genuine No-Results
        # heading is present.
        rows = re.findall(r"<tr[^>]*>(.*?)</tr>", src, re.DOTALL | re.IGNORECASE)
        data_rows_present = any(
            not re.search(r"<th|thead|DOC.TYPE|RECORDED|SALE.DATE|PROPERTY", row, re.IGNORECASE)
            for row in rows
        )
        if not data_rows_present:
            if driver.find_elements(By.XPATH, "//h1[contains(text(),'No Results')]"):
                log.info("  No results — stopping")
                break
            time.sleep(3)
            src = driver.page_source
            rows = re.findall(r"<tr[^>]*>(.*?)</tr>", src, re.DOTALL | re.IGNORECASE)

        page_recs = []
        data_row_count = 0

        for row in rows:
            if re.search(r"<th|thead|DOC.TYPE|RECORDED|SALE.DATE|PROPERTY", row, re.IGNORECASE):
                continue
            cells = re.findall(r"<td[^>]*>(.*?)</td>", row, re.DOTALL)
            cells = [re.sub(r"<[^>]+>", "", c).strip() for c in cells if c.strip()]
            if len(cells) < 4:
                continue

            doc_number = next((c for c in cells if DOC_NUM_RE.match(c)), "")
            if not doc_number:
                continue
            data_row_count += 1
            if doc_number in known_docs:
                continue

            dates = [c for c in cells if DATE_RE.match(c)]
            recorded_date = dates[0] if dates else ""
            sale_date = dates[1] if len(dates) >= 2 else ""

            # Property Address column: real street address when the notice
            # states one, otherwise a legal description (lot/block/acreage)
            # -- both land in the same cell, confirmed live 2026-08-26.
            addr_cell = ""
            for c in cells:
                if re.match(r"^\d+\.?\d*\s+[A-Z]", c.upper()) and "N/A" not in c.upper():
                    addr_cell = c
                    break

            legal_desc = ""
            for c in cells:
                if re.search(r"\b(LOTS?|LTS?|BLOCKS?|BLK|ACRES?|SURVEY|SUBDIVISION|SUBD|TRACT)\b", c, re.IGNORECASE):
                    legal_desc = c.upper()
                    break

            month, year = "", ""
            if recorded_date:
                parts = recorded_date.split("/")
                if len(parts) == 3:
                    month, year = parts[0], parts[2]

            rec = new_record(doc_number, "NOF", run_ts)
            rec["date_filed"] = f"{month}/{year}".strip("/")
            rec["sale_date"] = sale_date
            rec["legal_desc"] = legal_desc
            if addr_cell:
                rec["address"] = addr_cell.strip()
                m = re.search(r",\s*([A-Z ]+),\s*TEXAS,\s*(\d{5})", addr_cell.upper())
                if m:
                    rec["city"] = m.group(1).strip().title()
                    rec["zip"] = m.group(2)

            page_recs.append(rec)

        log.info(f"  offset={offset} | {len(page_recs)} new on page ({data_row_count} total rows)")
        for rec in page_recs:
            known_docs.add(rec["doc_number"])
            new_records.append(rec)

        consecutive_empty = 0 if data_row_count else consecutive_empty + 1
        if consecutive_empty >= 2 or 0 < data_row_count < 50:
            break
        offset += 50
        time.sleep(1.5)

    log.info(f"FC/Foreclosures: {len(new_records)} new records")
    return new_records


def auction_passed(sale_date_str):
    # 2026-09-01: was comparing against TODAY (UTC, the GitHub Actions
    # runner's clock) and a date vs a full datetime -- confirmed live in
    # bexar-leads this purged 418 leads (158 already in Jarvis) the
    # instant UTC crossed midnight into a sale date, hours before that
    # date even started in Central time, let alone before the actual
    # auction (which runs mid-morning to afternoon). Compare Central-time
    # calendar dates only, so a lead isn't purged until the day AFTER
    # its auction.
    if not sale_date_str:
        return False
    try:
        from zoneinfo import ZoneInfo
        m, d, y = sale_date_str.strip().split("/")
        today_central = datetime.now(ZoneInfo("America/Chicago")).date()
        return datetime(int(y), int(m), int(d)).date() < today_central
    except Exception:
        return False


def too_soon_to_work(sale_date_str, threshold_days=5):
    if not sale_date_str:
        return False
    try:
        m, d, y = sale_date_str.strip().split("/")
        dt = datetime(int(y), int(m), int(d))
        days_until = (dt - TODAY.replace(tzinfo=None)).days
        return 0 <= days_until <= threshold_days
    except Exception:
        return False


def purge_past_auctions(records):
    kept = []
    for rec in records:
        if rec.get("ghl_pushed") or rec.get("dash_phone"):
            kept.append(rec)
            continue
        sd = rec.get("sale_date", "")
        if sd and (auction_passed(sd) or too_soon_to_work(sd)):
            continue
        kept.append(rec)
    removed = len(records) - len(kept)
    if removed:
        log.info(f"Purged {removed} past-auction/too-soon leads")
    return kept


def score_record(rec):
    s = 5
    if rec.get("address"):
        s += 3
    sd = rec.get("sale_date")
    if sd:
        s += 2
    return min(s, 10)


def days_until_sale(sale_date_str):
    if not sale_date_str:
        return None
    try:
        m, d, y = sale_date_str.strip().split("/")
        return (datetime(int(y), int(m), int(d)) - TODAY.replace(tzinfo=None)).days
    except Exception:
        return None


def dedup(existing, new_recs):
    seen = {r["doc_number"]: r for r in existing}
    added = 0
    for rec in new_recs:
        if rec["doc_number"] not in seen:
            seen[rec["doc_number"]] = rec
            added += 1
    log.info(f"Dedup: {added} genuinely new of {len(new_recs)} scraped")
    return list(seen.values())


STREET_SUFFIX_WORDS = {
    "ST", "STREET", "DR", "DRIVE", "RD", "ROAD", "AVE", "AVENUE", "LN", "LANE",
    "CT", "COURT", "BLVD", "BOULEVARD", "WAY", "CIR", "CIRCLE", "TRL", "TRAIL",
    "PL", "PLACE", "PKWY", "PARKWAY", "LOOP", "RUN", "PASS", "XING", "CROSSING",
    "COVE", "BND", "BEND", "VW", "VIEW", "HOLW", "HOLLOW", "RDG", "RIDGE",
    "MDW", "MDWS", "MEADOW", "MEADOWS", "GLN", "GLEN", "HL", "HILL", "HLS",
    "HILLS", "PT", "POINT", "SQ", "SQUARE", "TER", "TERRACE", "WALK", "GRV",
    "GROVE", "VLY", "VALLEY", "N", "S", "E", "W", "NE", "NW", "SE", "SW",
}


def _street_core_tokens(street):
    """Uppercase, strip punctuation, drop directional/suffix words -- leaves
    just the house number + distinctive name word(s) so a county record's
    abbreviated form compares cleanly against Realtor.com's own formatting.
    `street` may be a pandas NA sentinel (from a DataFrame row), not just
    None -- `pd.NA or ""` raises 'boolean value of NA is ambiguous', so
    str() first."""
    street = str(street) if street is not None else ""
    if street in ("nan", "<NA>", "None"):
        street = ""
    s = re.sub(r"[^A-Z0-9 ]", " ", street.upper())
    return [t for t in s.split() if t not in STREET_SUFFIX_WORDS]


def address_matches(searched_addr, searched_zip, row_street, row_zip):
    """
    Verify a HomeHarvest/Realtor.com search result actually corresponds to
    the property we searched for, before trusting its on-market status.

    2026-09-22: confirmed live (bexar-leads) that scrape_property(location=
    ...) silently returns its best guess even when nothing real matches --
    "214 MUNIZ, SAN ANTONIO, TX 78223" returned an unrelated FOR_RENT
    listing miles away, and "22965 N ADDISON, SAN ANTONIO, TX" matched a
    property in Quinque, VIRGINIA (the parser read the house number as a
    zip code). Built this in from the start here rather than the same gap
    Bexar/Nueces/Travis had to find and fix the hard way. Require the
    house number to match exactly, at least one distinctive street-name
    word to overlap, and zip to match when both sides have one.
    """
    searched_tokens = _street_core_tokens(searched_addr)
    row_tokens = _street_core_tokens(row_street)
    if not searched_tokens or not row_tokens:
        return False
    searched_num = searched_tokens[0] if searched_tokens[0].isdigit() else None
    row_num = row_tokens[0] if row_tokens[0].isdigit() else None
    if not searched_num or searched_num != row_num:
        return False
    if not (set(searched_tokens[1:]) & set(row_tokens[1:])):
        return False
    sz = str(searched_zip) if searched_zip is not None else ""
    rz = str(row_zip) if row_zip is not None else ""
    sz = "" if sz in ("nan", "<NA>", "None") else sz.strip()[:5]
    rz = "" if rz in ("nan", "<NA>", "None") else rz.strip()[:5]
    if sz and rz and sz != rz:
        return False
    return True


def _first_matching_row(df, searched_addr, searched_zip):
    """Scan every row HomeHarvest returned (not just the first) for one that
    actually verifies against the searched address. Returns None if none do
    -- callers must treat that exactly like 'no results'."""
    for _, row in df.iterrows():
        if address_matches(searched_addr, searched_zip, row.get("street"), row.get("zip_code")):
            return row
    return None


def fetch_on_market_status(records):
    """
    Flags leads that are already listed for sale/rent elsewhere, using
    homeharvest (pip, MIT license) against Realtor.com's public page data --
    no API key, no cost, no Selenium driver needed (does its own HTTP).
    Ported from nueces-leads, address-verification fix included from day 1
    (see address_matches()).

    Soft dependency: any failure (network, no match, library error) just
    leaves on_market unset for that lead rather than breaking the run.
    Two passes: never-checked leads first (ON_MARKET_FETCH_LIMIT), then a
    refresh of already-checked leads older than ON_MARKET_REFRESH_DAYS
    (ON_MARKET_REFRESH_LIMIT) -- a lead can get listed by someone else
    weeks after we first looked, so a one-time check isn't enough.
    """
    import pandas as pd
    from homeharvest import scrape_property

    def clean(val):
        if val is None or pd.isna(val):
            return None
        s = str(val).strip()
        return None if s in ("", "nan", "<NA>", "None") else val

    cutoff = datetime.now(timezone.utc) - timedelta(days=ON_MARKET_REFRESH_DAYS)

    def needs_refresh(r):
        checked_at = r.get("on_market_checked_at")
        if not checked_at:
            return True
        try:
            return datetime.strptime(checked_at, "%Y-%m-%dT%H:%M:%SZ").replace(tzinfo=timezone.utc) < cutoff
        except Exception:
            return True

    never_checked = [r for r in records if r.get("address") and not r.get("on_market_checked_at")]
    stale_checked = [r for r in records if r.get("address") and r.get("on_market_checked_at") and needs_refresh(r)]

    candidates = never_checked[:ON_MARKET_FETCH_LIMIT] + stale_checked[:ON_MARKET_REFRESH_LIMIT]

    if not candidates:
        log.info("On-market: no eligible leads — skipping")
        return records

    log.info(f"On-market: {len(never_checked[:ON_MARKET_FETCH_LIMIT])} new + "
             f"{len(stale_checked[:ON_MARKET_REFRESH_LIMIT])} refresh "
             f"(caps={ON_MARKET_FETCH_LIMIT}/{ON_MARKET_REFRESH_LIMIT})")
    changed = 0
    errors = 0

    for rec in candidates:
        full_addr = f"{rec['address']}, {rec.get('city', '')}, TX {rec.get('zip', '')}".strip(", ")
        try:
            df = scrape_property(location=full_addr)
            now_iso = datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
            was_on_market = bool(rec.get("on_market"))

            if df is None or len(df) == 0:
                rec["on_market_checked_at"] = now_iso
                continue

            row = _first_matching_row(df, rec["address"], rec.get("zip"))
            if row is None:
                log.info(f"  On-market [{rec.get('doc_number')}] {full_addr}: "
                         f"{len(df)} result(s) returned but none verified against this address -- treating as no match")
                rec["on_market_checked_at"] = now_iso
                continue

            status = clean(row.get("status")) or ""
            rec["on_market"]            = status in ON_MARKET_STATUSES
            rec["on_market_status"]     = status
            rec["on_market_checked_at"] = now_iso

            if rec["on_market"] != was_on_market:
                changed += 1
                log.info(f"  On-market [{rec.get('doc_number')}] {full_addr}: "
                         f"{was_on_market} -> {rec['on_market']} (status={status})")
        except Exception as e:
            log.warning(f"  On-market [{rec.get('doc_number')}] {full_addr}: error: {e}")
            errors += 1
        finally:
            time.sleep(1)

    log.info(f"On-market: {changed} status changes, {errors} errors out of {len(candidates)} candidates")
    return records


def main():
    run_ts = TODAY.isoformat()
    existing = []
    if RECORDS_PATH.exists():
        existing = json.loads(RECORDS_PATH.read_text(encoding="utf-8"))
    log.info(f"Loaded {len(existing)} existing records")

    known_docs = {r["doc_number"] for r in existing}

    driver = get_driver()
    try:
        new_recs = scrape_foreclosures(known_docs, driver, run_ts)
        all_records = dedup(existing, new_recs)
        all_records = enrich_owners(all_records, driver)
    finally:
        driver.quit()

    all_records = purge_past_auctions(all_records)

    try:
        all_records = fetch_on_market_status(all_records)
    except Exception as e:
        log.warning(f"On-market status error: {e}")

    for rec in all_records:
        rec["score"] = score_record(rec)
        rec["days_until_sale"] = days_until_sale(rec.get("sale_date", ""))

    RECORDS_PATH.parent.mkdir(parents=True, exist_ok=True)
    RECORDS_PATH.write_text(
        json.dumps(all_records, ensure_ascii=True, separators=(",", ":")),
        encoding="utf-8",
    )
    log.info(f"Saved {len(all_records)} records to {RECORDS_PATH}")


if __name__ == "__main__":
    main()
