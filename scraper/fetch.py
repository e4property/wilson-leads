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

# Wilson's doc numbers are "YYYY-NNN" (e.g. "2020-38"), not the pure
# 7-10 digit numeric format Bexar/Nueces use -- confirmed live 2026-08-26.
DOC_NUM_RE = re.compile(r"^\d{4}-\d+$")
DATE_RE = re.compile(r"^\d{1,2}/\d{1,2}/\d{4}$")


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
    end_str = (TODAY + timedelta(days=45)).strftime("%Y%m%d")
    offset = 0
    consecutive_empty = 0
    new_records = []

    log.info("Scraping FC/Foreclosures...")

    while True:
        url = (
            f"{PUBLICSEARCH_BASE}/results"
            f"?department=FC"
            f"&instrumentDateRange={cutoff}%2C{end_str}"
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
        if "no results" in src.lower():
            log.info("  No results — stopping")
            break

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
    if not sale_date_str:
        return False
    try:
        m, d, y = sale_date_str.strip().split("/")
        return datetime(int(y), int(m), int(d)) < TODAY.replace(tzinfo=None)
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
    finally:
        driver.quit()

    all_records = dedup(existing, new_recs)
    all_records = purge_past_auctions(all_records)

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
