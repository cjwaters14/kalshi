"""
Combined Runner — Weather Forecast + Market Consensus
======================================================
Runs weather forecasts AND market implied distribution analysis,
only placing bets when BOTH signals agree a range is safe.

This eliminates false positives like the Denver scenario where weather
said 70°F but the market had already priced consensus at 76°F — meaning
a "65 or below" NO looked safe by weather but dangerous by market.

Decision logic:
    weather_safe  = range is WEATHER_BUFFER°F+ from weather forecast
    market_safe   = range is MARKET_BUFFER°F+ from market consensus
    bet only if   = weather_safe AND market_safe AND both point same direction

Confidence tiers (determines bet sizing):
    STRONG  (both signals agree, market is tight)  → BET_SIZE × 1.5
    NORMAL  (both agree, market moderate)          → BET_SIZE × 1.0
    WEAK    (marginal agreement)                   → BET_SIZE × 0.5  (or skip)

Run via GitHub Actions every 30min 10am–3pm ET on weekdays.
Run locally:   python combined_runner.py
"""

import os
import re
import uuid
import json
import base64
import requests
from datetime import datetime, date
from pathlib import Path
from zoneinfo import ZoneInfo
from urllib.parse import urlparse
from cryptography.hazmat.primitives import hashes, serialization
from cryptography.hazmat.primitives.asymmetric import padding as asym_padding

# ── CREDENTIALS ───────────────────────────────────────────────────────────────

KALSHI_PRIVATE_KEY = os.environ.get("KALSHI_PRIVATE_KEY", """""")
KALSHI_API_KEY_ID  = os.environ.get("KALSHI_API_KEY_ID",  "")
KALSHI_BASE_URL    = "https://api.elections.kalshi.com/trade-api/v2"

# ── CONFIG ────────────────────────────────────────────────────────────────────

WEATHER_BUFFER    = 4      # °F from weather forecast to qualify (raised from 5)
MARKET_BUFFER     = 4      # °F from market consensus to qualify (raised from 5)
ASK_MIN           = 75     # min NO ask in cents
ASK_MAX           = 99     # max NO ask in cents
OUTLIER_MAX_DELTA = 10     # °F — drop weather source if this far from median
MIN_SOURCES       = 2      # min weather sources needed
MAX_MKT_SPREAD    = 10.0   # °F — skip city if market is too uncertain
SKIP_WEAK_BETS    = True   # set False to include weak-confidence bets

# ── POSITION CONCENTRATION LIMITS ────────────────────────────────────────────
MAX_BETS_PER_CITY = 2      # never buy more than this many NO positions in one city
                            # prevents buying both sides of the distribution
PICK_ONE_SIDE     = True   # only bet on ranges above OR below consensus, not both
                            # e.g. if consensus is 72°F, only bet ABOVE or BELOW it
MIN_YES_PROB_GAP  = 5      # skip any range where YES probability > this %
                            # (market is too uncertain about that range to safely bet NO)
                            # e.g. 72-73° at 14% YES → skip

DAILY_SPEND_CAP  = float(os.environ.get("DAILY_SPEND_CAP",  "50"))
BET_SIZE_DOLLARS = float(os.environ.get("BET_SIZE_DOLLARS", "5"))
SPEND_STATE_FILE = Path(os.environ.get("SPEND_STATE_FILE",  "spend_state.json"))
FORECAST_LOG_FILE= Path(os.environ.get("FORECAST_LOG_FILE", "forecast_log.json"))

# ── DATE ──────────────────────────────────────────────────────────────────────

_raw = os.environ.get("KALSHI_DATE")
if _raw:
    KALSHI_DATE = _raw.upper()
    TODAY       = datetime.strptime(KALSHI_DATE, "%y%b%d").strftime("%Y-%m-%d")
else:
    _et         = datetime.now(ZoneInfo("America/New_York"))
    KALSHI_DATE = _et.strftime("%y%b%d").upper()
    TODAY       = _et.strftime("%Y-%m-%d")

# ── CITY CONFIG ───────────────────────────────────────────────────────────────

CITIES = [
    {"name": "New York (Central Park)", "kalshi_ticker": f"KXHIGHNY-{KALSHI_DATE}",
     "lat": 40.7829,  "lon": -73.9654, "tz": "America/New_York",    "peak_hour": 15},
    {"name": "Dallas/Fort Worth",       "kalshi_ticker": f"KXHIGHTDAL-{KALSHI_DATE}",
     "lat": 32.8998,  "lon": -97.0403, "tz": "America/Chicago",     "peak_hour": 15},
    {"name": "Minneapolis",             "kalshi_ticker": f"KXHIGHTMIN-{KALSHI_DATE}",
     "lat": 44.8820,  "lon": -93.2218, "tz": "America/Chicago",     "peak_hour": 15},
    {"name": "Boston",                  "kalshi_ticker": f"KXHIGHTBOS-{KALSHI_DATE}",
     "lat": 42.3631,  "lon": -71.0064, "tz": "America/New_York",    "peak_hour": 14},
    {"name": "Las Vegas",               "kalshi_ticker": f"KXHIGHTLV-{KALSHI_DATE}",
     "lat": 36.0840,  "lon": -115.1537,"tz": "America/Los_Angeles", "peak_hour": 15},
    {"name": "Washington DC",           "kalshi_ticker": f"KXHIGHTDC-{KALSHI_DATE}",
     "lat": 38.8521,  "lon": -77.0377, "tz": "America/New_York",    "peak_hour": 15},
    {"name": "Atlanta",                 "kalshi_ticker": f"KXHIGHTATL-{KALSHI_DATE}",
     "lat": 33.6407,  "lon": -84.4277, "tz": "America/New_York",    "peak_hour": 15},
    {"name": "San Antonio",             "kalshi_ticker": f"KXHIGHTSATX-{KALSHI_DATE}",
     "lat": 29.5341,  "lon": -98.4698, "tz": "America/Chicago",     "peak_hour": 15},
    {"name": "Seattle",                 "kalshi_ticker": f"KXHIGHTSEA-{KALSHI_DATE}",
     "lat": 47.4502,  "lon": -122.3088,"tz": "America/Los_Angeles", "peak_hour": 15},
    {"name": "New Orleans",             "kalshi_ticker": f"KXHIGHTNOLA-{KALSHI_DATE}",
     "lat": 29.9934,  "lon": -90.2580, "tz": "America/Chicago",     "peak_hour": 15},
    {"name": "Phoenix",                 "kalshi_ticker": f"KXHIGHTPHX-{KALSHI_DATE}",
     "lat": 33.4373,  "lon": -112.0078,"tz": "America/Phoenix",     "peak_hour": 15},
    {"name": "San Francisco",           "kalshi_ticker": f"KXHIGHTSFO-{KALSHI_DATE}",
     "lat": 37.6213,  "lon": -122.3790,"tz": "America/Los_Angeles", "peak_hour": 16},
]

NWS_HEADERS = {"User-Agent": "kalshi-combined-runner"}

# ── KALSHI AUTH ───────────────────────────────────────────────────────────────

def load_private_key():
    return serialization.load_pem_private_key(
        KALSHI_PRIVATE_KEY.encode("utf-8"), password=None
    )

def _kalshi_request(method, path, key, params=None, payload=None):
    full_url  = f"{KALSHI_BASE_URL}{path}"
    sign_path = urlparse(full_url).path.split("?")[0]
    timestamp = str(int(datetime.now().timestamp() * 1000))
    message   = f"{timestamp}{method}{sign_path}".encode("utf-8")
    sig = key.sign(message, asym_padding.PSS(
        mgf=asym_padding.MGF1(hashes.SHA256()),
        salt_length=asym_padding.PSS.DIGEST_LENGTH,
    ), hashes.SHA256())
    headers = {
        "KALSHI-ACCESS-KEY":       KALSHI_API_KEY_ID,
        "KALSHI-ACCESS-TIMESTAMP": timestamp,
        "KALSHI-ACCESS-SIGNATURE": base64.b64encode(sig).decode(),
        "Content-Type":            "application/json",
    }
    if method == "GET":
        r = requests.get(full_url, headers=headers, params=params, timeout=15)
    else:
        r = requests.post(full_url, headers=headers, json=payload, timeout=15)
    r.raise_for_status()
    return r.json()

def kalshi_get(path, key, params=None):
    return _kalshi_request("GET", path, key, params=params)

def kalshi_post(path, key, payload):
    return _kalshi_request("POST", path, key, payload=payload)

# ── SPEND STATE ───────────────────────────────────────────────────────────────

def load_spend_state():
    today = date.today().isoformat()
    if SPEND_STATE_FILE.exists():
        try:
            s = json.loads(SPEND_STATE_FILE.read_text())
            if s.get("date") == today:
                return s
        except Exception:
            pass
    return {"date": today, "spent": 0.0, "orders": []}

def save_spend_state(state):
    SPEND_STATE_FILE.write_text(json.dumps(state, indent=2))

def record_spend(state, ticker, dollars):
    state["spent"] = round(state["spent"] + dollars, 2)
    state["orders"].append({"ticker": ticker, "dollars": dollars,
                             "time": datetime.now().isoformat(), "source": "combined_runner"})
    save_spend_state(state)

def already_ordered(state, ticker):
    return any(o["ticker"] == ticker for o in state.get("orders", []))

# ── WEATHER SOURCES ───────────────────────────────────────────────────────────

def get_openmeteo_high(lat, lon):
    import time as _t
    for attempt in range(3):
        try:
            resp = requests.get(
                "https://api.open-meteo.com/v1/forecast",
                params={"latitude": lat, "longitude": lon,
                        "daily": "temperature_2m_max", "temperature_unit": "fahrenheit",
                        "forecast_days": 1, "timezone": "auto"},
                timeout=20,
            )
            resp.raise_for_status()
            val = resp.json()["daily"]["temperature_2m_max"][0]
            return float(val) if val and 30 < float(val) < 130 else None
        except Exception as e:
            if attempt < 2:
                _t.sleep(3)
            else:
                print(f"    [Open-Meteo] Failed: {e}")
    return None

def get_nws_high(lat, lon, city):
    try:
        if "nws_forecast_url" not in city:
            r = requests.get(f"https://api.weather.gov/points/{lat},{lon}",
                             headers=NWS_HEADERS, timeout=20)
            r.raise_for_status()
            city["nws_forecast_url"] = r.json()["properties"]["forecast"]
        r = requests.get(city["nws_forecast_url"], headers=NWS_HEADERS, timeout=20)
        r.raise_for_status()
        for p in r.json()["properties"]["periods"]:
            name = (p.get("name") or "").lower()
            if not p.get("isDaytime") or any(w in name for w in ("night","overnight","evening")):
                continue
            temp = p.get("temperature")
            if temp is None:
                continue
            val = float(temp)
            if (p.get("temperatureUnit","F").upper() == "C"):
                val = val * 9/5 + 32
            if 30 < val < 130:
                return val
    except Exception as e:
        print(f"    [NWS] Error: {e}")
    return None

def get_weather_forecast(city):
    """Fetch from both API sources, drop outliers, return average + sources dict."""
    readings = {}
    val = get_openmeteo_high(city["lat"], city["lon"])
    if val:
        readings["Open-Meteo"] = val
    val = get_nws_high(city["lat"], city["lon"], city)
    if val:
        readings["NWS"] = val

    if not readings:
        return None, {}

    vals   = sorted(readings.values())
    median = (vals[len(vals)//2] + vals[(len(vals)-1)//2]) / 2
    clean  = {k: v for k, v in readings.items() if abs(v - median) <= OUTLIER_MAX_DELTA}

    if len(clean) < 1:
        return None, {}

    avg = sum(clean.values()) / len(clean)
    return round(avg, 1), clean

# ── MARKET ANALYSIS ───────────────────────────────────────────────────────────

def parse_range(title):
    t = title.strip().lower()
    m = re.search(r"(\d+)\s*[°]?\s*(?:to|-)\s*(\d+)", t)
    if m:
        lo, hi = float(m.group(1)), float(m.group(2))
        return lo, hi, (lo+hi)/2
    m = re.search(r"(\d+)\s*[°]?\s*(or above|and above|\+|or more)", t)
    if m:
        lo = float(m.group(1))
        return lo, None, lo+2
    m = re.search(r"(\d+)\s*[°]?\s*(or below|and below|or less)", t)
    if m:
        hi = float(m.group(1))
        return None, hi, hi-2
    return None, None, 0.0

def get_market_consensus(markets):
    """Build implied distribution from YES prices, return consensus + spread."""
    legs = []
    for mkt in markets:
        title = (mkt.get("yes_sub_title") or mkt.get("subtitle") or mkt.get("title") or "").strip()
        lo, hi, mid = parse_range(title)
        if lo is None and hi is None:
            continue
        yes_ask = mkt.get("yes_ask") or float(mkt.get("yes_ask_dollars") or 0) * 100
        yes_bid = mkt.get("yes_bid") or float(mkt.get("yes_bid_dollars") or 0) * 100
        no_ask  = mkt.get("no_ask")  or float(mkt.get("no_ask_dollars")  or 0) * 100
        yes_mid = (yes_ask + yes_bid) / 2 if (yes_ask and yes_bid) else (yes_ask or yes_bid or 0)
        legs.append({"title": title, "ticker": mkt.get("ticker",""),
                     "lo": lo, "hi": hi, "mid": mid,
                     "yes_mid": yes_mid, "no_ask": int(no_ask) if no_ask else None})

    if not legs:
        return None, None, []

    total = sum(l["yes_mid"] for l in legs)
    if total <= 0:
        return None, None, legs

    consensus = sum(l["mid"] * l["yes_mid"] for l in legs) / total
    variance  = sum(l["yes_mid"] * (l["mid"] - consensus)**2 for l in legs) / total
    spread    = variance ** 0.5

    return round(consensus, 1), round(spread, 1), legs

# ── COMBINED DECISION ─────────────────────────────────────────────────────────

def evaluate_bet(leg, weather_fc, weather_rounded, mkt_consensus,
                 local_hour, peak_hour):
    """
    Return a confidence tier and bet recommendation, or None if not a bet.

    Tiers:
        STRONG — both signals agree by ≥ their respective buffers, market is tight
        NORMAL — both signals agree by their buffers
        WEAK   — one signal marginal (bet half size or skip)
        SKIP   — fails one or both signals
    """
    mid      = leg["mid"]
    no_ask   = leg["no_ask"]

    if not no_ask or not (ASK_MIN <= no_ask <= ASK_MAX):
        return None

    # Distance from each signal — use raw float, not rounded integer
    weather_dist = abs(mid - weather_fc)
    market_dist  = abs(mid - mkt_consensus)

    # Time-of-day adjustment: widen buffer earlier in the day
    hours_to_peak = max(0, peak_hour - local_hour)
    time_adj      = round(hours_to_peak * 0.4, 1)
    eff_weather_buf = WEATHER_BUFFER + time_adj
    eff_market_buf  = MARKET_BUFFER  + time_adj

    weather_safe = weather_dist >= eff_weather_buf
    market_safe  = market_dist  >= eff_market_buf

    # Both must agree on the same direction
    weather_dir = "below" if mid < weather_rounded else "above"
    market_dir  = "below" if mid < mkt_consensus   else "above"
    same_dir    = (weather_dir == market_dir)

    if not (weather_safe and market_safe and same_dir):
        # Check for weak: one signal marginal
        if weather_safe and market_dist >= eff_market_buf * 0.7 and same_dir:
            tier = "WEAK"
        elif market_safe and weather_dist >= eff_weather_buf * 0.7 and same_dir:
            tier = "WEAK"
        else:
            return None
    else:
        # Both safe — determine strength by combined margin and market tightness
        combined_margin = min(weather_dist - eff_weather_buf,
                              market_dist  - eff_market_buf)
        tier = "STRONG" if combined_margin >= 2.0 else "NORMAL"

    return {
        "tier"           : tier,
        "weather_fc"     : weather_fc,
        "weather_rounded": weather_rounded,
        "mkt_consensus"  : mkt_consensus,
        "weather_dist"   : round(weather_dist, 1),
        "market_dist"    : round(market_dist, 1),
        "eff_buffer"     : round(eff_weather_buf, 1),
        "time_adj"       : round(time_adj, 1),
        "hours_to_peak"  : round(hours_to_peak, 1),
        "same_dir"       : same_dir,
        "direction"      : weather_dir,
    }

def tier_multiplier(tier):
    return {"STRONG": 1.5, "NORMAL": 1.0, "WEAK": 0.5}.get(tier, 0)

# ── FORECAST LOG ──────────────────────────────────────────────────────────────

def save_forecast_log(city, forecast_f, sources):
    log = {}
    if FORECAST_LOG_FILE.exists():
        try:
            log = json.loads(FORECAST_LOG_FILE.read_text())
        except Exception:
            pass
    if TODAY not in log:
        log[TODAY] = {}
    existing = len((log[TODAY].get(city["name"]) or {}).get("sources", {}))
    if len(sources) >= existing:
        log[TODAY][city["name"]] = {
            "date": TODAY, "city": city["name"],
            "kalshi_ticker": city["kalshi_ticker"],
            "forecast_f": round(forecast_f, 1),
            "sources": {k: round(v, 1) for k, v in sources.items()},
            "source_count": len(sources),
            "logged_at": datetime.now().isoformat(),
        }
        FORECAST_LOG_FILE.write_text(json.dumps(log, indent=2))

# ── MAIN ──────────────────────────────────────────────────────────────────────

def main():
    print("\n" + "=" * 70)
    print("  COMBINED RUNNER — WEATHER + MARKET CONSENSUS")
    print(f"  Date       : {TODAY}  ({KALSHI_DATE})")
    print(f"  Run time   : {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
    print(f"  Weather buf: ±{WEATHER_BUFFER}°F  |  Market buf: ±{MARKET_BUFFER}°F")
    print(f"  Spend cap  : ${DAILY_SPEND_CAP:.2f}  |  Bet size: ${BET_SIZE_DOLLARS:.2f}")
    print("=" * 70 + "\n")

    key         = load_private_key()
    spend_state = load_spend_state()
    now_utc     = datetime.now(ZoneInfo("UTC"))
    all_bets    = []

    print(f"  Spent today: ${spend_state['spent']:.2f} / ${DAILY_SPEND_CAP:.2f}\n")
    if spend_state["spent"] >= DAILY_SPEND_CAP:
        print("  Daily cap reached — exiting.")
        return

    for city in CITIES:
        ticker = city["kalshi_ticker"]
        if ticker.startswith("TODO-"):
            continue

        tz         = ZoneInfo(city["tz"])
        local_now  = now_utc.astimezone(tz)
        local_hour = local_now.hour + local_now.minute / 60.0
        hours_left = max(0, city["peak_hour"] - local_hour)

        print(f"\n{'─' * 70}")
        print(f"  {city['name']}  |  {local_now.strftime('%H:%M')} local  "
              f"|  ~{hours_left:.1f}h to peak")
        print(f"{'─' * 70}")

        # ── Step 1: Weather forecast ──────────────────────────────────────────
        weather_fc, sources = get_weather_forecast(city)
        if weather_fc is None:
            print("  Weather: no sources available — skipping.")
            continue
        weather_rounded = round(weather_fc)
        src_str = "  ".join(f"{k}={v:.0f}°F" for k, v in sources.items())
        print(f"  Weather  : {weather_fc:.1f}°F  [{src_str}]")
        save_forecast_log(city, weather_fc, sources)

        # ── Step 2: Fetch markets ─────────────────────────────────────────────
        try:
            markets = []
            cursor  = None
            while True:
                params = {"event_ticker": ticker, "limit": 100}
                if cursor:
                    params["cursor"] = cursor
                data   = kalshi_get("/markets", key, params)
                batch  = data.get("markets", [])
                markets.extend(batch)
                cursor = data.get("cursor")
                if not cursor or not batch:
                    break
        except Exception as e:
            print(f"  Markets : fetch failed ({e}) — skipping.")
            continue

        # ── Step 3: Market consensus ──────────────────────────────────────────
        mkt_consensus, mkt_spread, legs = get_market_consensus(markets)
        if mkt_consensus is None:
            print("  Market  : could not build consensus — skipping.")
            continue

        # Flag if market is too uncertain
        if mkt_spread and mkt_spread > MAX_MKT_SPREAD:
            print(f"  Market  : consensus {mkt_consensus:.1f}°F  "
                  f"spread {mkt_spread:.1f}°F  ⚠️  wide — lower confidence")
        else:
            print(f"  Market  : consensus {mkt_consensus:.1f}°F  "
                  f"spread {mkt_spread:.1f}°F")

        # ── Step 4: Agreement check ───────────────────────────────────────────
        signal_gap = abs(weather_fc - mkt_consensus)
        if signal_gap > 5:
            print(f"  ⚠️  Signals diverge by {signal_gap:.1f}°F  "
                  f"(weather {weather_fc:.1f}°F vs market {mkt_consensus:.1f}°F) — "
                  f"market consensus takes precedence")
        else:
            print(f"  ✓  Signals agree within {signal_gap:.1f}°F")

        # ── Step 5: Evaluate each leg ─────────────────────────────────────────
        city_bets = []
        for leg in legs:
            eval_result = evaluate_bet(
                leg, weather_fc, weather_rounded, mkt_consensus,
                local_hour, city["peak_hour"]
            )
            if eval_result is None:
                continue
            if eval_result["tier"] == "WEAK" and SKIP_WEAK_BETS:
                continue

            city_bets.append({**leg, **eval_result})

        if city_bets:
            city_bets.sort(key=lambda b: (
                {"STRONG": 3, "NORMAL": 2, "WEAK": 1}[b["tier"]],
                b["market_dist"] + b["weather_dist"]
            ), reverse=True)

            # ── Filter 1: drop any range where market YES prob > MIN_YES_PROB_GAP
            # These are ranges the market is genuinely uncertain about
            before = len(city_bets)
            city_bets = [b for b in city_bets if b.get("yes_mid", 100) <= MIN_YES_PROB_GAP]
            if len(city_bets) < before:
                dropped = before - len(city_bets)
                print(f"  Dropped {dropped} bet(s) where market YES% > {MIN_YES_PROB_GAP}%")

            # ── Filter 2: pick one side — only bet above OR below consensus
            if PICK_ONE_SIDE and city_bets:
                above = [b for b in city_bets if b["mid"] > mkt_consensus]
                below = [b for b in city_bets if b["mid"] < mkt_consensus]
                if above and below:
                    # Pick the side with the best single bet (highest score)
                    best_above = max(above, key=lambda b: b["market_dist"] + b["weather_dist"])
                    best_below = max(below, key=lambda b: b["market_dist"] + b["weather_dist"])
                    if (best_above["market_dist"] + best_above["weather_dist"] >=
                        best_below["market_dist"] + best_below["weather_dist"]):
                        chosen_side, rejected_side = "ABOVE", below
                        city_bets = above
                    else:
                        chosen_side, rejected_side = "BELOW", above
                        city_bets = below
                    print(f"  Pick-one-side: betting {chosen_side} consensus "
                          f"({len(rejected_side)} opposite-side bet(s) removed)")

            # ── Filter 3: max bets per city
            if len(city_bets) > MAX_BETS_PER_CITY:
                city_bets = city_bets[:MAX_BETS_PER_CITY]
                print(f"  Capped at {MAX_BETS_PER_CITY} bet(s) per city")

            for b in city_bets:
                side = "ABOVE" if b["mid"] > mkt_consensus else "BELOW"
                print(f"  [{b['tier']:6}] BUY NO  {b['title']:<22}  "
                      f"{b['no_ask']}¢  "
                      f"({b['mid']:.0f}° vs weather {b['weather_fc']:.1f}° = {b['weather_dist']:.1f}°  "
                      f"market {b['mkt_consensus']:.1f}° = {b['market_dist']:.1f}°) [{side}]")
            all_bets.extend([{**b, "city": city["name"], "ticker_base": ticker}
                              for b in city_bets])
        else:
            print(f"  No qualifying bets (weather {weather_fc:.1f}°F, "
                  f"market {mkt_consensus:.1f}°F).")

    # ── ORDER PLACEMENT ───────────────────────────────────────────────────────
    print("\n\n" + "=" * 70)
    print("  ORDER PLACEMENT")
    print("=" * 70 + "\n")

    # Sort all bets: STRONG first, then by combined distance
    all_bets.sort(key=lambda b: (
        {"STRONG": 3, "NORMAL": 2, "WEAK": 1}[b["tier"]],
        b["market_dist"] + b["weather_dist"]
    ), reverse=True)

    orders_placed = 0
    for bet in all_bets:
        if spend_state["spent"] >= DAILY_SPEND_CAP:
            print("  Daily cap reached — stopping.")
            break

        ticker = bet["ticker"]
        if already_ordered(spend_state, ticker):
            print(f"  SKIP  {ticker}  — already ordered today")
            continue

        mult        = tier_multiplier(bet["tier"])
        bet_dollars = round(BET_SIZE_DOLLARS * mult, 2)
        contracts   = max(1, int((bet_dollars * 100) / bet["no_ask"]))
        actual_cost = round((contracts * bet["no_ask"]) / 100, 2)

        if spend_state["spent"] + actual_cost > DAILY_SPEND_CAP:
            print(f"  SKIP  {ticker}  — would exceed daily cap")
            continue

        print(f"  [{bet['tier']:6}] {bet['title']:<22}  {ticker}")
        print(f"           {bet['no_ask']}¢  ×{contracts}  = ${actual_cost:.2f}  "
              f"(weather {bet['weather_dist']:.1f}°, market {bet['market_dist']:.1f}° from consensus)")

        try:
            result = kalshi_post("/portfolio/orders", key, {
                "ticker"          : ticker,
                "action"          : "buy",
                "side"            : "no",
                "type"            : "limit",
                "count_fp"        : f"{contracts}.00",
                "no_price_dollars": f"{bet['no_ask'] / 100:.4f}",
                "client_order_id" : str(uuid.uuid4()),
            })
            order_id = result.get("order", {}).get("order_id", "unknown")
            record_spend(spend_state, ticker, actual_cost)
            orders_placed += 1
            print(f"           ✓ ORDER PLACED  [id: {order_id}]")
        except Exception as e:
            print(f"           ✗ Order failed: {e}")

    # ── SUMMARY ───────────────────────────────────────────────────────────────
    print(f"\n{'=' * 70}")
    print(f"  Run complete  |  Orders placed: {orders_placed}")
    print(f"  Spent today  : ${spend_state['spent']:.2f} / ${DAILY_SPEND_CAP:.2f}")

    if all_bets:
        strong = [b for b in all_bets if b["tier"] == "STRONG"]
        normal = [b for b in all_bets if b["tier"] == "NORMAL"]
        weak   = [b for b in all_bets if b["tier"] == "WEAK"]
        print(f"  Signal tiers : {len(strong)} STRONG  {len(normal)} NORMAL  {len(weak)} WEAK")
    print("=" * 70 + "\n")


if __name__ == "__main__":
    main()
