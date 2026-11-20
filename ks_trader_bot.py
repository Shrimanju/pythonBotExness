#!/usr/bin/env python3
"""KS Trader Desk -> Exness Trading API (demo-only, Entry 1 LIMIT execution; human-readable CMD messages).
Daily risk capital is captured from the current Exness balance at the first bot run of each IST day and then frozen for that day.

Strategy ported from the user's supplied Indie v5 indicator for its 1-minute
chart configuration. No market-order fallback, no add-on entries, no order expiry.
Adaptive hybrid trailing: M1, three-candle confirmation, swing + ATR + candle reaction + EMA/ADX.
"""
from __future__ import annotations

import base64
import hashlib
import json
import logging
import math
import os
import re
import sqlite3
import sys
import time
import uuid
from dataclasses import dataclass, replace
from datetime import datetime, timedelta, timezone
from zoneinfo import ZoneInfo
from decimal import Decimal, InvalidOperation, ROUND_HALF_UP
from pathlib import Path
from typing import Any
from urllib.parse import urlencode, urlparse

import pandas as pd
import requests
from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PrivateKey
from cryptography.hazmat.primitives.serialization import load_pem_private_key
from dotenv import load_dotenv
from decimal import Decimal
APP_VERSION = "1.7.4"
UTC = timezone.utc
IST = ZoneInfo("Asia/Kolkata")



def env_bool(name: str, default: bool = False) -> bool:
    raw = os.getenv(name)
    if raw is None:
        return default
    return raw.strip().lower() in {"1", "true", "yes", "y", "on"}


def b64url(raw: bytes) -> str:
    return base64.urlsafe_b64encode(raw).decode("ascii").rstrip("=")


def utc_iso(dt: datetime) -> str:
    return dt.astimezone(UTC).isoformat(timespec="seconds").replace("+00:00", "Z")


def dec(value: Any) -> Decimal:
    return Decimal(str(value))


def configure_logging(log_level: str) -> None:
    """Keep CMD messages simple while retaining full technical diagnostics in the log file."""
    root = logging.getLogger()
    root.handlers.clear()
    root.setLevel(logging.DEBUG)

    console = logging.StreamHandler(sys.stdout)
    configured_level = getattr(logging, log_level, logging.INFO)
    console.setLevel(max(logging.INFO, configured_level))
    console.setFormatter(logging.Formatter("%(asctime)s | %(message)s", datefmt="%H:%M:%S"))

    details = logging.FileHandler("ks_trader_bot.log", encoding="utf-8")
    details.setLevel(logging.DEBUG)
    details.setFormatter(logging.Formatter("%(asctime)s %(levelname)s %(message)s"))

    root.addHandler(console)
    root.addHandler(details)


class APIHTTPError(RuntimeError):
    def __init__(self, status_code: int, payload: Any):
        self.status_code = status_code
        self.payload = payload
        super().__init__(f"Exness API HTTP {status_code}: {payload}")


class UncertainPostError(RuntimeError):
    """POST outcome is unknown; the caller must reconcile and must not retry."""


@dataclass
class Config:
    api_key: str
    secret_key: str
    account_id: str
    gateway_url: str
    instrument: str
    account_mode: str
    trading_enabled: bool
    account_capital: float
    risk_percent: float
    risk_buffer_percent: float
    contract_size: float
    risk_reward: str
    poll_seconds: int
    db_path: str
    log_level: str
    candles_count: int

    @classmethod
    def from_env(cls) -> "Config":
        load_dotenv()
        cfg = cls(
            api_key=os.getenv("EXN_API_KEY", "").strip(),
            secret_key=os.getenv("EXN_SECRET_KEY", "").strip(),
            account_id=os.getenv("EXN_ACCOUNT_ID", "").strip(),
            gateway_url=os.getenv("EXN_GATEWAY_URL", "").strip().rstrip("/"),
            instrument=os.getenv("EXN_INSTRUMENT", "XAUUSD").strip(),
            account_mode=os.getenv("EXN_ACCOUNT_MODE", "demo").strip().lower(),
            trading_enabled=env_bool("TRADING_ENABLED", False),
            account_capital=float(os.getenv("ACCOUNT_CAPITAL", "1000.0")),
            risk_percent=float(os.getenv("RISK_PERCENT", "5.0")),
            risk_buffer_percent=float(os.getenv("RISK_BUFFER_PERCENT", "2.0")),
            contract_size=float(os.getenv("CONTRACT_SIZE", "100.0")),
            risk_reward=os.getenv("RISK_REWARD", "1:2").strip(),
            poll_seconds=int(os.getenv("POLL_SECONDS", "5")),
            db_path=os.getenv("STATE_DB", "ks_trader_state.sqlite3"),
            log_level=os.getenv("LOG_LEVEL", "INFO").upper(),
            candles_count=int(os.getenv("CANDLES_COUNT", "600")),
        )
        missing = [k for k, v in {
            "EXN_API_KEY": cfg.api_key,
            "EXN_SECRET_KEY": cfg.secret_key,
            "EXN_ACCOUNT_ID": cfg.account_id,
            "EXN_GATEWAY_URL": cfg.gateway_url,
        }.items() if not v]
        if missing:
            raise ValueError("Missing required .env values: " + ", ".join(missing))
        if not re.fullmatch(r"\d{1,20}", cfg.account_id):
            raise ValueError("EXN_ACCOUNT_ID must be the numeric Exness trading account ID.")
        if cfg.account_mode != "demo":
            raise ValueError("This build is demo-only. Set EXN_ACCOUNT_MODE=demo.")
        if cfg.risk_reward not in {"1:1", "1:1.5", "1:2", "1:3", "1:4"}:
            raise ValueError("RISK_REWARD must be one of 1:1, 1:1.5, 1:2, 1:3, 1:4.")
        if not (5.0 <= cfg.risk_percent <= 5.0):
            raise ValueError("RISK_PERCENT is the normal risk target and must be 5.0.")
        if not (0.0 <= cfg.risk_buffer_percent <= 2.0):
            raise ValueError("RISK_BUFFER_PERCENT must be between 0.0 and 2.0.")
        if cfg.risk_percent + cfg.risk_buffer_percent > 7.0:
            raise ValueError("Normal risk plus buffer cannot exceed the 7.0% maximum.")
        if not all(math.isfinite(x) for x in (cfg.account_capital, cfg.risk_percent, cfg.risk_buffer_percent, cfg.contract_size)):
            raise ValueError("ACCOUNT_CAPITAL, RISK_PERCENT, RISK_BUFFER_PERCENT and CONTRACT_SIZE must be finite numbers.")
        if cfg.account_capital < 1 or cfg.contract_size < 1:
            raise ValueError("ACCOUNT_CAPITAL and CONTRACT_SIZE must be positive.")
        if not (1 <= cfg.poll_seconds <= 60):
            raise ValueError("POLL_SECONDS must be between 1 and 60.")
        if not (300 <= cfg.candles_count <= 1500):
            raise ValueError("CANDLES_COUNT must be between 300 and 1500.")
        if len(cfg.secret_key) == 128 and re.fullmatch(r"[0-9a-fA-F]{128}", cfg.secret_key):
            pass
        elif "BEGIN PRIVATE KEY" in cfg.secret_key:
            pass
        else:
            raise ValueError("EXN_SECRET_KEY must be the 128-character hex Ed25519 private key or PKCS#8 PEM.")
        return cfg


class ExnessAPI:
    def __init__(self, cfg: Config):
        self.cfg = cfg
        self.session = requests.Session()
        self.session.headers.update({"User-Agent": f"KS-Trader-Desk/{APP_VERSION}", "Accept": "application/json"})
        self.private_key = self._load_private_key(cfg.secret_key)
        self.access_point: str | None = None

    @staticmethod
    def _load_private_key(raw: str) -> Ed25519PrivateKey:
        if "BEGIN PRIVATE KEY" in raw:
            key = load_pem_private_key(raw.encode(), password=None)
            if not isinstance(key, Ed25519PrivateKey):
                raise ValueError("The PEM key is not Ed25519.")
            return key
        key_bytes = bytes.fromhex(raw)
        if len(key_bytes) != 64:
            raise ValueError("Exness-generated Ed25519 key must decode to 64 bytes.")
        # Exness-generated 128-hex format = 32-byte seed + 32-byte public key.
        return Ed25519PrivateKey.from_private_bytes(key_bytes[:32])

    def _headers(self, method: str, path_query: str, body: bytes = b"", idem: str = "") -> dict[str, str]:
        timestamp = int(time.time() * 1000)
        body_hash = b64url(hashlib.sha256(body).digest())
        payload = {
            "api_key": self.cfg.api_key,
            "idempotency_key": idem,
            "timestamp": timestamp,
            "sign_version": 1,
            "method": method.upper(),
            "path": path_query,
            "body_hash": body_hash,
        }
        # Exness signs the compact JSON bytes, then base64url-encodes those same bytes.
        payload_bytes = json.dumps(payload, separators=(",", ":"), ensure_ascii=False).encode("utf-8")
        signature = self.private_key.sign(payload_bytes)
        return {
            "EXN-API-KEY": self.cfg.api_key,
            "EXN-IDEMPOTENCY-KEY": idem,
            "EXN-TIMESTAMP": str(timestamp),
            "EXN-SIGN-VERSION": "1",
            "EXN-DATA": b64url(payload_bytes),
            "EXN-SIGN": b64url(signature),
        }

    def request(self, method: str, path_query: str, body_obj: dict | None = None, *, gateway: bool = False, idem: str | None = None) -> dict:
        method = method.upper()
        body = b"" if body_obj is None else json.dumps(body_obj, separators=(",", ":"), ensure_ascii=False).encode("utf-8")
        # GET requests are safe to retry. Mutating requests are deliberately
        # sent once only: a timeout may occur after the broker accepted the order.
        idempotency = (idem or "") if method == "GET" else (idem or uuid.uuid4().hex)
        base = self.cfg.gateway_url if gateway else (self.access_point or "")
        if not base:
            raise RuntimeError("Exness account Access Point has not been resolved.")

        max_attempts = 4 if method == "GET" else 1
        last_error: Exception | None = None
        for attempt in range(max_attempts):
            headers = self._headers(method, path_query, body, idempotency)
            if body_obj is not None:
                headers["Content-Type"] = "application/json"
            try:
                response = self.session.request(
                    method, base + path_query,
                    data=body if body_obj is not None else None,
                    headers=headers, timeout=(5, 45), allow_redirects=False,
                )
            except requests.RequestException as exc:
                last_error = exc
                if method != "GET":
                    raise UncertainPostError(
                        "Mutating request transport failed; broker acceptance is unknown. "
                        "Do not retry blindly. Reconcile the account snapshot first."
                    ) from exc
                if attempt + 1 >= max_attempts:
                    raise
                delay = min(2 ** attempt, 8)
                logging.warning("Connection to Exness was interrupted. Retrying in %d second(s) (%d of %d).", delay, attempt + 1, max_attempts)
                logging.debug("GET transport error details: %r", exc)
                time.sleep(delay)
                continue

            try:
                data = response.json() if response.content else {}
            except ValueError:
                data = {"raw": response.text[:1000]}

            if response.ok:
                return data

            retryable_get = method == "GET" and response.status_code in {429, 500, 502, 503, 504}
            if retryable_get and attempt + 1 < max_attempts:
                delay = min(2 ** attempt, 8)
                logging.warning("Exness is temporarily unavailable (HTTP %d). Retrying in %d second(s).", response.status_code, delay)
                logging.debug("Retryable GET response details: %r", data)
                time.sleep(delay)
                continue
            if method != "GET" and response.status_code >= 500:
                raise UncertainPostError(
                    f"Mutating request returned HTTP {response.status_code}; acceptance may be unknown. "
                    "Do not retry blindly. Reconcile the account snapshot."
                )
            raise APIHTTPError(response.status_code, data)

        if last_error:
            raise last_error
        raise RuntimeError("Exness request failed without a response.")

    def discover_access_point(self) -> str:
        path = f"/v1/trading/access-point?{urlencode({'account_id': self.cfg.account_id})}"
        result = self.request("GET", path, gateway=True)
        host = result.get("access_point")
        if not isinstance(host, str) or not host:
            raise RuntimeError(f"Access-point discovery response missing access_point: {result}")
        if not host.startswith("https://"):
            host = "https://" + host.lstrip("/")
        parsed = urlparse(host)
        if parsed.scheme != "https" or not parsed.netloc:
            raise RuntimeError("Exness returned an invalid Access Point host.")
        self.access_point = host.rstrip("/")
        logging.info("Connected to Exness trading server.")
        return self.access_point

    def get(self, path_query: str) -> dict:
        return self.request("GET", path_query)

    def post(self, path: str, body: dict, idem: str | None = None) -> dict:
        return self.request("POST", path, body, idem=idem or uuid.uuid4().hex)

    def snapshot(self) -> dict:
        return self.get(f"/v1/trading/accounts/{self.cfg.account_id}/snapshot")

    def orders_history(self, start_time: str, instrument: str) -> dict:
        """Fetch the first page of historical orders from the lock start time onward."""
        params = {
            "from": start_time,
            "to": utc_iso(datetime.now(UTC)),
            "limit": 200,
            "instrument": instrument,
        }
        path = f"/v1/history/accounts/{self.cfg.account_id}/orders?{urlencode(params)}"
        return self.get(path)

    def orders_history_all_since(self, start: datetime, end: datetime, instrument: str) -> list[dict]:
        """Fetch every historical order since start, following Exness cursors."""
        params = {
            "from": utc_iso(start),
            "to": utc_iso(end),
            "limit": 200,
            "instrument": instrument,
        }
        path = f"/v1/history/accounts/{self.cfg.account_id}/orders?{urlencode(params)}"
        all_items: list[dict] = []
        seen_cursors: set[str] = set()
        for _ in range(100):
            page = self.get(path)
            items = page.get("items", []) or []
            if not isinstance(items, list):
                raise RuntimeError("Exness orders history returned an invalid items collection.")
            all_items.extend(row for row in items if isinstance(row, dict))
            cursor = page.get("next_cursor")
            if not cursor:
                if page.get("has_more"):
                    raise RuntimeError("Exness indicates more order-history pages but did not provide next_cursor.")
                return all_items
            cursor = str(cursor)
            if cursor in seen_cursors:
                raise RuntimeError("Exness orders-history pagination repeated a cursor; refusing incomplete trade-lock reconciliation.")
            seen_cursors.add(cursor)
            path = f"/v1/history/accounts/{self.cfg.account_id}/orders?{urlencode({'cursor': cursor, 'limit': 200})}"
        raise RuntimeError("Exness orders history exceeded 100 pages; refusing incomplete trade-lock reconciliation.")

    def deals_history(self, start_time: str, instrument: str) -> dict:
        """Fetch deal history to link a filled order to its position."""
        params = {
            "from": start_time,
            "to": utc_iso(datetime.now(UTC)),
            "limit": 200,
            "instrument": instrument,
        }
        path = f"/v1/history/accounts/{self.cfg.account_id}/deals?{urlencode(params)}"
        return self.get(path)

    def deals_history_all_since(self, start: datetime, end: datetime) -> list[dict]:
        """Fetch every account deal since start, following the opaque cursor."""
        params = {"from": utc_iso(start), "to": utc_iso(end), "limit": 200}
        path = f"/v1/history/accounts/{self.cfg.account_id}/deals?{urlencode(params)}"
        all_items: list[dict] = []
        seen_cursors: set[str] = set()
        for _ in range(100):
            page = self.get(path)
            items = page.get("items", []) or []
            if not isinstance(items, list):
                raise RuntimeError("Exness deals history returned an invalid items collection.")
            all_items.extend(row for row in items if isinstance(row, dict))
            cursor = page.get("next_cursor")
            if not cursor:
                if page.get("has_more"):
                    raise RuntimeError("Exness indicates more deal-history pages but did not provide next_cursor.")
                return all_items
            cursor = str(cursor)
            if cursor in seen_cursors:
                raise RuntimeError("Exness deals-history pagination repeated a cursor; refusing an incomplete balance calculation.")
            seen_cursors.add(cursor)
            path = f"/v1/history/accounts/{self.cfg.account_id}/deals?{urlencode({'cursor': cursor, 'limit': 200})}"
        raise RuntimeError("Exness deals history exceeded 100 pages; refusing an incomplete daily balance calculation.")

    def instrument_conditions(self) -> dict:
        return self.get(f"/v1/configuration/accounts/{self.cfg.account_id}/instruments/{self.cfg.instrument}/conditions")

    def candles(self, timeframe: str, count: int) -> pd.DataFrame:
        # Request a recent UTC time window. Exness candles are returned ascending.
        mins = count * (1 if timeframe == "M1" else 3)
        start = datetime.now(UTC) - timedelta(minutes=mins + 5)
        end = datetime.now(UTC)
        params = {
            "instrument": self.cfg.instrument,
            "timeframe": timeframe,
            "price_type": "both",
            "from": utc_iso(start),
            "to": utc_iso(end),
        }
        path = f"/v1/market-data/accounts/{self.cfg.account_id}/candles?{urlencode(params)}"
        data = self.get(path)
        rows = data.get("candles", [])
        if not rows:
            raise RuntimeError(f"No {timeframe} candles returned for {self.cfg.instrument}: {data}")
        # The Trading API's both-price response nests OHLC under bid/ask. Keep
        # bid OHLC in the legacy columns (signal parity) and retain ask OHLC for
        # correct SELL-position exit-side analysis. Fall back to flat bid rows
        # for older response variants.
        normalized = []
        for row in rows:
            item = dict(row)
            bid = row.get("bid") if isinstance(row.get("bid"), dict) else None
            ask = row.get("ask") if isinstance(row.get("ask"), dict) else None
            if bid:
                for col in ("open", "high", "low", "close"):
                    item[col] = bid.get(col)
            if ask:
                for col in ("open", "high", "low", "close"):
                    item[f"ask_{col}"] = ask.get(col)
            normalized.append(item)
        frame = pd.DataFrame(normalized)
        frame["time"] = pd.to_datetime(frame["time"], utc=True)
        for col in ["open", "high", "low", "close", "volume", "ask_open", "ask_high", "ask_low", "ask_close"]:
            if col in frame.columns:
                frame[col] = pd.to_numeric(frame[col], errors="coerce")
        frame = frame.dropna(subset=["time", "open", "high", "low", "close", "volume"])
        frame = frame.sort_values("time").drop_duplicates("time").reset_index(drop=True)
        now = pd.Timestamp.now(tz="UTC")
        duration = pd.Timedelta(minutes=1 if timeframe == "M1" else 3)
        # Never evaluate a still-forming candle.
        frame = frame[frame["time"] + duration <= now].reset_index(drop=True)
        return frame

    def place_entry_limit(self, signal: dict, volume_text: str, idem: str) -> dict:
        body = {
            "instrument": self.cfg.instrument,
            "side": signal["side"],
            "type": "limit",
            "volume": volume_text,
            "price": signal["entry_text"],
            "stop_loss_price": signal["sl_text"],
            "take_profit_price": signal["tp_text"],
            "comment": "KS Trader Desk Entry 1",
        }
        return self.post(f"/v1/trading/accounts/{self.cfg.account_id}/orders", body, idem=idem)

    def modify_active_order(self, order_id: str, stop_loss_text: str, idem: str) -> dict:
        """Modify the SL on the active SLTP order linked to an open position.

        Exness exposes position SL/TP modification through PATCH on the linked
        active SLTP order, not through a position PATCH endpoint.
        """
        body = {"stop_loss_price": stop_loss_text, "comment": "KS Trader Desk adaptive trailing"}
        path = f"/v1/trading/accounts/{self.cfg.account_id}/orders/{order_id}"
        return self.request("PATCH", path, body, idem=idem)

    def operation_status(self, operation_id: str) -> dict:
        return self.get(f"/v1/trading/accounts/{self.cfg.account_id}/operations/{operation_id}")


class StateStore:
    def __init__(self, path: str):
        self.conn = sqlite3.connect(path)
        self.conn.execute("""CREATE TABLE IF NOT EXISTS state (
            key TEXT PRIMARY KEY, value TEXT NOT NULL
        )""")
        self.conn.commit()

    def get(self, key: str, default: str = "") -> str:
        row = self.conn.execute("SELECT value FROM state WHERE key=?", (key,)).fetchone()
        return row[0] if row else default

    def set(self, key: str, value: Any) -> None:
        self.conn.execute("INSERT INTO state(key,value) VALUES(?,?) ON CONFLICT(key) DO UPDATE SET value=excluded.value", (key, str(value)))
        self.conn.commit()

    def get_json(self, key: str, default: Any = None) -> Any:
        raw = self.get(key, "")
        if not raw:
            return default
        return json.loads(raw)

    def set_json(self, key: str, value: Any) -> None:
        self.set(key, json.dumps(value, separators=(",", ":"), default=str))


def _deal_balance_impact(item: dict) -> Decimal:
    """Return the signed balance impact of one Exness deal.

    Exness exposes realized P/L or balance movement in profit.amount and
    the separately signed commission in commission. Adding both preserves
    the broker's debit/credit signs. Opening deals normally contribute only
    commission; their unrealized P/L does not change balance.
    """
    deal = item.get("deal", item)
    deal_type = str(deal.get("type", "")).lower()
    profit = deal.get("profit")
    if isinstance(profit, dict) and profit.get("amount") is not None:
        impact = dec(profit["amount"])
    elif deal_type == "open":
        impact = Decimal("0")
    else:
        raise RuntimeError(
            f"Exness deal {deal.get('deal_id', 'unknown')} type={deal_type!r} "
            "has no profit.amount; cannot reconstruct the midnight balance safely."
        )
    if deal.get("commission") not in (None, ""):
        impact += dec(deal["commission"])
    return impact


def get_daily_opening_balance(store: StateStore, api: ExnessAPI, snapshot: dict) -> tuple[Decimal, str]:
    """Reconstruct and freeze the actual 00:00 IST balance for the current day.

    Current Exness balance minus every signed account-deal movement since
    midnight gives the opening balance. It is cached per IST date. If the
    history is incomplete or ambiguous, trading fails closed rather than
    silently using a later balance.
    """
    now_ist = datetime.now(IST)
    day_key = now_ist.date().isoformat()
    cached = store.get_json("daily_opening_balance", {}) or {}
    if cached.get("date_ist") == day_key and cached.get("opening_balance") is not None:
        return dec(cached["opening_balance"]), day_key

    account_state = snapshot.get("account_state") or {}
    raw_balance = account_state.get("balance")
    if raw_balance in (None, ""):
        raise RuntimeError("Exness snapshot has no account_state.balance; daily risk capital cannot be established.")
    current_balance = dec(raw_balance)

    midnight_ist = datetime.combine(now_ist.date(), datetime.min.time(), tzinfo=IST)
    midnight_utc = midnight_ist.astimezone(UTC)
    now_utc = datetime.now(UTC)
    items = api.deals_history_all_since(midnight_utc, now_utc)

    net_change = Decimal("0")
    seen_deal_ids: set[str] = set()
    for item in items:
        deal = item.get("deal", item)
        event_time = item.get("event_time") or deal.get("create_time")
        if not event_time:
            raise RuntimeError("An Exness deal-history record has no event_time/create_time; cannot reconstruct 00:00 IST balance.")
        parsed_time = pd.Timestamp(event_time)
        if parsed_time.tzinfo is None:
            raise RuntimeError("An Exness deal-history timestamp has no timezone; cannot reconstruct 00:00 IST balance.")
        if parsed_time.to_pydatetime().astimezone(UTC) < midnight_utc:
            continue

        deal_id = str(deal.get("deal_id") or "")
        if deal_id and deal_id in seen_deal_ids:
            continue
        if deal_id:
            seen_deal_ids.add(deal_id)
        net_change += _deal_balance_impact(item)

    opening_balance = current_balance - net_change
    if not opening_balance.is_finite() or opening_balance <= 0:
        raise RuntimeError(f"Reconstructed 00:00 IST opening balance is invalid: {opening_balance}.")

    record = {
        "date_ist": day_key,
        "midnight_ist": midnight_ist.isoformat(),
        "computed_at": utc_iso(now_utc),
        "opening_balance": str(opening_balance),
        "current_balance_at_calculation": str(current_balance),
        "net_deals_balance_change": str(net_change),
        "deal_count": len(seen_deal_ids) if seen_deal_ids else len(items),
        "history_complete": True,
        "source": "Exness current snapshot balance minus all signed account deals since 00:00 IST",
    }
    store.set_json("daily_opening_balance", record)

    risk_percent = dec(os.getenv("RISK_PERCENT", "5.0"))
    risk_buffer_percent = dec(os.getenv("RISK_BUFFER_PERCENT", "2.0"))
    total_risk_percent = min(Decimal("7.0"), risk_percent + risk_buffer_percent)
    risk_budget = opening_balance * total_risk_percent / Decimal("100")
    logging.info(
        "Today's starting balance is $%.2f. Risk target %.2f%% + buffer %.2f%% = %.2f%% maximum ($%.2f).",
        float(opening_balance), float(risk_percent), float(risk_buffer_percent),
        float(total_risk_percent), float(risk_budget),
    )
    return opening_balance, day_key


# ---------- Indicator calculations ----------
def _indie_rma(series: pd.Series, length: int) -> pd.Series:
    """Reproduce Indie Rma: SMA seed, then Wilder recursive smoothing."""
    values = series.astype(float).to_numpy()
    out = [float("nan")] * len(values)
    previous = float("nan")
    for i, value in enumerate(values):
        if pd.isna(value):
            previous = float("nan")
            out[i] = float("nan")
            continue
        if pd.isna(previous):
            start = i - length + 1
            if start >= 0:
                window = values[start:i + 1]
                if not pd.isna(window).any():
                    previous = float(window.mean())
        else:
            previous = (float(value) + (length - 1) * previous) / length
        out[i] = previous
    return pd.Series(out, index=series.index, dtype=float)


def ema(series: pd.Series, length: int) -> pd.Series:
    """Reproduce Indie Ema: first valid value is an SMA, then EMA recursion."""
    values = series.astype(float).to_numpy()
    out = [float("nan")] * len(values)
    previous = float("nan")
    alpha = 2.0 / (length + 1.0)
    for i, value in enumerate(values):
        if pd.isna(value):
            previous = float("nan")
            out[i] = float("nan")
            continue
        if pd.isna(previous):
            start = i - length + 1
            if start >= 0:
                window = values[start:i + 1]
                if not pd.isna(window).any():
                    previous = float(window.mean())
        else:
            previous = alpha * float(value) + (1.0 - alpha) * previous
        out[i] = previous
    return pd.Series(out, index=series.index, dtype=float)


def rsi_wilder(close: pd.Series, length: int = 14) -> pd.Series:
    """Reproduce Indie Rsi: RMA(gains/losses), including its SMA seed."""
    delta = close.astype(float).diff()
    gain = delta.clip(lower=0.0)
    loss = (-delta).clip(lower=0.0)
    avg_gain = _indie_rma(gain, length)
    avg_loss = _indie_rma(loss, length)
    denominator = avg_gain + avg_loss
    # Indie Rsi uses divide(avg_gain, avg_gain + avg_loss, 1.0).
    ratio = avg_gain.div(denominator.where(denominator != 0.0))
    ratio = ratio.where(denominator != 0.0, 1.0)
    return 100.0 * ratio


def truth(x: Any) -> bool:
    return bool(x) if pd.notna(x) else False


def price_string(value: float, digits: int) -> str:
    """Round an order price to the broker's advertised point precision.

    Keep the unrounded Indie strategy value in signal logs for parity checks,
    but submit only a broker-valid price increment (e.g. 3 decimals for XAUUSD
    when point_digits=3). ROUND_HALF_UP avoids Python's banker's rounding.
    """
    quantum = Decimal("1").scaleb(-digits)
    rounded = dec(value).quantize(quantum, rounding=ROUND_HALF_UP)
    return format(rounded, f".{digits}f")


def volume_string(lot: float, conditions: dict) -> str:
    """Round volume DOWN to the broker step so actual risk never exceeds budget."""
    requested = dec(str(lot))
    vmin = dec(conditions.get("volume_min", "0"))
    vmax = dec(conditions.get("volume_max", "0"))
    step = dec(conditions.get("volume_step", "0"))
    if step <= 0 or vmin <= 0 or vmax < vmin:
        raise ValueError(f"Invalid broker volume specification: min={vmin}, max={vmax}, step={step}.")
    if requested < vmin:
        raise ValueError(f"Calculated lot {requested} is below broker minimum {vmin}; refusing to increase risk.")
    steps = ((requested - vmin) / step).to_integral_value(rounding="ROUND_FLOOR")
    actual = vmin + steps * step
    if actual < vmin or actual > vmax:
        raise ValueError(f"Rounded lot {actual} is outside broker volume range {vmin}..{vmax}.")
    return format(actual, "f")


def compute_signal(m1: pd.DataFrame, m3: pd.DataFrame, cfg: Config, pending: dict) -> tuple[dict | None, dict]:
    """Port of the supplied indicator's 1m configuration; closed bars only."""
    if len(m1) < 210 or len(m3) < 55:
        logging.info("Waiting for more completed 1-minute and 3-minute market data.")
        return None, pending

    d = m1.copy().reset_index(drop=True)
    for n in (9, 20, 50, 200):
        d[f"ema{n}"] = ema(d["close"], n)
    d["rsi"] = rsi_wilder(d["close"], 14)

    # Indie calc_on(ConfirmHtfEma, 3m) reads EMA20/50[1]. At each M1 bar,
    # select the latest 3m candle that was already closed before that M1 bar opened.
    m3x = m3.copy().reset_index(drop=True)
    m3x["ema20"] = ema(m3x["close"], 20)
    m3x["ema50"] = ema(m3x["close"], 50)
    m1_open = d.iloc[-1]["time"]
    completed_htf = m3x[m3x["time"] + pd.Timedelta(minutes=3) <= m1_open]
    if completed_htf.empty:
        return None, pending
    htf = completed_htf.iloc[-1]

    i = len(d) - 1
    c = d.iloc[i]
    p1, p2, p3 = d.iloc[i-1], d.iloc[i-2], d.iloc[i-3]
    ema9, ema20, ema50, ema200 = c.ema9, c.ema20, c.ema50, c.ema200
    rsi_now, rsi_prev = c.rsi, p1.rsi
    if pd.isna([ema9, ema20, ema50, ema200, rsi_now, rsi_prev, htf.ema20, htf.ema50]).any():
        return None, pending

    htf_buy = htf.ema20 > htf.ema50
    htf_sell = htf.ema20 < htf.ema50
    bullish_trend = ema20 > ema50 and ema50 > ema200
    bearish_trend = ema20 < ema50 and ema50 < ema200
    buy_momentum = rsi_now > 45
    sell_momentum = rsi_now < 55

    candle_range = c.high - c.low
    candidate_entry_price = (c.high + c.low) / 2.0
    candle_body = abs(c.close - c.open)
    lower_wick = min(c.open, c.close) - c.low
    upper_wick = c.high - max(c.open, c.close)

    bullish_close_momentum = candle_range > 0 and c.close > c.open and (c.close - c.low) / candle_range >= .75
    bearish_close_momentum = candle_range > 0 and c.close < c.open and (c.high - c.close) / candle_range >= .75
    bullish_engulfing = p1.close < p1.open and c.close > c.open and c.open <= p1.close and c.close >= p1.open
    bearish_engulfing = p1.close > p1.open and c.close < c.open and c.open >= p1.close and c.close <= p1.open
    bullish_rejection = candle_body > 0 and lower_wick >= candle_body * 1.2 and bullish_close_momentum
    bearish_rejection = candle_body > 0 and upper_wick >= candle_body * 1.2 and bearish_close_momentum
    bullish_hammer = candle_range > 0 and lower_wick >= candle_body * 2 and upper_wick <= candle_body * .8 and c.close > c.open and (c.close-c.low)/candle_range >= .60
    bearish_shooting_star = candle_range > 0 and upper_wick >= candle_body * 2 and lower_wick <= candle_body * .8 and c.close < c.open and (c.high-c.close)/candle_range >= .60
    previous_range = p1.high - p1.low
    previous_body = abs(p1.close-p1.open)
    morning_star = p2.close < p2.open and previous_range > 0 and previous_body <= previous_range*.35 and c.close > c.open and c.close > (p2.open+p2.close)/2
    evening_star = p2.close > p2.open and previous_range > 0 and previous_body <= previous_range*.35 and c.close < c.open and c.close < (p2.open+p2.close)/2
    bullish_break_previous = c.close > p1.high and c.close > c.open
    bearish_break_previous = c.close < p1.low and c.close < c.open
    bullish_strong_body = candle_range > 0 and candle_body/candle_range >= .60 and c.close > c.open and (c.close-c.low)/candle_range >= .70
    bearish_strong_body = candle_range > 0 and candle_body/candle_range >= .60 and c.close < c.open and (c.high-c.close)/candle_range >= .70

    # On the user's 1m chart, the indicator's 3m-chart-only candle/volume filter
    # and 3m-only volume impulse are inactive; MTF candle confirmations default True.
    bullish_mtf_candle_confirm = True
    bearish_mtf_candle_confirm = True
    bullish_price_action = (bullish_engulfing or bullish_rejection or bullish_hammer or morning_star or bullish_close_momentum or bullish_strong_body or bullish_break_previous) and bullish_mtf_candle_confirm
    bearish_price_action = (bearish_engulfing or bearish_rejection or bearish_shooting_star or evening_star or bearish_close_momentum or bearish_strong_body or bearish_break_previous) and bearish_mtf_candle_confirm

    avg_volume = d.iloc[i-10:i]["volume"].mean()
    volume_confirm = avg_volume > 0 and c.volume > avg_volume * 1.2
    buy_volume_confirm = volume_confirm
    sell_volume_confirm = volume_confirm

    support = d.iloc[i-10:i]["low"].min()
    resistance = d.iloc[i-10:i]["high"].max()
    sr_range = resistance - support
    support_zone = sr_range > 0 and c.low <= support + sr_range*.15 and c.close > support
    resistance_zone = sr_range > 0 and c.high >= resistance - sr_range*.15 and c.close < resistance

    bullish_breakout_volume_setup = c.close > resistance and c.close > c.open and volume_confirm and (bullish_strong_body or bullish_close_momentum)
    bearish_breakout_volume_setup = c.close < support and c.close < c.open and volume_confirm and (bearish_strong_body or bearish_close_momentum)

    buy_pullback = c.low <= ema20 and c.close > ema9 and c.close > c.open
    sell_pullback = c.high >= ema20 and c.close < ema9 and c.close < c.open
    buy_rejection_setup = support_zone and buy_volume_confirm and (bullish_engulfing or bullish_rejection)
    sell_rejection_setup = resistance_zone and sell_volume_confirm and (bearish_engulfing or bearish_rejection)

    bullish_ob_low = bullish_ob_high = None
    for j in range(1, 6):
        q = d.iloc[i-j]
        if q.close < q.open:
            bullish_ob_low, bullish_ob_high = q.low, q.high
            break
    bullish_ob_touch = bullish_ob_low is not None and c.low <= bullish_ob_high and c.high >= bullish_ob_low and c.close > bullish_ob_low and c.close > c.open and bullish_mtf_candle_confirm

    bearish_ob_low = bearish_ob_high = None
    for j in range(1, 6):
        q = d.iloc[i-j]
        if q.close > q.open:
            bearish_ob_low, bearish_ob_high = q.low, q.high
            break
    bearish_ob_touch = bearish_ob_low is not None and c.low <= bearish_ob_high and c.high >= bearish_ob_low and c.close < bearish_ob_high and c.close < c.open and bearish_mtf_candle_confirm

    bullish_fvg_valid = p1.low > p3.high
    bullish_fvg_low, bullish_fvg_high = p3.high, p1.low
    bullish_fvg_touch = bullish_fvg_valid and c.low <= bullish_fvg_high and c.high >= bullish_fvg_low and c.close > bullish_fvg_low and c.close > c.open
    bearish_fvg_valid = p1.high < p3.low
    bearish_fvg_low, bearish_fvg_high = p1.high, p3.low
    bearish_fvg_touch = bearish_fvg_valid and c.high >= bearish_fvg_low and c.low <= bearish_fvg_high and c.close < bearish_fvg_high and c.close < c.open

    hs_left, hs_head, hs_right = d.iloc[i-8].high, d.iloc[i-5].high, d.iloc[i-2].high
    hs_neckline = (d.iloc[i-7].low + d.iloc[i-3].low)/2
    hs_shoulders_similar = sr_range > 0 and abs(hs_left-hs_right) <= sr_range*.15
    head_shoulders_sell = hs_shoulders_similar and hs_head > hs_left and hs_head > hs_right and c.close < hs_neckline and c.close < c.open
    ihs_left, ihs_head, ihs_right = d.iloc[i-8].low, d.iloc[i-5].low, d.iloc[i-2].low
    ihs_neckline = (d.iloc[i-7].high + d.iloc[i-3].high)/2
    ihs_shoulders_similar = sr_range > 0 and abs(ihs_left-ihs_right) <= sr_range*.15
    inverse_head_shoulders_buy = ihs_shoulders_similar and ihs_head < ihs_left and ihs_head < ihs_right and c.close > ihs_neckline and c.close > c.open

    buy_existing_setup = buy_pullback and (bullish_ob_touch or bullish_fvg_touch or support_zone)
    sell_existing_setup = sell_pullback and (bearish_ob_touch or bearish_fvg_touch or resistance_zone)
    # 3m-chart-only volume impulse setup is false on a 1m chart.
    bullish_volume_impulse_setup = False
    bearish_volume_impulse_setup = False
    buy_condition = (htf_buy and bullish_trend and buy_momentum and bullish_price_action and (buy_existing_setup or buy_rejection_setup or bullish_ob_touch or bullish_fvg_touch or inverse_head_shoulders_buy)) or bullish_volume_impulse_setup
    sell_condition = (htf_sell and bearish_trend and sell_momentum and bearish_price_action and (sell_existing_setup or sell_rejection_setup or bearish_ob_touch or bearish_fvg_touch or head_shoulders_sell)) or bearish_volume_impulse_setup

    # Persistent breakout + volume pullback setup. Source order is: arm/refresh
    # a new breakout first, then validate an older pending setup on later bars.
    # Its 10-bar expiry is distinct from broker Entry 1 order expiry (none).
    bar_time = c.time
    pending = dict(pending)
    if bullish_breakout_volume_setup:
        pending = {"side": "buy", "time": bar_time.isoformat(), "average": candidate_entry_price, "low": c.low}
    elif bearish_breakout_volume_setup:
        pending = {"side": "sell", "time": bar_time.isoformat(), "average": candidate_entry_price, "high": c.high}

    if pending.get("side") == "buy" and bar_time > pd.Timestamp(pending["time"]):
        age = int((bar_time - pd.Timestamp(pending["time"])).total_seconds() // 60)
        if age > 10 or c.close < float(pending["low"]):
            pending = {}
    elif pending.get("side") == "sell" and bar_time > pd.Timestamp(pending["time"]):
        age = int((bar_time - pd.Timestamp(pending["time"])).total_seconds() // 60)
        if age > 10 or c.close > float(pending["high"]):
            pending = {}

    buy_breakout_pullback_ready = False
    sell_breakout_pullback_ready = False
    buy_breakout_ideal_entry = None
    sell_breakout_ideal_entry = None
    if pending.get("side") == "buy" and bar_time > pd.Timestamp(pending["time"]):
        pullback_confirm = c.close > c.open and (bullish_rejection or bullish_engulfing or bullish_hammer or bullish_close_momentum)
        if pullback_confirm:
            buy_average_touched = c.low <= float(pending["average"]) and c.close > float(pending["average"])
            buy_bottom_touched = c.low <= float(pending["low"]) and c.close > float(pending["low"])
            buy_breakout_pullback_ready = buy_average_touched or (not buy_average_touched and buy_bottom_touched)
            if buy_breakout_pullback_ready:
                buy_breakout_ideal_entry = float(pending["average"]) if buy_average_touched else float(pending["low"])
    if pending.get("side") == "sell" and bar_time > pd.Timestamp(pending["time"]):
        pullback_confirm = c.close < c.open and (bearish_rejection or bearish_engulfing or bearish_shooting_star or bearish_close_momentum)
        if pullback_confirm:
            sell_average_touched = c.high >= float(pending["average"]) and c.close < float(pending["average"])
            sell_top_touched = c.high >= float(pending["high"]) and c.close < float(pending["high"])
            sell_breakout_pullback_ready = sell_average_touched or (not sell_average_touched and sell_top_touched)
            if sell_breakout_pullback_ready:
                sell_breakout_ideal_entry = float(pending["average"]) if sell_average_touched else float(pending["high"])

    # Preserve the original BUY/SELL signal conditions without a deviation
    # filter. Entry 1 uses the completed confirmation candle midpoint.
    sell_entry_ready = sell_condition or sell_breakout_pullback_ready
    buy_entry_ready = buy_condition or buy_breakout_pullback_ready
    side = None
    if sell_entry_ready and not buy_entry_ready:
        side = "sell"
    elif buy_entry_ready:
        side = "buy"
    if side is None:
        return None, pending

    # Original Entry 1 logic: (confirmation candle high + low) / 2.
    entry = float(candidate_entry_price)
    if candle_range <= 0:
        logging.info("SIGNAL SKIPPED: completed confirmation candle has zero range.")
        return None, pending
    stop_buffer = max(candle_range * .25, abs(entry) * .00005)
    if side == "buy":
        recent_low = d.iloc[i-7:i+1]["low"].min()
        stop = min(recent_low, entry - stop_buffer)
        risk = entry - stop
    else:
        recent_high = d.iloc[i-7:i+1]["high"].max()
        stop = max(recent_high, entry + stop_buffer)
        risk = stop - entry
    total_risk_percent = min(7.0, cfg.risk_percent + cfg.risk_buffer_percent)
    risk_budget_cash = cfg.account_capital * total_risk_percent / 100.0
    risk_per_one_lot = risk * cfg.contract_size
    lot = 0.0
    risk_cash = float("nan")
    if risk_per_one_lot > 0 and risk_budget_cash > 0:
        raw_lot = risk_budget_cash / risk_per_one_lot
        lot = int(raw_lot * 100.0) / 100.0
        risk_cash = lot * risk_per_one_lot
    if not (risk > 0 and risk <= 15.0 and lot >= .01):
        logging.info("SIGNAL SKIPPED: The stop distance or calculated lot size does not meet the configured risk rules.")
        return None, pending
    rr = {"1:1": 1.0, "1:1.5": 1.5, "1:2": 2.0, "1:3": 3.0, "1:4": 4.0}[cfg.risk_reward]
    target = entry + risk*rr if side == "buy" else entry - risk*rr
    signal = {
        "bar_time": bar_time.isoformat(), "side": side,
        "entry": entry, "sl": stop, "tp": target, "lot": lot,
        "risk_cash": risk_cash, "risk_per_one_lot": risk_per_one_lot,
        "reason": "indicator primary signal or breakout pullback",
    }
    return signal, pending


def check_broker_compatibility(signal: dict, conditions: dict) -> dict:
    digits = int(conditions.get("point_digits", -1))
    if digits < 0:
        raise ValueError("Broker did not provide point_digits; refusing to submit an order.")
    if conditions.get("trade_mode") != "enabled":
        raise ValueError(f"Instrument trade_mode is not enabled: {conditions.get('trade_mode')}")
    # Exness may omit order_types or return it empty. Per its API runtime
    # semantics, an omitted/empty list is unspecified, not proof that limit
    # orders are disabled. If the broker explicitly supplies a non-empty list,
    # enforce it. The pending-order endpoint remains the final authority.
    raw_allowed = conditions.get("order_types")
    if isinstance(raw_allowed, (list, tuple, set)):
        allowed = [str(item).strip().lower() for item in raw_allowed if str(item).strip()]
    elif raw_allowed:
        allowed = [str(raw_allowed).strip().lower()]
    else:
        allowed = []

    if allowed and "limit" not in allowed:
        raise ValueError(f"Broker explicitly excludes limit orders: {allowed}")
    if not allowed:
        logging.warning(
            "Exness has not listed the allowed order types. The bot will try a LIMIT order only; it will never switch to a market order."
        )
    signal["entry_text"] = price_string(signal["entry"], digits)
    signal["sl_text"] = price_string(signal["sl"], digits)
    signal["tp_text"] = price_string(signal["tp"], digits)
    signal["volume_text"] = volume_string(signal["lot"], conditions)
    actual_volume = dec(signal["volume_text"])
    risk_per_one_lot = dec(signal.get("risk_per_one_lot", 0))
    if risk_per_one_lot <= 0:
        raise ValueError("Signal has no valid risk_per_one_lot; refusing broker submission.")
    signal["lot"] = float(actual_volume)
    signal["risk_cash"] = float(actual_volume * risk_per_one_lot)
    return signal



# ---------- Adaptive hybrid trailing manager ----------
TRAILING_TIMEFRAME = "M1"
TRAILING_CONFIRMATION_CANDLES = 3
TRAILING_ATR_PERIOD = 14
TRAILING_EMA_FAST = 9
TRAILING_EMA_SLOW = 21
TRAILING_ADX_PERIOD = 14
TRAILING_STRONG_ADX = 25.0
TRAILING_STRONG_ATR_MULTIPLIER = 1.5
TRAILING_WEAK_ATR_MULTIPLIER = 1.0
TRAILING_ACTIVATION_R = 1.0
TRAILING_STRUCTURE_R = 1.4
TRAILING_BE_TP_PROGRESS = 0.0  # Indie has no separate 70% TP-progress trigger
TRAILING_LOCK30_TP_PROGRESS = 0.85
TRAILING_LOCK60_TP_PROGRESS = 0.95


def _trailing_indicators(frame: pd.DataFrame) -> dict:
    """Calculate Wilder ATR/ADX and EMA values from completed candles only."""
    high = frame["high"].astype(float)
    low = frame["low"].astype(float)
    close = frame["close"].astype(float)
    prev_close = close.shift(1)
    tr = pd.concat([(high - low), (high - prev_close).abs(), (low - prev_close).abs()], axis=1).max(axis=1)
    atr = _indie_rma(tr, TRAILING_ATR_PERIOD)

    up = high.diff()
    down = -low.diff()
    plus_dm = pd.Series(0.0, index=frame.index)
    minus_dm = pd.Series(0.0, index=frame.index)
    plus_dm[(up > down) & (up > 0)] = up[(up > down) & (up > 0)]
    minus_dm[(down > up) & (down > 0)] = down[(down > up) & (down > 0)]
    safe_atr = atr.replace(0, float("nan"))
    plus_di = 100.0 * _indie_rma(plus_dm, TRAILING_ADX_PERIOD) / safe_atr
    minus_di = 100.0 * _indie_rma(minus_dm, TRAILING_ADX_PERIOD) / safe_atr
    denom = (plus_di + minus_di).replace(0, float("nan"))
    dx = 100.0 * (plus_di - minus_di).abs() / denom
    adx = _indie_rma(dx, TRAILING_ADX_PERIOD)
    ema_fast = ema(close, TRAILING_EMA_FAST)
    ema_slow = ema(close, TRAILING_EMA_SLOW)
    return {
        "atr": float(atr.iloc[-1]),
        "adx": float(adx.iloc[-1]),
        "plus_di": float(plus_di.iloc[-1]),
        "minus_di": float(minus_di.iloc[-1]),
        "ema_fast": float(ema_fast.iloc[-1]),
        "ema_slow": float(ema_slow.iloc[-1]),
    }


def _confirmed_swing(frame: pd.DataFrame, side: str, lookback: int = 80) -> tuple[float | None, int | None]:
    """Return latest 2-left/2-right confirmed pivot; never uses a live candle."""
    start = max(2, len(frame) - lookback)
    end = len(frame) - 2  # two completed right-side candles are required
    found = []
    for i in range(start, end):
        if side == "buy":
            value = float(frame.iloc[i]["low"])
            left = frame.iloc[i-2:i]["low"].astype(float)
            right = frame.iloc[i+1:i+3]["low"].astype(float)
            if value < float(left.min()) and value <= float(right.min()):
                found.append((value, i))
        else:
            value = float(frame.iloc[i]["high"])
            left = frame.iloc[i-2:i]["high"].astype(float)
            right = frame.iloc[i+1:i+3]["high"].astype(float)
            if value > float(left.max()) and value >= float(right.max()):
                found.append((value, i))
    return found[-1] if found else (None, None)


def _find_position_sltp_order(snapshot: dict, instrument: str, position_id: str) -> dict | None:
    matches = [
        row for row in (snapshot.get("orders", []) or [])
        if str(row.get("instrument", "")).upper() == instrument.upper()
        and str(row.get("order_type", "")).lower() == "sltp"
        and str(row.get("position_id", "")) == str(position_id)
        and str(row.get("state", "")).lower() in {"placed", "pending_new", "pending", "accepted"}
    ]
    return matches[0] if len(matches) == 1 else None


def _trailing_price_text(value: float, digits: int, side: str) -> str:
    """Round a stop conservatively: down for BUY, up for SELL."""
    quantum = Decimal("1").scaleb(-digits)
    raw = dec(value)
    rounding = "ROUND_FLOOR" if side == "buy" else "ROUND_CEILING"
    rounded = raw.quantize(quantum, rounding=rounding)
    return format(rounded, f".{digits}f")


def _trailing_candidate(frame: pd.DataFrame, side: str, entry: float, initial_sl: float,
                        current_sl: float, tp: float, point: float,
                        position_open_time: str | None = None,
                        trailing_state: dict | None = None) -> tuple[float | None, dict]:
    """Mirror the supplied Indie indicator's M1 adaptive trailing state machine.

    Trigger levels use the best favourable high/low since entry. A proposed
    level is then confirmed by three consecutive completed candle closes that
    remain beyond that level. The caller persists trailing_state between bars.
    """
    state = trailing_state if trailing_state is not None else {}
    cols = ("open", "high", "low", "close")
    if not all(col in frame.columns for col in cols):
        return None, {"reason": "required M1 OHLC data unavailable"}
    work = frame.copy().reset_index(drop=True)
    for col in cols:
        work[col] = pd.to_numeric(work[col], errors="coerce")
    work = work.dropna(subset=list(cols)).reset_index(drop=True)
    if "time" not in work.columns or not position_open_time:
        return None, {"reason": "position creation time unavailable; cannot identify post-entry candles"}
    try:
        opened_at = pd.to_datetime(position_open_time, utc=True)
        work["time"] = pd.to_datetime(work["time"], utc=True)
    except Exception:
        return None, {"reason": "invalid position creation timestamp"}
    post_open = work[work["time"] >= opened_at]
    if post_open.empty:
        return None, {"reason": "waiting for first fully post-entry completed M1 candle", "post_entry_candles": 0}

    initial_risk = abs(entry - initial_sl)
    target_distance = abs(tp - entry)
    if initial_risk <= 0 or target_distance <= 0:
        return None, {"reason": "invalid original risk or TP distance"}

    # Indie tracks the best excursion, not the minimum of the last three closes.
    if side == "buy":
        extreme = float(post_open["high"].max())
        old_extreme = state.get("favorable_extreme")
        if old_extreme not in (None, ""):
            extreme = max(extreme, float(old_extreme))
        state["favorable_extreme"] = str(extreme)
        favourable_move = extreme - entry
    else:
        extreme = float(post_open["low"].min())
        old_extreme = state.get("favorable_extreme")
        if old_extreme not in (None, ""):
            extreme = min(extreme, float(old_extreme))
        state["favorable_extreme"] = str(extreme)
        favourable_move = entry - extreme

    r_progress = favourable_move / initial_risk
    tp_progress = favourable_move / target_distance
    close = float(work.iloc[-1]["close"])
    proposed_sl = current_sl

    # Exact Indie thresholds: +1R break-even (buffer defaults to zero).
    if r_progress >= 1.0:
        proposed_sl = max(proposed_sl, entry) if side == "buy" else min(proposed_sl, entry)

    # Profit locks are percentages of the original TP distance.
    if tp_progress >= 0.95:
        locked = 0.60 * initial_risk
        proposed_sl = max(proposed_sl, entry + locked) if side == "buy" else min(proposed_sl, entry - locked)
    elif tp_progress >= 0.85:
        locked = 0.30 * initial_risk
        proposed_sl = max(proposed_sl, entry + locked) if side == "buy" else min(proposed_sl, entry - locked)

    metrics = _trailing_indicators(work)
    atr = metrics.get("atr", float("nan"))
    adx = metrics.get("adx", float("nan"))
    structure_details = {"atr": atr, "adx": adx, **metrics}

    # Match Indie: structure/reaction trailing starts at +1.4R and uses the
    # five-candle pivot centred two completed candles ago.
    if r_progress >= 1.4 and math.isfinite(atr) and atr > 0:
        strong = (
            math.isfinite(adx) and adx >= 25.0
            and ((metrics["plus_di"] > metrics["minus_di"] and metrics["ema_fast"] > metrics["ema_slow"]) if side == "buy"
                 else (metrics["minus_di"] > metrics["plus_di"] and metrics["ema_fast"] < metrics["ema_slow"]))
        )
        atr_buffer = atr * (1.5 if strong else 1.0)
        if len(work) >= 5:
            w = work.iloc[-5:].reset_index(drop=True)
            if side == "buy":
                pivot = float(w.iloc[2]["low"])
                confirmed_pivot = (pivot < float(w.iloc[1]["low"]) and pivot < float(w.iloc[3]["low"])
                                   and pivot <= float(w.iloc[0]["low"]) and pivot <= float(w.iloc[4]["low"]))
                if confirmed_pivot:
                    swing_candidate = pivot - atr_buffer
                    if swing_candidate > proposed_sl and swing_candidate < close:
                        proposed_sl = max(proposed_sl, swing_candidate)
                bearish_three = (float(w.iloc[4]["close"]) < float(w.iloc[3]["close"]) < float(w.iloc[2]["close"])
                                 and float(w.iloc[4]["close"]) < metrics["ema_fast"])
                if bearish_three:
                    reaction_candidate = float(w["low"].tail(3).min()) - atr
                    if reaction_candidate > proposed_sl and reaction_candidate < close:
                        proposed_sl = max(proposed_sl, reaction_candidate)
            else:
                pivot = float(w.iloc[2]["high"])
                confirmed_pivot = (pivot > float(w.iloc[1]["high"]) and pivot > float(w.iloc[3]["high"])
                                   and pivot >= float(w.iloc[0]["high"]) and pivot >= float(w.iloc[4]["high"]))
                if confirmed_pivot:
                    swing_candidate = pivot + atr_buffer
                    if swing_candidate < proposed_sl and swing_candidate > close:
                        proposed_sl = min(proposed_sl, swing_candidate)
                bullish_three = (float(w.iloc[4]["close"]) > float(w.iloc[3]["close"]) > float(w.iloc[2]["close"])
                                 and float(w.iloc[4]["close"]) > metrics["ema_fast"])
                if bullish_three:
                    reaction_candidate = float(w["high"].tail(3).max()) + atr
                    if reaction_candidate < proposed_sl and reaction_candidate > close:
                        proposed_sl = min(proposed_sl, reaction_candidate)

    # Candidate validity and confirmation mirror the Indie series logic.
    candidate_valid = (proposed_sl > current_sl and proposed_sl < close) if side == "buy" else (proposed_sl < current_sl and proposed_sl > close)
    candidate_raw = state.get("trail_candidate")
    candidate = float(candidate_raw) if candidate_raw not in (None, "") else None
    confirm_count = int(state.get("trail_confirm_count", 0) or 0)
    if candidate_valid:
        if candidate is None or (proposed_sl > candidate if side == "buy" else proposed_sl < candidate):
            candidate = proposed_sl
            confirm_count = 0

    if candidate is not None:
        still_safe = close > candidate if side == "buy" else close < candidate
        if still_safe:
            confirm_count += 1
        else:
            candidate = None
            confirm_count = 0

    state["trail_candidate"] = str(candidate) if candidate is not None else ""
    state["trail_confirm_count"] = confirm_count
    info = {**structure_details, "r": r_progress, "tp_progress": tp_progress,
            "favorable_extreme": extreme, "candidate": candidate,
            "confirmation_count": confirm_count}
    if candidate is not None and confirm_count >= 3 and (candidate > current_sl if side == "buy" else candidate < current_sl):
        state["trail_candidate"] = ""
        state["trail_confirm_count"] = 0
        stage = "lock_60_percent" if tp_progress >= .95 else "lock_30_percent" if tp_progress >= .85 else "break_even" if r_progress >= 1.0 else "structure_trailing"
        info.update({"reason": "Indie candidate confirmed", "stages": [stage]})
        return candidate, info

    reason = "waiting for three consecutive safe completed M1 closes" if candidate is not None else "no valid more-protective Indie trailing candidate"
    info["reason"] = reason
    return None, info


def _confirm_trailing_operation(store: StateStore, api: ExnessAPI, snapshot: dict, pending: dict) -> bool:
    """Resolve a previously submitted SL modification without blind resubmission."""
    target = str(pending.get("candidate_sl", ""))
    order_id = str(pending.get("order_id", ""))
    position_id = str(pending.get("position_id", ""))
    operation_id = str(pending.get("operation_id") or "")
    if operation_id:
        status_doc = api.operation_status(operation_id)
        state = str(status_doc.get("status", "")).lower()
        if state in {"rejected", "failed"}:
            logging.error("Exness could not apply the protective Stop Loss update. The existing Stop Loss remains in place.")
            logging.debug("Stop Loss operation response: %s", status_doc)
            trailing = store.get_json("adaptive_trailing_state", {}) or {}
            trailing["last_rejected_sl"] = target
            trailing["last_rejected_at"] = utc_iso(datetime.now(UTC))
            store.set_json("adaptive_trailing_state", trailing)
            store.set_json("trailing_pending_operation", {})
            return True
        if state not in {"confirmed", "completed", "succeeded", "success"}:
            logging.info("Your protective Stop Loss update is still being processed. The bot will not send a duplicate request.")
            return False
    orders = snapshot.get("orders", []) or []
    matched = [o for o in orders if str(o.get("order_id", "")) == order_id and str(o.get("position_id", "")) == position_id]
    if len(matched) == 1 and _history_decimal_equal(matched[0].get("stop_loss_price"), target):
        trailing = store.get_json("adaptive_trailing_state", {}) or {}
        trailing.update({"position_id": position_id, "current_sl": target, "last_confirmed_at": utc_iso(datetime.now(UTC)), "last_confirmed_bar": pending.get("bar_time"), "last_stage": pending.get("stage")})
        store.set_json("adaptive_trailing_state", trailing)
        store.set_json("trailing_pending_operation", {})
        logging.info("STOP LOSS UPDATED: Exness confirmed the new protective Stop Loss at %s.", target)
        return True
    logging.info("Exness processed the Stop Loss update; the bot is waiting for the account view to refresh.")
    return False


def run_adaptive_trailing(store: StateStore, api: ExnessAPI, snapshot: dict, m1: pd.DataFrame,
                          conditions: dict, instrument: str) -> None:
    """Evaluate and, when safe, modify the broker-side SL for the one open position."""
    positions = [p for p in (snapshot.get("positions", []) or [])
                 if str(p.get("instrument", "")).upper() == instrument.upper()
                 and str(p.get("state", "")).lower() in {"open", "opened"}]
    if not positions:
        # No open exposure remains for this instrument; an old trailing PATCH
        # can no longer affect a live position and must not block a later trade.
        stale_pending = store.get_json("trailing_pending_operation", {}) or {}
        if stale_pending:
            logging.info("No %s position is open. The previous Stop Loss update no longer needs monitoring.", instrument)
            store.set_json("trailing_pending_operation", {})
        return  # pending order is not a position; never trail it
    if len(positions) != 1:
        logging.error("STOP MANAGER PAUSED: More than one %s position was found. Manual review is required.", instrument)
        return
    position = positions[0]
    position_id = str(position.get("position_id", ""))
    side = str(position.get("direction", "")).lower()
    if side not in {"buy", "sell"} or not position_id:
        logging.error("STOP MANAGER PAUSED: Exness did not provide enough information to identify the open position.")
        return
    lock = store.get_json("trade_lock", {}) or {}
    if not lock.get("active") or not lock.get("idempotency_key"):
        logging.warning("Stop management skipped: position %s is not confirmed as an order placed by this bot.", position_id)
        return
    if lock.get("position_id") and str(lock.get("position_id")) != position_id:
        logging.error("STOP MANAGER PAUSED: The saved trade and Exness position do not match. No Stop Loss change will be sent.")
        return
    if not lock.get("position_id"):
        lock["position_id"] = position_id
        store.set_json("trade_lock", lock)
    sltp = _find_position_sltp_order(snapshot, instrument, position_id)
    if not sltp or not sltp.get("order_id") or sltp.get("stop_loss_price") in (None, ""):
        logging.error("STOP MANAGER PAUSED: Exness did not show one clear active Stop Loss order for position %s.", position_id)
        return

    pending_op = store.get_json("trailing_pending_operation", {}) or {}
    if pending_op:
        if str(pending_op.get("position_id")) != position_id:
            # Snapshot shows a different sole open position; the old position is
            # no longer exposed, so its old trailing operation cannot affect this one.
            logging.info("The previous position is closed. Stop management is now tracking the new position %s.", position_id)
            store.set_json("trailing_pending_operation", {})
            pending_op = {}
        else:
            _confirm_trailing_operation(store, api, snapshot, pending_op)
        if store.get_json("trailing_pending_operation", {}) or {}:
            return
        # Continue only on the next M1 bar after the previous operation resolved.

    trailing = store.get_json("adaptive_trailing_state", {}) or {}
    if str(trailing.get("position_id", "")) != position_id:
        trailing = {"position_id": position_id, "initialized_at": utc_iso(datetime.now(UTC))}
        store.set_json("adaptive_trailing_state", trailing)

    current_sl = float(dec(sltp["stop_loss_price"]))
    current_tp_raw = sltp.get("take_profit_price")
    if current_tp_raw in (None, ""):
        current_tp_raw = trailing.get("initial_tp") or store.get_json("trade_lock", {}).get("tp")
    if current_tp_raw in (None, ""):
        logging.error("STOP MANAGER PAUSED: Take Profit is unavailable for position %s.", position_id)
        return
    tp = float(dec(current_tp_raw))
    if position.get("open_price") in (None, ""):
        logging.error("STOP MANAGER PAUSED: Exness did not provide the entry price for position %s.", position_id)
        return
    entry = float(dec(position.get("open_price")))
    initial_sl_raw = trailing.get("initial_sl") or lock.get("sl") or sltp.get("stop_loss_price")
    if initial_sl_raw in (None, ""):
        logging.error("STOP MANAGER PAUSED: The original Stop Loss for position %s is unavailable.", position_id)
        return
    initial_sl = float(dec(initial_sl_raw))
    valid_geometry = (initial_sl < entry < tp) if side == "buy" else (tp < entry < initial_sl)
    if not valid_geometry:
        logging.error("STOP MANAGER PAUSED: The entry, Stop Loss and Take Profit prices do not form a valid trade setup.")
        return
    # Persist the initial risk anchors once. Do not replace them with a trailed SL.
    trailing.setdefault("initial_sl", str(initial_sl))
    trailing.setdefault("initial_tp", str(tp))
    trailing.setdefault("entry", str(entry))
    store.set_json("adaptive_trailing_state", trailing)

    bar_time = m1.iloc[-1]["time"].isoformat()
    if trailing.get("last_evaluated_bar") == bar_time:
        return
    trailing["last_evaluated_bar"] = bar_time
    store.set_json("adaptive_trailing_state", trailing)

    digits = int(conditions.get("point_digits", -1))
    if digits < 0:
        logging.error("STOP MANAGER PAUSED: Exness did not provide the required price precision.")
        return
    point = 10.0 ** (-digits)
    candidate, info = _trailing_candidate(
        m1, side, entry, initial_sl, current_sl, tp, point,
        position_open_time=position.get("create_time"),
        trailing_state=trailing,
    )
    store.set_json("adaptive_trailing_state", trailing)
    if candidate is None:
        logging.info("Protective Stop Loss is unchanged; current market conditions do not justify moving it.")
        return
    candidate_text = _trailing_price_text(candidate, digits, side)
    if str(trailing.get("last_rejected_sl", "")) == candidate_text:
        logging.info("The same Stop Loss price was previously declined. Waiting for a safer new price.")
        return
    candidate_rounded = float(candidate_text)
    # Recheck direction and one-way movement after conservative broker precision rounding.
    if (side == "buy" and candidate_rounded <= current_sl) or (side == "sell" and candidate_rounded >= current_sl):
        logging.info("Stop Loss remains unchanged because the new level would not protect the trade better.")
        return

    idem = "KST-TRAIL-" + uuid.uuid4().hex
    pending = {
        "status": "prepared", "position_id": position_id, "order_id": str(sltp["order_id"]),
        "candidate_sl": candidate_text, "previous_sl": str(sltp.get("stop_loss_price")),
        "operation_id": None, "idempotency_key": idem, "bar_time": bar_time,
        "stage": ",".join(info.get("stages", [])), "created_at": utc_iso(datetime.now(UTC)),
    }
    # Persist before PATCH. A timeout is uncertain and must never trigger a blind retry.
    store.set_json("trailing_pending_operation", pending)
    try:
        ack = api.modify_active_order(str(sltp["order_id"]), candidate_text, idem)
    except APIHTTPError as exc:
        trailing["last_rejected_sl"] = candidate_text
        trailing["last_rejected_at"] = utc_iso(datetime.now(UTC))
        store.set_json("adaptive_trailing_state", trailing)
        store.set_json("trailing_pending_operation", {})
        logging.error("Exness declined the Stop Loss update (HTTP %s). Your previous Stop Loss remains active.", exc.status_code)
        logging.debug("Stop Loss rejection details: %s", exc.payload)
        return
    except UncertainPostError as exc:
        pending["status"] = "uncertain"
        pending["error"] = str(exc)
        store.set_json("trailing_pending_operation", pending)
        logging.error("Stop Loss update status is uncertain. The bot will verify the current Stop Loss before trying anything else.")
        logging.debug("Stop Loss update transport details: %s", exc)
        return
    except Exception as exc:
        pending["status"] = "uncertain"
        pending["error"] = repr(exc)
        store.set_json("trailing_pending_operation", pending)
        logging.error("Stop Loss update status is uncertain. The bot will verify it with Exness before making another change.")
        logging.debug("Stop Loss update details:", exc_info=True)
        return

    operation_id = ack.get("operation_id")
    pending.update({"status": "acknowledged", "operation_id": str(operation_id) if operation_id else None, "ack": ack})
    store.set_json("trailing_pending_operation", pending)
    logging.info("PROTECTIVE STOP UPDATE: Moving Stop Loss from %s to %s. Waiting for Exness confirmation.", current_sl, candidate_text)
    if not operation_id:
        logging.warning("Exness did not return a confirmation reference for the Stop Loss update. The bot will verify it from the account snapshot.")
        return

    deadline = time.time() + 20
    while time.time() < deadline:
        try:
            status_doc = api.operation_status(str(operation_id))
        except Exception:
            logging.error("Could not check the Stop Loss update yet. The bot will check again before sending another update.")
            logging.debug("Stop update polling details:", exc_info=True)
            return
        op_state = str(status_doc.get("status", "")).lower()
        if op_state in {"rejected", "failed"}:
            trailing["last_rejected_sl"] = candidate_text
            trailing["last_rejected_at"] = utc_iso(datetime.now(UTC))
            store.set_json("adaptive_trailing_state", trailing)
            store.set_json("trailing_pending_operation", {})
            logging.error("Exness did not accept the Stop Loss update. The previous Stop Loss remains active.")
            logging.debug("Stop Loss operation response: %s", status_doc)
            return
        if op_state in {"confirmed", "completed", "succeeded", "success"}:
            fresh = api.snapshot()
            _confirm_trailing_operation(store, api, fresh, pending)
            return
        time.sleep(1.5)
    logging.info("Stop Loss update is still pending. The bot will confirm the result before making another change.")


def instrument_activity(snapshot: dict, instrument: str) -> tuple[list, list]:
    """Return matching active orders and open positions from an account snapshot."""
    orders = snapshot.get("orders", []) or []
    positions = snapshot.get("positions", []) or []
    active_orders = [
        o for o in orders
        if str(o.get("instrument", "")).upper() == instrument.upper()
        and str(o.get("state", "")).lower() in {"placed", "pending_new", "pending", "accepted"}
    ]
    open_positions = [
        p for p in positions
        if str(p.get("instrument", "")).upper() == instrument.upper()
        and str(p.get("state", "")).lower() in {"open", "opened"}
    ]
    return active_orders, open_positions


def _history_orders(history: dict) -> list[dict]:
    rows = history.get("items", []) or []
    return [row.get("order", row) for row in rows if isinstance(row, dict)]


def _history_deals(history: dict) -> list[dict]:
    rows = history.get("items", []) or []
    return [row.get("deal", row) for row in rows if isinstance(row, dict)]


def _history_time(value: Any) -> datetime | None:
    """Parse an Exness ISO timestamp into UTC, returning None if unavailable."""
    if not value:
        return None
    try:
        parsed = datetime.fromisoformat(str(value).replace("Z", "+00:00"))
        if parsed.tzinfo is None:
            parsed = parsed.replace(tzinfo=UTC)
        return parsed.astimezone(UTC)
    except (TypeError, ValueError):
        return None


def _history_decimal_equal(actual: Any, expected: Any) -> bool:
    """Compare broker decimal strings without binary-float rounding."""
    if actual in (None, "") or expected in (None, ""):
        return False
    try:
        return abs(Decimal(str(actual)) - Decimal(str(expected))) <= Decimal("0.0000001")
    except (InvalidOperation, TypeError, ValueError):
        return False


def _match_submission_order(
    rows: list[dict], lock: dict, instrument: str
) -> dict | None:
    """Find the opening LIMIT order for a lock whose IDs were never captured.

    The match uses the persisted signal's side, entry, SL, TP and volume, plus
    the submission timestamp. It deliberately requires every price/volume
    field so an unrelated XAUUSD order cannot be adopted accidentally.
    """
    expected = {
        "price": lock.get("entry"),
        "stop_loss_price": lock.get("sl"),
        "take_profit_price": lock.get("tp"),
        "volume": lock.get("volume"),
    }
    if any(value in (None, "") for value in expected.values()):
        return None

    expected_side = str(lock.get("side") or "").lower()
    lock_time = _history_time(lock.get("created_at"))
    matches: list[tuple[float, dict]] = []
    for row in rows:
        if str(row.get("instrument", "")).upper() != instrument.upper():
            continue
        if str(row.get("order_type", "")).lower() != "limit":
            continue
        if expected_side and str(row.get("direction", "")).lower() != expected_side:
            continue
        if not all(_history_decimal_equal(row.get(key), value) for key, value in expected.items()):
            continue

        row_time = _history_time(row.get("create_time"))
        if lock_time and row_time:
            delta = abs((row_time - lock_time).total_seconds())
            if delta > 600:
                continue
        else:
            # Without timestamps, a strict five-field match is still required.
            delta = 999999.0
        matches.append((delta, row))

    if not matches:
        return None
    matches.sort(key=lambda item: item[0])
    # If timestamps are unavailable and multiple identical orders exist, do
    # not guess which one belongs to this submission.
    if len(matches) > 1 and matches[0][0] == matches[1][0]:
        return None
    return matches[0][1]


def refresh_trade_lock(store: StateStore, api: ExnessAPI, snapshot: dict, instrument: str) -> bool:
    """Hold one-trade lock until a linked Exness SL/TP closing deal is confirmed."""
    lock = store.get_json("trade_lock", {}) or {}
    if not lock.get("active"):
        return False

    old_state = str(lock.get("state", "")).lower()
    if old_state == "rejected_signal_hold":
        logging.critical("NEW ENTRIES PAUSED: Exness rejected the previous entry request. Review the rejection before allowing another trade.")
        return True

    active_orders, open_positions = instrument_activity(snapshot, instrument)
    locked_order_id = str(lock.get("order_id") or "")
    locked_position_id = str(lock.get("position_id") or "")

    matching_orders = [
        order for order in active_orders
        if str(order.get("order_type", "")).lower() != "sltp"
        and (
            (locked_order_id and str(order.get("order_id", "")) == locked_order_id)
            or (locked_position_id and str(order.get("position_id", "")) == locked_position_id)
            or (not locked_order_id and not locked_position_id)
        )
    ]
    if matching_orders:
        found = matching_orders[0]
        if found.get("order_id"):
            lock["order_id"] = str(found["order_id"])
        if found.get("position_id"):
            lock["position_id"] = str(found["position_id"])
        lock["state"] = "pending_order"
        store.set_json("trade_lock", lock)
        if old_state != "pending_order":
            logging.info("Your %s LIMIT order is waiting for the market price to reach entry. No second order will be placed.", instrument)
        return True

    matching_positions = [
        position for position in open_positions
        if (locked_position_id and str(position.get("position_id", "")) == locked_position_id)
        or not locked_position_id
    ]
    if matching_positions:
        position = matching_positions[0]
        if position.get("position_id"):
            lock["position_id"] = str(position["position_id"])
        lock["state"] = "position_open"
        store.set_json("trade_lock", lock)
        # The human-readable trade dashboard reports the live position state.
        return True

    # No matching live activity: reconcile every available page of broker history.
    history_start = lock.get("created_at") or utc_iso(datetime.now(UTC) - timedelta(days=2))
    history_start_dt = _history_time(history_start) or (datetime.now(UTC) - timedelta(days=2))
    history_end_dt = datetime.now(UTC)
    order_items = api.orders_history_all_since(history_start_dt, history_end_dt, instrument)
    historical_orders = _history_orders({"items": order_items})
    deal_items = api.deals_history_all_since(history_start_dt, history_end_dt)
    historical_deals = _history_deals({"items": deal_items})

    # Identify the original Entry 1 LIMIT order, not a later closing MARKET order.
    source_order = None
    if locked_order_id:
        source_order = next(
            (row for row in historical_orders
             if str(row.get("order_id", "")) == locked_order_id
             and str(row.get("order_type", "")).lower() == "limit"),
            None,
        )
    if source_order is None and locked_position_id:
        expected_side = str(lock.get("side") or "").lower()
        source_order = next(
            (row for row in historical_orders
             if str(row.get("position_id", "")) == locked_position_id
             and str(row.get("order_type", "")).lower() == "limit"
             and (not expected_side or str(row.get("direction", "")).lower() == expected_side)),
            None,
        )

    # Critical recovery path: a very fast trade can open and close between
    # snapshots, leaving the persisted lock's order_id/position_id as None.
    if source_order is None and not locked_order_id and not locked_position_id:
        # Older lock records did not persist volume. Recover missing match fields
        # from the paired submission_state record written before the order POST.
        submission_record = store.get_json("submission_state", {}) or {}
        match_lock = dict(lock)
        for field in ("instrument", "side", "entry", "sl", "tp", "volume", "created_at"):
            if match_lock.get(field) in (None, "") and submission_record.get(field) not in (None, ""):
                match_lock[field] = submission_record[field]
        source_order = _match_submission_order(historical_orders, match_lock, instrument)
        if source_order:
            logging.info("The bot matched the previous entry with Exness history and is checking how that trade ended.")

    if source_order:
        historical_order_id = str(source_order.get("order_id") or "")
        historical_position_id = str(source_order.get("position_id") or "")
        if historical_order_id:
            lock["order_id"] = historical_order_id
            locked_order_id = historical_order_id
        if historical_position_id:
            lock["position_id"] = historical_position_id
            locked_position_id = historical_position_id

    # Find the opening deal by recovered position ID (order ID as fallback).
    opening_deal = None
    if locked_position_id:
        opening_deal = next(
            (deal for deal in historical_deals
             if str(deal.get("position_id", "")) == locked_position_id
             and str(deal.get("type", "")).lower() == "open"),
            None,
        )
    if opening_deal is None and locked_order_id:
        opening_deal = next(
            (deal for deal in historical_deals
             if str(deal.get("order_id", "")) == locked_order_id
             and str(deal.get("type", "")).lower() == "open"),
            None,
        )

    if opening_deal:
        deal_position_id = str(opening_deal.get("position_id") or "")
        if deal_position_id:
            locked_position_id = deal_position_id
            lock["position_id"] = deal_position_id
        deal_order_id = str(opening_deal.get("order_id") or "")
        if deal_order_id:
            lock["opening_order_id"] = deal_order_id
        lock["state"] = "awaiting_sl_tp_confirmation"

    source_state = str((source_order or {}).get("state", "")).lower()
    if source_order and source_state in {"cancelled", "canceled", "rejected"} and not opening_deal:
        lock.update({
            "active": False,
            "state": f"{source_state}_unfilled",
            "resolved_at": source_order.get("update_time") or source_order.get("create_time") or utc_iso(datetime.now(UTC)),
        })
        store.set_json("trade_lock", lock)
        logging.info("PENDING ENTRY ENDED: Exness marked the order as %s before it opened a position. The bot can watch for the next valid signal.", source_state.upper())
        return False

    # First retain the original strict TP/SL rule: require both a filled
    # linked SLTP order and its matching closing deal.
    exit_order = None
    exit_reason = None
    market_close_metadata: dict[str, Any] = {}
    if locked_position_id:
        for candidate in historical_orders:
            if (
                str(candidate.get("position_id", "")) != locked_position_id
                or str(candidate.get("order_type", "")).lower() != "sltp"
                or str(candidate.get("state", "")).lower() != "filled"
            ):
                continue
            candidate_order_id = str(candidate.get("order_id", ""))
            closing_deal = next(
                (deal for deal in historical_deals
                 if str(deal.get("position_id", "")) == locked_position_id
                 and str(deal.get("order_id", "")) == candidate_order_id
                 and str(deal.get("type", "")).lower() == "close"),
                None,
            )
            if not closing_deal:
                continue

            reported_reason = str(candidate.get("reason", "")).lower()
            if reported_reason in {"sl", "tp"}:
                exit_order, exit_reason = candidate, reported_reason.upper()
                break

            close_price = closing_deal.get("price")
            tp_price = candidate.get("take_profit_price") or (source_order or {}).get("take_profit_price")
            sl_price = candidate.get("stop_loss_price") or (source_order or {}).get("stop_loss_price")
            if _history_decimal_equal(close_price, tp_price):
                exit_order, exit_reason = candidate, "TP"
                break
            if _history_decimal_equal(close_price, sl_price):
                exit_order, exit_reason = candidate, "SL"
                break

    # Separate recovery path for a position closed by a filled non-SLTP order
    # (for example, a manual/external MARKET close). A close deal alone is not
    # enough: IDs, direction, filled order state, and full position volume must
    # all reconcile before the lock can be released.
    if not exit_order and locked_position_id and opening_deal:
        position_open_deals = [
            deal for deal in historical_deals
            if str(deal.get("position_id", "")) == locked_position_id
            and str(deal.get("type", "")).lower() == "open"
        ]
        opening_volume = Decimal("0")
        opening_deal_ids: set[str] = set()
        opening_directions: set[str] = set()
        for deal in position_open_deals:
            deal_id = str(deal.get("deal_id") or "")
            if deal_id and deal_id in opening_deal_ids:
                continue
            if deal_id:
                opening_deal_ids.add(deal_id)
            try:
                volume = dec(deal.get("volume"))
            except (InvalidOperation, TypeError, ValueError):
                continue
            if volume <= 0:
                continue
            opening_volume += volume
            direction = str(deal.get("direction") or "").lower()
            if direction in {"buy", "sell"}:
                opening_directions.add(direction)

        if not opening_directions:
            fallback_direction = str(lock.get("side") or "").lower()
            if fallback_direction in {"buy", "sell"}:
                opening_directions.add(fallback_direction)

        expected_close_directions = {
            "sell" if direction == "buy" else "buy"
            for direction in opening_directions
        }
        confirmed_closes: list[tuple[datetime, dict, dict]] = []
        closing_deal_ids: set[str] = set()
        closing_volume = Decimal("0")

        for deal in historical_deals:
            if (
                str(deal.get("position_id", "")) != locked_position_id
                or str(deal.get("type", "")).lower() != "close"
            ):
                continue
            deal_id = str(deal.get("deal_id") or "")
            if not deal_id or deal_id in closing_deal_ids:
                continue

            closing_order_id = str(deal.get("order_id") or "")
            if not closing_order_id:
                continue
            closing_order = next(
                (row for row in historical_orders
                 if str(row.get("position_id", "")) == locked_position_id
                 and str(row.get("order_id", "")) == closing_order_id
                 and str(row.get("state", "")).lower() == "filled"
                 and str(row.get("order_type", "")).lower() != "sltp"),
                None,
            )
            if not closing_order:
                continue

            close_direction = str(deal.get("direction") or closing_order.get("direction") or "").lower()
            if expected_close_directions and close_direction not in expected_close_directions:
                continue

            try:
                volume = dec(deal.get("volume"))
            except (InvalidOperation, TypeError, ValueError):
                continue
            if volume <= 0:
                continue

            closing_deal_ids.add(deal_id)
            closing_volume += volume
            close_time = _history_time(deal.get("create_time")) or _history_time(closing_order.get("update_time")) or datetime.min.replace(tzinfo=UTC)
            confirmed_closes.append((close_time, deal, closing_order))

        volume_tolerance = Decimal("0.0000001")
        if opening_volume > 0 and closing_volume + volume_tolerance >= opening_volume and confirmed_closes:
            confirmed_closes.sort(key=lambda item: item[0])
            latest_close_time, latest_close_deal, latest_close_order = confirmed_closes[-1]
            exit_order = latest_close_order
            exit_reason = (
                "MARKET"
                if str(latest_close_order.get("order_type", "")).lower() == "market"
                else "EXTERNAL"
            )

            # Retain an audit trail. This is deliberately not labeled SL or TP.
            market_close_metadata = {
                "close_order_id": str(latest_close_order.get("order_id") or ""),
                "closing_deal_ids": sorted(closing_deal_ids),
                "opening_volume": str(opening_volume),
                "closing_volume": str(closing_volume),
                "close_price": latest_close_deal.get("price"),
                "closed_at": latest_close_deal.get("create_time") or latest_close_order.get("update_time") or utc_iso(datetime.now(UTC)),
            }
            profit_values: list[Decimal] = []
            all_close_profits_present = True
            for _, close_deal, _ in confirmed_closes:
                profit = close_deal.get("profit")
                if isinstance(profit, dict) and profit.get("amount") not in (None, ""):
                    try:
                        profit_values.append(dec(profit["amount"]))
                    except (InvalidOperation, TypeError, ValueError):
                        all_close_profits_present = False
                        break
                else:
                    all_close_profits_present = False
                    break
            if all_close_profits_present and len(profit_values) == len(confirmed_closes):
                market_close_metadata["realized_profit"] = str(sum(profit_values, Decimal("0")))

    if exit_order and exit_reason:
        lock.update({
            "active": False,
            "state": f"closed_by_{exit_reason.lower()}",
            "closed_by": exit_reason,
            "closed_at": market_close_metadata.get("closed_at") or exit_order.get("update_time") or utc_iso(datetime.now(UTC)),
            "order_id": locked_order_id or lock.get("order_id"),
            "position_id": locked_position_id or lock.get("position_id"),
        })
        if market_close_metadata:
            lock.update(market_close_metadata)
        store.set_json("trade_lock", lock)
        if market_close_metadata:
            realized = market_close_metadata.get("realized_profit")
            pnl_text = f" | Realized P/L: ${float(dec(realized)):.2f}" if realized not in (None, "") else ""
            close_kind = "MANUAL / MARKET EXIT" if exit_reason == "MARKET" else "EXTERNAL EXIT"
            logging.info(
                "TRADE CLOSED: %s | Position %s | Fully closed volume %s / %s%s. New signals can be considered.",
                close_kind, locked_position_id,
                market_close_metadata.get("closing_volume"), market_close_metadata.get("opening_volume"), pnl_text,
            )
        else:
            close_label = "TAKE PROFIT" if exit_reason == "TP" else "STOP LOSS"
            logging.info("TRADE CLOSED: Exness confirms %s was hit for position %s. The bot can watch for the next valid setup.", close_label, locked_position_id)
        return False

    lock["state"] = "awaiting_sl_tp_confirmation"
    store.set_json("trade_lock", lock)
    if old_state != "awaiting_sl_tp_confirmation":
        logging.warning(
            "The previous trade is not fully reconciled yet (order %s, position %s). "
            "The bot is checking Exness history; new entries remain paused for safety.",
            lock.get("order_id"), lock.get("position_id"),
        )
    return True


def _display_price(value: Any, digits: int = 3) -> str:
    if value in (None, ""):
        return "N/A"
    try:
        return f"{float(dec(value)):.{max(0, min(digits, 8))}f}"
    except Exception:
        return str(value)


def display_trade_dashboard(store: StateStore, snapshot: dict, m1: pd.DataFrame,
                            instrument: str, account_mode: str, contract_size: float,
                            daily_opening_balance: float, risk_percent: float,
                            risk_buffer_percent: float, conditions: dict,
                            trailing_enabled: bool) -> None:
    """Print a concise, human-readable CMD dashboard from broker-confirmed data."""
    orders, positions = instrument_activity(snapshot, instrument)
    digits = int(conditions.get("point_digits", 3) or 3)
    now_ist = datetime.now(IST).strftime("%d-%b-%Y %I:%M:%S %p IST")
    lines = ["", "=" * 68, f" KS TRADER DESK | {instrument} | {account_mode.upper()} ACCOUNT", "=" * 68,
             f"Time: {now_ist}"]
    if positions:
        position = positions[0]
        pid = str(position.get("position_id", "N/A"))
        side = str(position.get("direction", "unknown")).upper()
        entry_raw = position.get("open_price")
        volume_raw = position.get("volume")
        lock = store.get_json("trade_lock", {}) or {}
        trail = store.get_json("adaptive_trailing_state", {}) or {}
        sltp = _find_position_sltp_order(snapshot, instrument, pid) or {}
        entry = float(dec(entry_raw)) if entry_raw not in (None, "") else None
        volume = float(dec(volume_raw if volume_raw not in (None, "") else lock.get("volume"))) if (volume_raw not in (None, "") or lock.get("volume") not in (None, "")) else None
        tp_raw = sltp.get("take_profit_price") or lock.get("tp") or trail.get("initial_tp")
        sl_broker = sltp.get("stop_loss_price")
        # Prefer the latest SL confirmed and persisted after Exness snapshot confirmation.
        sl_current = trail.get("current_sl") or sl_broker
        sl_initial = trail.get("initial_sl") or lock.get("sl")
        # The exit side is bid for BUY and ask for SELL.
        current = None
        if not m1.empty:
            last = m1.iloc[-1]
            col = "close" if side == "BUY" else "ask_close"
            fallback = "close"
            raw = last.get(col, None)
            if raw is None or pd.isna(raw):
                raw = last.get(fallback, None)
            if raw is not None and not pd.isna(raw):
                current = float(raw)
        tp = float(dec(tp_raw)) if tp_raw not in (None, "") else None
        initial_sl = float(dec(sl_initial)) if sl_initial not in (None, "") else None
        cur_sl = float(dec(sl_current)) if sl_current not in (None, "") else None
        risk_distance = abs(entry - initial_sl) if entry is not None and initial_sl is not None else None
        favourable = ((current-entry) if side == "BUY" else (entry-current)) if current is not None and entry is not None and side in {"BUY", "SELL"} else None
        r_multiple = favourable / risk_distance if favourable is not None and risk_distance and risk_distance > 0 else None
        tp_distance = abs(tp-entry) if tp is not None and entry is not None else None
        tp_progress = favourable / tp_distance * 100 if favourable is not None and tp_distance and tp_distance > 0 else None
        est_pl = favourable * contract_size * volume if favourable is not None and volume is not None else None
        risk_cash = risk_distance * contract_size * volume if risk_distance is not None and volume is not None else None
        trailing_pending = store.get_json("trailing_pending_operation", {}) or {}
        stage = trail.get("last_stage") or (" / ".join(trail.get("stages", [])) if trail.get("stages") else "Monitoring structure")
        lines += ["", f"TRADE IN PROGRESS : {side} POSITION", f"Position ID  : {pid}",
                  f"Lot / Volume : {volume:.2f}" if volume is not None else "Lot / Volume : N/A",
                  f"Entry Price  : {_display_price(entry, digits)}",
                  f"Market Price  : {_display_price(current, digits)}  (latest completed candle)",
                  f"Take Profit  : {_display_price(tp, digits)}",
                  f"Current Stop  : {_display_price(cur_sl, digits)}  (confirmed by Exness)",
                  f"Initial Stop  : {_display_price(initial_sl, digits)}" if initial_sl is not None else "Initial Stop  : Not available",
                  f"Initial Risk : {risk_distance:.{digits}f} price units" if risk_distance is not None else "Initial Risk : N/A",
                  f"Planned Risk  : ~${risk_cash:.2f}" if risk_cash is not None else "Planned Risk  : Not available",
                  f"Open P/L      : ~${est_pl:.2f} gross estimate" if est_pl is not None else "Open P/L      : Not available",
                  f"Open R       : {r_multiple:+.2f}R" if r_multiple is not None else "Open R       : N/A",
                  f"TP Progress  : {tp_progress:.1f}%" if tp_progress is not None else "TP Progress  : N/A",
                  f"Stop Manager  : {'ON' if trailing_enabled else 'OFF'} | Stage: {stage}"]
        if trailing_pending:
            lines.append(f"Stop Update   : Waiting for Exness to confirm {_display_price(trailing_pending.get('candidate_sl'), digits)}")
        else:
            lines.append("Stop Update   : No change pending")
        if est_pl is not None:
            lines.append("P/L note     : Gross estimate; excludes commission, swap and broker adjustments")
    elif orders:
        order = orders[0]
        lines += ["", f"WAITING FOR ENTRY : {str(order.get('direction', '')).upper()} LIMIT ORDER",
                  f"Order ID     : {order.get('order_id', 'N/A')}",
                  f"Direction    : {str(order.get('direction', 'N/A')).upper()}",
                  f"Entry Price  : {_display_price(order.get('price'), digits)}",
                  f"Stop Loss    : {_display_price(order.get('stop_loss_price'), digits)}",
                  f"Take Profit  : {_display_price(order.get('take_profit_price'), digits)}",
                  f"Volume       : {order.get('volume', 'N/A')}",
                  "Next Step     : Waiting for market price to reach the entry level",
                  "Safety        : No second XAUUSD entry will be placed while this order is active"]
    else:
        lines += ["", "TRADE STATUS : NO ACTIVE XAUUSD TRADE", "Watching completed 1-minute candles for the next valid setup."]
    total_risk_percent = min(7.0, risk_percent + risk_buffer_percent)
    daily_budget = (
        daily_opening_balance
        * Decimal(str(total_risk_percent))
        / Decimal("100")
    )
    lines += ["", f"Daily Opening Balance: ${daily_opening_balance:.2f}",
              f"Risk Budget          : {risk_percent:.2f}% + {risk_buffer_percent:.2f}% buffer = {total_risk_percent:.2f}% (${daily_budget:.2f})", 
              f"New Entries          : {'ON (DEMO LIMIT only)' if os.getenv('TRADING_ENABLED', 'false').strip().lower() in {'1','true','yes','y','on'} else 'OFF'}",
              "=" * 68, ""]
    print("\n".join(lines), flush=True)


def pending_submission_blocks(store: StateStore, snapshot: dict, instrument: str) -> bool:
    """Fail closed while an earlier POST has an unresolved outcome."""
    record = store.get_json("submission_state", {}) or {}
    status = str(record.get("status", "")).lower()
    if status not in {"prepared", "uncertain", "acknowledged"}:
        return False
    orders, positions = instrument_activity(snapshot, instrument)
    if orders or positions:
        record["status"] = "reconciled_present"
        record["reconciled_at"] = utc_iso(datetime.now(UTC))
        store.set_json("submission_state", record)
        logging.warning(
            "The earlier order is now visible in your Exness account (%d pending order(s), %d open position(s)). The bot will wait and will not place another entry.",
            len(orders), len(positions),
        )
        return False
    logging.critical("The previous order's result is still unknown. The bot has paused new entries until Exness confirms what happened.")
    return True


def create_submission_record(store: StateStore, signal: dict) -> str:
    """Persist intent and idempotency key before the single mutating POST."""
    existing = store.get_json("submission_state", {}) or {}
    if str(existing.get("status", "")).lower() in {"prepared", "uncertain", "acknowledged"}:
        raise RuntimeError("An earlier order submission is unresolved; refusing another POST.")
    idem = "KS1-" + uuid.uuid4().hex
    record = {
        "status": "prepared",
        "idempotency_key": idem,
        "created_at": utc_iso(datetime.now(UTC)),
        "instrument": signal.get("instrument"),
        "side": signal.get("side"),
        "bar_time": signal.get("bar_time"),
        "entry": signal.get("entry_text"),
        "sl": signal.get("sl_text"),
        "tp": signal.get("tp_text"),
        "volume": signal.get("volume_text"),
        "risk_cash": signal.get("risk_cash"),
    }
    store.set_json("submission_state", record)
    store.set_json("trade_lock", {
        "active": True,
        "state": "submission_pending",
        "created_at": record["created_at"],
        "instrument": record.get("instrument"),
        "side": record.get("side"),
        "entry": record.get("entry"),
        "sl": record.get("sl"),
        "tp": record.get("tp"),
        "volume": record.get("volume"),
        "order_id": None,
        "position_id": None,
        "idempotency_key": idem,
    })
    return idem


def update_submission(store: StateStore, status: str, **fields: Any) -> None:
    record = store.get_json("submission_state", {}) or {}
    record.update(fields)
    record["status"] = status
    record["updated_at"] = utc_iso(datetime.now(UTC))
    store.set_json("submission_state", record)


def main() -> int:
    cfg = Config.from_env()
    trailing_enabled = env_bool("ADAPTIVE_TRAILING_ENABLED", cfg.trading_enabled)
    configure_logging(cfg.log_level)
    logging.info("=" * 68)
    logging.info("KS TRADER DESK is starting (version %s).", APP_VERSION)
    logging.info("Account: %s | Market: %s", cfg.account_mode.upper(), cfg.instrument)
    logging.info("Entry method: LIMIT orders only | No market-order fallback")
    logging.info(
        "Risk per trade: %.2f%% target + %.2f%% buffer = %.2f%% maximum | Reward ratio: %s | Stop manager: %s",
        cfg.risk_percent, cfg.risk_buffer_percent,
        min(7.0, cfg.risk_percent + cfg.risk_buffer_percent),
        cfg.risk_reward, "ON" if trailing_enabled else "OFF",
    )
    if cfg.trading_enabled:
        logging.info("New DEMO entries are ENABLED. The bot will only trade when a valid signal appears.")
    else:
        logging.info("New entries are OFF. The bot will monitor signals without placing orders.")
    logging.info("=" * 68)

    store = StateStore(cfg.db_path)
    api = ExnessAPI(cfg)
    api.discover_access_point()
    conditions = api.instrument_conditions()
    logging.info(
        "XAUUSD trading settings loaded: price decimals=%s, minimum lot=%s, lot step=%s.",
        conditions.get("point_digits"), conditions.get("volume_min"), conditions.get("volume_step"),
    )
    if conditions.get("instrument") and str(conditions["instrument"]).upper() != cfg.instrument.upper():
        raise RuntimeError(f"API returned conditions for {conditions['instrument']}, not {cfg.instrument}.")

    pending = {}
    try:
        pending = store.get_json("breakout_pending", {}) or {}
    except Exception:
        logging.error("Saved breakout setup could not be restored. A fresh setup will be used.")
        logging.debug("Breakout restore details:", exc_info=True)
        pending = {}

    snap = api.snapshot()
    orders, positions = instrument_activity(snap, cfg.instrument)
    logging.info("Account check: %d pending order(s) and %d open position(s) found for %s.", len(orders), len(positions), cfg.instrument)
    daily_opening_balance, daily_balance_date = get_daily_opening_balance(store, api, snap)
    logging.info(
        "Today's opening balance (%s IST): $%.2f | Risk target %.2f%% + buffer %.2f%% = maximum $%.2f (%.2f%%).",
        daily_balance_date, float(daily_opening_balance), cfg.risk_percent,
        cfg.risk_buffer_percent,
        float(daily_opening_balance * dec(min(7.0, cfg.risk_percent + cfg.risk_buffer_percent)) / Decimal("100")),
        min(7.0, cfg.risk_percent + cfg.risk_buffer_percent),
    )
    unresolved = pending_submission_blocks(store, snap, cfg.instrument)
    existing_lock = store.get_json("trade_lock", {}) or {}
    previous_submission = store.get_json("submission_state", {}) or {}
    if str(previous_submission.get("status", "")).lower() == "rejected":
        if not existing_lock.get("active"):
            existing_lock.update({
                "active": True,
                "state": "rejected_signal_hold",
                "http_status": previous_submission.get("http_status"),
                "created_at": previous_submission.get("created_at") or utc_iso(datetime.now(UTC)),
            })
            store.set_json("trade_lock", existing_lock)
        logging.warning("A previous entry was rejected by Exness. New entries remain paused until that rejection is reviewed.")
    if not existing_lock.get("active") and (orders or positions):
        # Adopt existing activity after an upgrade/restart rather than risking
        # a second entry while a pre-existing trade is still running.
        adopted = orders[0] if orders else None
        adopted_position = positions[0] if positions else None
        created = (adopted or adopted_position or {}).get("create_time") or utc_iso(datetime.now(UTC))
        store.set_json("trade_lock", {
            "active": True, "state": "adopted_existing_activity", "created_at": created,
            "instrument": cfg.instrument,
            "order_id": (adopted or {}).get("order_id"),
            "position_id": (adopted_position or {}).get("position_id"),
            "side": (adopted or adopted_position or {}).get("direction"),
            "entry": str((adopted or {}).get("price", "")),
        })
        logging.warning("An existing XAUUSD order or position was found. The bot will manage/wait for it and will not place another entry.")
    last_bar = store.get("last_processed_m1", "")

    while True:
        try:
            m1 = api.candles("M1", cfg.candles_count)
            m3 = api.candles("M3", max(300, min(cfg.candles_count, 900)))
            if len(m1) < 210 or len(m3) < 55:
                logging.info("Waiting for enough completed market candles before checking for a signal.")
                time.sleep(cfg.poll_seconds)
                continue
            bar_ts = m1.iloc[-1]["time"].isoformat()
            if bar_ts == last_bar:
                time.sleep(cfg.poll_seconds)
                continue

            snap = api.snapshot()
            active_orders, open_positions = instrument_activity(snap, cfg.instrument)
            trade_locked = refresh_trade_lock(store, api, snap, cfg.instrument)
            unresolved = pending_submission_blocks(store, snap, cfg.instrument)
            # Run once per newly completed M1 candle. Pending orders are ignored;
            # only an actually open position with its linked active SLTP order is managed.
            if trade_locked and open_positions and trailing_enabled:
                run_adaptive_trailing(store, api, snap, m1, conditions, cfg.instrument)
            if trade_locked or active_orders or open_positions:
                display_trade_dashboard(
                    store, snap, m1, cfg.instrument, cfg.account_mode, cfg.contract_size,
                    daily_opening_balance, cfg.risk_percent, cfg.risk_buffer_percent,
                    conditions, trailing_enabled,
                )
            if trade_locked:
                store.set("last_processed_m1", bar_ts)
                last_bar = bar_ts
                time.sleep(cfg.poll_seconds)
                continue
            if unresolved:
                store.set("last_processed_m1", bar_ts)
                last_bar = bar_ts
                time.sleep(cfg.poll_seconds)
                continue

            if active_orders or open_positions:
                logging.info(
                    "Existing %s activity: %d active order(s), %d open position(s). "
                    "No new Entry 1 order will be submitted.",
                    cfg.instrument, len(active_orders), len(open_positions),
                )
                store.set("last_processed_m1", bar_ts)
                last_bar = bar_ts
                time.sleep(cfg.poll_seconds)
                continue

            daily_opening_balance, daily_balance_date = get_daily_opening_balance(store, api, snap)
            risk_cfg = replace(cfg, account_capital=float(daily_opening_balance))
            signal, pending = compute_signal(m1, m3, risk_cfg, pending)
            store.set_json("breakout_pending", pending)
            # Consume this closed bar before validation/submission so the same
            # signal cannot be replayed on each polling iteration.
            store.set("last_processed_m1", bar_ts)
            last_bar = bar_ts

            if signal:
                signal = check_broker_compatibility(signal, conditions)
                signal["instrument"] = cfg.instrument
                logging.info("-" * 58)
                logging.info("NEW %s SIGNAL | %s", signal["side"].upper(), cfg.instrument)
                logging.info("Entry price : %s (confirmation candle midpoint)", signal["entry_text"])
                logging.info("Stop Loss   : %s", signal["sl_text"])
                logging.info("Take Profit : %s", signal["tp_text"])
                logging.info("Lot size    : %s", signal["volume_text"])
                logging.info("Planned risk: $%.2f (maximum allowed %.2f%%) | Reward ratio: %s", signal["risk_cash"], min(7.0, cfg.risk_percent + cfg.risk_buffer_percent), cfg.risk_reward)
                logging.info("Signal time : %s", signal["bar_time"])
                logging.info("-" * 58)
                if cfg.trading_enabled:
                    snap2 = api.snapshot()
                    orders2, positions2 = instrument_activity(snap2, cfg.instrument)
                    if orders2 or positions2:
                        logging.warning("A different XAUUSD order or position appeared before submission. This signal was skipped to avoid duplicate trades.")
                    else:
                        idem = create_submission_record(store, signal)
                        try:
                            # Exactly one POST attempt. Never auto-retry after a timeout/5xx.
                            ack = api.place_entry_limit(signal, signal["volume_text"], idem=idem)
                        except APIHTTPError as exc:
                            update_submission(store, "rejected", http_status=exc.status_code, error=str(exc))
                            lock = store.get_json("trade_lock", {}) or {}
                            lock.update({
                                "active": True,
                                "state": "rejected_signal_hold",
                                "http_status": exc.status_code,
                                "rejection_payload": exc.payload,
                            })
                            store.set_json("trade_lock", lock)
                            logging.error(
                                "ORDER REJECTED: Exness declined this entry (HTTP %s). New entries are paused until the rejection is reviewed.",
                                exc.status_code,
                            )
                            logging.debug("Exness rejection details: %s", exc.payload)
                        except UncertainPostError as exc:
                            update_submission(store, "uncertain", error=str(exc))
                            logging.error("ORDER STATUS UNCERTAIN: Exness did not confirm whether it received the order. The bot will not send it again automatically.")
                            logging.debug("Order submission details: %s", exc)
                        except Exception as exc:
                            # Unexpected failures after POST initiation are treated as uncertain.
                            update_submission(store, "uncertain", error=repr(exc))
                            logging.error("ORDER STATUS UNCERTAIN: Something interrupted the order request. The bot will check Exness and will not repeat the request automatically.")
                            logging.debug("Order POST exception details:", exc_info=True)
                        else:
                            operation_id = ack.get("operation_id")
                            update_submission(
                                store, "acknowledged", ack=ack,
                                operation_id=str(operation_id) if operation_id else None,
                            )
                            logging.info("ORDER SENT: Your %s LIMIT order was sent to Exness. Waiting for confirmation.", signal["side"].upper())
                            if operation_id:
                                deadline = time.time() + 30
                                while time.time() < deadline:
                                    status_doc = api.operation_status(str(operation_id))
                                    op_state = str(status_doc.get("status", "")).lower()
                                    if op_state in {"rejected", "failed"}:
                                        update_submission(store, "rejected", operation_status=status_doc)
                                        lock = store.get_json("trade_lock", {}) or {}
                                        lock.update({"active": False, "state": "submission_rejected"})
                                        store.set_json("trade_lock", lock)
                                        logging.error("ORDER REJECTED: Exness did not accept this LIMIT order. No order is considered active.")
                                        logging.debug("Order operation response: %s", status_doc)
                                        break
                                    if op_state in {"cancelled", "canceled"}:
                                        update_submission(store, "cancelled", operation_status=status_doc)
                                        logging.warning("ENTRY REQUEST CANCELLED: Exness cancelled the order request. The bot will verify the account history before allowing another entry.")
                                        logging.debug("Order operation response: %s", status_doc)
                                        break
                                    if op_state in {"confirmed", "completed", "succeeded", "success"}:
                                        update_submission(store, "acknowledged", operation_status=status_doc)
                                        logging.info("ORDER CONFIRMED: Exness registered your %s LIMIT order. Waiting for market price to reach %s.", signal["side"].upper(), signal["entry_text"])
                                        break
                                    time.sleep(2)
                                    time.sleep(2)
                            else:
                                logging.warning("Exness has not provided a confirmation reference yet. The bot will check the account before sending anything else.")
                            snap3 = api.snapshot()
                            orders3, positions3 = instrument_activity(snap3, cfg.instrument)
                            logging.info("Exness account check: %d pending order(s), %d open position(s).", len(orders3), len(positions3))
                            if orders3 or positions3:
                                update_submission(store, "reconciled_present", reconciled_at=utc_iso(datetime.now(UTC)))
                            elif str((store.get_json("submission_state", {}) or {}).get("status", "")) != "rejected":
                                logging.error("ORDER NOT YET VISIBLE: Exness acknowledged the request, but the account does not show it yet. New entries are paused while the bot checks again.")
                else:
                    logging.info("SIGNAL ONLY: no order was placed because automatic entries are turned OFF.")

            time.sleep(cfg.poll_seconds)
        except KeyboardInterrupt:
            logging.info("KS Trader Desk stopped safely.")
            return 0
        except Exception as exc:
            logging.error("TEMPORARY ISSUE: The bot could not complete this market check. It will reconnect and try again.")
            logging.debug("Main loop error details:", exc_info=True)
            # GET recovery is safe and retried inside request(); no order POST is repeated.
            try:
                api.discover_access_point()
                snap = api.snapshot()
                orders, positions = instrument_activity(snap, cfg.instrument)
                logging.info("Connection restored. Exness shows %d pending order(s) and %d open position(s).", len(orders), len(positions))
                pending_submission_blocks(store, snap, cfg.instrument)
            except Exception:
                logging.error("Could not reconnect to Exness yet. The bot will pause briefly and try again.")
                logging.debug("Exness reconnection details:", exc_info=True)
            time.sleep(max(cfg.poll_seconds, 5))


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except Exception as exc:
        logging.basicConfig(level=logging.ERROR)
        logging.error("The bot could not start. Please check ks_trader_bot.log for technical details.")
        logging.debug("Startup error details:", exc_info=True)
        raise SystemExit(1)
