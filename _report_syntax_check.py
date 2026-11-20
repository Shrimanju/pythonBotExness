from __future__ import annotations
import os, re
from pathlib import Path
from datetime import datetime, timezone
from decimal import Decimal, InvalidOperation
from zoneinfo import ZoneInfo
from typing import Any
IST=ZoneInfo('Asia/Kolkata')
UTC=timezone.utc
class ExnessAPI: pass
class StateStore: pass
def dec(value: Any): return Decimal(str(value))
def _history_orders(history): return [row.get('order',row) for row in history.get('items',[]) if isinstance(row,dict)]
def _history_deals(history): return [row.get('deal',row) for row in history.get('items',[]) if isinstance(row,dict)]
def _history_time(value):
 if not value:return None
 try:
  dt=datetime.fromisoformat(str(value).replace('Z','+00:00'))
  return (dt.replace(tzinfo=UTC) if dt.tzinfo is None else dt).astimezone(UTC)
 except Exception:return None
# ---------- Hourly daily trade report (IST) ----------
DAILY_REPORT_PATH = Path(os.getenv('DAILY_REPORT_FILE', 'KS_Trader_Desk_Daily_Report.txt'))
