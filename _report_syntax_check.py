from __future__ import annotations
import os,re
from pathlib import Path
from datetime import datetime,timezone
from decimal import Decimal,InvalidOperation
from zoneinfo import ZoneInfo
from typing import Any
IST=ZoneInfo('Asia/Kolkata')
UTC=timezone.utc
class ExnessAPI: pass
def dec(x): return Decimal(str(x))
def _history_orders(h): return [r.get('order',r) for r in h.get('items',[]) if isinstance(r,dict)]
def _history_deals(h): return [r.get('deal',r) for r in h.get('items',[]) if isinstance(r,dict)]
def _history_time(v):
 if not v:return None
 try:
  d=datetime.fromisoformat(str(v).replace('Z','+00:00'))
  return (d.replace(tzinfo=UTC) if d.tzinfo is None else d).astimezone(UTC)
 except Exception:return None
# ---------- Hourly daily trade report (IST) ----------
DAILY_REPORT_PATH = Path(os.getenv('DAILY_REPORT_FILE', 'KS_Trader_Desk_Daily_Report.txt'))

def _report_money(value: Decimal) -> str:
    return f'${value:,.2f}'

def _report_cash_for_order(order: dict, reason: str) -> Decimal | None:
    entry, sl, tp, volume = (order.get(k) for k in ('price', 'stop_loss_price', 'take_profit_price', 'volume'))
    if any(v in (None, '') for v in (entry, sl, tp, volume)): return None
    try:
        entry_d, sl_d, tp_d, volume_d = map(dec, (entry, sl, tp, volume))
        contract_size = dec(os.getenv('CONTRACT_SIZE', '100.0'))
    except (InvalidOperation, TypeError, ValueError): return None
    if volume_d <= 0 or str(order.get('direction', '')).lower() not in {'buy', 'sell'}: return None
    if reason == 'SL': return -(abs(entry_d - sl_d) * contract_size * volume_d)
    if reason == 'TP': return abs(tp_d - entry_d) * contract_size * volume_d
    return None

def _classify_report_orders(order_items: list[dict], deal_items: list[dict], start_utc: datetime, end_utc: datetime, instrument: str) -> dict:
    orders = _history_orders({'items': order_items})
    deals = _history_deals({'items': deal_items})
    opened = [d for d in deals if str(d.get('type', '')).lower() == 'open']
    opened_order_ids = {str(d.get('order_id') or '') for d in opened}
    opened_position_ids = {str(d.get('position_id') or '') for d in opened}
    report = {'total': 0, 'active_count': 0, 'inactive_count': 0, 'active_pnl': Decimal('0'), 'inactive_pnl': Decimal('0'), 'profit_day': Decimal('0')}
    seen = set()
    for order in orders:
        if str(order.get('order_type', '')).lower() != 'limit' or str(order.get('instrument', '')).upper() != instrument.upper(): continue
        created = _history_time(order.get('create_time'))
        if not created or not (start_utc <= created <= end_utc): continue
        oid = str(order.get('order_id') or '')
        if not oid or oid in seen: continue
        seen.add(oid)
        pid = str(order.get('position_id') or '')
        if oid in opened_order_ids or (pid and pid in opened_position_ids):
            report['total'] += 1
            report['active_count'] += 1
            if pid:
                for deal in deals:
                    if str(deal.get('position_id') or '') == pid and str(deal.get('type', '')).lower() == 'close':
                        profit = deal.get('profit')
                        if isinstance(profit, dict) and profit.get('amount') not in (None, ''):
                            report['active_pnl'] += dec(profit['amount'])
            continue
        reason = str(order.get('reason', '')).lower()
        if reason not in {'sl', 'tp'}: continue
        estimate = _report_cash_for_order(order, reason.upper())
        if estimate is None: continue
        report['total'] += 1
        report['inactive_count'] += 1
        report['inactive_pnl'] += estimate
    report['profit_day'] = report['active_pnl']
    return report

def _update_daily_report_file(report: dict, report_date) -> None:
    DAILY_REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    label, separator = report_date.strftime('%d-%b-%Y'), '=' * 31
    block = '\n'.join([separator, f'Date : {label}',
        f'Number of trades taken per day : {report["total"]}',
        f'Overall active orders : {report["active_count"]}',
        f'Overall inactive orders : {report["inactive_count"]}',
        f'Profit of the day : {_report_money(report["profit_day"])}',
        f'P/L of active orders : {_report_money(report["active_pnl"])}',
        f'P/L of inactive orders : {_report_money(report["inactive_pnl"])}', separator])
    old = DAILY_REPORT_PATH.read_text(encoding='utf-8') if DAILY_REPORT_PATH.exists() else ''
    pattern = re.compile(r'(?ms)^={10,}[^\n]*\n.*?^={10,}\\s*$')
    chunks = list(pattern.finditer(old))
    rebuilt, inserted = [], False
    for match in chunks:
        section = match.group(0)
        if f'Date : {label}' in section:
            if not inserted: rebuilt.append(block); inserted = True
        else: rebuilt.append(section.strip())
    if not inserted: rebuilt.append(block)
    DAILY_REPORT_PATH.write_text('\n'.join(rebuilt).rstrip() + '\n', encoding='utf-8')

def update_hourly_daily_report(api: ExnessAPI, snapshot: dict, instrument: str) -> None:
    now_ist = datetime.now(IST)
    midnight_ist = datetime.combine(now_ist.date(), datetime.min.time(), tzinfo=IST)
    start_utc, end_utc = midnight_ist.astimezone(UTC), datetime.now(UTC)
    orders = api.orders_history_all_since(start_utc, end_utc, instrument)
    deals = api.deals_history_all_since(start_utc, end_utc)
    report = _classify_report_orders(orders, deals, start_utc, end_utc, instrument)
    for position in (snapshot.get('positions', []) or []):
        if str(position.get('instrument', '')).upper() != instrument.upper() or str(position.get('state', '')).lower() not in {'open', 'opened'}: continue
        raw = position.get('profit')
        if isinstance(raw, dict): raw = raw.get('amount')
        if raw not in (None, ''): report['active_pnl'] += dec(raw)
    report['profit_day'] = report['active_pnl']
    _update_daily_report_file(report, now_ist.date())
    logging.info('Hourly daily report refreshed: %s | trades %d | active %d | inactive %d | active P/L %s | inactive P/L %s', DAILY_REPORT_PATH, report['total'], report['active_count'], report['inactive_count'], _report_money(report['active_pnl']), _report_money(report['inactive_pnl']))
