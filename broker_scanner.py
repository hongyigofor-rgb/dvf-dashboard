#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
DeepValueFund Terminal (DVF-PRO) — broker_scanner.py
=====================================================
主力分點鎖碼篩選：連續 ≥ 3 個交易日「前 5 大買超分點」合計買超 > 當日成交量 15%，
且有 ≥ 2 個相同分點連續出現在前 5 大 → [DOMINANT BROKER ACCUMULATION]。

資料來源（只使用合規管道；不破解驗證碼）
  1. FinMind TaiwanStockTradingDailyReport — 需 FINMIND_TOKEN 且為贊助等級（免費等級回 400）。
  2. 手動匯入 CSV — 自行於證交所「買賣日報表查詢系統」（bsr.twse.com.tw，需人工輸入驗證碼）下載，
     存為 ~/GOFOR/broker_data/YYYYMMDD/<代號>.csv（多日即多個資料夾）。
  兩者皆無資料時輸出 signal="N/A"，不影響其他模組。

隔日沖排除
  a. 手動名單 broker_blacklist.json（分點名稱關鍵字；預設為市場常見傳聞名單，請自行校正）。
  b. 資料驅動：視窗內同一分點「T 日買超、T+1 日賣超 ≥ 80%」出現 ≥ 2 次 → 自動判定隔日沖並排除。

用法
  scanner.py 會在掃描時自動呼叫 annotate()；亦可單獨執行：
    python broker_scanner.py                 # 重新標註 candidates.json / candidates.js
    python broker_scanner.py --codes 1313    # 只看指定代號（印出明細，不寫檔）
只使用 Python 標準函式庫。本模組為籌碼研究工具，不構成投資建議。
"""
from __future__ import annotations

import argparse
import csv
import datetime as dt
import io
import json
import os
import re
import ssl
import sys
import urllib.parse
import urllib.request
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple

BASE_DIR = Path(__file__).resolve().parent
FINMIND = "https://api.finmindtrade.com/api/v4/data"
BROKER_TH = {
    "top_n": 5,                 # 每日取前 N 大買超分點
    "conc_min_pct": 15.0,       # 前 N 大買超合計 / 當日成交量 門檻
    "min_streak": 3,            # 連續天數門檻
    "min_persistent": 2,        # 連續期間每天都在前 N 大的「特定分點」最少家數
    "window_days": 10,          # 分析最近 N 個有分點資料的交易日
    "daytrade_sell_ratio": 0.8, # T+1 賣超 ≥ T 日買超 × 80% 視為隔日沖動作
    "daytrade_min_hits": 2,     # 出現 ≥ 2 次 → 判定隔日沖分點
}
SIGNAL = "DOMINANT BROKER ACCUMULATION"
DEFAULT_BLACKLIST = {
    "_note": "隔日沖分點名稱關鍵字（子字串比對）。此為市場常見傳聞名單，未經驗證，請依自身觀察增刪。",
    "keywords": [],
}


def _log(msg: str) -> None:
    print(f"{dt.datetime.now():%H:%M:%S} [broker] {msg}", flush=True)


def _num(v: Any) -> Optional[float]:
    try:
        s = str(v).replace(",", "").replace("=", "").replace('"', "").strip()
        return float(s) if s not in ("", "-", "--") else None
    except ValueError:
        return None


def load_blacklist(path: Path) -> List[str]:
    if not path.exists():
        path.write_text(json.dumps(DEFAULT_BLACKLIST, ensure_ascii=False, indent=1) + "\n", "utf-8")
    try:
        return [k for k in json.loads(path.read_text("utf-8")).get("keywords", []) if k]
    except (json.JSONDecodeError, AttributeError):
        return list(DEFAULT_BLACKLIST["keywords"])


def _norm_broker(raw: str) -> Tuple[str, str]:
    """'9268凱基台北' / '1020合　　庫' → ('9268', '凱基台北')。"""
    s = re.sub(r"[\s　]+", "", str(raw))
    m = re.match(r"^([0-9A-Za-z]{4})(.*)$", s)
    return (m.group(1).upper(), m.group(2)) if m else (s, s)


# ──────────────────────────────────────────────────────────────────────────────
# 資料來源
# ──────────────────────────────────────────────────────────────────────────────
def parse_bsr_csv(text: str) -> Dict[str, Dict[str, float]]:
    """
    證交所買賣日報表 CSV（每列並排兩組「序號,券商,價格,買進股數,賣出股數」）→ {分點代號: {name, buy, sell}}（股）。
    以容錯方式逐列尋找符合 5 欄樣式的區塊，避免版式小幅變動造成失敗。
    """
    out: Dict[str, Dict[str, Any]] = {}
    for row in csv.reader(io.StringIO(text.lstrip("﻿"))):
        cells = [c.strip() for c in row]
        i = 0
        while i + 4 < len(cells):
            seq, brk, price, buy, sell = cells[i:i + 5]
            if seq.isdigit() and brk and _num(price) is not None and _num(buy) is not None and _num(sell) is not None:
                bid, name = _norm_broker(brk)
                d = out.setdefault(bid, {"name": name, "buy": 0.0, "sell": 0.0})
                d["buy"] += _num(buy)
                d["sell"] += _num(sell)
                i += 5
            else:
                i += 1
    return out


def load_csv_days(code: str, data_dir: Path) -> Dict[str, Dict[str, Dict[str, Any]]]:
    days: Dict[str, Dict[str, Dict[str, Any]]] = {}
    if not data_dir.exists():
        return days
    for d in sorted(p for p in data_dir.iterdir() if p.is_dir() and re.match(r"^\d{8}$", p.name)):
        f = d / f"{code}.csv"
        if f.exists():
            for enc in ("utf-8-sig", "cp950", "big5"):
                try:
                    parsed = parse_bsr_csv(f.read_text(enc))
                    break
                except UnicodeDecodeError:
                    parsed = {}
            if parsed:
                days[f"{d.name[:4]}-{d.name[4:6]}-{d.name[6:]}"] = parsed
    return days


def load_finmind_days(code: str, token: str, start: str, cache_dir: Path) -> Dict[str, Dict[str, Dict[str, Any]]]:
    """FinMind TaiwanStockTradingDailyReport（贊助等級）。欄位以容錯方式解析；免費等級會回 400 → 回傳空 dict。"""
    if not token:
        return {}
    key = cache_dir / f"broker_{code}_{dt.date.today():%Y%m%d}.json"
    rows: List[Dict[str, Any]] = []
    if key.exists():
        rows = json.loads(key.read_text("utf-8"))
    else:
        try:
            ctx = ssl.create_default_context()
            try:
                import certifi  # type: ignore
                ctx = ssl.create_default_context(cafile=certifi.where())
            except ImportError:
                pass
            q = urllib.parse.urlencode({"dataset": "TaiwanStockTradingDailyReport", "data_id": code, "start_date": start})
            req = urllib.request.Request(f"{FINMIND}?{q}", headers={"Authorization": f"Bearer {token}", "User-Agent": "DVF-PRO"})
            with urllib.request.urlopen(req, timeout=60, context=ctx) as r:
                payload = json.loads(r.read().decode("utf-8"))
            if payload.get("status") != 200:
                _log(f"FinMind broker data unavailable for {code}: {payload.get('msg')}")
                return {}
            rows = payload.get("data") or []
            cache_dir.mkdir(parents=True, exist_ok=True)
            key.write_text(json.dumps(rows, ensure_ascii=False), "utf-8")
        except Exception as e:  # noqa: BLE001
            _log(f"FinMind broker fetch failed for {code}: {type(e).__name__} {e}")
            return {}
    days: Dict[str, Dict[str, Dict[str, Any]]] = {}
    for r in rows:
        bid = str(r.get("securities_trader_id") or r.get("broker_id") or "").strip()
        name = str(r.get("securities_trader") or r.get("broker") or bid).strip()
        if not bid:
            bid, name = _norm_broker(name)
        d = days.setdefault(r.get("date", ""), {}).setdefault(bid, {"name": name, "buy": 0.0, "sell": 0.0})
        d["buy"] += _num(r.get("buy")) or 0.0
        d["sell"] += _num(r.get("sell")) or 0.0
    return {k: v for k, v in days.items() if k}


# ──────────────────────────────────────────────────────────────────────────────
# 判讀
# ──────────────────────────────────────────────────────────────────────────────
def analyze(code: str, days: Dict[str, Dict[str, Dict[str, Any]]], blacklist: List[str],
            fallback_volume: Optional[Dict[str, float]] = None, source: str = "") -> Dict[str, Any]:
    T = BROKER_TH
    dates = sorted(days)[-T["window_days"]:]
    if not dates:
        return {"signal": "N/A", "source": source or "無", "days_available": 0, "thresholds": T,
                "commentary": "無分點資料（FinMind 分點需贊助等級 token；或將證交所買賣日報表 CSV 放入 broker_data/YYYYMMDD/）。"}
    # 隔日沖：T 日買超、T+1 日賣超 ≥ 80%
    hits: Dict[str, int] = {}
    for a, b in zip(dates, dates[1:]):
        for bid, x in days[a].items():
            nb = x["buy"] - x["sell"]
            y = days[b].get(bid)
            if nb > 0 and y and (y["sell"] - y["buy"]) >= nb * T["daytrade_sell_ratio"]:
                hits[bid] = hits.get(bid, 0) + 1
    auto_dt = {bid for bid, n in hits.items() if n >= T["daytrade_min_hits"]}
    names = {bid: x["name"] for d in dates for bid, x in days[d].items()}
    manual = {bid for bid, nm in names.items() if any(k.replace("-", "") in nm.replace("-", "") for k in blacklist)}
    excluded = auto_dt | manual
    daily = []
    for d in dates:
        vol = sum(x["buy"] for x in days[d].values()) or ((fallback_volume or {}).get(d) or 0) * 1000
        nets = sorted(((bid, x["buy"] - x["sell"]) for bid, x in days[d].items() if bid not in excluded), key=lambda t: -t[1])
        top = [(bid, n) for bid, n in nets if n > 0][:T["top_n"]]
        conc = sum(n for _, n in top) / vol * 100 if vol else None
        daily.append({"date": d, "volume_lots": round(vol / 1000), "conc_pct": round(conc, 2) if conc is not None else None,
                      "top": [{"id": bid, "name": names.get(bid, bid), "net_lots": round(n / 1000)} for bid, n in top]})
    streak, persistent = 0, None
    for row in reversed(daily):
        if row["conc_pct"] is None or row["conc_pct"] <= T["conc_min_pct"]:
            break
        ids = {x["id"] for x in row["top"]}
        nxt = ids if persistent is None else persistent & ids
        if len(nxt) < T["min_persistent"] and streak >= 1:
            break
        persistent, streak = nxt, streak + 1
    persistent = persistent or set()
    hit = streak >= T["min_streak"] and len(persistent) >= T["min_persistent"]
    span = daily[-streak:] if streak else []
    cum = {bid: sum(next((x["net_lots"] for x in r["top"] if x["id"] == bid), 0) for r in span) for bid in persistent}
    pb = [{"id": bid, "name": names.get(bid, bid), "net_lots_streak": cum[bid]} for bid in sorted(persistent, key=lambda b: -cum[b])]
    if hit:
        concs = " / ".join("%.1f%%" % r["conc_pct"] for r in span)
        text = (f"連續 {streak} 日前 {T['top_n']} 大買超分點合計 > 成交量 {T['conc_min_pct']:.0f}%（{concs}），"
                f"特定分點 {'、'.join(x['name'] for x in pb)} 連續進榜，累計買超 {sum(cum.values()):,} 張 → 主力分點鎖碼")
    elif daily[-1]["conc_pct"] is not None:
        text = (f"最新 {daily[-1]['date']} 前 {T['top_n']} 大買超集中度 {daily[-1]['conc_pct']:.1f}%，連續達標 {streak} 日"
                f"（需 ≥ {T['min_streak']} 日且 ≥ {T['min_persistent']} 家相同分點）→ 未觸發")
    else:
        text = "分點資料不足以計算集中度"
    if excluded:
        text += f"；已排除隔日沖分點 {len(excluded)} 家"
    return {"signal": SIGNAL if hit else "NONE", "source": source, "days_available": len(dates), "streak": streak,
            "latest_conc_pct": daily[-1]["conc_pct"], "persistent_brokers": pb, "daily": daily,
            "excluded": [{"id": b, "name": names.get(b, b), "reason": "隔日沖（資料判定）" if b in auto_dt else "隔日沖（手動名單）"}
                         for b in sorted(excluded)],
            "thresholds": T, "commentary": text + "。"}


def annotate(candidates: List[Dict[str, Any]], base_dir: Path = BASE_DIR, token: Optional[str] = None) -> Dict[str, Any]:
    """為每檔候選股寫入 c['broker']，並回傳摘要（scanner.py 呼叫）。"""
    token = token if token is not None else os.environ.get("FINMIND_TOKEN", "")
    blacklist = load_blacklist(base_dir / "broker_blacklist.json")
    data_dir = base_dir / "broker_data"
    start = (dt.date.today() - dt.timedelta(days=21)).isoformat()
    n_hit = n_data = 0
    for c in candidates:
        h = c.get("history") or {}
        fb = dict(zip(h.get("dates", []), h.get("volume", [])))
        days, src = load_csv_days(c["code"], data_dir), "證交所買賣日報表 CSV（手動匯入）"
        if not days:
            days, src = load_finmind_days(c["code"], token, start, base_dir / "cache" / "broker"), "FinMind TaiwanStockTradingDailyReport"
        b = analyze(c["code"], days, blacklist, fb, src if days else "")
        c["broker"] = b
        n_data += b["days_available"] > 0
        n_hit += b["signal"] == SIGNAL
    summary = {"stocks_with_data": n_data, "accumulating": n_hit, "thresholds": BROKER_TH,
               "sources": "CSV: broker_data/YYYYMMDD/<code>.csv；FinMind: FINMIND_TOKEN（贊助等級）"}
    _log(f"broker annotate: {n_data}/{len(candidates)} with data · {n_hit} {SIGNAL}")
    return summary


def main() -> int:
    ap = argparse.ArgumentParser(description="DVF-PRO 主力分點鎖碼篩選")
    ap.add_argument("--data", default=str(BASE_DIR / "candidates.json"))
    ap.add_argument("--codes", nargs="+", help="只分析並印出指定代號（不寫檔）")
    args = ap.parse_args()
    path = Path(args.data)
    data = json.loads(path.read_text("utf-8"))
    cands = [c for c in data["candidates"] if not args.codes or c["code"] in args.codes]
    summary = annotate(cands)
    if args.codes:
        for c in cands:
            print(c["code"], c["name"], json.dumps(c["broker"], ensure_ascii=False, indent=1)[:1500])
        return 0
    data["broker_summary"] = summary
    js = json.dumps(data, ensure_ascii=False, indent=1)
    for name, content in (("candidates.json", js), ("candidates.js", "/* auto-generated by scanner.py */\nwindow.DVF_DATA = " + js + ";\n")):
        tmp = path.with_name(name + ".tmp")
        tmp.write_text(content, "utf-8")
        os.replace(tmp, path.with_name(name))
    _log("candidates.json / candidates.js updated")
    return 0


if __name__ == "__main__":
    sys.exit(main())
