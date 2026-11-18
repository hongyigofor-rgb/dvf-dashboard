#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
DeepValueFund Terminal (DVF-PRO) — intraday_monitor.py
=======================================================
盤中輕量監控：讀 candidates.json 的候選股與基準值 → 批次抓證交所 MIS 即時行情 → 重算即時漲跌、P/B、
預估量比、均線位置 → 規則引擎產生 live_review / alerts → 寫 live_quotes.json / live_quotes.js（window.DVF_LIVE）。

    python intraday_monitor.py --once     # 單次快照（測試用）
    python intraday_monitor.py --loop     # 週一至週五 09:00–13:35 每 20 秒一輪；其餘時段只做一次快照後結束

只使用 Python 標準函式庫。資料源：https://mis.twse.com.tw/stock/api/getStockInfo.jsp（公開、免登入；
上市 tse_、上櫃 otc_）。每輪只發 1 個批次請求（每批最多 50 檔），請勿把間隔調到 5 秒以下以免被暫時封鎖。
重大警報（🔥 / 🚨 / 🎯 / 核心持股 ✅）以 .live_alert_sent_YYYYMMDD.json 去重，同一天同一檔同一類只通知一次。
.env 設定 SUPABASE_URL 與 SUPABASE_ANON_KEY 時，每 60 秒 upsert 一份到 Supabase（表名 SUPABASE_LIVE_TABLE，預設 dvf_live_quotes）。
本工具為盤中參考訊號，不構成投資建議；預估量比以線性外推，早盤通常偏高。
"""
from __future__ import annotations

import argparse
import datetime as dt
import json
import os
import ssl
import subprocess
import sys
import time
import urllib.parse
import urllib.request
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple

BASE_DIR = Path(__file__).resolve().parent
TPE = dt.timezone(dt.timedelta(hours=8))
MIS_URL = "https://mis.twse.com.tw/stock/api/getStockInfo.jsp"
LOOP_SEC = 20
SUPABASE_SEC = 60
PUBLISH_SEC = 60          # GitHub Pages 發布間隔（publish_site.py，背景執行）
OPEN_MIN, CLOSE_MIN, LOOP_END_MIN = 9 * 60, 13 * 60 + 30, 13 * 60 + 35
SESSION_MIN = 270          # 09:00–13:30
SMOOTH_MIN = 15            # 開盤前 15 分鐘以 15 分鐘計，避免預估量暴衝
BATCH = 50
TH = {"breakout_vr": 1.5, "surge_vr": 2.0, "surge_chg": 2.0}
NOTIFY_TYPES = {"STOP", "TARGET", "BREAKOUT", "CORE_RECLAIM"}
LOG_PATH = BASE_DIR / "logs" / "intraday.log"


def now_tpe() -> dt.datetime:
    return dt.datetime.now(TPE)


def log(msg: str) -> None:
    line = f"{now_tpe():%Y-%m-%d %H:%M:%S} {msg}"
    print(line, flush=True)
    try:
        LOG_PATH.parent.mkdir(exist_ok=True)
        if LOG_PATH.exists() and LOG_PATH.stat().st_size > 5 * 1024 * 1024:
            os.replace(LOG_PATH, LOG_PATH.with_suffix(".log.1"))
        with LOG_PATH.open("a", encoding="utf-8") as f:
            f.write(line + "\n")
    except OSError:
        pass


def load_env(path: Path) -> Dict[str, str]:
    env: Dict[str, str] = {}
    if path.exists():
        for line in path.read_text("utf-8").splitlines():
            line = line.strip()
            if line and not line.startswith("#") and "=" in line:
                k, v = line.split("=", 1)
                env[k.strip()] = v.strip().strip('"').strip("'")
    for k in ("SUPABASE_URL", "SUPABASE_ANON_KEY", "SUPABASE_LIVE_TABLE", "CORE_POSITIONS"):
        if os.environ.get(k):
            env[k] = os.environ[k]
    return env


def _ctx() -> ssl.SSLContext:
    try:
        import certifi  # type: ignore
        ctx = ssl.create_default_context(cafile=certifi.where())
    except ImportError:
        ctx = ssl.create_default_context()
    if hasattr(ssl, "VERIFY_X509_STRICT"):
        ctx.verify_flags &= ~ssl.VERIFY_X509_STRICT
    return ctx


def num(v: Any) -> Optional[float]:
    try:
        f = float(str(v).replace(",", ""))
        return f if f > 0 else None
    except (TypeError, ValueError):
        return None


def r2(v: Optional[float], d: int = 2) -> Optional[float]:
    return None if v is None else round(v, d)


# ── 基準資料 ──────────────────────────────────────────────────────────────────
def parse_core(spec: str) -> Dict[str, Dict[str, Any]]:
    """CORE_POSITIONS=代號:目標價[:成本[:張數]] → 核心持股（雲端無 AI 覆盤時以 secret 提供）。"""
    out: Dict[str, Dict[str, Any]] = {}
    for item in (spec or "").split(","):
        f = [x.strip() for x in item.split(":")]
        try:
            if f[0]:
                cost = float(f[2]) if len(f) > 2 and f[2] else None
                out[f[0]] = {"code": f[0], "target": float(f[1]) if len(f) > 1 and f[1] else None, "cost": cost,
                             "hard_stop": round(cost * 0.92, 2) if cost else None}
        except ValueError:
            continue
    return out


def load_baseline(path: Path, core_spec: str = "") -> Tuple[Dict[str, Any], List[Dict[str, Any]]]:
    data = json.loads(path.read_text("utf-8"))
    core = {p["code"]: p for p in ((data.get("daily_briefing") or {}).get("core_positions") or []) if not p.get("missing")}
    if not core and core_spec:
        core = parse_core(core_spec)
    out = []
    for c in data.get("candidates", []):
        tm = c.get("tech_metrics") or {}
        cp = core.get(c["code"])
        out.append({
            "code": c["code"], "name": c.get("name", ""), "market": c.get("market", "TWSE"),
            "bvps": c.get("book_value"), "ma20": tm.get("ma20"), "ma60": tm.get("ma60"),
            "avg_vol_20": c.get("avg_vol_20"), "prev_close_scan": c.get("close"),
            "tech_rating": tm.get("tech_rating"), "tech_short": tm.get("tech_short"),
            "is_core": bool(cp),
            # 核心持股：以持有成本 −8% 為硬停損、CORE_POSITIONS 目標價；其餘：掃描收盤為計畫進場價、−8% 停損、T0.85 目標
            "entry": (cp or {}).get("cost") or c.get("close"),
            "entry_basis": "持有成本" if cp and cp.get("cost") else "掃描收盤（計畫進場參考）",
            "stop": (cp or {}).get("hard_stop") or c.get("stop_loss_price"),
            "stop_basis": "成本 −8% 硬停損" if cp and cp.get("hard_stop") else "計畫進場 −8% 停損",
            "target": (cp or {}).get("target") or c.get("target_price_085"),
            "target_basis": "CORE_POSITIONS 目標價" if cp and cp.get("target") else "T0.85（0.85×BVPS）",
        })
    return {"data_date": data.get("data_date"), "generated_at": data.get("generated_at")}, out


# ── MIS 即時行情 ─────────────────────────────────────────────────────────────
def fetch_mis(stocks: List[Dict[str, Any]]) -> Dict[str, Dict[str, Any]]:
    out: Dict[str, Dict[str, Any]] = {}
    for i in range(0, len(stocks), BATCH):
        chunk = stocks[i:i + BATCH]
        ex_ch = "|".join(f"{'otc' if s['market'] == 'TPEx' else 'tse'}_{s['code']}.tw" for s in chunk)
        url = MIS_URL + "?" + urllib.parse.urlencode({"ex_ch": ex_ch, "json": 1, "delay": 0, "_": int(time.time() * 1000)}, safe="|_.")
        req = urllib.request.Request(url, headers={"User-Agent": "Mozilla/5.0 DVF-PRO", "Referer": "https://mis.twse.com.tw/stock/index.jsp"})
        with urllib.request.urlopen(req, timeout=10, context=_ctx()) as r:
            js = json.loads(r.read().decode("utf-8"))
        if js.get("rtcode") != "0000":
            raise RuntimeError(f"MIS rtcode {js.get('rtcode')} {js.get('rtmessage')}")
        for m in js.get("msgArray", []):
            out[str(m.get("c"))] = m
    return out


def parse_quote(m: Dict[str, Any], prev_scan: Optional[float]) -> Dict[str, Any]:
    first = lambda s: num((s or "").split("_")[0])  # noqa: E731
    z, b, a, y = num(m.get("z")), first(m.get("b")), first(m.get("a")), num(m.get("y"))
    if z:
        price, src = z, "成交"
    elif b and a:
        price, src = round((b + a) / 2, 2), "買賣中價"
    elif b or a:
        price, src = b or a, "最佳買價" if b else "最佳賣價"
    else:
        price, src = y or prev_scan, "昨收"
    d, t = str(m.get("d") or ""), str(m.get("t") or "")
    return {"price": price, "price_src": src, "prev_close": y or prev_scan, "open": num(m.get("o")), "high": num(m.get("h")),
            "low": num(m.get("l")), "vol_lots": int(num(m.get("v")) or 0), "bid": b, "ask": a,
            "session_date": f"{d[:4]}-{d[4:6]}-{d[6:]}" if len(d) == 8 else None, "mis_time": t or None}


def elapsed_minutes(session_date: Optional[str], mis_time: Optional[str], now: dt.datetime) -> int:
    """已開盤分鐘數（0–270）：非今日場次或已收盤 → 270。"""
    if session_date != now.date().isoformat():
        return SESSION_MIN
    try:
        hh, mm = int(mis_time[:2]), int(mis_time[3:5])  # type: ignore[index]
        m = hh * 60 + mm
    except (TypeError, ValueError):
        m = now.hour * 60 + now.minute
    return max(0, min(SESSION_MIN, m - OPEN_MIN))


# ── 規則引擎 ─────────────────────────────────────────────────────────────────
def review(b: Dict[str, Any], q: Dict[str, Any], elapsed: int) -> Dict[str, Any]:
    p, prev = q["price"], q["prev_close"]
    chg = (p - prev) if p and prev else None
    chg_pct = chg / prev * 100 if chg is not None else None
    est = q["vol_lots"] * SESSION_MIN / max(elapsed, SMOOTH_MIN) if elapsed > 0 else None
    vr = est / b["avg_vol_20"] if est is not None and b.get("avg_vol_20") else None
    bias = lambda m: (p / m - 1) * 100 if p and m else None  # noqa: E731
    b20, b60 = bias(b["ma20"]), bias(b["ma60"])
    above20 = b20 is not None and b20 >= 0
    above60 = b60 is not None and b60 >= 0
    was_above20 = bool(prev and b["ma20"] and prev >= b["ma20"])
    state = ("ABOVE_BOTH" if above20 and above60 else "ABOVE_MA20" if above20 else "ABOVE_MA60" if above60
             else "BELOW_BOTH" if b20 is not None else "NA")
    label = {"ABOVE_BOTH": "站上月線與季線", "ABOVE_MA20": "站上月線、季線下", "ABOVE_MA60": "月線下、季線上",
             "BELOW_BOTH": "月線與季線下", "NA": "均線資料不足"}[state]
    cross = "盤中站上月線" if above20 and not was_above20 else "盤中跌破月線" if not above20 and was_above20 and b20 is not None else None

    items: List[Dict[str, str]] = []
    add = lambda typ, icon, level, msg: items.append({"type": typ, "icon": icon, "level": level, "msg": msg})  # noqa: E731
    if p and b.get("stop") and p <= b["stop"]:
        add("STOP", "🚨", "HIGH", f"🚨 跌破風控停損線 {b['stop']:.2f}（{b['stop_basis']}），建議執行紀律")
    if p and b.get("target") and p >= b["target"]:
        add("TARGET", "🎯", "HIGH", f"🎯 觸及目標價區 {b['target']:.2f}（{b['target_basis']}），可分批獲利了結")
    if b.get("tech_rating") != "STRONG_BREAKOUT" and above20 and vr is not None and vr >= TH["breakout_vr"]:
        add("BREAKOUT", "🔥", "HIGH", f"🔥 盤中帶量突破月線，右側點火訊號（預估量比 {vr:.2f}x，月線 {b['ma20']:.2f}）")
    if vr is not None and vr >= TH["surge_vr"] and chg_pct is not None and chg_pct > TH["surge_chg"]:
        add("SURGE", "⚡", "MEDIUM", f"⚡ 盤中異常爆量上攻，主力點火（預估量比 {vr:.2f}x、漲幅 {chg_pct:+.2f}%）")
    if vr is not None and vr >= TH["surge_vr"] and chg_pct is not None and chg_pct < -TH["surge_chg"]:
        add("DUMP", "🔻", "MEDIUM", f"🔻 盤中爆量下殺，留意賣壓與停損（預估量比 {vr:.2f}x、跌幅 {chg_pct:+.2f}%）")
    if b["is_core"] and b20 is not None:
        if above20 and not was_above20:
            add("CORE_RECLAIM", "✅", "HIGH", f"✅ {b['name']}盤中收復月線轉強（月線 {b['ma20']:.2f}，{b20:+.1f}%）")
        elif above20:
            add("CORE_WATCH", "🛡️", "INFO", f"🛡️ {b['name']}站穩月線之上（{b20:+.1f}%）")
        else:
            add("CORE_WATCH", "🛡️", "INFO", f"🛡️ {b['name']}距月線 {b['ma20']:.2f} 還差 {-b20:.1f}%（需漲至 {b['ma20']:.2f}）")
    if not any(x["level"] in ("HIGH", "MEDIUM") for x in items):
        add("CALM", "·", "INFO", f"盤中量價平穩（預估量比 {vr:.2f}x，距月線 {b20:+.1f}%）" if vr is not None and b20 is not None
            else "盤中量價平穩（量比或均線資料不足）")
    order = {"HIGH": 0, "MEDIUM": 1, "INFO": 2}
    items.sort(key=lambda x: order[x["level"]])
    return {
        "code": b["code"], "name": b["name"], **q,
        "change": r2(chg), "change_pct": r2(chg_pct), "elapsed_min": elapsed,
        "est_vol_lots": round(est) if est is not None else None, "avg_vol_20": b.get("avg_vol_20"), "est_vol_ratio": r2(vr),
        "bvps": b.get("bvps"), "pb_live": r2(p / b["bvps"]) if p and b.get("bvps") else None,
        "ma20": b["ma20"], "ma60": b["ma60"], "bias_ma20_pct": r2(b20), "bias_ma60_pct": r2(b60),
        "live_tech": {"state": state, "label": label, "cross": cross},
        "tech_rating": b.get("tech_rating"), "tech_short": b.get("tech_short"), "is_core": b["is_core"],
        "entry": b.get("entry"), "entry_basis": b["entry_basis"], "stop": b.get("stop"), "stop_basis": b["stop_basis"],
        "target": b.get("target"), "target_basis": b["target_basis"],
        "to_stop_pct": r2((b["stop"] / p - 1) * 100) if p and b.get("stop") else None,
        "to_target_pct": r2((b["target"] / p - 1) * 100) if p and b.get("target") else None,
        "live_review": items, "review_text": items[0]["msg"],
    }


# ── 通知與同步 ───────────────────────────────────────────────────────────────
def notify_new(alerts: List[Dict[str, Any]], today: str) -> int:
    path = BASE_DIR / f".live_alert_sent_{today.replace('-', '')}.json"
    for old in BASE_DIR.glob(".live_alert_sent_*.json"):
        if old != path:
            old.unlink(missing_ok=True)
    sent = set(json.loads(path.read_text("utf-8"))) if path.exists() else set()
    n = 0
    for a in alerts:
        key = f"{a['code']}:{a['type']}"
        if a["type"] not in NOTIFY_TYPES or key in sent:
            continue
        msg = a["msg"].replace('"', "'").replace("\\", "")
        title = f"DVF-PRO 盤中 · {a['code']} {a['name']} {a['price']}"
        try:
            subprocess.run(["/usr/bin/osascript", "-e", f'display notification "{msg}" with title "{title}" sound name "Glass"'],
                           timeout=10, capture_output=True)
        except (OSError, subprocess.SubprocessError):
            pass
        sent.add(key)
        n += 1
        log(f"NOTIFY {key} {a['msg']}")
    path.write_text(json.dumps(sorted(sent), ensure_ascii=False), "utf-8")
    return n


def supabase_sync(env: Dict[str, str], payload: Dict[str, Any]) -> str:
    url, key = env.get("SUPABASE_URL", "").rstrip("/"), env.get("SUPABASE_ANON_KEY", "")
    table = env.get("SUPABASE_LIVE_TABLE") or "dvf_live_quotes"
    body = json.dumps([{"id": "latest", "updated_at": payload["updated_at"], "payload": payload}], ensure_ascii=False).encode("utf-8")
    req = urllib.request.Request(f"{url}/rest/v1/{table}?on_conflict=id", data=body, method="POST", headers={
        "apikey": key, "Authorization": f"Bearer {key}", "Content-Type": "application/json",
        "Prefer": "resolution=merge-duplicates,return=minimal"})
    with urllib.request.urlopen(req, timeout=10, context=_ctx()) as r:
        return str(r.status)


def publish_ready() -> bool:
    cfg = BASE_DIR / "site" / ".git" / "config"
    return cfg.exists() and '[remote "origin"]' in cfg.read_text("utf-8", errors="ignore")


def start_publish(prev: Optional[subprocess.Popen], wait: bool = False) -> Optional[subprocess.Popen]:
    """背景執行 publish_site.py；上一次尚未結束就略過。"""
    if prev is not None and prev.poll() is None:
        return prev
    out = (BASE_DIR / "logs" / "publish.log").open("a")
    proc = subprocess.Popen([sys.executable, str(BASE_DIR / "publish_site.py")], cwd=str(BASE_DIR),
                            stdout=out, stderr=subprocess.STDOUT, start_new_session=True)
    if wait:
        try:
            proc.wait(timeout=150)
        except subprocess.TimeoutExpired:
            pass
    return proc


def write_outputs(payload: Dict[str, Any]) -> None:
    js = json.dumps(payload, ensure_ascii=False, indent=1)
    for name, content in (("live_quotes.json", js),
                          ("live_quotes.js", "/* auto-generated by intraday_monitor.py */\nwindow.DVF_LIVE = " + js + ";\n")):
        tmp = BASE_DIR / (name + ".tmp")
        tmp.write_text(content, "utf-8")
        os.replace(tmp, BASE_DIR / name)


# ── 主流程 ───────────────────────────────────────────────────────────────────
def in_loop_window(now: dt.datetime) -> bool:
    m = now.hour * 60 + now.minute
    return now.weekday() < 5 and OPEN_MIN <= m < LOOP_END_MIN


def snapshot(base_meta: Dict[str, Any], base: List[Dict[str, Any]], notify: bool) -> Dict[str, Any]:
    now = now_tpe()
    errors: List[str] = []
    try:
        mis = fetch_mis(base)
    except Exception as e:  # noqa: BLE001
        mis = {}
        errors.append(f"MIS: {type(e).__name__} {e}")
    quotes: Dict[str, Any] = {}
    alerts: List[Dict[str, Any]] = []
    sess = None
    for b in base:
        m = mis.get(b["code"])
        if not m:
            errors.append(f"{b['code']} 無 MIS 報價")
            continue
        q = parse_quote(m, b["prev_close_scan"])
        sess = sess or q["session_date"]
        r = review(b, q, elapsed_minutes(q["session_date"], q["mis_time"], now))
        quotes[b["code"]] = r
        for it in r["live_review"]:
            if it["level"] in ("HIGH", "MEDIUM"):
                alerts.append({"code": b["code"], "name": b["name"], "price": r["price"], "change_pct": r["change_pct"],
                               "time": r["mis_time"], **it})
    alerts.sort(key=lambda a: ({"HIGH": 0, "MEDIUM": 1}[a["level"]], a["code"]))
    m_now = now.hour * 60 + now.minute
    today = now.date().isoformat()
    market_open = bool(sess == today and now.weekday() < 5 and OPEN_MIN <= m_now < CLOSE_MIN + 5)
    phase = "OPEN" if market_open else "PRE" if now.weekday() < 5 and m_now < OPEN_MIN else "CLOSED"
    payload = {"schema": "dvf-pro-live/1", "updated_at": now.isoformat(timespec="seconds"), "market_open": market_open,
               "phase": phase, "session_date": sess, "baseline_data_date": base_meta.get("data_date"),
               "loop_sec": LOOP_SEC, "source": "TWSE MIS getStockInfo.jsp（盤中約 5 秒延遲）",
               "thresholds": TH, "alerts": alerts, "quotes": quotes, "errors": errors}
    write_outputs(payload)
    if notify and sess == today:
        notify_new(alerts, today)
    return payload


def acquire_lock() -> Optional[Path]:
    lock = BASE_DIR / "logs" / ".intraday.pid"
    lock.parent.mkdir(exist_ok=True)
    if lock.exists():
        try:
            os.kill(int(lock.read_text().strip()), 0)
            return None
        except (ValueError, OSError):
            pass
    lock.write_text(str(os.getpid()))
    return lock


def main() -> int:
    ap = argparse.ArgumentParser(description="DVF-PRO intraday live monitor")
    g = ap.add_mutually_exclusive_group()
    g.add_argument("--loop", action="store_true", help="週一至週五 09:00–13:35 每 20 秒循環；其餘時段快照一次後結束")
    g.add_argument("--once", action="store_true", help="單次快照（預設）")
    ap.add_argument("--data", default=str(BASE_DIR / "candidates.json"))
    ap.add_argument("--no-notify", action="store_true", help="不發 macOS 通知")
    ap.add_argument("--no-sync", action="store_true", help="不同步 Supabase")
    ap.add_argument("--no-publish", action="store_true", help="不發布到 GitHub Pages")
    args = ap.parse_args()

    data_path = Path(args.data)
    if not data_path.exists():
        log("找不到 candidates.json，請先執行 scanner.py")
        return 2
    lock = acquire_lock() if args.loop else None
    if args.loop and lock is None:
        log("另一個 --loop 監控仍在執行，略過")
        return 0
    env = load_env(BASE_DIR / ".env")
    use_sb = bool(env.get("SUPABASE_URL") and env.get("SUPABASE_ANON_KEY")) and not args.no_sync
    last_sb, mtime, last_pub = 0.0, 0.0, 0.0
    pub_proc: Optional[subprocess.Popen] = None
    use_pub = not args.no_publish and publish_ready()
    base_meta: Dict[str, Any] = {}
    base: List[Dict[str, Any]] = []
    try:
        if args.loop:   # 08:30–09:00 啟動 → 等到開盤
            now = now_tpe()
            if now.weekday() < 5 and 8 * 60 + 30 <= now.hour * 60 + now.minute < OPEN_MIN:
                wait = (now.replace(hour=9, minute=0, second=0, microsecond=0) - now).total_seconds()
                log(f"等待開盤 {wait:.0f} 秒")
                time.sleep(max(0, wait))
        rounds = 0
        while True:
            t0 = time.time()
            if data_path.stat().st_mtime != mtime:   # 15:10 掃描更新後自動換新基準
                mtime = data_path.stat().st_mtime
                base_meta, base = load_baseline(data_path, env.get("CORE_POSITIONS", ""))
            pl = snapshot(base_meta, base, notify=not args.no_notify)
            rounds += 1
            hi = sum(1 for a in pl["alerts"] if a["level"] == "HIGH")
            log(f"{'LIVE' if pl['market_open'] else 'SNAP'} 場次 {pl['session_date']} · {len(pl['quotes'])}/{len(base)} 檔 · "
                f"警報 {hi} 重大 / {len(pl['alerts'])} 總計" + (f" · 錯誤 {len(pl['errors'])}" if pl["errors"] else ""))
            if rounds == 1:
                for a in pl["alerts"]:
                    log(f"  {a['code']} {a['name']} {a['price']} · {a['msg']}")
            if use_sb and time.time() - last_sb >= SUPABASE_SEC:
                try:
                    supabase_sync(env, pl)
                    last_sb = time.time()
                except Exception as e:  # noqa: BLE001
                    log(f"Supabase 同步失敗：{type(e).__name__} {e}")
                    last_sb = time.time()
            if use_pub and time.time() - last_pub >= PUBLISH_SEC:
                pub_proc = start_publish(pub_proc, wait=not args.loop)
                last_pub = time.time()
            now = now_tpe()
            if not args.loop or not in_loop_window(now):
                break
            # 平日盤中但 MIS 場次不是今天（國定假日）：09:10 後確認即結束
            if pl["session_date"] and pl["session_date"] != now.date().isoformat() and now.hour * 60 + now.minute >= OPEN_MIN + 10:
                log(f"今日無交易（MIS 場次 {pl['session_date']}），結束監控")
                break
            time.sleep(max(1.0, LOOP_SEC - (time.time() - t0)))
    except KeyboardInterrupt:
        log("中斷")
    finally:
        if lock and lock.exists():
            lock.unlink(missing_ok=True)
    log("監控結束")
    return 0


if __name__ == "__main__":
    sys.exit(main())
