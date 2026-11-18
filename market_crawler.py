#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
DeepValueFund Terminal (DVF-PRO) — market_crawler.py
=====================================================
市場情報彙整：國際財經／期貨頭條、台股新聞、證交所官方重大訊息。只使用 Python 標準函式庫。

來源（皆為公開、免驗證碼）
  1. Google News RSS（國際財經／期貨）— 關鍵字搜尋結果，來自各媒體（Reuters、Bloomberg、CNBC…），
     每則保留實際發布媒體；並非 Bloomberg 官方 RSS。
  2. Google News RSS（台股）— 關鍵字自動帶入核心持股與篩選命中標的名稱。
  3. 證交所 OpenAPI t187ap04_L「上市公司每日重大訊息」— 官方公告，只保留追蹤中的代號。

抓取失敗時只回傳空結果與錯誤原因，不產生任何替代或示範新聞。
scanner.py 會在寫出 candidates.json 前呼叫 fetch_market_intelligence()；亦可單獨執行：
    python market_crawler.py      # 抓取並寫入 candidates.json / candidates.js 的 live_news
新聞標題為外部文字，僅供參考，不構成投資建議。
"""
from __future__ import annotations

import datetime as dt
import json
import os
import re
import ssl
import sys
import urllib.parse
import urllib.request
import xml.etree.ElementTree as ET
from email.utils import parsedate_to_datetime
from pathlib import Path
from typing import Any, Dict, List, Optional

BASE_DIR = Path(__file__).resolve().parent
TPE = dt.timezone(dt.timedelta(hours=8))
GNEWS = "https://news.google.com/rss/search?"
TWSE_MATERIAL = "https://openapi.twse.com.tw/v1/opendata/t187ap04_L"
PER_FEED = 8
RECENCY = "when:3d"     # Google News 搜尋運算子：只取近 3 日，避免撈到數月前的舊頁面
INTL_QUERY = "Bloomberg market headlines OR 國際期貨 OR 原油 OR PVC"      # 沿用原版查詢字串
TW_BASE_TERMS = ["台股 重大訊息", "原物料期貨"]


def _ctx() -> ssl.SSLContext:
    try:
        import certifi  # type: ignore
        ctx = ssl.create_default_context(cafile=certifi.where())
    except ImportError:
        ctx = ssl.create_default_context()
    if hasattr(ssl, "VERIFY_X509_STRICT"):
        ctx.verify_flags &= ~ssl.VERIFY_X509_STRICT   # TWSE 憑證缺 SKI，Python 3.13+ 需關閉 strict
    return ctx


def _get(url: str, timeout: int = 15) -> bytes:
    req = urllib.request.Request(url, headers={"User-Agent": "Mozilla/5.0 DVF-PRO"})
    with urllib.request.urlopen(req, timeout=timeout, context=_ctx()) as r:
        return r.read()


def _tpe_iso(d: dt.datetime) -> str:
    return d.astimezone(TPE).isoformat(timespec="minutes")


def fetch_google_news(label: str, query: str, lang: str = "en-US", gl: str = "US") -> List[Dict[str, Any]]:
    ceid = f"{gl}:{lang.split('-')[0]}" if lang != "zh-TW" else "TW:zh-Hant"
    url = GNEWS + urllib.parse.urlencode({"q": f"({query}) {RECENCY}", "hl": lang, "gl": gl, "ceid": ceid})
    root = ET.fromstring(_get(url))
    out = []
    for it in root.findall(".//item")[:PER_FEED]:
        title = (it.findtext("title") or "").strip()
        src = it.find("source")
        publisher = (src.text or "").strip() if src is not None else ""
        if publisher and title.endswith(" - " + publisher):
            title = title[: -len(publisher) - 3].strip()
        try:
            when = _tpe_iso(parsedate_to_datetime(it.findtext("pubDate") or ""))
        except (TypeError, ValueError):
            when = None
        if title:
            out.append({"kind": "news", "feed": label, "title": title, "publisher": publisher or "Google News",
                        "time": when, "url": (it.findtext("link") or "").strip() or None})
    return out


def fetch_twse_material(codes: List[str]) -> List[Dict[str, Any]]:
    rows = json.loads(_get(TWSE_MATERIAL, timeout=30).decode("utf-8-sig"))
    want = set(codes)
    out = []
    for r in rows:
        code = str(r.get("公司代號", "")).strip()
        if want and code not in want:
            continue
        subj = re.sub(r"\s+", " ", str(r.get("主旨 ") or r.get("主旨") or "")).strip()
        d, t = str(r.get("發言日期", "")), str(r.get("發言時間", "")).zfill(6)
        try:
            when = dt.datetime(int(d[:-4]) + 1911, int(d[-4:-2]), int(d[-2:]), int(t[:2]), int(t[2:4]), tzinfo=TPE).isoformat(timespec="minutes")
        except ValueError:
            when = None
        out.append({"kind": "twse_material", "feed": "證交所重大訊息（官方）", "code": code,
                    "name": str(r.get("公司名稱", "")).strip(), "title": f"{code} {str(r.get('公司名稱', '')).strip()}：{subj}",
                    "subject": subj, "clause": str(r.get("符合條款", "")).strip(), "publisher": "TWSE / MOPS",
                    "time": when, "url": None, "detail": str(r.get("說明", "")).replace("\r", "").strip()[:800]})
    return out


def fetch_market_intelligence(watch: Optional[List[Dict[str, str]]] = None) -> Dict[str, Any]:
    """
    watch：[{"code": "2392", "name": "正崴"}, ...]（scanner.py 傳入核心持股＋篩選命中＋自選）。
    回傳 {"updated_at", "items", "errors", "sources"}；不寫檔、不產生替代新聞。
    """
    watch = watch or []
    now = dt.datetime.now(TPE)
    print(f"=== [DVF-PRO] 市場情報彙整 ({now:%Y-%m-%d %H:%M}) ===", flush=True)
    names = [w["name"] for w in watch if w.get("name")][:6]
    tw_query = " OR ".join(TW_BASE_TERMS + names)
    tasks = [("國際財經／期貨（Google News）", lambda: fetch_google_news("國際財經／期貨（Google News）", INTL_QUERY, "en-US", "US")),
             ("台股新聞（Google News）", lambda: fetch_google_news("台股新聞（Google News）", tw_query, "zh-TW", "TW")),
             ("證交所重大訊息（官方）", lambda: fetch_twse_material([w["code"] for w in watch]))]
    items: List[Dict[str, Any]] = []
    errors: List[str] = []
    for label, fn in tasks:
        try:
            got = fn()
            items += got
            print(f"  {label}: {len(got)} 筆", flush=True)
        except Exception as e:  # noqa: BLE001
            errors.append(f"{label}: {type(e).__name__} {e}")
            print(f"  ⚠ {label} 失敗：{type(e).__name__} {e}", flush=True)
    seen, uniq = set(), []
    for it in items:
        k = re.sub(r"\W+", "", it["title"].lower())[:80]
        if k not in seen:
            seen.add(k)
            uniq.append(it)
    uniq.sort(key=lambda x: x.get("time") or "", reverse=True)
    print(f"✅ 市場情報 {len(uniq)} 筆" + (f"（{len(errors)} 個來源失敗）" if errors else ""), flush=True)
    return {"updated_at": now.isoformat(timespec="seconds"), "items": uniq, "errors": errors,
            "sources": ["Google News RSS（國際／台股關鍵字搜尋，非 Bloomberg 官方）", "TWSE OpenAPI t187ap04_L（上市公司每日重大訊息）"],
            "queries": {"intl": INTL_QUERY, "tw": tw_query}}


def _watch_from(data: Dict[str, Any]) -> List[Dict[str, str]]:
    return [{"code": c["code"], "name": c.get("name", "")} for c in data.get("candidates", [])]


def main() -> int:
    path = BASE_DIR / "candidates.json"
    data = json.loads(path.read_text("utf-8")) if path.exists() else {"candidates": []}
    news = fetch_market_intelligence(_watch_from(data))
    data["live_news"], data["news_updated_at"], data["news_meta"] = news["items"], news["updated_at"], \
        {k: news[k] for k in ("errors", "sources", "queries")}
    js = json.dumps(data, ensure_ascii=False, indent=1)
    for name, content in (("candidates.json", js), ("candidates.js", "/* auto-generated by scanner.py */\nwindow.DVF_DATA = " + js + ";\n")):
        tmp = BASE_DIR / (name + ".tmp")
        tmp.write_text(content, "utf-8")
        os.replace(tmp, BASE_DIR / name)
    print("已寫入 candidates.json / candidates.js（live_news）")
    return 0


if __name__ == "__main__":
    sys.exit(main())
