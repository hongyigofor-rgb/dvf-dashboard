#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
DeepValueFund Terminal (DVF-PRO) — scanner.py
================================================
盤後自動化數據爬蟲 + 多因子深度價值轉機篩選引擎 + 流動性風控計算器。

資料來源
  - TWSE OpenAPI : BWIBBU_ALL (本益比/殖利率/股價淨值比)、STOCK_DAY_ALL (日成交資訊)
  - TPEx OpenAPI : tpex_mainboard_peratio_analysis、tpex_mainboard_daily_close_quotes
  - FinMind v4   : TaiwanStockFinancialStatements (單季 EPS)、TaiwanStockPrice (量能歷史)
  - Yahoo Finance: v8 chart（CL=F、CT=F、HG=F、^BDI→BDRY、ZC=F 國際商品期貨；{code}.TW/.TWO 個股序列）
  - Yahoo Finance: 跨國同業標竿（台股龍頭 1402/1301/1904/1101/2002/2603/1216 …、中美指標 601233.SS/DOW/IP …）
  - 新浪財經    : InnerFuturesNewService.getDailyKLine（PF0 短纖、TA0 PTA、EB0 苯乙烯、SP0 紙漿、V0 PVC、EG0 乙二醇）
  - 公司基本資料 : TWSE t187ap03_L / TPEx mopsfin_t187ap03_O（產業別）

宏觀商品連動（Macro & Commodity Linkage Engine）＋ 領先－滯後時間序列引擎
  依細分產業鏈配對 1~3 個期貨因子，計算 Lag 0 / Lead 5·10·20D 的 Pearson r 與方向一致率，
  以「產業直接度 × 領先相關強度」推算建議權重，加權 20 日利差判讀 TAILWIND / NEUTRAL / HEADWIND（不影響三道濾網）。

合理市價模擬（Fair Value）
  A 利差與 ROE 折現（Gordon P/B，45%）＋ B 跨國同業比價（35%）＋ C 淨值中樞 0.85x（20%）→ Bear / Base / Bull 三情境。

三道濾網（＋產業純化）
  1. 深度價值安全邊際 : 0 < P/B <= 0.8
  2. 籌碼洗淨窒息量   : 當日成交張數 >= 300 張 (解除上限，VCS 僅作標籤與排序參考)
  ◆ 景氣循環產業白名單：只保留紡織、塑膠、造紙、鋼鐵、電纜、化學、橡膠、航運、水泥、食品、油電燃氣；
     剔除營建、金融、觀光、文創、生技、電子代工等（避免建商交屋入帳造成的假性虧轉盈）
  3. 基本面拐點驗證   : 最新單季 EPS > 0，且 (去年同季 EPS < 0 → 由虧轉盈) 或 (YoY 成長 >= 50%)

輸出
  candidates.json  — dashboard.html 透過 HTTP 讀取
  candidates.js    — 同內容包成 window.DVF_DATA，讓 file:// 雙擊開啟也能載入

只使用 Python 標準函式庫（certifi 為選用，可解決 macOS 憑證問題）。相容 Python 3.9+。
本程式僅為研究/教育用途之量化篩選工具，不構成任何投資建議。
"""
from __future__ import annotations

import argparse
import bisect
import csv
import io
import concurrent.futures
import datetime as dt
import json
import logging
import math
import os
import re
import ssl
import subprocess
import sys
import time
import urllib.error
import urllib.parse
import urllib.request
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple

# ──────────────────────────────────────────────────────────────────────────────
# 常數設定
# ──────────────────────────────────────────────────────────────────────────────
TPE = dt.timezone(dt.timedelta(hours=8))
BASE_DIR = Path(__file__).resolve().parent

TWSE_PB = "https://openapi.twse.com.tw/v1/exchangeReport/BWIBBU_ALL"
TWSE_QUOTE = "https://openapi.twse.com.tw/v1/exchangeReport/STOCK_DAY_ALL"
# OpenAPI 通常延遲到隔日才更新 → 以 TWSE 官網盤後端點作為「當日」備援來源
TWSE_RWD_PB = "https://www.twse.com.tw/rwd/zh/afterTrading/BWIBBU_d"
TWSE_RWD_QUOTE = "https://www.twse.com.tw/rwd/zh/afterTrading/MI_INDEX"
TPEX_PB = "https://www.tpex.org.tw/openapi/v1/tpex_mainboard_peratio_analysis"
TPEX_QUOTE = "https://www.tpex.org.tw/openapi/v1/tpex_mainboard_daily_close_quotes"
FINMIND = "https://api.finmindtrade.com/api/v4/data"
YAHOO_CHART = "https://query1.finance.yahoo.com/v8/finance/chart/{symbol}"
SINA_KLINE = "https://stock2.finance.sina.com.cn/futures/api/jsonp.php/var=/InnerFuturesNewService.getDailyKLine"
TWSE_COMPANY = "https://openapi.twse.com.tw/v1/opendata/t187ap03_L"
TWSE_FIN_INCOME = "https://openapi.twse.com.tw/v1/opendata/t187ap06_L_ci"    # 一般業綜合損益表（最新一期、年度累計、千元）
TWSE_FIN_BALANCE = "https://openapi.twse.com.tw/v1/opendata/t187ap07_L_ci"   # 一般業資產負債表
TDCC_HOLDING = "https://opendata.tdcc.com.tw/getOD.ashx?id=1-5"              # 集保戶股權分散表（僅最新一週）
TPEX_COMPANY = "https://www.tpex.org.tw/openapi/v1/mopsfin_t187ap03_O"

DEFAULTS = {
    "pb_max": 0.80,          # 第一道濾網：P/B 上限
    "vol_min": 300,          # 第二道濾網：成交張數下限
    "vol_max": 2500,         # 第二道濾網：成交張數上限
    "eps_growth_min": 0.50,  # 第三道濾網：YoY 成長門檻
    "stop_pct": 0.08,        # 硬停損 -8%
    "hc_rr": 3.0,            # 風報比 >= 3.0 → HIGH CONVICTION
}

# ── 宏觀商品期貨 ─────────────────────────────────────────────────────────────
# sources：依序嘗試的 Yahoo 代碼。Yahoo 已不提供 ^BDI，改以 BDRY（Breakwave 乾散貨運費 ETF）作為代理。
COMMODITIES = [
    {"symbol": "CL=F", "name": "WTI CRUDE", "zh": "WTI 原油", "short": "原油", "unit": "USD/bbl", "sources": ["CL=F"]},
    {"symbol": "CT=F", "name": "ICE COTTON #2", "zh": "ICE 棉花", "short": "棉花", "unit": "USc/lb", "sources": ["CT=F"]},
    {"symbol": "HG=F", "name": "COMEX COPPER", "zh": "COMEX 精銅", "short": "銅", "unit": "USD/lb", "sources": ["HG=F"]},
    {"symbol": "^BDI", "name": "BALTIC DRY INDEX", "zh": "波羅的海乾散貨", "short": "BDI", "unit": "pts", "sources": ["^BDI", "BDRY"]},
    {"symbol": "ZC=F", "name": "CBOT CORN", "zh": "CBOT 玉米", "short": "玉米", "unit": "USc/bu", "sources": ["ZC=F"]},
]
COMMODITY_BY_SYMBOL = {c["symbol"]: c for c in COMMODITIES}

INDUSTRY_NAMES = {
    "01": "水泥工業", "02": "食品工業", "03": "塑膠工業", "04": "紡織纖維", "05": "電機機械", "06": "電器電纜",
    "08": "玻璃陶瓷", "09": "造紙工業", "10": "鋼鐵工業", "11": "橡膠工業", "12": "汽車工業", "14": "建材營造",
    "15": "航運業", "16": "觀光餐旅", "17": "金融保險", "18": "貿易百貨", "19": "綜合", "20": "其他",
    "21": "化學工業", "22": "生技醫療", "23": "油電燃氣", "24": "半導體", "25": "電腦及週邊設備", "26": "光電",
    "27": "通信網路", "28": "電子零組件", "29": "電子通路", "30": "資訊服務", "31": "其他電子", "32": "文化創意",
    "33": "農業科技", "34": "電子商務", "35": "綠能環保", "36": "數位雲端", "37": "運動休閒", "38": "居家生活",
}

# ── 細分產業鏈因子模型（Lead-Lag Time-Series Engine）─────────────────────────
# src：sina＝新浪財經中國期貨主連；macro＝上方 Yahoo 國際期貨；derived＝由其他因子推算
FACTORS = {
    "PF0": {"src": "sina", "name": "鄭商所短纖（聚酯加工絲代表）", "short": "加工絲PF0", "unit": "CNY/t"},
    "TA0": {"src": "sina", "name": "鄭商所 PTA", "short": "PTA TA0", "unit": "CNY/t"},
    "EB0": {"src": "sina", "name": "大商所苯乙烯（純苯衍生）", "short": "苯乙烯EB0", "unit": "CNY/t"},
    "SP0": {"src": "sina", "name": "上期所紙漿", "short": "中國紙漿SP0", "unit": "CNY/t"},
    "V0": {"src": "sina", "name": "大商所 PVC", "short": "PVC V0", "unit": "CNY/t"},
    "EG0": {"src": "sina", "name": "大商所乙二醇", "short": "乙二醇EG0", "unit": "CNY/t"},
    "HC0": {"src": "sina", "name": "上期所熱軋卷板", "short": "熱卷HC0", "unit": "CNY/t"},
    "I0": {"src": "sina", "name": "大商所鐵礦石", "short": "鐵礦I0", "unit": "CNY/t"},
    "M0": {"src": "sina", "name": "大商所豆粕", "short": "豆粕M0", "unit": "CNY/t"},
    "CL=F": {"src": "macro", "name": "WTI 原油", "short": "WTI原油", "unit": "USD/bbl"},
    "CT=F": {"src": "macro", "name": "ICE 棉花", "short": "棉花CT", "unit": "USc/lb"},
    "HG=F": {"src": "macro", "name": "COMEX 精銅", "short": "銅HG", "unit": "USD/lb"},
    "^BDI": {"src": "macro", "name": "乾散貨運費（BDRY 代理 BDI）", "short": "BDI*", "unit": "USD"},
    "ZC=F": {"src": "macro", "name": "CBOT 玉米", "short": "玉米ZC", "unit": "USc/bu"},
    "CPL*": {"src": "derived", "from": ["EB0"], "name": "CPL 己內醯胺（推算）", "short": "CPL*", "unit": "CNY/t (EB0)",
             "note": "CPL 無期貨、新浪無純苯期貨 → 以苯乙烯 EB0（同為純苯衍生物）價格 1:1 連動推算"},
    "PTA+CPL": {"src": "derived", "from": ["TA0", "CPL*"], "name": "PTA＋CPL 原料成本鏈", "short": "PTA/CPL",
                "unit": "index", "note": "PTA 與 CPL*（苯乙烯推算）指數等權平均"},
}
# role：price＝售價端（上漲有利）/ cost＝成本端（下跌有利）；directness：產業直接度 0~1
CHAIN_MODELS = {
    "polyester_nylon": {"label": "聚酯/尼龍", "chain": "化纖加工鏈（聚酯加工絲＋尼龍）", "tag": "加工絲PF0/CPL",
                        "factors": [("PF0", "price", 1.0), ("PTA+CPL", "cost", 0.9), ("CL=F", "cost", 0.6)]},
    "polyester": {"label": "聚酯", "chain": "聚酯化纖鏈", "tag": "加工絲PF0/PTA",
                  "factors": [("PF0", "price", 1.0), ("TA0", "cost", 0.9), ("CL=F", "cost", 0.6)]},
    "nylon": {"label": "尼龍", "chain": "尼龍化纖鏈（CPL→尼龍粒→絲）", "tag": "CPL/加工絲PF0",
              "factors": [("CPL*", "cost", 0.9), ("PF0", "price", 0.6), ("CL=F", "cost", 0.5)]},
    "textile": {"label": "紡織", "chain": "紡織纖維", "tag": "加工絲PF0/棉花",
                "factors": [("PF0", "price", 0.8), ("TA0", "cost", 0.8), ("CT=F", "price", 0.6)]},
    "paper": {"label": "造紙", "chain": "紙漿造紙鏈", "tag": "中國紙漿SP0", "factors": [("SP0", "cost", 1.0)]},
    "plastics": {"label": "塑化", "chain": "塑膠化工鏈", "tag": "PVC/EG/原油",
                 "factors": [("V0", "price", 0.8), ("EG0", "price", 0.6), ("CL=F", "cost", 0.8)]},
    "rubber": {"label": "橡膠", "chain": "橡膠", "tag": "WTI原油", "factors": [("CL=F", "cost", 0.9)]},
    "food": {"label": "食品", "chain": "食品／農糧飼料", "tag": "玉米/豆粕M0",
             "factors": [("ZC=F", "cost", 0.9), ("M0", "cost", 0.8)]},
    "cable": {"label": "電纜", "chain": "電器電纜", "tag": "銅HG", "factors": [("HG=F", "price", 1.0)]},
    "steel": {"label": "鋼鐵", "chain": "鋼鐵（熱卷售價 − 鐵礦成本）", "tag": "熱卷HC0/鐵礦I0",
              "factors": [("HC0", "price", 1.0), ("I0", "cost", 0.8)]},
    "shipping": {"label": "航運", "chain": "散裝航運", "tag": "BDI*", "factors": [("^BDI", "price", 0.9)]},
    "oilgas": {"label": "油電", "chain": "油電燃氣", "tag": "WTI原油", "factors": [("CL=F", "price", 0.9)]},
}
CODE_CHAIN = {"1444": "polyester_nylon", "1455": "polyester_nylon", "1402": "polyester", "1409": "polyester",
              "1440": "polyester", "1447": "nylon"}
INDUSTRY_CHAIN = {"04": "textile", "09": "paper", "03": "plastics", "21": "plastics", "11": "rubber", "02": "food",
                  "06": "cable", "10": "steel", "15": "shipping", "23": "oilgas"}
# 景氣循環／原物料產業白名單（TWSE/TPEx 產業別代碼）；其餘一律剔除
CYCLICAL_WHITELIST = {"04": "紡織纖維", "03": "塑膠工業", "09": "造紙工業", "10": "鋼鐵工業", "06": "電器電纜",
                      "21": "化學工業", "11": "橡膠工業", "15": "航運業", "01": "水泥工業", "02": "食品工業",
                      "23": "油電燃氣"}
# 明確黑名單（僅用於標示剔除原因）
SECTOR_BLACKLIST = {"14": "營建／建材營造（交屋入帳造成假性虧轉盈）", "17": "金融保險", "16": "觀光餐旅",
                    "32": "文化創意", "22": "生技醫療"}
NO_FUTURES_NOTE = {"01": "水泥無可直接對應之公開期貨（中國動力煤期貨流動性已枯竭），以個股基本面與報價調漲公告為主。"}
# 跨國同業標竿：(Yahoo 代碼, 名稱, 層級)。層級 TW＝台股龍頭；CN／US／INTL＝中美及國際指標股
SECTOR_PEERS = {
    "textile": {"label": "聚酯／化纖／尼龍紡織", "peers": [("1402.TW", "遠東新", "TW"), ("601233.SS", "桐昆股份", "CN"),
                                                          ("600346.SS", "恆力石化", "CN")]},
    "plastics": {"label": "塑膠／石化", "peers": [("1301.TW", "台塑", "TW"), ("DOW", "陶氏化學", "US"),
                                               ("600309.SS", "萬華化學", "CN")]},
    "paper": {"label": "造紙", "peers": [("1904.TW", "正隆", "TW"), ("IP", "國際紙業", "US"), ("002078.SZ", "太陽紙業", "CN")]},
    "cement": {"label": "水泥", "peers": [("1101.TW", "台泥", "TW"), ("600585.SS", "海螺水泥", "CN")]},
    "steel": {"label": "鋼鐵", "peers": [("2002.TW", "中鋼", "TW"), ("NUE", "紐柯鋼鐵", "US"), ("600019.SS", "寶鋼股份", "CN")]},
    "shipping": {"label": "航運", "peers": [("2603.TW", "長榮", "TW"), ("2606.TW", "裕民", "TW"), ("ZIM", "ZIM 以星", "INTL"),
                                          ("SBLK", "Star Bulk", "INTL")]},
    "food": {"label": "食品", "peers": [("1216.TW", "統一", "TW"), ("ADM", "ADM", "US")]},
}
PEER_GROUP_BY_INDUSTRY = {"04": "textile", "03": "plastics", "21": "plastics", "09": "paper", "01": "cement",
                          "10": "steel", "15": "shipping", "02": "food"}
TIER_ZH = {"TW": "台股龍頭", "CN": "中國指標", "US": "美國指標", "INTL": "國際標竿"}
PEER_TH = {"catch_up": 5.0, "divergence": -5.0}
PEER_SIGNAL_ZH = {"CATCH-UP READY": "龍頭已動、落後補漲", "PEER DIVERGENCE": "同業轉弱警示", "IN LINE": "與同業同步",
                  "N/A": "資料不足"}
# 合理市價模擬：A 利差 ROE 折現 45%／B 同業比價 35%／C 淨值中樞 20%
FV_PARAMS = {
    "ke": 0.085, "g": 0.015,                 # 資金成本、永續成長率
    "pb_cap": 1.15, "pb_floor": 0.30,        # 模型 A 合理 P/B 上下限（下限為重資產清算／重置價值的保守假設）
    "macro_lambda": 0.04,                    # WMS ±100 → 正常化 ROE ±4 個百分點
    "liq_disc": 0.18,                        # 中小型股流動性折價
    "peer_pb_default": 0.95,                 # 無同業 P/B 時的產業常態中樞
    "weights": {"A": 0.45, "B": 0.35, "C": 0.20},
    "scenarios": {                           # 三情境參數位移
        "bear": {"ke_shift": 0.015, "roe_shift": -0.02, "liq_shift": 0.10, "anchor_pb": 0.70},
        "base": {"ke_shift": 0.0, "roe_shift": 0.0, "liq_shift": 0.0, "anchor_pb": 0.85},
        "bull": {"ke_shift": -0.015, "roe_shift": 0.03, "liq_shift": -0.10, "anchor_pb": 1.00},
    },
}
# 中美同業 P/B「常態基準參考值」— 使用者於 2026-11-14 提供的靜態設定，非即時報價；
# 公開 API 無免驗證來源，請定期（如每季財報後）自行更新。台股龍頭仍取 TWSE/TPEx 每日 P/B。
PEER_PB_MANUAL_ASOF = "2026-11-14"
PEER_PB_MANUAL: Dict[str, float] = {
    # 化纖
    "601233.SS": 1.08,   # 桐昆股份
    "600346.SS": 1.42,   # 恆力石化
    # 塑化
    "DOW": 1.35,         # 陶氏化學
    "600309.SS": 2.45,   # 萬華化學
    # 造紙
    "IP": 1.65,          # 國際紙業
    "002078.SZ": 1.28,   # 太陽紙業
    # 水泥
    "600585.SS": 0.68,   # 海螺水泥
    # 鋼鐵
    "NUE": 1.60,         # 紐柯鋼鐵
    "600019.SS": 0.72,   # 寶鋼股份
}
# 自選股強制分析：custom_watchlist.json（JSON 陣列）＋ --analyze 單次代號，一律跳過四道濾網，
# 輸出完整分析並標記 source="CUSTOM"（不納入 Mode A/B 自動分配）。檔案不存在時以下列預設值建立。
CUSTOM_WATCHLIST_FILE = "custom_watchlist.json"
# 籌碼：千張大戶＝持股分級 15（> 1,000,000 股）；散戶＝分級 1~8（< 50 張）
CHIP_TH = {"accum_big": 0.5, "distrib_big": -1.0, "margin_usage_high": 25.0, "low_pos": 0.35, "tdcc_keep_days": 120}
CUSTOM_DEFAULT = ["1444", "1447", "2392"]
CODE_RE = re.compile(r"^\d{4,6}[A-Z]?$")
FA_DAYS = 1100   # 財報回溯天數（約 12 季：顯示 8 季＋ TTM／YoY 所需前置季）
LEADS = (0, 5, 10, 20)   # 期貨領先股價的交易日數
RET_H = 5                # 以 5 日對數報酬計算相關（避免價格水準的假性相關）
WINDOW = 60              # 個股分析視窗：近 60 個交易日
MACRO_TH = {
    "w_tail": 2.5,          # 加權利差 Σ w·sign·20D% ≥ +2.5 → TAILWIND
    "w_head": -2.5,         # ≤ −2.5 → HEADWIND
    "base_strength": 0.25,  # 權重 = 直接度 × (0.25 + |r|)
    "divergence_5d": 2.0,   # 5 日與 20 日方向相反且 |5D| ≥ 2% → 提示轉折
}
RATING_ZH = {"TAILWIND": "利差順風", "NEUTRAL": "中性觀望", "HEADWIND": "成本逆風", "N/A": "無對應期貨"}

STOCK_CODE_RE = re.compile(r"^[1-9]\d{3}$")  # 一般普通股（排除 00 開頭 ETF、權證、特別股）

log = logging.getLogger("dvf")


class RateLimited(Exception):
    """FinMind 免費額度用盡（HTTP 402）。"""


# ──────────────────────────────────────────────────────────────────────────────
# 工具函式
# ──────────────────────────────────────────────────────────────────────────────
def now_tpe() -> dt.datetime:
    return dt.datetime.now(TPE)


def num(v: Any) -> Optional[float]:
    """安全轉換數字：處理逗號、空字串、'---'、'+0.19' 等交易所格式。"""
    if v is None:
        return None
    if isinstance(v, (int, float)):
        return float(v) if math.isfinite(v) else None
    s = str(v).strip().replace(",", "")
    if s in ("", "-", "--", "---", "----", "N/A", "NA", "null"):
        return None
    try:
        f = float(s)
    except ValueError:
        return None
    return f if math.isfinite(f) else None


def roc_to_iso(s: Optional[str]) -> Optional[str]:
    """民國日期 '1151112' → '2026-11-12'。"""
    if not s:
        return None
    s = str(s).strip().replace("/", "")
    if not s.isdigit() or len(s) < 7:
        return None
    y, m, d = int(s[:-4]) + 1911, int(s[-4:-2]), int(s[-2:])
    try:
        return dt.date(y, m, d).isoformat()
    except ValueError:
        return None


def mean(xs: List[float]) -> Optional[float]:
    xs = [x for x in xs if x is not None]
    return sum(xs) / len(xs) if xs else None


def clamp(x: float, lo: float, hi: float) -> float:
    return max(lo, min(hi, x))


def r2(x: Optional[float], n: int = 2) -> Optional[float]:
    return None if x is None else round(x, n)


def quarter_label(iso: str) -> str:
    y, m = int(iso[:4]), int(iso[5:7])
    return f"{y}Q{(m - 1) // 3 + 1}"


def make_ssl_context() -> ssl.SSLContext:
    """
    macOS + python.org 版 Python 常缺根憑證 → 優先使用 certifi。
    Python 3.13 起預設 VERIFY_X509_STRICT，TWSE 憑證缺 Subject Key Identifier 會驗證失敗 → 關閉 strict 旗標
    （仍保留完整憑證鏈與主機名稱驗證）。
    """
    try:
        import certifi  # type: ignore

        ctx = ssl.create_default_context(cafile=certifi.where())
    except ImportError:
        ctx = ssl.create_default_context()
    if hasattr(ssl, "VERIFY_X509_STRICT"):
        ctx.verify_flags &= ~ssl.VERIFY_X509_STRICT
    return ctx


# ──────────────────────────────────────────────────────────────────────────────
# HTTP 客戶端（重試 + 快取）
# ──────────────────────────────────────────────────────────────────────────────
class Http:
    UA = "Mozilla/5.0 (Macintosh; Intel Mac OS X) DVF-PRO-Scanner/1.0"

    def __init__(self, timeout: int = 30, retries: int = 3):
        self.timeout = timeout
        self.retries = retries
        self.ctx = make_ssl_context()

    def _get(self, url: str, params: Optional[Dict[str, Any]], headers: Optional[Dict[str, str]],
             timeout: Optional[int], parse) -> Any:
        full = url + ("?" + urllib.parse.urlencode(params) if params else "")
        hdrs = {"User-Agent": self.UA, "Accept": "application/json, text/plain, */*"}
        hdrs.update(headers or {})
        last_err: Optional[Exception] = None
        for attempt in range(1, self.retries + 1):
            try:
                req = urllib.request.Request(full, headers=hdrs)
                with urllib.request.urlopen(req, timeout=timeout or self.timeout, context=self.ctx) as resp:
                    raw = resp.read()
                return parse(raw.decode("utf-8-sig", errors="replace"))
            except urllib.error.HTTPError as e:
                if e.code == 402:
                    raise RateLimited(f"FinMind quota exhausted ({url})") from e
                last_err = e
                if 400 <= e.code < 500 and e.code != 429:
                    break
            except (urllib.error.URLError, TimeoutError, ValueError, ConnectionError, OSError) as e:
                last_err = e
            wait = 2 ** attempt
            log.warning("GET failed (%s/%s) %s → %s; retry in %ss", attempt, self.retries, url, last_err, wait)
            time.sleep(wait)
        raise RuntimeError(f"GET {full} failed: {last_err}")

    def get_json(self, url: str, params: Optional[Dict[str, Any]] = None,
                 headers: Optional[Dict[str, str]] = None, timeout: Optional[int] = None) -> Any:
        return self._get(url, params, headers, timeout, json.loads)

    def get_text(self, url: str, params: Optional[Dict[str, Any]] = None,
                 headers: Optional[Dict[str, str]] = None, timeout: Optional[int] = None,
                 validate=None) -> str:
        """validate(text) 失敗時丟 ValueError → 觸發重試（新浪偶爾回傳空內容）。"""
        return self._get(url, params, headers, timeout, (lambda t: validate(t) or t) if validate else (lambda t: t))


class FinMind:
    def __init__(self, http: Http, token: Optional[str], cache_dir: Path, sleep: float):
        self.http = http
        self.token = token
        self.cache_dir = cache_dir
        self.sleep = sleep
        self.calls = 0
        cache_dir.mkdir(parents=True, exist_ok=True)
        cutoff = time.time() - 7 * 86400  # 快取保留 7 天
        for f in cache_dir.glob("*.json"):
            if f.stat().st_mtime < cutoff:
                f.unlink(missing_ok=True)

    def data(self, dataset: str, code: str, start: str, cache_key: str) -> List[Dict[str, Any]]:
        path = self.cache_dir / f"{dataset}_{code}_{cache_key}_{start.replace('-', '')}.json"
        if path.exists():
            try:
                return json.loads(path.read_text("utf-8"))
            except json.JSONDecodeError:
                path.unlink(missing_ok=True)
        headers = {"Authorization": f"Bearer {self.token}"} if self.token else None
        payload = self.http.get_json(FINMIND, {"dataset": dataset, "data_id": code, "start_date": start}, headers)
        self.calls += 1
        time.sleep(self.sleep)
        if not isinstance(payload, dict) or payload.get("status") != 200:
            msg = payload.get("msg") if isinstance(payload, dict) else payload
            if isinstance(msg, str) and "upper limit" in msg.lower():
                raise RateLimited(msg)
            raise RuntimeError(f"FinMind {dataset} {code}: {msg}")
        rows = payload.get("data") or []
        path.write_text(json.dumps(rows, ensure_ascii=False), "utf-8")
        return rows


# ──────────────────────────────────────────────────────────────────────────────
# 市場資料載入
# ──────────────────────────────────────────────────────────────────────────────
def load_twse(http: Http) -> Tuple[Dict[str, Dict[str, Any]], Optional[str]]:
    pb_rows = http.get_json(TWSE_PB)
    q_rows = http.get_json(TWSE_QUOTE)
    quotes = {str(r.get("Code", "")).strip(): r for r in q_rows}
    out: Dict[str, Dict[str, Any]] = {}
    dates = set()
    for r in pb_rows:
        code = str(r.get("Code", "")).strip()
        q = quotes.get(code)
        if not q:
            continue
        dates.add(roc_to_iso(q.get("Date")))
        out[code] = {
            "code": code,
            "name": str(r.get("Name", "")).strip(),
            "market": "TWSE",
            "pb": num(r.get("PBratio")),
            "pe": num(r.get("PEratio")),
            "dividend_yield": num(r.get("DividendYield")),
            "close": num(q.get("ClosingPrice")),
            "open": num(q.get("OpeningPrice")),
            "high": num(q.get("HighestPrice")),
            "low": num(q.get("LowestPrice")),
            "change": num(q.get("Change")),
            "volume_shares": num(q.get("TradeVolume")),
            "trade_value": num(q.get("TradeValue")),
            "data_date": roc_to_iso(q.get("Date")),
        }
    dates.discard(None)
    return out, (max(dates) if dates else None)


def _rwd_table(payload: Any, *required: str) -> Tuple[List[str], List[List[Any]]]:
    """從 TWSE 官網 JSON 取出含指定欄位的表格（支援 fields/data 與 tables[] 兩種格式）。"""
    if not isinstance(payload, dict) or payload.get("stat") != "OK":
        return [], []
    tables = payload.get("tables") or [payload]
    for t in tables:
        fields = t.get("fields") or []
        if all(f in fields for f in required):
            return fields, t.get("data") or []
    return [], []


def load_twse_rwd(http: Http, date: dt.date) -> Tuple[Dict[str, Dict[str, Any]], Optional[str]]:
    """TWSE 官網盤後資料（當日 14:30~15:30 起可取得）。欄位與 OpenAPI 對齊。"""
    ymd = date.strftime("%Y%m%d")
    f_pb, pb_rows = _rwd_table(http.get_json(TWSE_RWD_PB, {"date": ymd, "selectType": "ALL", "response": "json"}),
                               "證券代號", "股價淨值比")
    f_q, q_rows = _rwd_table(http.get_json(TWSE_RWD_QUOTE, {"date": ymd, "type": "ALLBUT0999", "response": "json"}),
                             "證券代號", "收盤價", "成交股數")
    if not pb_rows or not q_rows:
        return {}, None
    pbi = {f: i for i, f in enumerate(f_pb)}
    qi = {f: i for i, f in enumerate(f_q)}
    quotes = {str(r[qi["證券代號"]]).strip(): r for r in q_rows}
    iso = date.isoformat()
    out: Dict[str, Dict[str, Any]] = {}
    for r in pb_rows:
        code = str(r[pbi["證券代號"]]).strip()
        q = quotes.get(code)
        if not q:
            continue
        sign = re.sub(r"<[^>]+>", "", str(q[qi["漲跌(+/-)"]])).strip() if "漲跌(+/-)" in qi else ""
        diff = num(q[qi["漲跌價差"]]) if "漲跌價差" in qi else None
        out[code] = {
            "code": code,
            "name": str(r[pbi["證券名稱"]]).strip(),
            "market": "TWSE",
            "pb": num(r[pbi["股價淨值比"]]),
            "pe": num(r[pbi["本益比"]]) if "本益比" in pbi else None,
            "dividend_yield": num(r[pbi["殖利率(%)"]]) if "殖利率(%)" in pbi else None,
            "close": num(q[qi["收盤價"]]),
            "open": num(q[qi["開盤價"]]),
            "high": num(q[qi["最高價"]]),
            "low": num(q[qi["最低價"]]),
            "change": None if diff is None else (-diff if sign == "-" else diff),
            "volume_shares": num(q[qi["成交股數"]]),
            "trade_value": num(q[qi["成交金額"]]),
            "data_date": iso,
        }
    return out, iso


def load_tpex(http: Http) -> Tuple[Dict[str, Dict[str, Any]], Optional[str]]:
    pb_rows = http.get_json(TPEX_PB)
    q_rows = http.get_json(TPEX_QUOTE)
    quotes = {str(r.get("SecuritiesCompanyCode", "")).strip(): r for r in q_rows}
    out: Dict[str, Dict[str, Any]] = {}
    dates = set()
    for r in pb_rows:
        code = str(r.get("SecuritiesCompanyCode", "")).strip()
        q = quotes.get(code)
        if not q:
            continue
        dates.add(roc_to_iso(q.get("Date")))
        out[code] = {
            "code": code,
            "name": str(r.get("CompanyName", "")).strip(),
            "market": "TPEx",
            "pb": num(r.get("PriceBookRatio")),
            "pe": num(r.get("PriceEarningRatio")),
            "dividend_yield": num(r.get("YieldRatio")),
            "close": num(q.get("Close")),
            "open": num(q.get("Open")),
            "high": num(q.get("High")),
            "low": num(q.get("Low")),
            "change": num(q.get("Change")),
            "volume_shares": num(q.get("TradingShares")),
            "trade_value": num(q.get("TransactionAmount")),
            "data_date": roc_to_iso(q.get("Date")),
        }
    dates.discard(None)
    return out, (max(dates) if dates else None)


# ──────────────────────────────────────────────────────────────────────────────
# 因子計算
# ──────────────────────────────────────────────────────────────────────────────
def eps_signal(rows: List[Dict[str, Any]], growth_min: float) -> Dict[str, Any]:
    """第三道濾網：最新單季 EPS > 0 且（去年同季 < 0 或 YoY >= 50%）。"""
    eps_map = {r["date"]: num(r.get("value")) for r in rows if r.get("type") == "EPS" and num(r.get("value")) is not None}
    # 財報已公布但 EPS 欄位尚未入庫時（FinMind 常見）→ 以歸屬母公司淨利 ÷ 推算股數估計，並標示 estimated
    nip = {r["date"]: num(r.get("value")) for r in rows
           if r.get("type") == "EquityAttributableToOwnersOfParent" and num(r.get("value")) is not None}
    ratios = sorted(nip[d] / eps_map[d] for d in eps_map if d in nip and abs(eps_map[d]) >= 0.05)
    estimated = []
    if ratios:
        shares = ratios[len(ratios) // 2]
        for d in nip:
            if d not in eps_map and d > max(eps_map, default=""):
                eps_map[d] = round(nip[d] / shares, 2)
                estimated.append(d)
    eps = sorted(eps_map.items())
    res: Dict[str, Any] = {"pass": False, "signal": None, "reason": None, "eps_estimated": bool(estimated) and eps and eps[-1][0] in estimated,
                           "history": [{"q": quarter_label(d), "eps": v, "est": d in estimated} for d, v in eps[-8:]]}
    if not eps:
        res["reason"] = "NO_EPS_DATA"
        return res
    latest_date, latest = eps[-1]
    yoy_date = f"{int(latest_date[:4]) - 1}{latest_date[4:]}"
    base = dict(eps).get(yoy_date)
    res.update({"eps_latest": latest, "eps_period": quarter_label(latest_date),
                "eps_yoy_base": base, "eps_yoy_period": quarter_label(yoy_date), "eps_growth_pct": None})
    if latest <= 0:
        res["reason"] = "EPS_NOT_POSITIVE"
        return res
    if base is None:
        res["reason"] = "NO_YOY_BASE"
        return res
    if base <= 0:  # 由虧（或打平）轉盈
        res.update({"pass": True, "signal": "TURNAROUND"})
        return res
    growth = (latest - base) / base
    res["eps_growth_pct"] = round(growth * 100, 1)
    if growth >= growth_min:
        res.update({"pass": True, "signal": "GROWTH"})
    else:
        res["reason"] = "GROWTH_BELOW_THRESHOLD"
    return res


# ──────────────────────────────────────────────────────────────────────────────
# 技術分析與指標評價（TECH）：MA5/20/60、乖離率、RSI(14)、KD(9,3,3)、MACD(12,26,9)
# 價格為 FinMind 日 K（未還原除權息），與一般看盤軟體預設一致；除權息缺口會使均線與 MACD 短暫失真。
# ──────────────────────────────────────────────────────────────────────────────
TECH_MIN_BARS = 35        # MACD(12,26,9) 至少需要 26+9 根；MA60 需 60 根，不足時 MA60 相關條件不成立
TECH_KD_CROSS_DAYS = 3    # 「KD 黃金交叉」：近 3 個交易日內 K 由下往上穿越 D
TECH_LABELS = {
    "STRONG_BREAKOUT": ("🔥 強勢突破 / 多頭點火", "🔥 多頭點火"),
    "BOTTOM_REVERSAL": ("📈 底部轉強 / 站上月線", "📈 站上月線"),
    "OVERSOLD_BASE": ("💎 超跌背離 / 築底期", "💎 築底超跌"),
    "WEAK_BELOW_MA": ("⚠️ 弱勢探底 / 均線反壓", "⚠️ 均線反壓"),
    "NEUTRAL": ("⚖️ 區間整理 / 中性", "⚖️ 區間整理"),
}


def _ema(vals: List[float], n: int) -> List[float]:
    k, out = 2 / (n + 1), []
    for i, v in enumerate(vals):
        out.append(v if i == 0 else v * k + out[-1] * (1 - k))
    return out


def _rsi_wilder(close: List[float], n: int = 14) -> List[Optional[float]]:
    out: List[Optional[float]] = [None] * len(close)
    if len(close) <= n:
        return out
    ch = [close[i] - close[i - 1] for i in range(1, len(close))]
    ag = sum(max(x, 0) for x in ch[:n]) / n
    al = sum(max(-x, 0) for x in ch[:n]) / n
    for i in range(n, len(close)):
        if i > n:
            x = ch[i - 1]
            ag, al = (ag * (n - 1) + max(x, 0)) / n, (al * (n - 1) + max(-x, 0)) / n
        out[i] = 100.0 if al == 0 else 100 - 100 / (1 + ag / al)
    return out


def _kd(high: List[float], low: List[float], close: List[float], n: int = 9) -> Tuple[List[Optional[float]], List[Optional[float]]]:
    """台灣慣用 KD：RSV(9)，K = 2/3·K前 + 1/3·RSV，D = 2/3·D前 + 1/3·K，起始值 50。"""
    K: List[Optional[float]] = [None] * len(close)
    D: List[Optional[float]] = [None] * len(close)
    k = d = 50.0
    for i in range(n - 1, len(close)):
        hh, ll = max(high[i - n + 1:i + 1]), min(low[i - n + 1:i + 1])
        rsv = 50.0 if hh == ll else (close[i] - ll) / (hh - ll) * 100
        k = k * 2 / 3 + rsv / 3
        d = d * 2 / 3 + k / 3
        K[i], D[i] = k, d
    return K, D


def build_tech(bars: List[Dict[str, Any]]) -> Dict[str, Any]:
    """bars：[{d, c, h, l}]（舊→新，最後一根為報價日）。回傳 tech_metrics；資料不足時 status=UNAVAILABLE、數值為 None。"""
    bars = [b for b in bars if b.get("c")]
    for b in bars:   # 高低價缺值（例如當日僅有收盤）時以收盤代替
        b["h"], b["l"] = b.get("h") or b["c"], b.get("l") or b["c"]
    n = len(bars)
    if n < TECH_MIN_BARS:
        return {"status": "UNAVAILABLE", "reason": f"日 K 僅 {n} 根，少於 {TECH_MIN_BARS} 根，無法計算 MACD／RSI／KD。",
                "bars": n, "tech_rating": None, "tech_signal": None, "tech_short": None}
    C, H, Lo = [b["c"] for b in bars], [b["h"] for b in bars], [b["l"] for b in bars]
    close = C[-1]
    sma = lambda k, off=0: sum(C[n - k - off:n - off]) / k if n - off >= k else None  # noqa: E731
    ma5, ma20, ma60, ma20_5 = sma(5), sma(20), sma(60), sma(20, 5)
    bias = lambda m: (close / m - 1) * 100 if m else None  # noqa: E731
    rsi = _rsi_wilder(C, 14)
    K, D = _kd(H, Lo, C, 9)
    e12, e26 = _ema(C, 12), _ema(C, 26)
    dif = [a - b for a, b in zip(e12, e26)]
    dea = _ema(dif, 9)
    osc = [a - b for a, b in zip(dif, dea)]

    k0, d0, k1, d1 = K[-1], D[-1], K[-2], D[-2]
    golden = any(K[i] > D[i] and K[i - 1] <= D[i - 1] for i in range(n - TECH_KD_CROSS_DAYS, n))
    dead = any(K[i] < D[i] and K[i - 1] >= D[i - 1] for i in range(n - TECH_KD_CROSS_DAYS, n))
    kd_up = k0 > d0 and k0 > k1
    o0, o1 = osc[-1], osc[-2]
    macd_state = ("翻紅" if o0 > 0 >= o1 else "紅柱擴張" if o0 > 0 and o0 > o1 else "紅柱縮減" if o0 > 0
                  else "翻綠" if o0 < 0 <= o1 else "綠柱收斂" if o0 < 0 and o0 > o1 else "綠柱擴大" if o0 < 0 else "零軸")
    red_expand = o0 > 0 and o0 > o1
    above20, above60 = close > ma20, ma60 is not None and close > ma60
    below20, below60 = close < ma20, ma60 is not None and close < ma60
    r0 = rsi[-1]

    reasons: List[str] = []
    if above20 and above60 and (golden or red_expand):
        rating = "STRONG_BREAKOUT"
        reasons += ["收盤站上 MA20 與 MA60"] + (["KD 近 3 日黃金交叉"] if golden else []) + (["MACD 柱狀體翻紅擴張"] if red_expand else [])
    elif above20 and ((r0 is not None and 50 <= r0 <= 70) or kd_up):
        rating = "BOTTOM_REVERSAL"
        reasons += ["收盤站上 MA20"] + ([f"RSI {r0:.1f} 介於 50~70"] if r0 is not None and 50 <= r0 <= 70 else []) + (["KD 向上（K>D 且 K 上升）"] if kd_up else [])
    elif (r0 is not None and r0 < 35) or k0 < 20:
        rating = "OVERSOLD_BASE"
        reasons += ([f"RSI {r0:.1f} < 35"] if r0 is not None and r0 < 35 else []) + ([f"K {k0:.1f} < 20"] if k0 < 20 else [])
    elif below20 and below60 and o0 < 0:
        rating = "WEAK_BELOW_MA"
        reasons += ["收盤低於 MA20 與 MA60", "MACD 柱狀體為負"]
    else:
        rating = "NEUTRAL"
        reasons.append("未觸發其他條件")

    align = (None if None in (ma5, ma20, ma60) else "多頭排列" if ma5 > ma20 > ma60 else "空頭排列" if ma5 < ma20 < ma60 else "均線糾結")
    slope20 = (ma20 / ma20_5 - 1) * 100 if ma20_5 else None
    slope_txt = None if slope20 is None else "上彎" if slope20 > 0.5 else "下彎" if slope20 < -0.5 else "走平"
    kd_txt = "黃金交叉" if golden else "死亡交叉" if dead else "向上" if kd_up else "向下" if k0 < k1 else "持平"
    pos = lambda m, nm: "—" if m is None else f"{'站上' if close > m else '跌破' if close < m else '貼近'}{nm} {round(m, 2):.2f}（{round(bias(m), 2):+.1f}%）"  # noqa: E731
    comment = (f"{pos(ma20, 'MA20')}、{pos(ma60, 'MA60')}；MA20 {slope_txt or '—'}、{align or '均線資料不足'}。"
               + (f"RSI {r0:.1f}" if r0 is not None else "RSI —"))
    comment += f"，KD {k0:.1f}/{d0:.1f} {kd_txt}，MACD 柱 {o0:+.3f}（{macd_state}）。→ {TECH_LABELS[rating][0]}"
    if rating == "OVERSOLD_BASE":
        comment += "：位於深度價值左側低檔區，宜等 KD 黃金交叉或站回 MA20 再加碼。"
    elif rating == "WEAK_BELOW_MA":
        comment += "：均線反壓，冰山建倉宜放慢、嚴守 −8% 停損。"
    elif rating == "STRONG_BREAKOUT":
        comment += "：多頭點火，留意乖離過大時勿追價。"
    elif rating == "BOTTOM_REVERSAL":
        comment += "：右側轉強訊號，可依計畫分批建倉。"
    else:
        comment += "：方向未明，依基本面與籌碼決定節奏。"
    r = lambda v, d=2: None if v is None else round(v, d)  # noqa: E731
    return {"status": "OK", "as_of": bars[-1]["d"], "bars": n, "close": close,
            "ma5": r(ma5), "ma20": r(ma20), "ma60": r(ma60), "bias_ma20_pct": r(bias(ma20)), "bias_ma60_pct": r(bias(ma60)),
            "ma_alignment": align, "ma20_slope_5d_pct": r(slope20), "ma20_slope": slope_txt,
            "rsi14": r(r0, 1), "k": r(k0, 1), "d": r(d0, 1), "k_prev": r(k1, 1), "d_prev": r(d1, 1),
            "kd_cross": "GOLDEN" if golden else "DEAD" if dead else None, "kd_state": kd_txt,
            "macd_dif": r(dif[-1], 3), "macd_dea": r(dea[-1], 3), "macd_osc": r(o0, 3), "macd_osc_prev": r(o1, 3), "macd_state": macd_state,
            "tech_rating": rating, "tech_signal": TECH_LABELS[rating][0], "tech_short": TECH_LABELS[rating][1],
            "reasons": reasons, "comment": comment,
            "params": "MA5/20/60 · RSI(14, Wilder) · KD(9,3,3) · MACD(12,26,9) · 日 K 未還原除權息"}


def volume_compression(today_lots: float, hist_lots: List[float], vol_min: float, vol_max: float) -> Dict[str, Any]:
    """
    量能窒息度評分 VCS (0~100，越高越「窒息」)
      relative = clamp((1 - blended) / 0.6, 0, 1)，blended = 0.5·今日量/ADV60 + 0.5·ADV5/ADV60
                 （量縮到均量 40% 以下即滿分）
      absolute = clamp((vol_max - 今日量) / (vol_max - vol_min), 0, 1)
                 （越接近流動性帶下緣越窒息）
      VCS      = 100 × (0.7·relative + 0.3·absolute)；無歷史資料時僅用 absolute。
    """
    absolute = clamp((vol_max - today_lots) / (vol_max - vol_min), 0.0, 1.0)
    adv5, adv20, adv60 = mean(hist_lots[-5:]), mean(hist_lots[-20:]), mean(hist_lots[-60:])
    if len(hist_lots) >= 20 and adv60:
        blended = 0.5 * today_lots / adv60 + 0.5 * (adv5 or today_lots) / adv60
        relative = clamp((1 - blended) / 0.6, 0.0, 1.0)
        score, method = 100 * (0.7 * relative + 0.3 * absolute), "RELATIVE+ABSOLUTE"
    else:
        score, method = 100 * absolute, "ABSOLUTE_ONLY"
    score = round(score)
    tag = "ICE" if score >= 75 else "COLD" if score >= 50 else "COOL" if score >= 25 else "WARM"
    return {"vcs": score, "vcs_tag": tag, "vcs_method": method,
            "avg_vol_5": r2(adv5, 1), "avg_vol_20": r2(adv20, 1), "avg_vol_60": r2(adv60, 1),
            "vol_ratio_60": r2(today_lots / adv60, 3) if adv60 else None}


def derive_metrics(s: Dict[str, Any], p: Dict[str, float]) -> Dict[str, Any]:
    close, pb = s["close"], s["pb"]
    bv = close / pb
    t085, t100 = bv * 0.85, bv
    up085, up100 = (t085 / close - 1) * 100, (t100 / close - 1) * 100
    rr = up085 / (p["stop_pct"] * 100)       # 以第一階段（保守）修復空間計算風報比
    rr100 = up100 / (p["stop_pct"] * 100)
    return {
        "book_value": r2(bv),
        "discount_pct": r2((1 - pb) * 100, 1),
        "target_price_085": r2(t085),
        "upside_085_pct": r2(up085),
        "target_price_100": r2(t100),
        "upside_100_pct": r2(up100),
        "stop_loss_price": r2(close * (1 - p["stop_pct"])),
        "risk_reward_ratio": r2(rr),
        "risk_reward_ratio_100": r2(rr100),
        "conviction": "HIGH CONVICTION" if rr >= p["hc_rr"] else "STANDARD",
    }


# ──────────────────────────────────────────────────────────────────────────────
# 宏觀商品連動引擎
# ──────────────────────────────────────────────────────────────────────────────
def _pct(a: Optional[float], b: Optional[float]) -> Optional[float]:
    return r2((a / b - 1) * 100) if a is not None and b else None


def fetch_yahoo_series(http: Http, symbol: str, rng: str = "6mo") -> Dict[str, Any]:
    """Yahoo v8 chart 日線 → {dates, close, currency}（日期以 UTC 日期表示）。"""
    payload = http.get_json(YAHOO_CHART.format(symbol=urllib.parse.quote(symbol, safe="=.")),
                            {"range": rng, "interval": "1d"})
    res = ((payload or {}).get("chart") or {}).get("result") or []
    if not res:
        raise RuntimeError(((payload or {}).get("chart") or {}).get("error") or "empty result")
    r = res[0]
    ts = r.get("timestamp") or []
    closes = (r.get("indicators", {}).get("quote") or [{}])[0].get("close") or []
    rows = [(dt.datetime.fromtimestamp(t, dt.timezone.utc).date().isoformat(), num(c))
            for t, c in zip(ts, closes) if num(c) is not None]
    dedup: Dict[str, float] = {}
    for d, c in rows:
        dedup[d] = c  # 同日多筆時取最後一筆
    dates = sorted(dedup)
    if len(dates) < 6:
        raise RuntimeError(f"only {len(dates)} bars")
    return {"dates": dates, "close": [dedup[d] for d in dates], "currency": r.get("meta", {}).get("currency")}


def fetch_commodity(http: Http, spec: Dict[str, Any]) -> Dict[str, Any]:
    out: Dict[str, Any] = {k: spec[k] for k in ("symbol", "name", "zh", "short", "unit")}
    errors = []
    for src in spec["sources"]:
        try:
            ser = fetch_yahoo_series(http, src)
            px = ser["close"]
            last = px[-1]
            out.update({
                "source_symbol": src,
                "proxy": src != spec["symbol"],
                "currency": ser["currency"],
                "last": r2(last, 4),
                "chg_1d_pct": _pct(last, px[-2]),
                "chg_5d_pct": _pct(last, px[-6]),
                "chg_20d_pct": _pct(last, px[-21]) if len(px) >= 21 else None,
                "as_of": ser["dates"][-1],
                "spark": [r2(c, 4) for c in px[-30:]],
                "error": None,
                "_series": {"dates": ser["dates"], "close": px},
            })
            if out["proxy"]:
                out["proxy_note"] = f"Yahoo 無 {spec['symbol']} 報價，以 {src} 代理"
            return out
        except Exception as e:  # noqa: BLE001
            errors.append(f"{src}: {e}")
    out.update({"source_symbol": None, "proxy": False, "last": None, "chg_1d_pct": None, "chg_5d_pct": None,
                "chg_20d_pct": None, "as_of": None, "spark": [], "error": "; ".join(errors)})
    return out


def fetch_commodities(http: Http) -> List[Dict[str, Any]]:
    out = []
    for spec in COMMODITIES:
        q = fetch_commodity(http, spec)
        if q["error"]:
            log.warning("CMDTY %-5s failed: %s", spec["symbol"], q["error"])
        else:
            log.info("CMDTY %-5s %-10s last %10.3f  5D %+6.2f%%  20D %s%s", q["symbol"], q["source_symbol"], q["last"],
                     q["chg_5d_pct"] or 0, "n/a" if q["chg_20d_pct"] is None else f"{q['chg_20d_pct']:+.2f}%",
                     "  (proxy)" if q["proxy"] else "")
        out.append(q)
    return out


def load_industries(http: Http) -> Dict[str, str]:
    """公司代號 → 產業別代碼（TWSE + TPEx 公司基本資料）。"""
    out: Dict[str, str] = {}
    for url, code_key, ind_key in ((TWSE_COMPANY, "公司代號", "產業別"),
                                   (TPEX_COMPANY, "SecuritiesCompanyCode", "SecuritiesIndustryCode")):
        try:
            for r in http.get_json(url):
                code, ind = str(r.get(code_key, "")).strip(), str(r.get(ind_key, "")).strip()
                if code and ind:
                    out[code] = ind.zfill(2)
        except Exception as e:  # noqa: BLE001
            log.warning("Industry list failed (%s): %s", url, e)
    log.info("Industry map loaded: %d companies", len(out))
    return out


def _sina_validate(text: str) -> None:
    i, j = text.find("("), text.rfind(")")
    if i < 0 or j <= i or text[i + 1:j].strip() in ("", "null"):
        raise ValueError("empty Sina payload")


def fetch_sina_series(http: Http, code: str, cache_dir: Path, day_key: str, keep: int = 200) -> Dict[str, Any]:
    """新浪財經中國期貨主連日 K（只保留最近 keep 筆，按日快取）。"""
    path = cache_dir / f"sina_{code}_{day_key}.json"
    if path.exists():
        try:
            return json.loads(path.read_text("utf-8"))
        except json.JSONDecodeError:
            path.unlink(missing_ok=True)
    try:
        text = http.get_text(SINA_KLINE, {"symbol": code}, {"Referer": "https://finance.sina.com.cn/"},
                             timeout=30, validate=_sina_validate)
    except Exception:
        # 新浪偶有長時間卡住 → 退回最近一次快取（快取保留 7 天），並標註資料日
        old = sorted(cache_dir.glob(f"sina_{code}_*.json"))
        if not old:
            raise
        ser = json.loads(old[-1].read_text("utf-8"))
        ser["stale_cache"] = old[-1].stem.rsplit("_", 1)[-1]
        log.warning("Sina %s fetch failed → using cached %s", code, ser["stale_cache"])
        return ser
    rows = json.loads(text[text.find("(") + 1:text.rfind(")")])
    rows = [r for r in rows if num(r.get("c"))][-keep:]
    ser = {"dates": [r["d"] for r in rows], "close": [num(r["c"]) for r in rows]}
    path.write_text(json.dumps(ser), "utf-8")
    return ser


def derive_series(parts: List[Dict[str, Any]]) -> Dict[str, Any]:
    """多個序列取共同日期，各自以首日 = 100 標準化後等權平均。"""
    if len(parts) == 1:
        return {"dates": list(parts[0]["dates"]), "close": list(parts[0]["close"])}
    maps = [dict(zip(p["dates"], p["close"])) for p in parts]
    common = sorted(set.intersection(*[set(m) for m in maps]))
    base = [m[common[0]] for m in maps]
    return {"dates": common, "close": [round(sum(m[d] / b for m, b in zip(maps, base)) / len(maps) * 100, 4)
                                       for d in common]}


def load_factor_series(http: Http, macro_list: List[Dict[str, Any]], cache_dir: Path,
                       warnings: List[str]) -> Dict[str, Dict[str, Any]]:
    """回傳 因子 key → {dates, close, last, chg_*}；失敗者帶 error。"""
    cache_dir.mkdir(parents=True, exist_ok=True)
    day_key = now_tpe().strftime("%Y%m%d")
    macro = {q["symbol"]: q for q in macro_list}
    # 新浪回應慢且大（完整歷史數百 KB）→ 並行抓取
    sina_keys = [k for k, f in FACTORS.items() if f["src"] == "sina"]
    sina: Dict[str, Any] = {}
    with concurrent.futures.ThreadPoolExecutor(max_workers=len(sina_keys)) as ex:
        futs = {ex.submit(fetch_sina_series, http, k, cache_dir, day_key): k for k in sina_keys}
        for fut in concurrent.futures.as_completed(futs):
            try:
                sina[futs[fut]] = fut.result()
            except Exception as e:  # noqa: BLE001
                sina[futs[fut]] = e
    out: Dict[str, Dict[str, Any]] = {}
    for key, f in FACTORS.items():
        try:
            if f["src"] == "sina":
                if isinstance(sina[key], Exception):
                    raise sina[key]
                ser = sina[key]
                if ser.get("stale_cache"):
                    warnings.append(f"Factor {key}: Sina fetch failed, using cache from {ser['stale_cache']}.")
            elif f["src"] == "macro":
                q = macro.get(key) or {}
                if not q.get("_series"):
                    raise RuntimeError(q.get("error") or "macro series unavailable")
                ser = q["_series"]
            else:
                avail = [k for k in f["from"] if k in out and not out[k].get("error")]
                if not avail:
                    raise RuntimeError(f"depends on unavailable {f['from']}")
                ser = derive_series([out[k] for k in avail])
                if len(avail) < len(f["from"]):
                    ser["partial"] = f"{'/'.join(k for k in f['from'] if k not in avail)} 暫缺，僅以 {'/'.join(avail)} 計算"
                    warnings.append(f"Factor {key}: {ser['partial']}")
            px = ser["close"]
            out[key] = {"dates": ser["dates"], "close": px, "last": r2(px[-1], 4), "as_of": ser["dates"][-1],
                        "chg_5d_pct": _pct(px[-1], px[-6]) if len(px) > 5 else None,
                        "chg_20d_pct": _pct(px[-1], px[-21]) if len(px) > 20 else None,
                        "chg_60d_pct": _pct(px[-1], px[-61]) if len(px) > 60 else None, "error": None,
                        "stale_cache": ser.get("stale_cache"), "partial": ser.get("partial")}
            log.info("FACTOR %-8s %-6s last %10.3f  5D %s  20D %s  (%s)", key, f["src"], px[-1],
                     out[key]["chg_5d_pct"], out[key]["chg_20d_pct"], ser["dates"][-1])
        except Exception as e:  # noqa: BLE001
            out[key] = {"error": str(e)}
            warnings.append(f"Factor {key} unavailable: {e}")
            log.warning("FACTOR %s failed: %s", key, e)
    return out


def fetch_stock_series(http: Http, s: Dict[str, Any], fallback: List[Dict[str, Any]]) -> Tuple[Dict[str, Any], str]:
    """個股收盤序列：Yahoo {code}.TW / .TWO（6 個月），失敗時退回 FinMind 歷史。以交易所報價日對齊最新收盤。"""
    sym = f"{s['code']}.{'TW' if s['market'] == 'TWSE' else 'TWO'}"
    try:
        ser, src = fetch_yahoo_series(http, sym), f"Yahoo {sym}"
        dates, close = ser["dates"], ser["close"]
    except Exception as e:  # noqa: BLE001
        log.warning("Stock series %s failed (%s) → FinMind history", sym, e)
        dates, close, src = [h["d"] for h in fallback], [h["c"] for h in fallback], "FinMind"
    sd = s.get("data_date")
    if sd:
        keep = [i for i, d in enumerate(dates) if d < sd]
        dates, close = [dates[i] for i in keep] + [sd], [close[i] for i in keep] + [s["close"]]
    return {"dates": dates, "close": close}, src


def pearson(x: List[float], y: List[float]) -> Optional[float]:
    n = len(x)
    if n < 8:
        return None
    mx, my = sum(x) / n, sum(y) / n
    sxx = sum((a - mx) ** 2 for a in x)
    syy = sum((b - my) ** 2 for b in y)
    if sxx <= 0 or syy <= 0:
        return None
    return sum((a - mx) * (b - my) for a, b in zip(x, y)) / math.sqrt(sxx * syy)


def lead_lag(stock: Dict[str, Any], fac: Dict[str, Any]) -> Dict[str, Dict[str, Any]]:
    """
    股價 5 日對數報酬 (t-5→t) 對 期貨 5 日對數報酬 (j-L-5→j-L)，j＝t 當日（含）以前最後一個期貨交易日。
    L＝期貨領先股價的期貨交易日數。Lag 0 為同日對照（期貨收盤可能晚於台股收盤，不可直接交易）。
    """
    fd, fc = fac["dates"], fac["close"]
    sd, sc = stock["dates"], stock["close"]
    pos = [bisect.bisect_right(fd, d) - 1 for d in sd]
    out: Dict[str, Dict[str, Any]] = {}
    for L in LEADS:
        xs: List[float] = []
        ys: List[float] = []
        for i in range(RET_H, len(sc)):
            j = pos[i] - L
            if j - RET_H < 0 or not sc[i - RET_H] or not fc[j - RET_H]:
                continue
            ys.append(math.log(sc[i] / sc[i - RET_H]))
            xs.append(math.log(fc[j] / fc[j - RET_H]))
        r = pearson(xs, ys)
        hits = [(a > 0) == (b > 0) for a, b in zip(xs, ys) if a != 0 and b != 0]
        out[str(L)] = {"r": None if r is None else round(r, 3),
                       "hit": round(sum(hits) / len(hits), 3) if hits else None, "n": len(xs)}
    return out


def _alloc_100(raw: List[float]) -> List[int]:
    """依比例分配整數百分比，總和固定 100（最大餘數法）。"""
    tot = sum(raw) or 1.0
    exact = [x / tot * 100 for x in raw]
    base = [int(math.floor(e)) for e in exact]
    for i in sorted(range(len(raw)), key=lambda k: exact[k] - base[k], reverse=True)[:100 - sum(base)]:
        base[i] += 1
    return base


def rate_weighted(ws: float) -> str:
    return "TAILWIND" if ws >= MACRO_TH["w_tail"] else "HEADWIND" if ws <= MACRO_TH["w_head"] else "NEUTRAL"


def build_factor_model(s: Dict[str, Any], industry_code: Optional[str], stock: Dict[str, Any],
                       fdata: Dict[str, Dict[str, Any]], stock_src: str) -> Tuple[Dict[str, Any], Optional[Dict[str, Any]], Dict[str, Any]]:
    """回傳 (commodity_linkage, factor_model, timeseries)。"""
    industry = INDUSTRY_NAMES.get(industry_code or "", industry_code or "未知")
    win_d, win_c = stock["dates"][-WINDOW:], stock["close"][-WINDOW:]
    ts: Dict[str, Any] = {"dates": win_d, "stock": [r2(c, 3) for c in win_c], "stock_source": stock_src, "factors": {}}
    key = CODE_CHAIN.get(s["code"]) or INDUSTRY_CHAIN.get(industry_code or "")
    base = {"industry_code": industry_code, "industry": industry}
    if not key:
        return ({**base, "mapped": False, "label": industry[:2], "tag": "", "legs": [], "rating": "N/A",
                 "rating_zh": RATING_ZH["N/A"], "score": None,
                 "commentary": NO_FUTURES_NOTE.get(industry_code or "",
                                                   f"{industry}無直接對應之商品期貨，不納入利差判讀，以個股基本面為主。")}, None, ts)
    model = CHAIN_MODELS[key]
    stock_w = {"dates": win_d, "close": win_c}
    factors: List[Dict[str, Any]] = []
    for fk, role, direct in model["factors"]:
        fd = fdata.get(fk) or {"error": "not loaded"}
        f = FACTORS[fk]
        row: Dict[str, Any] = {"key": fk, "name": f["name"], "short": f["short"], "unit": f["unit"], "role": role,
                               "sign": 1 if role == "price" else -1, "directness": direct,
                               "source": {"sina": "新浪財經", "macro": "Yahoo Finance", "derived": "推算"}[f["src"]],
                               "proxy": f["src"] == "derived" or fk == "^BDI",
                               "note": "；".join(x for x in (f.get("note"), fd.get("partial"),
                                                            f"新浪連線失敗，沿用 {fd['stale_cache']} 快取" if fd.get("stale_cache") else None) if x) or None}
        if fd.get("error"):
            row.update({"error": fd["error"], "weight": 0})
            factors.append(row)
            continue
        ll = lead_lag(stock_w, fd)
        best = max((L for L in ll if ll[L]["r"] is not None), key=lambda L: abs(ll[L]["r"]), default=None)
        pos = [bisect.bisect_right(fd["dates"], d) - 1 for d in win_d]
        raw = [fd["close"][p] if p >= 0 else None for p in pos]
        first = next((v for v in raw if v), None)
        ts["factors"][fk] = {"raw": [r2(v, 4) for v in raw],
                             "idx": [r2(v / first * 100, 3) if v and first else None for v in raw]}
        row.update({"last": fd["last"], "as_of": fd["as_of"], "chg_5d_pct": fd["chg_5d_pct"],
                    "chg_20d_pct": fd["chg_20d_pct"], "chg_60d_pct": fd["chg_60d_pct"], "lead_lag": ll,
                    "best_lead": None if best is None else int(best),
                    "best_r": None if best is None else ll[best]["r"],
                    "best_hit": None if best is None else ll[best]["hit"],
                    "best_n": None if best is None else ll[best]["n"]})
        factors.append(row)

    ok = [f for f in factors if not f.get("error")]
    if not ok:
        return ({**base, "mapped": True, "label": model["label"], "tag": model["tag"], "chain": model["chain"],
                 "legs": [], "rating": "N/A", "rating_zh": RATING_ZH["N/A"], "score": None,
                 "commentary": "期貨序列暫缺，本次無法判讀利差結構。"}, None, ts)
    raws = [f["directness"] * (MACRO_TH["base_strength"] + abs(f["best_r"] or 0)) for f in ok]
    for f, w in zip(ok, _alloc_100(raws)):
        f["weight"] = w
    ws = sum(f["weight"] / 100 * f["sign"] * (f["chg_20d_pct"] or 0) for f in ok)
    rating = rate_weighted(ws)
    score = int(clamp(round(ws * 5), -100, 100))

    name = s["name"]
    for f in ok:
        r, L, hit = f["best_r"], f["best_lead"], f["best_hit"]
        side = "售價端" if f["role"] == "price" else "成本端"
        lvl = "直接" if f["directness"] >= 0.9 else "次要" if f["directness"] >= 0.7 else "間接／總體"
        if r is None:
            rel = "樣本不足，無法計算相關"
        else:
            when = f"領先{name}約 {L} 個交易日" if L else f"與{name}同步連動（Lag 0）"
            strength = "強" if abs(r) >= 0.5 else "中等" if abs(r) >= 0.3 else "偏弱"
            rel = f"歷史數據顯示{f['short']}{when}，r={r:+.2f}（{strength}），方向一致率 {hit:.0%}"
        f["rationale"] = (f"{rel}；屬{side}{lvl}因子（直接度 {f['directness']:.1f}）"
                          f" → 建議權重 {f['weight']}%" + ("，相關偏弱故權重主要來自產業直接度" if r is not None and abs(r) < 0.3 else ""))

    price = next((f for f in ok if f["role"] == "price"), None)
    cost = next((f for f in ok if f["role"] == "cost"), None)
    spread = None
    if price and cost:
        sp20 = (price["chg_20d_pct"] or 0) - (cost["chg_20d_pct"] or 0)
        pi, ci = ts["factors"][price["key"]]["idx"], ts["factors"][cost["key"]]["idx"]
        spread = {"label": f"{price['short']} − {cost['short']}", "price": price["key"], "cost": cost["key"],
                  "spread_20d_pp": round(sp20, 2),
                  "values": [r2(a - b, 3) if a is not None and b is not None else None for a, b in zip(pi, ci)]}
        ts["spread"] = {"label": spread["label"], "values": spread["values"]}

    parts = []
    if spread:
        parts.append(f"產品端 {price['short']} 20 日 {price['chg_20d_pct']:+.1f}%、成本端 {cost['short']} "
                     f"{cost['chg_20d_pct']:+.1f}% → 加工利差 {spread['spread_20d_pp']:+.1f} 個百分點"
                     f"{'擴大' if spread['spread_20d_pp'] > 0 else '收斂'}")
    else:
        parts.append("、".join(f"{f['short']}（{'售價' if f['role'] == 'price' else '成本'}端）20 日 {f['chg_20d_pct']:+.1f}%"
                              for f in ok))
    lead = max((f for f in ok if f["best_r"] is not None), key=lambda f: abs(f["best_r"]), default=None)
    if lead:
        parts.append(f"領先性最強為 {lead['short']}（{'Lead ' + str(lead['best_lead']) + 'D' if lead['best_lead'] else 'Lag 0'}，"
                     f"r={lead['best_r']:+.2f}）")
    tail = {"TAILWIND": "，基本面拐點獲商品期貨確認", "HEADWIND": "，留意毛利壓縮風險", "NEUTRAL": ""}[rating]
    parts.append(f"加權利差 {ws:+.1f} → {rating} {RATING_ZH[rating]}{tail}")
    text = "；".join(parts) + "。"
    for f in ok:
        c5, c20 = f["chg_5d_pct"], f["chg_20d_pct"]
        if c5 is not None and c20 and c5 * c20 < 0 and abs(c5) >= MACRO_TH["divergence_5d"]:
            text += f"惟{f['short']}近 5 日 {c5:+.1f}% 反向，留意趨勢轉折。"
    notes = [f["note"] for f in ok if f.get("note")] + [f"{f['short']}以 BDRY 乾散貨運費 ETF 代理" for f in ok if f["key"] == "^BDI"]
    if notes:
        text += "（" + "；".join(dict.fromkeys(notes)) + "）"

    fm = {"model": key, "label": model["label"], "chain": model["chain"], "tag": model["tag"], "factors": factors,
          "spread": {k: v for k, v in (spread or {}).items() if k != "values"} or None,
          "weighted_spread": round(ws, 2), "score": score, "rating": rating, "rating_zh": RATING_ZH[rating],
          "thresholds": {"tail": MACRO_TH["w_tail"], "head": MACRO_TH["w_head"]},
          "method": (f"相關係數＝股價 {RET_H} 日對數報酬 vs 期貨 {RET_H} 日對數報酬（重疊樣本，近 {WINDOW} 日）；"
                     f"Lead L＝期貨較股價提前 L 個期貨交易日；Lag 0 為同日對照，期貨收盤可能晚於台股，不可直接交易；"
                     f"權重＝直接度 ×（{MACRO_TH['base_strength']} + |最佳 r|）正規化為 100%；"
                     f"加權利差＝Σ 權重 × 方向（售價 +／成本 −）× 20 日漲跌%，≥ {MACRO_TH['w_tail']} 為 TAILWIND、"
                     f"≤ {MACRO_TH['w_head']} 為 HEADWIND。重疊報酬之有效樣本約 n/{RET_H}，|r| < 0.3 視為偏弱。")}
    legs = [{"symbol": f["key"], "short": f["short"], "zh": f["name"], "role": f["role"], "last": f.get("last"),
             "chg_5d_pct": f.get("chg_5d_pct"), "chg_20d_pct": f.get("chg_20d_pct"), "weight": f.get("weight"),
             "effect": None if f.get("chg_20d_pct") is None else ("favorable" if f["sign"] * f["chg_20d_pct"] > 1
                                                                  else "unfavorable" if f["sign"] * f["chg_20d_pct"] < -1 else "flat"),
             "proxy": f["proxy"]} for f in factors]
    link = {**base, "mapped": True, "label": model["label"], "tag": model["tag"], "chain": model["chain"], "model": key,
            "legs": legs, "rating": rating, "rating_zh": RATING_ZH[rating], "score": score,
            "weighted_spread": round(ws, 2), "commentary": text}
    return link, fm, ts


# ──────────────────────────────────────────────────────────────────────────────
# 跨國同業龍頭比價與補漲動能（Global Sector Peer & Catch-Up Engine）
# ──────────────────────────────────────────────────────────────────────────────
def _ret(px: List[float], k: int) -> Optional[float]:
    return _pct(px[-1], px[-1 - k]) if len(px) > k else None


def _mean(xs: List[Optional[float]]) -> Optional[float]:
    xs = [x for x in xs if x is not None]
    return sum(xs) / len(xs) if xs else None


class PeerCache:
    """同業標竿序列只抓一次（多檔候選股共用同一組龍頭）。"""

    def __init__(self, http: Http):
        self.http = http
        self.data: Dict[str, Any] = {}

    def get(self, sym: str) -> Dict[str, Any]:
        if sym not in self.data:
            try:
                self.data[sym] = fetch_yahoo_series(self.http, sym)
            except Exception as e:  # noqa: BLE001
                log.warning("PEER %s failed: %s", sym, e)
                self.data[sym] = {"error": str(e)}
        return self.data[sym]


def build_peer_analysis(s: Dict[str, Any], industry_code: Optional[str], stock: Dict[str, Any],
                        cache: PeerCache, pb_lookup=None) -> Tuple[Optional[Dict[str, Any]], Dict[str, Any]]:
    """回傳 (peer_analysis, timeseries.peers)。Catch-Up Gap = 同業平均 20D − 本檔 20D。"""
    gkey = PEER_GROUP_BY_INDUSTRY.get(industry_code or "")
    if not gkey:
        return None, {}
    grp = SECTOR_PEERS[gkey]
    sc = stock["close"]
    win_d, win_c = stock["dates"][-WINDOW:], sc[-WINDOW:]
    stock_w = {"dates": win_d, "close": win_c}
    target = {"chg_5d_pct": _ret(sc, 5), "chg_20d_pct": _ret(sc, 20), "chg_60d_pct": _ret(sc, 60)}
    s20 = target["chg_20d_pct"]
    peers: List[Dict[str, Any]] = []
    ts_peers: Dict[str, Any] = {}
    for sym, name, tier in grp["peers"]:
        if sym.split(".")[0] == s["code"]:
            continue  # 本身就是龍頭時略過
        row: Dict[str, Any] = {"symbol": sym, "name": name, "tier": tier, "tier_zh": TIER_ZH[tier]}
        # P/B：台股取 TWSE/TPEx 本益比淨值比表；中美股僅接受 PEER_PB_MANUAL 手動值
        pb = PEER_PB_MANUAL.get(sym)
        row["pb_source"] = "manual" if pb else None
        if pb is None and tier == "TW" and pb_lookup:
            pb = pb_lookup(sym.split(".")[0])
            row["pb_source"] = "TWSE/TPEx" if pb else None
        row["pb"] = pb if pb and pb > 0 else None
        ser = cache.get(sym)
        if ser.get("error"):
            peers.append({**row, "error": ser["error"]})
            continue
        px = ser["close"]
        ll = lead_lag(stock_w, ser)
        best = max((L for L in ll if ll[L]["r"] is not None), key=lambda L: abs(ll[L]["r"]), default=None)
        pos = [bisect.bisect_right(ser["dates"], d) - 1 for d in win_d]
        raw = [px[p] if p >= 0 else None for p in pos]
        first = next((v for v in raw if v), None)
        ts_peers[sym] = {"raw": [r2(v, 4) for v in raw],
                         "idx": [r2(v / first * 100, 3) if v and first else None for v in raw]}
        p20 = _ret(px, 20)
        peers.append({**row, "currency": ser.get("currency"), "last": r2(px[-1], 4), "as_of": ser["dates"][-1],
                      "chg_5d_pct": _ret(px, 5), "chg_20d_pct": p20, "chg_60d_pct": _ret(px, 60),
                      "lead_lag": ll, "best_lead": None if best is None else int(best),
                      "best_r": None if best is None else ll[best]["r"],
                      "best_hit": None if best is None else ll[best]["hit"],
                      "gap_20d_pp": None if p20 is None or s20 is None else round(p20 - s20, 2)})
    ok = [p for p in peers if not p.get("error")]
    tw_avg = _mean([p["chg_20d_pct"] for p in ok if p["tier"] == "TW"])
    gl_avg = _mean([p["chg_20d_pct"] for p in ok if p["tier"] != "TW"])
    peer_avg = _mean([tw_avg, gl_avg])  # 台股龍頭組與中美指標組各占一半
    gap = None if peer_avg is None or s20 is None else round(peer_avg - s20, 2)
    name = s["name"]
    if gap is None:
        sig, text = "N/A", "同業標竿或本檔序列不足，無法計算補漲剪刀差。"
    elif gap >= PEER_TH["catch_up"]:
        sig = "CATCH-UP READY"
        text = (f"同業龍頭 20 日平均 {peer_avg:+.1f}%（台股 {tw_avg if tw_avg is not None else float('nan'):+.1f}%／中美 "
                f"{gl_avg if gl_avg is not None else float('nan'):+.1f}%），{name} 僅 {s20:+.1f}%，落後 {gap:.1f} 個百分點 → 龍頭已動、落後補漲")
        if peer_avg < 0:
            text += "（惟同業本身亦在下跌，屬相對抗跌而非龍頭已發動，宜待龍頭轉強再確認）"
    elif peer_avg <= PEER_TH["divergence"] and gap <= PEER_TH["divergence"]:
        sig = "PEER DIVERGENCE"
        text = f"同業龍頭 20 日平均 {peer_avg:+.1f}% 明顯轉弱，{name} 逆勢 {s20:+.1f}%（領先同業 {-gap:.1f} 個百分點）→ 同業轉弱警示，留意補跌風險"
    else:
        sig = "IN LINE"
        text = f"同業龍頭 20 日平均 {peer_avg:+.1f}%、{name} {s20:+.1f}%，剪刀差 {gap:+.1f} 個百分點，走勢大致同步"
    lead = max((p for p in ok if p.get("best_r") is not None), key=lambda p: abs(p["best_r"]), default=None)
    if lead and gap is not None:
        text += (f"；與{name}連動最強為 {lead['name']}（{'Lead ' + str(lead['best_lead']) + 'D' if lead['best_lead'] else 'Lag 0'}，"
                 f"r={lead['best_r']:+.2f}）")
    text += "。"
    return ({"group": gkey, "label": grp["label"], "target": target, "peers": peers,
             "tw_avg_20d": r2(tw_avg), "global_avg_20d": r2(gl_avg), "peer_avg_20d": r2(peer_avg),
             "catch_up_gap": gap, "signal": sig, "signal_zh": PEER_SIGNAL_ZH[sig],
             "thresholds": PEER_TH, "commentary": text,
             "method": (f"Catch-Up Gap＝（台股龍頭組 20D 平均 與 中美指標組 20D 平均 再取平均）− 本檔 20D；"
                        f"≥ +{PEER_TH['catch_up']:.0f} 為 CATCH-UP READY，同業平均 ≤ {PEER_TH['divergence']:.0f}% 且 Gap ≤ "
                        f"{PEER_TH['divergence']:.0f} 為 PEER DIVERGENCE。r＝5 日對數報酬相關，Lead L＝同業較本檔提前 L 個交易日；"
                        f"中美股以當地收盤日對齊台股日期（as-of），有時差。")}, ts_peers)


# ──────────────────────────────────────────────────────────────────────────────
# 多因子合理市價模擬引擎（Multi-Factor Fair Value Pricing Simulator）
# ──────────────────────────────────────────────────────────────────────────────
def fair_value_calc(inp: Dict[str, Any], prm: Dict[str, Any], roe_base: float) -> Dict[str, Any]:
    """三情境 × 三支柱。dashboard.html 的 fvCalc() 以相同公式即時重算（滑桿）。"""
    out: Dict[str, Any] = {}
    bv, w = inp["bvps"], prm["weights"]
    for name, sc in prm["scenarios"].items():
        ke = prm["ke"] + sc["ke_shift"]
        roe = roe_base + sc["roe_shift"]
        liq = clamp(prm["liq_disc"] + sc["liq_shift"], 0.0, 0.9)
        pb_a = clamp((roe - prm["g"]) / (ke - prm["g"]), prm["pb_floor"], prm["pb_cap"])
        pb_b = inp["peer_pb_mean"] * (1 - liq)
        a, b, c = pb_a * bv, pb_b * bv, sc["anchor_pb"] * bv
        price = w["A"] * a + w["B"] * b + w["C"] * c
        out[name] = {"price": round(price, 2), "upside_pct": round((price / inp["close"] - 1) * 100, 1),
                     "models": {"A": {"pb": round(pb_a, 3), "price": round(a, 2), "roe": round(roe, 4), "ke": round(ke, 4)},
                                "B": {"pb": round(pb_b, 3), "price": round(b, 2), "liq": round(liq, 3)},
                                "C": {"pb": sc["anchor_pb"], "price": round(c, 2)}}}
    return out


def build_fair_value(c: Dict[str, Any], peer: Optional[Dict[str, Any]]) -> Dict[str, Any]:
    prm = FV_PARAMS
    bv = c["book_value"]
    eps = c.get("eps_latest")
    roe_q = (eps * 4 / bv) if eps is not None and bv else 0.0
    wms = (c.get("commodity_linkage") or {}).get("score")
    pbs = [{"symbol": p["symbol"], "name": p["name"], "tier": p["tier"], "pb": p.get("pb"), "source": p.get("pb_source")}
           for p in ((peer or {}).get("peers") or [])]
    got = [p["pb"] for p in pbs if p["pb"]]
    fallback = not got
    srt = sorted(got)   # 中位數：避免單一高溢價龍頭（如萬華 2.45x）拉高同業中樞
    peer_pb = (srt[len(srt) // 2] if len(srt) % 2 else (srt[len(srt) // 2 - 1] + srt[len(srt) // 2]) / 2) if got else prm["peer_pb_default"]
    inp = {"bvps": bv, "close": c["close"], "eps_q": eps, "eps_period": c.get("eps_period"), "roe_q_ann": round(roe_q, 4),
           "wms": wms, "peer_pb_mean": round(peer_pb, 3), "peer_pb_method": "median", "peer_pb_n": len(got), "peer_pb_list": pbs,
           "peer_pb_fallback": fallback}
    roe_base = inp["roe_q_ann"] + prm["macro_lambda"] * (wms or 0) / 100   # 用已存檔的四捨五入值，確保與前端 fvCalc 完全一致
    sc = fair_value_calc(inp, prm, roe_base)
    notes = []
    if sc["base"]["models"]["A"]["pb"] <= prm["pb_floor"] + 1e-9:
        notes.append(f"模型 A 觸及 P/B 下限 {prm['pb_floor']:.2f}x：正常化 ROE {roe_base:.1%} 接近或低於 g {prm['g']:.1%}，"
                     f"Gordon 模型在獲利低谷期會趨近 0，下限代表重資產清算／重置價值的保守假設。")
    if fallback:
        notes.append(f"同業 P/B 皆未取得 → 以產業常態中樞 {prm['peer_pb_default']:.2f}x 代替。")
    elif len(got) < len(pbs):
        miss = [p["symbol"] for p in pbs if not p["pb"]]
        notes.append(f"同業 P/B 僅取得 {len(got)}/{len(pbs)} 檔（缺 {', '.join(miss)}；中美股 P/B 可填入 scanner.py 的 PEER_PB_MANUAL）。")
    manual = [p for p in pbs if p["source"] == "manual"]
    if manual:
        notes.append(f"中美同業 P/B 為手動常態基準值（{PEER_PB_MANUAL_ASOF} 設定，非即時）："
                     + "、".join(f"{p['name']} {p['pb']:.2f}x" for p in manual) + "；台股龍頭為 TWSE/TPEx 當日 P/B。")
    if abs(roe_q) < 0.03:
        notes.append("單季年化 ROE 偏低（轉機初期），模型 A 對 ROE 假設極敏感，建議在次頁以「正常化 ROE」滑桿測試景氣中樞情境。")
    base = sc["base"]["price"]
    return {"inputs": inp, "params": prm, "roe_norm": round(roe_base, 4), "scenarios": sc,
            "base_fair": base, "fair_upside_pct": sc["base"]["upside_pct"],
            "discount_pct": round((c["close"] / base - 1) * 100, 1) if base else None, "notes": notes}


# ──────────────────────────────────────────────────────────────────────────────
# 個股深度基本面、杜邦拆解與風險因子引擎（[FA] 模組）
# ──────────────────────────────────────────────────────────────────────────────
_PREV_Q = {"06-30": "03-31", "09-30": "06-30", "12-31": "09-30"}
_AR_KEYS = ("AccountsReceivableNet", "BillsReceivableNet", "AccountsReceivableDuefromRelatedPartiesNet")
_AP_KEYS = ("AccountsPayable", "AccountsPayableToRelatedParties", "NotesPayable")
_DEBT_KEYS = ("ShorttermBorrowings", "ShorttermNotesAndBillsPayable", "CurrentPortionOfLongtermLiabilities",
              "LongtermBorrowings", "BondsPayable")


def fa_pivot(rows: List[Dict[str, Any]]) -> Dict[str, Dict[str, float]]:
    by: Dict[str, Dict[str, float]] = {}
    for r in rows:
        t, v = r.get("type"), num(r.get("value"))
        if not t or v is None or str(t).endswith("_per"):
            continue
        by.setdefault(r["date"], {})[t] = v
    return by


def fa_decumulate(by: Dict[str, Dict[str, float]]) -> Dict[str, Dict[str, float]]:
    """現金流量表為年度累計 → 拆成單季（Q1 原值；Qn = 累計 n − 累計 n−1；缺前一季則為 None）。"""
    out: Dict[str, Dict[str, float]] = {}
    for d, cur in by.items():
        mmdd = d[5:]
        if mmdd == "03-31":
            out[d] = dict(cur)
            continue
        prev = by.get(f"{d[:4]}-{_PREV_Q.get(mmdd, '')}")
        if prev is None:
            continue
        out[d] = {t: v - prev[t] for t, v in cur.items() if t in prev}
    return out


def _g(d: Dict[str, float], *keys: str) -> Optional[float]:
    for k in keys:
        if d.get(k) is not None:
            return d[k]
    return None


def _mn(v: Optional[float]) -> str:
    """元 → 百萬元字串；缺值顯示 —。"""
    return "—" if v is None else f"{v / 1e6:,.0f}"


def fa_placeholder(reason: str) -> Dict[str, Any]:
    """財報分析無法產出時的安全預設結構（欄位與 build_fundamentals 相同，數值一律 None，不推估、不補值）。"""
    return {"status": "UNAVAILABLE", "reason": reason, "source": "—", "latest": None, "latest_date": None, "quarters": [],
            "dupont": {"npm": None, "at": None, "em": None, "roe": None, "yoy_q": None, "d_npm": None, "d_at": None,
                       "d_em": None, "d_roe": None, "driver": "資料不足", "quality": "N/A"},
            "z": {"value": None, "zone": None, "x": None},
            "scores": {"profitability": None, "efficiency": None, "liquidity": None, "solvency": None},
            "fa_score": None, "operating_risk": None, "financial_risk": None,
            "risk_factors": [], "risk_counts": {"HIGH": 0, "MODERATE": 0, "STRENGTH": 0},
            "twse_check": {"available": False}, "notes": [reason]}


def fa_summary(fa: Dict[str, Any]) -> Dict[str, Any]:
    """前後端共用的精簡 FA 摘要（杜邦三因子＋Altman Z＋風險因子）。"""
    dp, z = fa.get("dupont") or {}, fa.get("z") or {}
    return {"status": fa.get("status", "OK"), "reason": fa.get("reason"), "period": fa.get("latest"),
            "roe": dp.get("roe"), "npm": dp.get("npm"), "asset_turnover": dp.get("at"), "equity_multiplier": dp.get("em"),
            "z_score": z.get("value"), "altman_z_status": z.get("zone"), "fa_score": fa.get("fa_score"),
            "operating_risk": fa.get("operating_risk"), "financial_risk": fa.get("financial_risk"),
            "risk_factors": [{"severity": r["severity"], "title": r["title"]} for r in fa.get("risk_factors") or []],
            "risk_counts": fa.get("risk_counts") or {"HIGH": 0, "MODERATE": 0, "STRENGTH": 0}}


def _gsum(d: Dict[str, float], keys) -> Optional[float]:
    vals = [d[k] for k in keys if d.get(k) is not None]
    return sum(vals) if vals else None


def _div(a: Optional[float], b: Optional[float]) -> Optional[float]:
    return a / b if a is not None and b not in (None, 0) else None


def _avg(a: Optional[float], b: Optional[float]) -> Optional[float]:
    if a is None:
        return b
    if b is None:
        return a
    return (a + b) / 2


def _lin(v: Optional[float], bad: float, good: float) -> Optional[float]:
    """把指標線性映射到 0~100（bad → 0、good → 100）。"""
    if v is None:
        return None
    return clamp((v - bad) / (good - bad) * 100, 0, 100)


def _mean_score(xs: List[Optional[float]]) -> Optional[float]:
    xs = [x for x in xs if x is not None]
    return round(sum(xs) / len(xs), 1) if xs else None


def load_twse_fin(http: Http) -> Dict[str, Dict[str, Any]]:
    """TWSE OpenAPI 一般業最新一期財報（年度累計，單位：千元）→ 用於核對 FinMind。"""
    out: Dict[str, Dict[str, Any]] = {}
    try:
        inc = {r["公司代號"]: r for r in http.get_json(TWSE_FIN_INCOME)}
        bal = {r["公司代號"]: r for r in http.get_json(TWSE_FIN_BALANCE)}
    except Exception as e:  # noqa: BLE001
        log.warning("TWSE financial statements unavailable: %s", e)
        return out
    for code in set(inc) | set(bal):
        i, b = inc.get(code, {}), bal.get(code, {})
        src = i or b
        try:
            period = f"{int(src['年度']) + 1911}Q{int(src['季別'])}"
        except (KeyError, ValueError):
            continue
        k = lambda v: None if num(v) is None else num(v) * 1000  # noqa: E731
        out[code] = {"period": period, "revenue_ytd": k(i.get("營業收入")), "op_income_ytd": k(i.get("營業利益（損失）")),
                     "ni_parent_ytd": k(i.get("淨利（淨損）歸屬於母公司業主")), "eps_ytd": num(i.get("基本每股盈餘（元）")),
                     "total_assets": k(b.get("資產總計")), "equity_total": k(b.get("權益總計")),
                     "bvps_ref": num(b.get("每股參考淨值"))}
    log.info("TWSE OpenAPI financials loaded: %d companies", len(out))
    return out


def _risk(sev: str, code: str, title: str, metrics: List[str], why: str, action: str) -> Dict[str, Any]:
    return {"severity": sev, "code": code, "title": title, "metrics": metrics, "why": why, "action": action}


def build_fundamentals(s: Dict[str, Any], fm: "FinMind", day_key: str, start: str,
                       stock: Optional[Dict[str, Any]], twse_fin: Dict[str, Dict[str, Any]]) -> Optional[Dict[str, Any]]:
    code = s["code"]
    inc = fa_pivot(fm.data("TaiwanStockFinancialStatements", code, start, day_key))
    bs = fa_pivot(fm.data("TaiwanStockBalanceSheet", code, start, day_key))
    cf = fa_decumulate(fa_pivot(fm.data("TaiwanStockCashFlowsStatement", code, start, day_key)))
    dates = sorted(set(inc) & set(bs))
    if len(dates) < 2:
        return None
    px_dates, px = (stock or {}).get("dates", []), (stock or {}).get("close", [])
    rows: List[Dict[str, Any]] = []
    for i, d in enumerate(dates):
        I, B, C = inc[d], bs[d], cf.get(d, {})
        P = bs.get(dates[i - 1]) if i > 0 else None
        P = P or {}
        rev, cogs = _g(I, "Revenue"), _g(I, "CostOfGoodsSold")
        if _g(I, "GrossProfit") is None and _g(I, "OperatingIncome") is None:
            cogs = None   # 非一般業格式：CostOfGoodsSold 實為「營業成本及費用合計」，不可據以推算毛利與存貨週轉
        gp = _g(I, "GrossProfit") if _g(I, "GrossProfit") is not None else (rev - cogs if rev is not None and cogs is not None else None)
        oi, nonop = _g(I, "OperatingIncome"), _g(I, "TotalNonoperatingIncomeAndExpense")
        pti = _g(I, "PreTaxIncome", "IncomeBeforeTaxFromContinuingOperations")
        if nonop is None and None not in (oi, pti):
            nonop = pti - oi
        ni = _g(I, "IncomeAfterTaxes", "IncomeFromContinuingOperations")
        nip = _g(I, "EquityAttributableToOwnersOfParent") if _g(I, "EquityAttributableToOwnersOfParent") is not None else ni
        ta, eq, eqp = _g(B, "TotalAssets"), _g(B, "Equity"), _g(B, "EquityAttributableToOwnersOfParent", "Equity")
        inv, ppe, ca, cl = _g(B, "Inventories"), _g(B, "PropertyPlantAndEquipment"), _g(B, "CurrentAssets"), _g(B, "CurrentLiabilities")
        cash, liab, re_, ncl = _g(B, "CashAndCashEquivalents"), _g(B, "Liabilities"), _g(B, "RetainedEarnings"), _g(B, "NoncurrentLiabilities")
        prepay, stb = _g(B, "Prepayments") or 0.0, _g(B, "ShorttermBorrowings") or 0.0
        ar, ap, debt = _gsum(B, _AR_KEYS), _gsum(B, _AP_KEYS), _gsum(B, _DEBT_KEYS) or 0.0
        shares = (_g(B, "OrdinaryShare", "CapitalStock") or 0) / 10 or None
        eps = _g(I, "EPS")
        eps_est = eps is None and nip is not None and shares is not None
        if eps_est:
            eps = nip / shares
        a_ta, a_eq = _avg(ta, _g(P, "TotalAssets")), _avg(eq, _g(P, "Equity"))
        a_inv, a_ar, a_ap, a_ppe = (_avg(inv, _g(P, "Inventories")), _avg(ar, _gsum(P, _AR_KEYS)),
                                    _avg(ap, _gsum(P, _AP_KEYS)), _avg(ppe, _g(P, "PropertyPlantAndEquipment")))
        ocf, capex = _g(C, "CashFlowsFromOperatingActivities"), _g(C, "PropertyAndPlantAndEquipment")
        dio = _div(a_inv, cogs) * 91.25 if _div(a_inv, cogs) is not None and cogs and cogs > 0 else None
        dso = _div(a_ar, rev) * 91.25 if _div(a_ar, rev) is not None and rev and rev > 0 else None
        dpo = _div(a_ap, cogs) * 91.25 if _div(a_ap, cogs) is not None and cogs and cogs > 0 else None
        r = {"q": quarter_label(d), "date": d, "rev": rev, "gp": gp, "oi": oi, "nonop": nonop, "pti": pti, "ni": ni,
             "nip": nip, "eps": eps, "eps_est": eps_est,
             "gpm": _div(gp, rev), "opm": _div(oi, rev), "ptm": _div(pti, rev), "npm": _div(ni, rev),
             "nonop_share": _div(nonop, pti) if pti and abs(pti) > 0 else None,
             "roe_ann": _div(ni * 4 if ni is not None else None, a_eq),
             "at": _div(rev * 4 if rev is not None else None, a_ta), "em": _div(a_ta, a_eq),
             "dio": dio, "dso": dso, "dpo": dpo,
             "ccc": dio + dso - dpo if None not in (dio, dso, dpo) else None,
             "inv_turn": _div(cogs * 4 if cogs is not None else None, a_inv),
             "fa_turn": _div(rev * 4 if rev is not None else None, a_ppe),
             "debt_ratio": _div(liab, ta), "ltf_ppe": _div((eq or 0) + (ncl or 0), ppe) if eq is not None else None,
             "current": _div(ca, cl), "quick": _div(ca - inv - prepay, cl) if None not in (ca, inv) else None,
             "net_de": _div(debt - (cash or 0), eq), "st_borrow_share": _div(stb, liab),
             "ocf": ocf, "capex": capex, "fcf": ocf + capex if None not in (ocf, capex) else None,
             "dep": _g(C, "Depreciation"), "int_exp": _g(C, "InterestExpense"),
             "bvps": _div(eqp, shares), "shares": shares, "ta": ta, "eq": eq, "liab": liab,
             "_wc": (ca - cl) if None not in (ca, cl) else None, "_re": re_}
        # Altman Z（製造業）：X4 使用季末市值，僅在股價序列涵蓋該季末時計算
        p_at = None
        if px_dates:
            k = bisect.bisect_right(px_dates, d) - 1
            if k >= 0 and (dt.date.fromisoformat(d) - dt.date.fromisoformat(px_dates[k])).days <= 7:
                p_at = px[k]
        if d == dates[-1] and p_at is None:
            p_at = s["close"]
        r["_mcap"] = p_at * shares if p_at and shares else None
        rows.append(r)

    for i, r in enumerate(rows):
        if i >= 3:
            w = rows[i - 3:i + 1]
            ttm = {k: (sum(x[k] for x in w) if all(x[k] is not None for x in w) else None)
                   for k in ("rev", "gp", "oi", "ni", "pti", "ocf", "fcf", "int_exp", "capex", "dep")}
            r.update({"ocf_ttm": ttm["ocf"], "fcf_ttm": ttm["fcf"], "ni_ttm": ttm["ni"], "oi_ttm": ttm["oi"],
                      "ocf_ni_ttm": _div(ttm["ocf"], ttm["ni"]) if ttm["ni"] and ttm["ni"] > 0 else None,
                      "fcfps_ttm": _div(ttm["fcf"], r["shares"]),
                      "icr_ttm": _div((ttm["pti"] or 0) + ttm["int_exp"], ttm["int_exp"])
                      if ttm["int_exp"] and ttm["int_exp"] > 0 and ttm["pti"] is not None else None,
                      "dol_ttm": _div(ttm["gp"], ttm["oi"]) if ttm["oi"] and ttm["oi"] > 0 else None,
                      "capex_dep": _div(-ttm["capex"], ttm["dep"]) if None not in (ttm["capex"], ttm["dep"]) else None})
            if r["ta"] and r["liab"] and r["_mcap"] and None not in (r["_wc"], r["_re"], ttm["pti"], ttm["rev"]):
                x = [r["_wc"] / r["ta"], r["_re"] / r["ta"], (ttm["pti"] + (ttm["int_exp"] or 0)) / r["ta"],
                     r["_mcap"] / r["liab"], ttm["rev"] / r["ta"]]
                r["z"] = 1.2 * x[0] + 1.4 * x[1] + 3.3 * x[2] + 0.6 * x[3] + 1.0 * x[4]
                r["z_x"] = [round(v, 4) for v in x]
        if i >= 4:
            y = rows[i - 4]
            r["rev_yoy"] = _div(r["rev"], y["rev"]) - 1 if _div(r["rev"], y["rev"]) is not None else None
            r["dio_yoy_d"] = r["dio"] - y["dio"] if None not in (r["dio"], y["dio"]) else None

    L = rows[-1]
    Y = rows[-5] if len(rows) >= 5 else None
    last4 = rows[-4:]

    # ── 杜邦驅動判讀（最新季 vs 去年同季）──
    def chg(k):
        return None if Y is None or L.get(k) is None or Y.get(k) is None else L[k] - Y[k]
    d_npm, d_at, d_em, d_roe = chg("npm"), chg("at"), chg("em"), chg("roe_ann")
    nonop_heavy = (L["pti"] or 0) > 0 and (L["nonop_share"] or 0) > 0.35
    core_neg_profit = L["oi"] is not None and L["oi"] <= 0 and (L["ni"] or 0) > 0
    if L["roe_ann"] is None:
        driver, quality = "資料不足", "N/A"
    elif L["roe_ann"] <= 0:
        driver, quality = "ROE 為負：稅後淨利率為負主導（虧損期），三因子拆解僅供參考", "LOSS"
    elif nonop_heavy or core_neg_profit:
        driver, quality = "主要由業外收益拉抬（本業營益率偏弱，需留意持續性）", "LOW"
    elif d_em is not None and Y and Y.get("em") and d_em / Y["em"] > 0.10 and (d_npm or 0) <= 0.005 and (d_at or 0) <= 0.02:
        driver, quality = "主要由財務槓桿（權益乘數上升）拉抬（需留意持續性）", "LOW"
    elif (d_npm or 0) > 0 and (d_at or 0) > 0 and (d_em is None or Y is None or not Y.get("em") or d_em / Y["em"] <= 0.05):
        driver, quality = "由本業淨利率與週轉率雙升驅動（高品質）", "HIGH"
    elif (d_npm or 0) > 0:
        driver, quality = "以淨利率改善為主要驅動", "MEDIUM"
    elif (d_at or 0) > 0:
        driver, quality = "以資產週轉率提升為主要驅動", "MEDIUM"
    else:
        driver, quality = "淨利率與週轉率同步下滑，ROE 動能轉弱", "LOW"
    if L["oi"] is None and quality == "HIGH":   # 無營業利益可驗證本業 → 不給高品質判定
        driver, quality = "淨利率與週轉率雙升（財報格式未提供營業利益，無法確認是否來自本業）", "MEDIUM"

    # ── 四維度評分（0~100）──
    sc_prof = _mean_score([_lin(L["opm"], -0.05, 0.10), _lin(L["npm"], -0.05, 0.10), _lin(L["roe_ann"], -0.05, 0.15),
                           _lin(abs(L["nonop_share"]) if L["nonop_share"] is not None else None, 1.0, 0.0),
                           _lin(L.get("ocf_ni_ttm"), 0.0, 1.2) if L.get("ocf_ni_ttm") is not None
                           else (60.0 if (L.get("ocf_ttm") or 0) > 0 else 0.0 if L.get("ocf_ttm") is not None else None)])
    sc_eff = _mean_score([_lin(L["ccc"], 150, 30), _lin(L["at"], 0.3, 1.5), _lin(L["fa_turn"], 0.5, 4.0),
                          _lin(L.get("dio_yoy_d"), 30, -10), None if L["oi"] is None else 0.0 if L["oi"] <= 0 else _lin(L.get("dol_ttm"), 8, 2)])
    sc_liq = _mean_score([_lin(L["current"], 0.8, 2.0), _lin(L["quick"], 0.5, 1.5), _lin(L["st_borrow_share"], 0.6, 0.1),
                          _lin(_div(_g(bs[dates[-1]], "CashAndCashEquivalents"), _g(bs[dates[-1]], "CurrentLiabilities")), 0.05, 0.5)])
    sc_sol = _mean_score([_lin(L["debt_ratio"], 0.75, 0.30), _lin(L.get("z"), 1.2, 3.5), _lin(L.get("icr_ttm"), 1.0, 10.0),
                          _lin(L["net_de"], 1.5, 0.0), _lin(L["ltf_ppe"], 0.8, 2.0)])
    fa_score = _mean_score([sc_prof, sc_eff, sc_liq, sc_sol])
    lvl = lambda v: None if v is None else "LOW" if v >= 65 else "MODERATE" if v >= 40 else "HIGH"  # noqa: E731
    z = L.get("z")
    z_zone = None if z is None else "SAFE" if z > 2.99 else "GREY" if z >= 1.81 else "DISTRESS"

    # ── Risk Factor 風險因子解析 ──
    pct_ = lambda v: "—" if v is None else f"{v * 100:.1f}%"  # noqa: E731
    rf: List[Dict[str, Any]] = []
    if nonop_heavy or core_neg_profit:
        rf.append(_risk("HIGH", "NONOP_DEPENDENCE", "業外一次性收益依賴風險",
                        [f"業外損益占稅前淨利 {'> 300%' if (L['nonop_share'] or 0) > 3 else pct_(L['nonop_share'])}", f"{L['q']} 營業利益 {_mn(L['oi'])} 百萬、稅後 {_mn(L['ni'])} 百萬"],
                        "本業尚未賺錢，獲利主要來自處分資產、投資收益或匯兌等業外項目，可持續性低。",
                        "以本業營業利益為準評估；扣除業外後重算本益比，部位減半或等待本業轉正。"))
    neg_oi = sum(1 for x in last4 if (x["oi"] or 0) < 0)
    if neg_oi >= 3:
        oi_txt = " / ".join("%s %sM" % (x["q"][2:], format((x["oi"] or 0) / 1e6, ",.0f")) for x in last4)
        rf.append(_risk("HIGH", "CORE_LOSS", "本業持續虧損（近 4 季 ≥ 3 季營業損失）",
                        [f"近 4 季營業利益：{oi_txt}"],
                        "營業利益長期為負代表產品價差或產能利用率不足以覆蓋固定成本，EPS 轉正可能仰賴業外。",
                        "EPS 拐點需以「營業利益轉正」再確認；未轉正前不宜重押。"))
    if L.get("ocf_ttm") is not None and L["ocf_ttm"] < 0:
        rf.append(_risk("HIGH", "OCF_NEGATIVE", "帳面獲利未轉化為實質現金流入",
                        [f"近四季累計營業現金流 {L['ocf_ttm'] / 1e6:,.0f} 百萬"],
                        "營業活動持續淨流出，獲利品質差，可能需舉債或增資支應營運。", "追蹤下一季 OCF 是否轉正；搭配負債比觀察。"))
    dsv = []
    if L.get("icr_ttm") is not None and L["icr_ttm"] < 2.5:
        dsv.append(f"利息保障倍數 {L['icr_ttm']:.2f}x < 2.5")
    if L["quick"] is not None and L["quick"] < 0.8:
        dsv.append(f"速動比率 {pct_(L['quick'])} < 80%")
    if z is not None and z < 1.81:
        dsv.append(f"Altman Z {math.floor(z * 100) / 100:.2f} < 1.81")
    if dsv:
        rf.append(_risk("HIGH", "DEBT_SERVICE", "短期償債壓力／高利率環境利息侵蝕風險", dsv,
                        "營運獲利不足以穩健支應利息或短期負債，利率上升或銀行緊縮時壓力放大。",
                        "優先選擇 ICR > 3、速動比 > 1 的同業；持有期間追蹤短借續借與增資公告。"))
    mod = []
    if L.get("dio_yoy_d") is not None and L["dio_yoy_d"] > 15:
        mod.append(f"DIO 較去年同期 +{L['dio_yoy_d']:.0f} 天（{L['dio']:.0f} 天）")
    if L.get("dol_ttm") is not None and L["dol_ttm"] > 3.5:
        mod.append(f"營運槓桿 DOL {'> 50' if L['dol_ttm'] > 50 else format(L['dol_ttm'], '.1f')}x > 3.5（營業利益占毛利比重低）")
    if mod:
        rf.append(_risk("MODERATE", "INVENTORY_DOL", "庫存去化偏慢／高固定成本營運槓桿風險", mod,
                        "存貨天數拉長可能面臨跌價損失；高營運槓桿使營收小幅下滑即大幅侵蝕營益。",
                        "留意下季存貨跌價提列與毛利率；以分批建倉降低單一季報衝擊。"))
    if L.get("rev_yoy") is not None and L["rev_yoy"] < -0.15:
        rf.append(_risk("MODERATE", "REVENUE_DECLINE", "營收動能轉弱",
                        [f"{L['q']} 營收 YoY {pct_(L['rev_yoy'])}"], "營收年減逾 15%，景氣或接單轉弱。", "搭配月營收追蹤，連兩月年減擴大則降低部位。"))
    if z_zone == "GREY":
        rf.append(_risk("MODERATE", "Z_GREY", "Altman Z 灰色地帶", [f"Z = {math.floor(z * 100) / 100:.2f}（1.81~2.99）"],
                        "財務體質中性偏弱，景氣下行時可能滑入警戒區。", "與同業比較負債結構；避免高槓桿加碼。"))
    if L["debt_ratio"] is not None and L["debt_ratio"] > 0.60:
        rf.append(_risk("MODERATE", "HIGH_LEVERAGE", "負債比偏高", [f"負債比 {pct_(L['debt_ratio'])} > 60%"],
                        "財務槓桿高，ROE 易被槓桿放大而非本業驅動。", "檢視淨負債權益比與利息保障倍數。"))
    if L["current"] is not None and L["current"] < 1.0:
        rf.append(_risk("MODERATE", "CURRENT_LT_1", "流動負債大於流動資產", [f"流動比率 {pct_(L['current'])} < 100%"],
                        "短期資金缺口需仰賴續借或營運現金流支應。", "追蹤短期借款變化與 OCF。"))
    if z is not None and z > 2.5 and (L.get("ocf_ttm") or 0) > 0 and (L["opm"] or 0) > 0:
        rf.append(_risk("STRENGTH", "BALANCE_INFLECTION", "資產負債表穩健＋本業實質拐點確認",
                        [f"Z {math.floor(z * 100) / 100:.2f} > 2.5", f"OCF TTM {L['ocf_ttm'] / 1e6:,.0f} 百萬 > 0", f"OPM {pct_(L['opm'])} > 0"],
                        "財務安全邊際充足且本業已實質獲利，價值修復的基本面支撐較強。", "可作為核心持股候選，依 RULE SPEC 正常建倉。"))
    if L.get("ocf_ni_ttm") is not None and L["ocf_ni_ttm"] > 1 and (L.get("fcf_ttm") or 0) > 0:
        rf.append(_risk("STRENGTH", "CASH_QUALITY", "獲利含金量高（現金流大於帳面獲利）",
                        [f"OCF/NI TTM {L['ocf_ni_ttm']:.2f}x", f"FCF TTM {L['fcf_ttm'] / 1e6:,.0f} 百萬"],
                        "營業現金流與自由現金流皆健康，獲利可信度高。", "—"))
    if L["net_de"] is not None and L["net_de"] < 0:
        rf.append(_risk("STRENGTH", "NET_CASH", "淨現金部位", [f"淨負債權益比 {pct_(L['net_de'])}"],
                        "現金大於有息負債，抗景氣循環能力佳。", "—"))
    order = {"HIGH": 0, "MODERATE": 1, "STRENGTH": 2}
    rf.sort(key=lambda x: order[x["severity"]])

    # ── TWSE OpenAPI 核對 ──
    tw = twse_fin.get(code)
    check: Dict[str, Any] = {"available": bool(tw)}
    if tw:
        pe = {"Q1": "03-31", "Q2": "06-30", "Q3": "09-30", "Q4": "12-31"}[tw["period"][-2:]]
        pdate = f"{tw['period'][:4]}-{pe}"
        check["period"] = tw["period"]
        check["bvps_ref"] = tw["bvps_ref"]
        if pdate in bs and tw["total_assets"]:
            fa_ta = _g(bs[pdate], "TotalAssets")
            check["assets_diff_pct"] = round((fa_ta / tw["total_assets"] - 1) * 100, 3) if fa_ta else None
        ytd = [inc[x].get("EquityAttributableToOwnersOfParent") for x in dates if x[:4] == pdate[:4] and x <= pdate]
        if tw["ni_parent_ytd"] is not None and ytd and None not in ytd:
            check["ni_ytd_twse"] = tw["ni_parent_ytd"]
            check["ni_ytd_finmind"] = sum(ytd)
            check["ni_diff_pct"] = round((sum(ytd) / tw["ni_parent_ytd"] - 1) * 100, 3) if tw["ni_parent_ytd"] else None
        check["match"] = all(abs(check.get(k) or 0) < 0.5 for k in ("assets_diff_pct", "ni_diff_pct"))

    keep = ("q", "date", "rev", "gp", "oi", "nonop", "pti", "ni", "eps", "eps_est", "gpm", "opm", "ptm", "npm", "nonop_share",
            "roe_ann", "at", "em", "dio", "dso", "dpo", "ccc", "inv_turn", "fa_turn", "debt_ratio", "ltf_ppe", "current", "quick",
            "net_de", "st_borrow_share", "ocf", "capex", "fcf", "bvps", "ocf_ttm", "fcf_ttm", "ocf_ni_ttm", "fcfps_ttm",
            "icr_ttm", "dol_ttm", "capex_dep", "z", "rev_yoy", "dio_yoy_d")
    rnd = lambda v: round(v, 4) if isinstance(v, float) and abs(v) < 1e5 else (round(v) if isinstance(v, float) else v)  # noqa: E731
    out_rows = [{k: rnd(r.get(k)) for k in keep} for r in rows[-8:]]
    notes = []
    if L["oi"] is None:
        notes.append("此公司財報採非一般業格式（如控股／投資型或含金融子公司），FinMind 未提供毛利與營業利益，毛利率、營業利益率、業外占比、存貨週轉、營運槓桿不計算；Altman Z 製造業版對此類合併報表適用性低，僅供參考。")
    if L["eps_est"]:
        notes.append(f"{L['q']} EPS 尚未公布，以歸屬母公司淨利 ÷ 股數推算（{L['eps']:+.2f}）。")
    if L.get("z") is None:
        notes.append("Altman Z 需完整四季損益與季末市值，資料不足時不計算。")
    return {"status": "OK", "source": "FinMind 季報（損益為單季、資產負債為季末、現金流量由年度累計拆成單季）＋ TWSE OpenAPI 最新一期核對",
            "latest": L["q"], "latest_date": L["date"], "quarters": out_rows,
            "dupont": {"npm": rnd(L["npm"]), "at": rnd(L["at"]), "em": rnd(L["em"]), "roe": rnd(L["roe_ann"]),
                       "yoy_q": Y["q"] if Y else None, "d_npm": rnd(d_npm), "d_at": rnd(d_at), "d_em": rnd(d_em), "d_roe": rnd(d_roe),
                       "driver": driver, "quality": quality},
            "z": {"value": rnd(z), "zone": z_zone, "x": L.get("z_x")},
            "scores": {"profitability": sc_prof, "efficiency": sc_eff, "liquidity": sc_liq, "solvency": sc_sol},
            "fa_score": fa_score, "operating_risk": lvl(sc_eff), "financial_risk": lvl(_mean_score([sc_liq, sc_sol])),
            "risk_factors": rf, "risk_counts": {k: sum(1 for x in rf if x["severity"] == k) for k in order},
            "twse_check": check, "notes": notes}


# ──────────────────────────────────────────────────────────────────────────────
# 大戶籌碼吸籌偵測（Smart-Money & Chip Flow Analyzer）
# ──────────────────────────────────────────────────────────────────────────────
def _tdcc_parse(text: str) -> Tuple[Optional[str], Dict[str, List[float]]]:
    """TDCC 集保戶股權分散表 CSV → (資料日 ISO, {代號: [千張大戶%, 散戶<50張%, 千張大戶人數, 總人數]})。"""
    rows = csv.reader(io.StringIO(text.lstrip("﻿")))
    next(rows, None)
    acc: Dict[str, Dict[int, Tuple[float, float]]] = {}
    date = None
    for r in rows:
        if len(r) < 6:
            continue
        date = date or r[0].strip()
        try:
            lvl = int(r[2])
        except ValueError:
            continue
        acc.setdefault(r[1].strip(), {})[lvl] = (num(r[3]) or 0.0, num(r[5]) or 0.0)
    out: Dict[str, List[float]] = {}
    for code, lv in acc.items():
        if 15 not in lv:
            continue
        out[code] = [lv[15][1], round(sum(lv.get(k, (0, 0))[1] for k in range(1, 9)), 2), lv[15][0], lv.get(17, (0, 0))[0]]
    iso = f"{date[:4]}-{date[4:6]}-{date[6:8]}" if date and len(date) == 8 else None
    return iso, out


class HoldingHistory:
    """集保週資料：TDCC 開放資料僅提供最新一週 → 每次執行把全市場快照存到 cache/tdcc，逐週累積歷史。"""

    def __init__(self, http: Http, cache_dir: Path):
        self.dir = cache_dir
        self.dir.mkdir(parents=True, exist_ok=True)
        cutoff = time.time() - CHIP_TH["tdcc_keep_days"] * 86400
        for f in self.dir.glob("tdcc_*.json"):
            if f.stat().st_mtime < cutoff:
                f.unlink(missing_ok=True)
        try:
            iso, snap = _tdcc_parse(http.get_text(TDCC_HOLDING, timeout=60))
            if iso and snap:
                path = self.dir / f"tdcc_{iso.replace('-', '')}.json"
                if not path.exists():
                    path.write_text(json.dumps(snap, separators=(",", ":")), "utf-8")
                log.info("TDCC holding distribution %s: %d securities", iso, len(snap))
        except Exception as e:  # noqa: BLE001
            log.warning("TDCC open data unavailable: %s", e)
        self.snaps: Dict[str, Dict[str, List[float]]] = {}
        for f in sorted(self.dir.glob("tdcc_*.json")):
            d = f.stem.split("_")[1]
            try:
                self.snaps[f"{d[:4]}-{d[4:6]}-{d[6:]}"] = json.loads(f.read_text("utf-8"))
            except json.JSONDecodeError:
                continue
        log.info("TDCC history: %d weekly snapshot(s) %s", len(self.snaps), list(self.snaps)[-3:])

    def weeks(self, code: str) -> List[Dict[str, Any]]:
        return [{"date": d, "big_pct": v[0], "retail_pct": v[1], "big_holders": int(v[2]), "holders": int(v[3])}
                for d, s in sorted(self.snaps.items()) if (v := s.get(code))]


def _finmind_holding(fm: "FinMind", code: str, start: str, day_key: str) -> List[Dict[str, Any]]:
    """FinMind TaiwanStockHoldingSharesPer（贊助等級才開放；免費等級回 400 時回傳空串列）。欄位解析為容錯寫法。"""
    try:
        rows = fm.data("TaiwanStockHoldingSharesPer", code, start, day_key)
    except Exception as e:  # noqa: BLE001
        log.debug("FinMind holding unavailable %s: %s", code, e)
        return []
    by: Dict[str, Dict[str, float]] = {}
    for r in rows:
        lvl = str(r.get("HoldingSharesLevel", "")).replace(" ", "").lower()
        pct = num(r.get("percent"))
        if pct is None:
            continue
        d = by.setdefault(r["date"], {"big": 0.0, "retail": 0.0, "big_people": 0.0})
        nums = [int(x) for x in re.findall(r"\d+", lvl.replace(",", ""))]
        if "morethan" in lvl or (nums and nums[0] >= 1000001):
            d["big"] += pct
            d["big_people"] += num(r.get("people")) or 0
        elif nums and max(nums) <= 50000:
            d["retail"] += pct
    return [{"date": k, "big_pct": round(v["big"], 2), "retail_pct": round(v["retail"], 2),
             "big_holders": int(v["big_people"]), "holders": None} for k, v in sorted(by.items()) if v["big"] > 0]


def build_chip(s: Dict[str, Any], hold: HoldingHistory, fm: "FinMind", day_key: str,
               stock: Optional[Dict[str, Any]], use_finmind_holding: bool) -> Dict[str, Any]:
    code = s["code"]
    today = now_tpe().date()
    weeks: List[Dict[str, Any]] = []
    src = "TDCC 集保結算所開放資料（每週；本機逐週累積）"
    if use_finmind_holding:
        weeks = _finmind_holding(fm, code, (today - dt.timedelta(days=70)).isoformat(), day_key)
        if weeks:
            src = "FinMind TaiwanStockHoldingSharesPer（贊助等級）"
    if not weeks:
        weeks = hold.weeks(code)
    weeks = weeks[-8:]
    d4 = d4r = d1 = None
    if weeks:
        L = weeks[-1]
        ld = dt.date.fromisoformat(L["date"])
        prior = [w for w in weeks[:-1] if 24 <= (ld - dt.date.fromisoformat(w["date"])).days <= 32]
        if prior:
            b = min(prior, key=lambda w: abs((ld - dt.date.fromisoformat(w["date"])).days - 28))
            d4, d4r = round(L["big_pct"] - b["big_pct"], 2), round(L["retail_pct"] - b["retail_pct"], 2)
        if len(weeks) >= 2:
            d1 = round(L["big_pct"] - weeks[-2]["big_pct"], 2)
    # 融資（FinMind 免費資料，單位：張）
    margin: Dict[str, Any] = {"dates": [], "balance": []}
    try:
        rows = fm.data("TaiwanStockMarginPurchaseShortSale", code, (today - dt.timedelta(days=80)).isoformat(), day_key)
        rows = [r for r in rows if num(r.get("MarginPurchaseTodayBalance")) is not None][-41:]
        bal = [num(r["MarginPurchaseTodayBalance"]) for r in rows]
        lim = num(rows[-1].get("MarginPurchaseLimit")) if rows else None
        margin = {"dates": [r["date"] for r in rows], "balance": [int(x) for x in bal],
                  "limit": int(lim) if lim else None,
                  "usage_pct": round(bal[-1] / lim * 100, 2) if rows and lim else None,
                  "d20": int(bal[-1] - bal[-21]) if len(bal) > 20 else None,
                  "d20_pct": round((bal[-1] / bal[-21] - 1) * 100, 1) if len(bal) > 20 and bal[-21] else None}
    except Exception as e:  # noqa: BLE001
        log.warning("Margin data failed %s: %s", code, e)
    # 股價 60 日位置（0＝區間低點、1＝高點）
    pos = None
    px = (stock or {}).get("close", [])[-60:]
    if px:
        lo, hi = min(px), max(px)
        pos = round((s["close"] - lo) / (hi - lo), 3) if hi > lo else 0.5
    T = CHIP_TH
    if d4 is None:
        need = 5 - len(weeks)
        sig, why = "N/A", f"集保週資料累積中（已有 {len(weeks)} 週，4 週增減需約 5 週快照；再約 {max(need, 1)} 週後啟用）"
    elif d4 >= T["accum_big"] and (d4r or 0) < 0:
        sig, why = "ACCUMULATION", f"近 4 週千張大戶 {d4:+.2f}pp、散戶 {d4r:+.2f}pp → 大戶吸籌中"
    elif d4 <= T["distrib_big"] and (d1 is None or d1 < 0):
        sig, why = "DISTRIBUTION", f"近 4 週千張大戶 {d4:+.2f}pp 且最新一週仍減碼 → 大戶派發警示"
    else:
        sig, why = "NEUTRAL", f"近 4 週千張大戶 {d4:+.2f}pp、散戶 {d4r:+.2f}pp → 籌碼持平"
    d20, usage = margin.get("d20"), margin.get("usage_pct")
    mstate = None if d20 is None else "WASH" if d20 < 0 else "BUILDUP" if d20 > 0 else "FLAT"
    parts = [why]
    if d20 is not None:
        pct_txt = f"（{margin['d20_pct']:+.1f}%）" if margin.get("d20_pct") is not None else ""
        use_txt = f"、使用率 {usage:.2f}%" if usage is not None else ""
        parts.append(f"融資近 20 日 {d20:+,} 張{pct_txt}{use_txt}"
                     + ("，融資清洗中" if mstate == "WASH" else "，融資增加" if mstate == "BUILDUP" else ""))
    if pos is not None:
        parts.append(f"股價位於 60 日區間 {pos:.0%} 位置")
    return {"source": src, "weeks": weeks, "weeks_available": len(weeks),
            "latest": weeks[-1] if weeks else None, "d4w_big": d4, "d4w_retail": d4r, "d1w_big": d1,
            "signal": sig, "signal_zh": {"ACCUMULATION": "大戶吸籌中", "DISTRIBUTION": "大戶派發警示",
                                         "NEUTRAL": "籌碼持平", "N/A": "資料累積中"}[sig],
            "margin": margin, "margin_state": mstate, "price_pos_60d": pos, "thresholds": T,
            "commentary": "；".join(parts) + "。"}


def chip_risk_factors(chip: Dict[str, Any]) -> List[Dict[str, Any]]:
    out = []
    m, T = chip["margin"], CHIP_TH
    low = chip["price_pos_60d"] is not None and chip["price_pos_60d"] <= T["low_pos"]
    if low and chip["margin_state"] == "WASH" and (chip["d4w_big"] or 0) > 0:
        out.append(_risk("STRENGTH", "CHIP_ACCUM_WASH", "大戶吸籌＋融資清洗（籌碼高度安定）",
                         [f"千張大戶 4 週 {chip['d4w_big']:+.2f}pp", f"融資 20 日 {m['d20']:+,} 張",
                          f"股價位於 60 日區間 {chip['price_pos_60d']:.0%}"],
                         "低檔融資浮額退場、大戶同步承接，籌碼由散戶轉往大戶，安定度高。", "可作為建倉時機的加分條件。"))
    if (m.get("usage_pct") or 0) > T["margin_usage_high"] and (m.get("d20") or 0) > 0:
        out.append(_risk("MODERATE", "MARGIN_HEAVY", "融資浮額偏高風險",
                         [f"融資使用率 {m['usage_pct']:.1f}% > {T['margin_usage_high']:.0f}%", f"融資 20 日 +{m['d20']:,} 張"],
                         "融資籌碼持續堆積，股價回檔時易出現斷頭賣壓。", "避免追價；留意融資維持率與斷頭價位。"))
    if chip["signal"] == "DISTRIBUTION":
        out.append(_risk("MODERATE", "CHIP_DISTRIBUTION", "大戶派發警示",
                         [f"千張大戶 4 週 {chip['d4w_big']:+.2f}pp"], "大戶持股連續下降，籌碼由大戶流向散戶。",
                         "暫緩加碼，觀察大戶持股是否止穩。"))
    return out


# ──────────────────────────────────────────────────────────────────────────────
# 主流程
# ──────────────────────────────────────────────────────────────────────────────
def fetch_market(http: Http, markets: List[str]) -> Tuple[Dict[str, Dict[str, Any]], Dict[str, Optional[str]], List[str]]:
    universe: Dict[str, Dict[str, Any]] = {}
    dates: Dict[str, Optional[str]] = {}
    warnings: List[str] = []
    loaders = {"twse": ("TWSE", load_twse), "tpex": ("TPEx", load_tpex)}
    today = now_tpe().date()
    for key in markets:
        label, fn = loaders[key]
        data: Dict[str, Dict[str, Any]] = {}
        d: Optional[str] = None
        try:
            data, d = fn(http)
            log.info("%-5s OpenAPI  %4d securities (data date %s)", label, len(data), d)
        except Exception as e:  # noqa: BLE001
            warnings.append(f"{label} OpenAPI fetch failed: {e}")
            log.error("%s OpenAPI fetch failed: %s", label, e)
        if key == "twse" and d != today.isoformat():
            # OpenAPI 落後 → 由今天往回找最近一個有盤後資料的交易日（週末／假日執行時回到上個交易日）
            for back in range(0, 7):
                day = today - dt.timedelta(days=back)
                if day.weekday() >= 5 or (d and day.isoformat() <= d):
                    continue
                try:
                    rwd, rd = load_twse_rwd(http, day)
                except Exception as e:  # noqa: BLE001
                    log.warning("TWSE website fallback failed (%s): %s", day, e)
                    break
                if rwd:
                    data, d = rwd, rd
                    log.info("%-5s website  %4d securities (data date %s) ← newer than OpenAPI", label, len(rwd), rd)
                    break
                log.info("%-5s website  no data for %s", label, day)
        if data:
            universe.update(data)
            dates[label] = d
    return universe, dates, warnings


def wait_for_fresh(http: Http, markets: List[str], wait_minutes: int):
    """15:10 執行時交易所資料可能尚未更新 → 每 5 分鐘重試直到資料日期 = 今天或逾時。"""
    deadline = time.time() + wait_minutes * 60
    today = now_tpe().date().isoformat()
    while True:
        universe, dates, warnings = fetch_market(http, markets)
        fresh = bool(dates) and all(d == today for d in dates.values())
        if fresh or time.time() >= deadline:
            return universe, dates, warnings, not fresh
        log.info("Data not yet updated for %s (got %s). Retrying in 5 min...", today, dates)
        time.sleep(300)


def run(args: argparse.Namespace) -> int:
    p = dict(DEFAULTS)
    p.update({"pb_max": args.pb_max, "vol_min": args.vol_min, "vol_max": args.vol_max})
    http = Http()
    out_dir = Path(args.out_dir).expanduser().resolve()
    out_dir.mkdir(parents=True, exist_ok=True)
    markets = [m.strip().lower() for m in args.markets.split(",") if m.strip()]

    t0 = time.time()
    log.info("═" * 72)
    log.info("DVF-PRO SCANNER  start %s  markets=%s", now_tpe().strftime("%Y-%m-%d %H:%M:%S"), markets)

    if args.wait_fresh > 0:
        universe, mdates, warnings, stale = wait_for_fresh(http, markets, args.wait_fresh)
    else:
        universe, mdates, warnings = fetch_market(http, markets)
        today = now_tpe().date().isoformat()
        stale = not mdates or any(d != today for d in mdates.values())
    if not universe:
        log.error("No market data loaded. Existing candidates.json left untouched.")
        return 2
    data_date = max(d for d in mdates.values() if d) if any(mdates.values()) else None
    if stale:
        warnings.append(f"Exchange data date {mdates} differs from today {now_tpe().date()} (holiday or not yet updated).")

    # ── 全市場統計 ──
    stocks = [s for s in universe.values()
              if STOCK_CODE_RE.match(s["code"]) and s["pb"] is not None and s["close"] and s["close"] > 0]
    by_market: Dict[str, Dict[str, int]] = {}
    for s in stocks:
        m = by_market.setdefault(s["market"], {"scanned": 0, "undervalued": 0})
        m["scanned"] += 1
        if 0 < s["pb"] < p["pb_max"]:
            m["undervalued"] += 1

    # ── 第一道濾網：P/B ──
    stage1 = [s for s in stocks if 0 < s["pb"] < p["pb_max"]]
    # ── 第二道濾網：成交張數 ──
    stage2 = []
    for s in stage1:
        lots = (s["volume_shares"] or 0) / 1000.0
        if lots >= p["vol_min"]:
            s["volume_lots"] = round(lots)
            stage2.append(s)
    log.info("Universe %d → P/B<%.2f: %d → Volume %d~%d 張: %d",
             len(stocks), p["pb_max"], len(stage1), p["vol_min"], p["vol_max"], len(stage2))

    # ── 宏觀商品期貨與產業別 ──
    macro_list: List[Dict[str, Any]] = []
    industries: Dict[str, str] = {}
    if not args.no_macro:
        macro_list = fetch_commodities(http)
        for q in macro_list:
            if q["error"]:
                warnings.append(f"Commodity {q['symbol']} unavailable: {q['error']}")
            elif q.get("proxy"):
                warnings.append(f"Commodity {q['symbol']} uses proxy {q['source_symbol']}.")
    if not (args.no_macro and args.all_sectors):
        industries = load_industries(http)
    fdata: Dict[str, Dict[str, Any]] = {}
    if not args.no_macro:
        fdata = load_factor_series(http, macro_list, out_dir / "cache" / "futures", warnings)

    # ── 產業純化：景氣循環／原物料白名單 ──
    sector_excluded: List[Dict[str, Any]] = []
    if args.all_sectors:
        stage2c = stage2
    elif not industries:
        stage2c = stage2
        warnings.append("Industry map unavailable — cyclical sector filter skipped this run.")
    else:
        stage2c = []
        for s in stage2:
            ind = industries.get(s["code"])
            if ind in CYCLICAL_WHITELIST:
                stage2c.append(s)
                continue
            why = SECTOR_BLACKLIST.get(ind or "") or f"非景氣循環（{INDUSTRY_NAMES.get(ind or '', '未知產業')}）"
            sector_excluded.append({"code": s["code"], "name": s["name"], "industry_code": ind,
                                    "industry": INDUSTRY_NAMES.get(ind or "", "未知"), "reason": why})
            log.info("SECTOR skip %s %-6s [%s] %s", s["code"], s["name"], INDUSTRY_NAMES.get(ind or "", ind), why)
    excluded_by: Dict[str, int] = {}
    for x in sector_excluded:
        excluded_by[x["industry"]] = excluded_by.get(x["industry"], 0) + 1
    log.info("Sector filter: %d → %d (已過濾非景氣循環／建設股 %d 檔)", len(stage2), len(stage2c), len(sector_excluded))

    peer_cache = PeerCache(http)

    # ── 第三道濾網：基本面拐點 ──
    fm = FinMind(http, args.token, out_dir / "cache" / "finmind", args.sleep)
    today_key = now_tpe().strftime("%Y%m%d")
    eps_start = (now_tpe().date() - dt.timedelta(days=FA_DAYS)).isoformat()
    price_start = (now_tpe().date() - dt.timedelta(days=240)).isoformat()   # 約 160 個交易日：MA60＋MACD 暖機
    candidates: List[Dict[str, Any]] = []
    checked = unverified = 0
    rate_limited = False

    def enrich(s: Dict[str, Any], ep: Dict[str, Any]) -> Dict[str, Any]:
        """通過濾網（或觀察名單）標的：量能、估值、期貨連動、同業、合理價、財報 FA。"""
        nonlocal rate_limited
        # 量能歷史（只對命中標的抓取，節省 API 額度）
        hist: List[Dict[str, Any]] = []
        if not args.no_history:
            try:
                rows = fm.data("TaiwanStockPrice", s["code"], price_start, (s["data_date"] or today_key).replace("-", ""))
                hist = [{"d": r["date"], "c": num(r.get("close")), "v": round((num(r.get("Trading_Volume")) or 0) / 1000),
                         "h": num(r.get("max")), "l": num(r.get("min"))}
                        for r in rows if num(r.get("close"))]
            except RateLimited:
                rate_limited = True
                warnings.append("FinMind rate limit hit while fetching price history.")
            except Exception as e:  # noqa: BLE001
                log.warning("Price history failed %s: %s", s["code"], e)
        sd = s["data_date"] or data_date
        if sd:  # FinMind 可能比交易所 OpenAPI 新或舊 → 以該股報價日為準對齊
            hist = [h for h in hist if h["d"] < sd]
            hist.append({"d": sd, "c": s["close"], "v": s["volume_lots"], "h": s.get("high"), "l": s.get("low")})
        tech = build_tech([dict(h) for h in hist])
        hist = hist[-60:]
        prior = [h["v"] for h in hist[:-1]]  # 均量不含當日

        c = {
            "code": s["code"], "name": s["name"], "market": s["market"],
            "close": s["close"], "change": s["change"],
            "change_pct": r2((s["change"] / (s["close"] - s["change"]) * 100)
                             if s["change"] is not None and s["close"] != s["change"] else None),
            "open": s["open"], "high": s["high"], "low": s["low"],
            "pb": s["pb"], "pe": s["pe"], "dividend_yield": s["dividend_yield"],
            "volume_lots": s["volume_lots"],
            "trade_value": s["trade_value"],
            "daily_buy_cap_lots": max(1, math.floor(s["volume_lots"] * 0.15)),
        }
        c.update(derive_metrics(s, p))
        c.update(volume_compression(s["volume_lots"], prior, p["vol_min"], p["vol_max"]))
        c["tech_metrics"] = tech
        c.update({
            "eps_signal": ep.get("signal"),
            "eps_latest": ep.get("eps_latest"),
            "eps_period": ep.get("eps_period"),
            "eps_yoy_base": ep.get("eps_yoy_base"),
            "eps_yoy_period": ep.get("eps_yoy_period"),
            "eps_growth_pct": ep.get("eps_growth_pct"),
            "eps_history": ep.get("history", []),
            "history": {"dates": [h["d"] for h in hist], "close": [h["c"] for h in hist],
                        "volume": [h["v"] for h in hist]},
        })
        if not args.no_macro:
            stock_ser, stock_src = fetch_stock_series(http, s, hist)
            link, fmodel, tseries = build_factor_model(s, industries.get(s["code"]), stock_ser, fdata, stock_src)
            peer, ts_peers = build_peer_analysis(s, industries.get(s["code"]), stock_ser, peer_cache,
                                                 lambda code: (universe.get(code) or {}).get("pb"))
            tseries["peers"] = ts_peers
            c.update({"industry_code": link["industry_code"], "industry": link["industry"],
                      "commodity_linkage": link, "factor_model": fmodel, "timeseries": tseries, "peer_analysis": peer})
            c["fair_value"] = build_fair_value(c, peer)
        fa_reason = None
        try:
            c["fundamentals"] = build_fundamentals(s, fm, today_key, eps_start,
                                                   stock_ser if not args.no_macro else None, twse_fin)
            if c["fundamentals"] is None:
                fa_reason = "FinMind 季報不足 2 季（新上市、財報格式不支援或尚未公布），無法進行杜邦與排雷分析。"
        except RateLimited:
            rate_limited = True
            warnings.append("FinMind rate limit hit while fetching statements.")
            fa_reason = "FinMind API 額度已用完，本次未取得財報；額度恢復後重新掃描即可。"
        except Exception as e:  # noqa: BLE001
            log.warning("FA failed %s: %s", s["code"], e, exc_info=True)
            fa_reason = f"財報分析計算失敗（{type(e).__name__}: {e}），詳見 logs/scanner.log。"
        if fa_reason:
            c["fundamentals"] = fa_placeholder(fa_reason)
        try:
            chip = build_chip(s, holding, fm, today_key, stock_ser if not args.no_macro else None, bool(args.token))
            c["chip"] = chip
            fa = c.get("fundamentals")
            if fa:
                fa["risk_factors"] += chip_risk_factors(chip)
                order = {"HIGH": 0, "MODERATE": 1, "STRENGTH": 2}
                fa["risk_factors"].sort(key=lambda x: order[x["severity"]])
                fa["risk_counts"] = {k: sum(1 for x in fa["risk_factors"] if x["severity"] == k) for k in order}
        except Exception as e:  # noqa: BLE001
            log.warning("Chip analysis failed %s: %s", s["code"], e)
        c["fa_summary"] = fa_summary(c["fundamentals"])
        c["eps_estimated"] = bool(ep.get("eps_estimated"))
        return c



    twse_fin = load_twse_fin(http) if not args.skip_fundamentals else {}
    holding = HoldingHistory(http, out_dir / "cache" / "tdcc")

    for i, s in enumerate(sorted(stage2c, key=lambda x: x["pb"]), 1):
        if args.skip_fundamentals:
            ep = {"pass": True, "signal": "UNVERIFIED", "history": []}
        elif rate_limited:
            unverified += 1
            continue
        else:
            try:
                ep = eps_signal(fm.data("TaiwanStockFinancialStatements", s["code"], eps_start, today_key),
                                p["eps_growth_min"])
                checked += 1
            except RateLimited as e:
                rate_limited = True
                unverified += 1
                warnings.append(f"FinMind rate limit hit after {fm.calls} calls — set FINMIND_TOKEN. ({e})")
                log.error("FinMind rate limited: remaining %d stocks unverified", len(stage2c) - i + 1)
                continue
            except Exception as e:  # noqa: BLE001
                unverified += 1
                log.warning("EPS fetch failed %s: %s", s["code"], e)
                continue
        mark = "PASS" if ep["pass"] else "fail"
        log.info("[%3d/%3d] %s %-6s P/B %.2f  %4d張  EPS %s → %s %s", i, len(stage2c), s["code"], s["name"],
                 s["pb"], s["volume_lots"], ep.get("eps_latest"), mark, ep.get("signal") or ep.get("reason"))
        if not ep["pass"]:
            continue

        candidates.append(enrich(s, ep))

    # ── 自選股強制分析（custom_watchlist.json ＋ --analyze）：跳過四道濾網 ──
    custom_codes = list(dict.fromkeys(args.custom_codes + (args.analyze or [])))
    custom_errors: List[Dict[str, str]] = []
    by_code = {c["code"]: c for c in candidates}
    for code in custom_codes:
        if code in by_code:            # 本身已通過濾網 → 保留 SCREEN 身分，只標記為自選
            by_code[code]["custom"] = True
            continue
        s = universe.get(code)
        if not s or not s.get("close"):
            custom_errors.append({"code": code, "error": "查無最新收盤價或 P/B（代號錯誤、非上市櫃普通股或今日無成交）"})
            log.warning("CUSTOM %s: no quote", code)
            continue
        if not (s.get("pb") or 0) > 0:
            custom_errors.append({"code": code, "name": s.get("name"), "error": f"P/B 無效（{s.get('pb')}，可能淨值為負），無法估值"})
            log.warning("CUSTOM %s: invalid P/B", code)
            continue
        s["volume_lots"] = round((s["volume_shares"] or 0) / 1000)
        failed, why = [], []
        if not s["pb"] < p["pb_max"]:
            failed.append("P/B")
            why.append(f"P/B {s['pb']:.2f} ≥ {p['pb_max']}")
        if not (s["volume_lots"] >= p["vol_min"]):
            failed.append("成交量")
            why.append(f"成交 {s['volume_lots']:,} 張不在 {p['vol_min']:.0f}~{p['vol_max']:.0f}")
        if industries and industries.get(code) not in CYCLICAL_WHITELIST:
            failed.append("產業白名單")
            why.append(f"非景氣循環產業（{INDUSTRY_NAMES.get(industries.get(code) or '', '未知')}）")
        try:
            ep = eps_signal(fm.data("TaiwanStockFinancialStatements", code, eps_start, today_key), p["eps_growth_min"])
        except Exception as e:  # noqa: BLE001
            log.warning("CUSTOM %s EPS fetch failed: %s", code, e)
            ep = {"pass": False, "reason": "EPS_UNAVAILABLE", "history": []}
        if not ep["pass"]:
            failed.append("最新季EPS")
            est = "（推算）" if ep.get("eps_estimated") else ""
            why.append(f"最新單季 EPS {ep.get('eps_period') or '—'} = {ep.get('eps_latest')}{est}（{ep.get('reason')}）")
        try:
            c = enrich(s, ep)
        except Exception as e:  # noqa: BLE001
            custom_errors.append({"code": code, "name": s.get("name"), "error": f"分析失敗：{e}"})
            log.warning("CUSTOM %s enrich failed: %s", code, e)
            continue
        c.update({"source": "CUSTOM", "custom": True, "watch": True, "failed_filters": failed,
                  "note": "自選強制分析（未通過：" + ("、".join(failed) or "無") + "）" + ("：" + "；".join(why) if why else "")})
        if not ep["pass"]:
            c["eps_signal"] = "FAIL"
        log.info("CUSTOM %s %s → %s", code, s["name"], c["note"])
        candidates.append(c)
    for c in candidates:
        c.setdefault("source", "SCREEN")

    # ── 主力分點鎖碼（broker_scanner.py）：連續 ≥3 日前 5 大買超分點 > 成交量 15% ──
    broker_summary: Optional[Dict[str, Any]] = None
    if not args.no_broker:
        try:
            sys.path.insert(0, str(BASE_DIR))
            import broker_scanner  # noqa: E402
            broker_summary = broker_scanner.annotate(candidates, BASE_DIR, args.token or "")
        except Exception as e:  # noqa: BLE001
            warnings.append(f"broker_scanner failed: {e}")
            log.warning("broker_scanner failed: %s", e)

    candidates.sort(key=lambda c: (c["conviction"] != "HIGH CONVICTION", -(c["risk_reward_ratio"] or 0), -c["vcs"]))

    result = {
        "schema": "dvf-pro/1",
        "generated_at": now_tpe().isoformat(timespec="seconds"),
        "data_date": data_date,
        "market_dates": mdates,
        "data_stale": stale,
        "params": p,
        "total_scanned": len(stocks),
        "undervalued_market_count": len(stage1),
        "undervalued_ratio": r2(len(stage1) / len(stocks), 4) if stocks else None,
        "by_market": by_market,
        "funnel": {
            "universe": len(stocks),
            "pb_pass": len(stage1),
            "volume_pass": len(stage2),
            "sector_filter": not args.all_sectors and bool(industries),
            "sector_pass": len(stage2c),
            "sector_excluded": len(sector_excluded),
            "sector_excluded_by": excluded_by,
            "fundamental_checked": checked,
            "fundamental_unverified": unverified,
            "fundamental_pass": sum(1 for c in candidates if not c.get("watch")),
            "custom": sum(1 for c in candidates if c.get("source") == "CUSTOM"),
            "high_conviction": sum(1 for c in candidates if c["conviction"] == "HIGH CONVICTION" and not c.get("watch")),
        },
        "finmind_calls": fm.calls,
        "elapsed_sec": round(time.time() - t0, 1),
        "warnings": warnings,
        "custom_watchlist": args.custom_codes,
        "custom_analyze": args.analyze or [],
        "custom_errors": custom_errors,
        "broker_summary": broker_summary,
        "sector_whitelist": CYCLICAL_WHITELIST,
        "sector_excluded_list": sector_excluded,
        "macro_commodities": [{k: v for k, v in q.items() if k != "_series"} for q in macro_list],
        "china_futures": [{"symbol": k, "name": FACTORS[k]["name"], "short": FACTORS[k]["short"],
                           "unit": FACTORS[k]["unit"], **{x: v.get(x) for x in ("last", "as_of", "chg_5d_pct",
                                                                               "chg_20d_pct", "chg_60d_pct", "error")}}
                          for k, v in fdata.items() if FACTORS[k]["src"] == "sina"],
        "macro_thresholds": MACRO_TH,
        "candidates": candidates,
    }
    # ── 市場情報（market_crawler.py）：國際財經／期貨頭條、台股新聞、證交所重大訊息 ──
    if not args.no_news:
        try:
            sys.path.insert(0, str(BASE_DIR))
            import market_crawler  # noqa: E402
            news = market_crawler.fetch_market_intelligence([{"code": c["code"], "name": c["name"]} for c in candidates])
            result.update({"live_news": news["items"], "news_updated_at": news["updated_at"],
                           "news_meta": {k: news[k] for k in ("errors", "sources", "queries")}})
            for e in news["errors"]:
                warnings.append(f"News source failed: {e}")
        except Exception as e:  # noqa: BLE001
            warnings.append(f"market_crawler failed: {e}")
            log.warning("market_crawler failed: %s", e)

    # 保留上一份 AI 覆盤（daily_briefing.py 稍後會覆寫）；資料日不同時標記 stale，網頁仍可查看
    try:
        prev = json.loads((out_dir / "candidates.json").read_text("utf-8")).get("daily_briefing")
        if prev:
            prev["stale"] = prev.get("data_date") != result["data_date"]
            result["daily_briefing"] = prev
    except (OSError, json.JSONDecodeError):
        pass
    write_outputs(out_dir, result)
    log.info("RESULT %d candidates (%d HIGH CONVICTION) · FinMind calls %d · %.1fs",
             len(candidates), result["funnel"]["high_conviction"], fm.calls, result["elapsed_sec"])
    for c in candidates:
        log.info("  %s %-6s %-5s close %7.2f  P/B %.2f  BV %7.2f  T.85 %7.2f (+%5.1f%%)  T1 %7.2f (+%5.1f%%)  "
                 "R/R %.2f  VCS %3d %-4s  %s", c["code"], c["name"], c["market"], c["close"], c["pb"],
                 c["book_value"], c["target_price_085"], c["upside_085_pct"], c["target_price_100"],
                 c["upside_100_pct"], c["risk_reward_ratio"], c["vcs"], c["vcs_tag"], c["conviction"])
        if c.get("commodity_linkage"):
            lk = c["commodity_linkage"]
            log.info("        [%s] %s → %s %s", lk["label"], lk.get("tag") or "—", lk["rating"], lk["commentary"])
            for f in (c.get("factor_model") or {}).get("factors", []):
                if f.get("error"):
                    log.info("          %-8s ERROR %s", f["key"], f["error"])
                    continue
                log.info("          %-8s %-5s w=%3d%%  20D %+6.1f%%  r[L0/5/10/20]= %s  best Lead %sD r=%s",
                         f["key"], f["role"], f["weight"], f["chg_20d_pct"] or 0,
                         " ".join("—" if f["lead_lag"][str(L)]["r"] is None else f"{f['lead_lag'][str(L)]['r']:+.2f}" for L in LEADS),
                         f["best_lead"], f["best_r"])
        ch = c.get("chip")
        if ch:
            log.info("        CHIP %s · weeks %d · big %s (4W %s) · margin 20D %s usage %s%% · pos %s",
                     ch["signal"], ch["weeks_available"], (ch["latest"] or {}).get("big_pct"), ch["d4w_big"],
                     ch["margin"].get("d20"), ch["margin"].get("usage_pct"), ch["price_pos_60d"])
        tm = c.get("tech_metrics") or {}
        if tm.get("status") == "OK":
            log.info("        TECH %s · MA20 %s (%+.1f%%) MA60 %s · RSI %s · KD %s/%s %s · MACD OSC %+.3f %s",
                     tm["tech_signal"], tm["ma20"], tm["bias_ma20_pct"], tm["ma60"], tm["rsi14"], tm["k"], tm["d"],
                     tm["kd_state"], tm["macd_osc"], tm["macd_state"])
        elif tm:
            log.info("        TECH N/A · %s", tm.get("reason"))
        fa = c.get("fundamentals")
        if fa and fa.get("status") == "UNAVAILABLE":
            log.info("        FA N/A · %s", fa.get("reason"))
        elif fa:
            dp = fa["dupont"]
            log.info("        FA %s score %s · Z %s %s · OpRisk %s · FinRisk %s · ROE %s = NPM %s × AT %s × EM %s · %s",
                     fa["latest"], fa["fa_score"], fa["z"]["value"], fa["z"]["zone"], fa["operating_risk"], fa["financial_risk"],
                     dp["roe"], dp["npm"], dp["at"], dp["em"], dp["driver"])
            for x in fa["risk_factors"]:
                log.info("          [%s] %s · %s", x["severity"], x["title"], "；".join(x["metrics"]))
            if fa["twse_check"].get("available"):
                log.info("          TWSE check %s", fa["twse_check"])
        fvx = c.get("fair_value")
        if fvx:
            scx = fvx["scenarios"]
            log.info("        FAIR VALUE bear %.2f / BASE %.2f (%+.1f%%) / bull %.2f · ROE_q %.1f%% → norm %.1f%% · peer P/B %.2fx (n=%d)",
                     scx["bear"]["price"], scx["base"]["price"], scx["base"]["upside_pct"], scx["bull"]["price"],
                     fvx["inputs"]["roe_q_ann"] * 100, fvx["roe_norm"] * 100, fvx["inputs"]["peer_pb_mean"], fvx["inputs"]["peer_pb_n"])
            m = scx["base"]["models"]
            log.info("          A %.2f (P/B %.2fx)  B %.2f (P/B %.2fx)  C %.2f (P/B %.2fx)  %s", m["A"]["price"], m["A"]["pb"],
                     m["B"]["price"], m["B"]["pb"], m["C"]["price"], m["C"]["pb"], " ".join(fvx["notes"])[:160])
        pa = c.get("peer_analysis")
        if pa:
            log.info("        PEERS [%s] gap %s → %s · %s", pa["label"], pa["catch_up_gap"], pa["signal"], pa["commentary"])
            for q in pa["peers"]:
                if q.get("error"):
                    log.info("          %-10s ERROR %s", q["symbol"], q["error"])
                else:
                    log.info("          %-10s %-6s %-4s 5D %+6.1f%%  20D %+6.1f%%  60D %s  best %sD r=%s", q["symbol"], q["name"],
                             q["tier"], q["chg_5d_pct"] or 0, q["chg_20d_pct"] or 0, q["chg_60d_pct"], q["best_lead"], q["best_r"])
    for w in warnings:
        log.warning("WARN %s", w)
    if not args.no_briefing:
        run_briefing(out_dir / "candidates.json")
    return 0


def run_briefing(data_path: Path) -> None:
    """掃描完成後執行 daily_briefing.py（AI 覆盤＋推播）；任何失敗都不影響掃描結果。"""
    script = BASE_DIR / "daily_briefing.py"
    if not script.exists():
        log.info("daily_briefing.py not found — briefing skipped")
        return
    try:
        r = subprocess.run([sys.executable, str(script), "--data", str(data_path)],
                           capture_output=True, text=True, timeout=600)
        for line in (r.stdout or "").strip().splitlines()[-6:]:
            log.info("BRIEFING %s", line[20:] if len(line) > 20 else line)
        if r.returncode != 0:
            log.warning("Briefing exited with %s: %s", r.returncode, (r.stderr or "").strip()[-300:])
    except (OSError, subprocess.SubprocessError) as e:
        log.warning("Briefing failed to run: %s", e)


def write_outputs(out_dir: Path, result: Dict[str, Any]) -> None:
    """原子寫入：先寫 .tmp 再 rename，避免 dashboard 讀到半份檔案。"""
    js = json.dumps(result, ensure_ascii=False, indent=1)
    for name, content in (("candidates.json", js),
                          ("candidates.js", "/* auto-generated by scanner.py */\nwindow.DVF_DATA = " + js + ";\n")):
        tmp = out_dir / (name + ".tmp")
        tmp.write_text(content, "utf-8")
        os.replace(tmp, out_dir / name)
    log.info("Wrote %s and candidates.js", out_dir / "candidates.json")


def update_custom_watchlist(path: Path, add: Optional[List[str]], remove: Optional[List[str]]) -> List[str]:
    """讀取（不存在則以 CUSTOM_DEFAULT 建立）並套用 --add / --remove，回傳最新自選清單。"""
    codes: List[str] = []
    if path.exists():
        try:
            raw = json.loads(path.read_text("utf-8"))
            codes = [str(x).strip().upper() for x in raw if CODE_RE.match(str(x).strip().upper())]
        except (json.JSONDecodeError, TypeError):
            log.warning("%s 格式錯誤（需為 JSON 陣列），以預設值重建", path.name)
            codes = list(CUSTOM_DEFAULT)
    else:
        codes = list(CUSTOM_DEFAULT)
        log.info("Created %s with defaults %s", path.name, codes)
    changed = not path.exists()
    for x in add or []:
        x = str(x).strip().upper()
        if not CODE_RE.match(x):
            raise ValueError(f"--add 代號格式錯誤：{x}")
        if x not in codes:
            codes.append(x)
            changed = True
    for x in remove or []:
        x = str(x).strip().upper()
        if x in codes:
            codes.remove(x)
            changed = True
        else:
            log.warning("--remove %s 不在自選清單中", x)
    codes = list(dict.fromkeys(codes))
    if changed:
        tmp = path.with_suffix(".json.tmp")
        tmp.write_text(json.dumps(codes, ensure_ascii=False, indent=1) + "\n", "utf-8")
        os.replace(tmp, path)
        log.info("custom_watchlist.json → %s", codes)
    return codes


def setup_logging(out_dir: Path, verbose: bool) -> None:
    (out_dir / "logs").mkdir(parents=True, exist_ok=True)
    fmt = logging.Formatter("%(asctime)s %(levelname)-7s %(message)s", "%Y-%m-%d %H:%M:%S")
    log.setLevel(logging.DEBUG if verbose else logging.INFO)
    for h in (logging.StreamHandler(sys.stdout), logging.FileHandler(out_dir / "logs" / "scanner.log", encoding="utf-8")):
        h.setFormatter(fmt)
        log.addHandler(h)


def main() -> int:
    ap = argparse.ArgumentParser(description="DVF-PRO 盤後深度價值轉機掃描器")
    ap.add_argument("--out-dir", default=str(BASE_DIR), help="輸出目錄（預設：與 scanner.py 同資料夾）")
    ap.add_argument("--token", default=os.environ.get("FINMIND_TOKEN"), help="FinMind API token（或設環境變數 FINMIND_TOKEN）")
    ap.add_argument("--markets", default="twse,tpex", help="掃描市場：twse,tpex")
    ap.add_argument("--pb-max", type=float, default=DEFAULTS["pb_max"])
    ap.add_argument("--vol-min", type=float, default=DEFAULTS["vol_min"])
    ap.add_argument("--vol-max", type=float, default=DEFAULTS["vol_max"])
    ap.add_argument("--wait-fresh", type=int, default=0, metavar="MIN",
                    help="資料日期不是今天時，每 5 分鐘重試，最多等待 MIN 分鐘（cron 建議 90）")
    ap.add_argument("--sleep", type=float, default=0.35, help="FinMind 呼叫間隔秒數")
    ap.add_argument("--skip-fundamentals", action="store_true", help="略過第三道 EPS 濾網（除錯用）")
    ap.add_argument("--no-history", action="store_true", help="不抓量能歷史（VCS 改用絕對量法）")
    ap.add_argument("--no-macro", action="store_true", help="不抓國際商品期貨與產業連動")
    ap.add_argument("--no-news", action="store_true", help="不執行 market_crawler.py（新聞與重大訊息）")
    ap.add_argument("--no-broker", action="store_true", help="不執行 broker_scanner.py（主力分點鎖碼）")
    ap.add_argument("--no-briefing", action="store_true", help="掃描後不執行 daily_briefing.py（AI 覆盤與推播）")
    ap.add_argument("--add", nargs="+", metavar="CODE", help="加入自選股（寫入 custom_watchlist.json，自動去重）並掃描")
    ap.add_argument("--remove", nargs="+", metavar="CODE", help="自 custom_watchlist.json 移除代號並掃描")
    ap.add_argument("--analyze", nargs="+", metavar="CODE", help="單次強制分析（不寫入自選清單）")
    ap.add_argument("--all-sectors", action="store_true", help="停用景氣循環產業白名單（保留營建、電子等全部產業）")
    ap.add_argument("-v", "--verbose", action="store_true")
    args = ap.parse_args()
    setup_logging(Path(args.out_dir).expanduser().resolve(), args.verbose)
    try:
        args.custom_codes = update_custom_watchlist(Path(args.out_dir).expanduser().resolve() / CUSTOM_WATCHLIST_FILE,
                                                    args.add, args.remove)
    except ValueError as e:
        log.error("%s", e)
        return 2
    if args.analyze:
        bad = [x for x in args.analyze if not CODE_RE.match(x.strip().upper())]
        if bad:
            log.error("--analyze 代號格式錯誤：%s", bad)
            return 2
        args.analyze = [x.strip().upper() for x in args.analyze]
    try:
        return run(args)
    except KeyboardInterrupt:
        log.warning("Interrupted.")
        return 130


if __name__ == "__main__":
    sys.exit(main())
