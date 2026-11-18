#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
DVF-PRO — publish_site.py：把戰情室發布到 GitHub Pages（手機／平板看盤用）
==========================================================================
建立 ~/GOFOR/site/（獨立 git repo，與專案本身分開），只放「白名單」檔案：
    index.html        ← dashboard.html（移除內嵌 DEMO_DATA、加 noindex）
    candidates.js / candidates.json  ← 遮蔽持股後的掃描結果
    live_quotes.js    ← 遮蔽持股後的盤中即時報價
    .nojekyll、.github/workflows/pages.yml（GitHub Actions 部署，不受 Pages 每小時 10 次建置限制）
.env、briefings/、cache/、logs/ 與任何 .py 都不會進入 site/。

遮蔽（公開網址看不到）：核心持股的成本／目標價／停損／張數、AI 覆盤全文、Gemini 討論提示詞、
即時報價中以成本計算的停損與目標。選股、技術、財報、新聞、即時行情照常顯示。

每次發布都以「單一 commit」強制推送（不累積歷史），repo 永遠只有最新一版。
尚未設定遠端（git remote origin）時只建置、不推送，並提示設定方式（見 README 第 18 節）。

    python publish_site.py            # 建置＋推送
    python publish_site.py --no-push  # 只建置（檢查 site/ 內容）
"""
from __future__ import annotations

import argparse
import copy
import datetime as dt
import fcntl
import hashlib
import json
import os
import re
import subprocess
import sys
from pathlib import Path
from typing import Any, Dict

BASE_DIR = Path(__file__).resolve().parent
SITE = BASE_DIR / "site"
TPE = dt.timezone(dt.timedelta(hours=8))
HIDDEN = "（公開網址已隱藏）"
BOT = ["-c", "user.name=DVF-PRO Publisher", "-c", "user.email=dvf-pro-publisher@users.noreply.github.com"]

def log(msg: str) -> None:
    print(f"{dt.datetime.now(TPE):%Y-%m-%d %H:%M:%S} [publish] {msg}", flush=True)


# ── 遮蔽 ─────────────────────────────────────────────────────────────────────
def redact_candidates(d: Dict[str, Any]) -> Dict[str, Any]:
    d = copy.deepcopy(d)
    b = d.get("daily_briefing")
    if isinstance(b, dict):
        d["daily_briefing"] = {
            k: b.get(k) for k in ("data_date", "generated_at", "engine", "model", "is_ai", "stale")
        } | {"core_positions": [], "public_redacted": True,
             "ai_markdown": "## 公開網址已隱藏 AI 覆盤\n\nAI 盤後覆盤含持股成本與部位內容，僅在本機戰情室（~/GOFOR/dashboard.html）顯示。",
             "discussion_prompt": HIDDEN}
    for k in ("custom_errors",):
        d.pop(k, None)
    d["public_redacted"] = True
    return d


def redact_live(d: Dict[str, Any]) -> Dict[str, Any]:
    d = copy.deepcopy(d)
    for q in (d.get("quotes") or {}).values():
        if q.get("is_core"):
            for k in ("entry", "stop", "target", "to_stop_pct", "to_target_pct"):
                q[k] = None
            q["entry_basis"] = q["stop_basis"] = q["target_basis"] = HIDDEN
            for it in q.get("live_review") or []:
                if it["type"] == "STOP":
                    it["msg"] = "🚨 跌破核心持股停損線（價位已隱藏），建議執行紀律"
                elif it["type"] == "TARGET":
                    it["msg"] = "🎯 觸及核心持股目標價區（價位已隱藏）"
            if q.get("live_review"):
                q["review_text"] = q["live_review"][0]["msg"]
    core = {c for c, q in (d.get("quotes") or {}).items() if q.get("is_core")}
    for a in d.get("alerts") or []:
        if a["code"] in core and a["type"] in ("STOP", "TARGET"):
            a["msg"] = d["quotes"][a["code"]]["live_review"][0]["msg"] if a["type"] == "STOP" else "🎯 觸及核心持股目標價區（價位已隱藏）"
    d["public_redacted"] = True
    return d


def build_index(html: str) -> str:
    html, n = re.subn(r"(const DEMO_DATA = /\*__DEMO_DATA__\*/).*?;\n", r"\1null;\n", html, count=1, flags=re.S)
    if n != 1:
        raise RuntimeError("dashboard.html 找不到 DEMO_DATA 標記，為避免外流未遮蔽資料，停止發布")
    html = html.replace('<meta charset="utf-8">', '<meta charset="utf-8">\n<meta name="robots" content="noindex,nofollow,noarchive">', 1)
    build = hashlib.sha1(html.encode("utf-8")).hexdigest()[:12]   # 程式版本：index.html 內容變更才會變
    return html.replace('<meta charset="utf-8">', f'<meta charset="utf-8">\n<meta name="dvf-build" content="{build}">', 1)


def assert_clean(site: Path, secrets: Dict[str, str]) -> None:
    """最後一道防線：發布內容不得含核心持股成本或 .env 密鑰值。"""
    blob = "\n".join(p.read_text("utf-8", errors="ignore") for p in site.rglob("*") if p.is_file() and ".git" not in p.parts)
    for label, val in secrets.items():
        if val and len(val) >= 4 and val in blob:
            raise RuntimeError(f"發布內容含敏感值（{label}），停止發布")


def env_secrets() -> Dict[str, str]:
    """.env（本機）與環境變數（GitHub Actions secrets）中的敏感值，供發布前比對。"""
    out: Dict[str, str] = {}
    p = BASE_DIR / ".env"
    lines = p.read_text("utf-8").splitlines() if p.exists() else []
    lines += [f"{k}={v}" for k, v in os.environ.items() if k == "CORE_POSITIONS" or k.endswith(("_KEY", "_TOKEN", "_PASSWORD"))]
    for line in lines:
        if "=" in line and not line.strip().startswith("#"):
            k, v = line.split("=", 1)
            k, v = k.strip(), v.strip().strip('"').strip("'")
            if any(t in k for t in ("KEY", "TOKEN", "PASSWORD", "SECRET", "WEBHOOK", "EMAIL", "USER")):
                out[k] = v
            elif k == "CORE_POSITIONS":
                for i, part in enumerate(v.split(",")):
                    f = part.split(":")
                    if len(f) >= 3 and f[2]:
                        v_js = json.dumps(float(f[2]))   # 以發布檔的 JSON 形式比對，避免誤判一般股價
                        out[f"CORE_COST_{i}"] = f'"cost":{v_js}'
                        out[f"CORE_ENTRY_{i}"] = f'"entry":{v_js}'
    return out


# ── 建置與推送 ───────────────────────────────────────────────────────────────
def write(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_name(path.name + ".tmp")
    tmp.write_text(text, "utf-8")
    os.replace(tmp, path)


def build(SITE: Path = SITE) -> None:
    SITE.mkdir(parents=True, exist_ok=True)
    cand = json.loads((BASE_DIR / "candidates.json").read_text("utf-8"))
    pub = json.dumps(redact_candidates(cand), ensure_ascii=False, separators=(",", ":"))
    write(SITE / "candidates.json", pub)
    write(SITE / "candidates.js", "/* DVF-PRO public build (redacted) */\nwindow.DVF_DATA = " + pub + ";\n")
    lq = BASE_DIR / "live_quotes.json"
    if lq.exists():
        live = json.dumps(redact_live(json.loads(lq.read_text("utf-8"))), ensure_ascii=False, separators=(",", ":"))
        write(SITE / "live_quotes.json", live)
        write(SITE / "live_quotes.js", "/* DVF-PRO public build (redacted) */\nwindow.DVF_LIVE = " + live + ";\n")
    index = build_index((BASE_DIR / "dashboard.html").read_text("utf-8"))
    write(SITE / "index.html", index)
    build = re.search(r'name="dvf-build" content="([0-9a-f]+)"', index).group(1)
    write(SITE / "version.json", json.dumps({"build": build, "published_at": dt.datetime.now(TPE).isoformat(timespec="seconds")}))
    write(SITE / ".nojekyll", "")
    write(SITE / "README.md", "# DVF-PRO 戰情室（公開唯讀版）\n\n自動產生，請勿手動修改。持股成本、AI 覆盤等個人資料已在發布前遮蔽。\n")
    for stray in SITE.iterdir():   # 白名單以外的檔案一律移除
        if stray.name not in {".git", ".nojekyll", "index.html", "candidates.js", "candidates.json", "live_quotes.js", "live_quotes.json", "version.json", "README.md"}:
            if stray.is_file():
                stray.unlink()
    assert_clean(SITE, env_secrets())


def git(*args: str, check: bool = True, timeout: int = 60) -> subprocess.CompletedProcess:
    env = dict(os.environ, GIT_TERMINAL_PROMPT="0")   # 排程中絕不卡在帳密輸入
    return subprocess.run(["git", "-C", str(SITE), *BOT, *args], capture_output=True, text=True, check=check, timeout=timeout, env=env)


def push() -> bool:
    if not (SITE / ".git").exists():
        git("init", "-q", "-b", "main")
        git("config", "credential.helper", "osxkeychain")
    remote = git("remote", "get-url", "origin", check=False).stdout.strip()
    if not remote:
        log("site/ 尚未設定 GitHub 遠端，只建置不推送（設定方式見 README 第 18 節）")
        return False
    git("add", "-A")
    tree = git("write-tree").stdout.strip()
    head = git("rev-parse", "-q", "--verify", "HEAD^{tree}", check=False).stdout.strip()
    if tree == head:
        log("內容無變更，略過推送")
        return True
    msg = f"DVF-PRO update {dt.datetime.now(TPE):%Y-%m-%d %H:%M:%S}"
    commit = git("commit-tree", tree, "-m", msg).stdout.strip()   # 無父節點 → 不累積歷史
    git("update-ref", "refs/heads/main", commit)
    git("symbolic-ref", "HEAD", "refs/heads/main")
    r = git("push", "-q", "--force", "origin", "main", check=False, timeout=90)
    if r.returncode != 0:
        log(f"推送失敗：{(r.stderr or r.stdout).strip()[-300:]}")
        return False
    log(f"已推送 {commit[:8]} → {remote.split('@')[-1]}")
    return True


def main() -> int:
    ap = argparse.ArgumentParser(description="Publish DVF-PRO dashboard to GitHub Pages")
    ap.add_argument("--no-push", action="store_true")
    ap.add_argument("--out", metavar="DIR", help="只建置到指定資料夾（GitHub Actions 雲端部署用），不做 git 操作")
    args = ap.parse_args()
    if args.out:
        try:
            build(Path(args.out).resolve())
            log(f"已建置 {args.out}")
            return 0
        except Exception as e:  # noqa: BLE001
            log(f"建置失敗：{type(e).__name__} {e}")
            return 1
    lock_path = BASE_DIR / "logs" / ".publish.lock"
    lock_path.parent.mkdir(exist_ok=True)
    with lock_path.open("w") as lf:
        try:
            fcntl.flock(lf, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            log("另一個發布仍在進行，略過")
            return 0
        try:
            build()
            if not args.no_push:
                push()
        except Exception as e:  # noqa: BLE001
            log(f"發布失敗：{type(e).__name__} {e}")
            return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
