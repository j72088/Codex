# -*- coding: utf-8 -*-
import json

import json, time, threading, queue, datetime as dt, csv, zipfile, traceback, platform, argparse, math
import re
import random
import tempfile
from dataclasses import dataclass, field
from pathlib import Path
import sys
import os
from urllib.parse import quote
from typing import Optional, Dict, Any, List, Tuple
from uuid import uuid4
from PySide6 import QtCore, QtGui, QtWidgets
Qt = QtCore.Qt  # Qt alignment/keys alias
from PySide6.QtCharts import QChart, QChartView, QLineSeries, QBarSeries, QBarSet, QValueAxis, QBarCategoryAxis
import requests

# ---- Version (must be defined before any title strings use it) ----
APP_VERSION = '8.11.1'
# Optional: websocket streaming for Loop A (requires websocket-client)
try:
    import websocket
except Exception:
    websocket = None

import xml.etree.ElementTree as ET
import html
from zoneinfo import ZoneInfo

# --- Time helpers (ET) ---
try:
    _ET_TZ = ZoneInfo("America/New_York")
except Exception:
    _ET_TZ = None

def now_et() -> dt.datetime:
    """Return current time in US/Eastern as timezone-aware datetime when possible."""
    if _ET_TZ is not None:
        return dt.datetime.now(tz=_ET_TZ)
    # Fallback: naive local time (still usable for simple hour checks)
    return dt.datetime.now()


def _safe_float(x, default: float = 0.0) -> float:
    try:
        if x is None:
            return float(default)
        return float(x)
    except Exception:
        return float(default)


def fmt_price(px, is_crypto: bool = False) -> str:
    """Human-friendly price formatting.

    This is intentionally defensive: it must never raise.
    It was missing in v8.2.8 which caused a NameError during crypto exit placement,
    triggering a false 'unprotected' panic close loop.
    """
    try:
        if px is None:
            return "-"
        f = float(px)
        # Crypto can have more decimals; keep it readable but precise.
        dec = 6 if is_crypto else 2
        s = f"{f:.{dec}f}"
        s = s.rstrip("0").rstrip(".")
        return s if s else "0"
    except Exception:
        return "-"




def _fmt_qty_for_feed(qty, sym: str) -> str:
    try:
        q = float(qty)
    except Exception:
        return str(qty)
    try:
        if is_crypto_symbol(sym):
            return (f"{q:.6f}").rstrip("0").rstrip(".")
        # stocks: prefer int
        if abs(q - round(q)) < 1e-9:
            return str(int(round(q)))
        return (f"{q:.4f}").rstrip("0").rstrip(".")
    except Exception:
        return str(qty)

def feed_why_for_trade(t) -> str:
    """Compact WHY for the live feed, with qty + protective stop if known.

    Phase 3 requirement: include visible news boost + macro adj on the WHY line.
    Guardrail: never duplicate nboost/macro tokens even if the base WHY already contains them.
    """
    try:
        sym = getattr(t, "symbol", "") or ""
        base_raw = (getattr(t, "why", "") or "").replace("\r", " ").replace("\n", " ").strip()

        # Strip any pre-existing nboost/macro tokens from the base WHY (prevents duplicates in the feed).
        base_clean = ""
        if base_raw:
            toks = [tok.strip() for tok in base_raw.split("|")]
            toks = [tok for tok in toks if tok and not tok.lower().startswith("nboost=") and not tok.lower().startswith("macro=")]
            base_clean = " | ".join(toks).strip()

        qty = getattr(t, "qty", None)
        stop_px = getattr(t, "stop_px", None)

        parts = []
        if base_clean:
            parts.append(base_clean)
        if qty is not None:
            parts.append(f"qty={_fmt_qty_for_feed(qty, sym)}")
        if stop_px is not None and float(stop_px) > 0:
            parts.append(f"stop={fmt_price(float(stop_px), is_crypto=is_crypto_symbol(sym))}")
        else:
            parts.append("stop=n/a")

        # Visible news/macro influence (exactly one token each)
        try:
            nb = float(getattr(t, "news_boost", getattr(t, "newsBoost", 0.0)) or 0.0)
        except Exception:
            nb = 0.0
        try:
            ma = float(getattr(t, "macro_adj", getattr(t, "macroAdj", 0.0)) or 0.0)
        except Exception:
            ma = 0.0
        parts.append(f"nboost={nb:+.1f}")
        parts.append(f"macro={ma:+.1f}")

        return " | ".join([p for p in parts if p])
    except Exception:
        return (getattr(t, "why", "") or "").replace("\r", " ").replace("\n", " ").strip()

def floor_crypto_qty(qty: float, *, step: float = 1e-6, eps: float = 1e-12) -> float:
    """Floor crypto qty to a broker-friendly increment.

    Important: we **never** round up, because rounding up can make Alpaca reject exits
    ('insufficient balance') when some quantity is reserved by resting orders.
    """
    try:
        q = float(qty)
    except Exception:
        return 0.0
    if not math.isfinite(q) or q <= 0:
        return 0.0
    try:
        s = float(step)
    except Exception:
        s = 1e-6
    if s <= 0:
        s = 1e-6
    # subtract a tiny epsilon before flooring to avoid float edge-cases like 1.00000000002
    n = math.floor((q / s) - eps)
    floored = n * s
    # Clamp to [0, qty] to avoid negatives from epsilon in tiny quantities
    if floored < 0:
        return 0.0
    if floored > q:
        return max(0.0, q - s)
    return floored
def _ensure_dir(p: Path) -> None:
    try:
        p.mkdir(parents=True, exist_ok=True)
    except Exception:
        # best effort; callers will handle failures
        pass


# CSV headers (used by Open Journal / Export Logs)
JOURNAL_HEADERS_OLD = ["ts", "trade_id", "symbol", "side", "qty", "entry_price", "exit_price", "pnl", "why", "notes"]
JOURNAL_HEADERS = ["ts", "trade_id", "symbol", "side", "qty", "entry_price", "exit_price", "pnl", "pnl_pct", "stop_price", "why", "why_verbose", "news_conf", "news_pub_et", "news_age_m", "news_source", "news_headline", "notes"]
TRADE_EVENTS_HEADERS = ["ts","event","symbol","side","qty","price","info"]



# --- SECTION: NEWS SENTIMENT + BOOST (Phase 3 news influence) ---

_BULL_KW = [
    "rally", "surge", "soar", "jumps", "jump", "breakout", "bullish", "upgrade", "beats", "record", "adopts", "adoption", "partnership", "integrat", "approve", "approval", "etf", "inflows", "buy", "accumulat", "support", "good sign", "strong", "spike", "spikes", "pops", "pop", "popped", "breaks out", "breaks", "strength", "stronger", "leading", "charge ahead", "upside"
]
_BEAR_KW = [
    "fall", "falls", "dump", "plunge", "crash", "bearish", "downgrade", "lawsuit", "ban", "hack", "exploit", "charged", "sec", "investigation", "fear", "terrify", "warning", "risk", "reignite", "tariff", "recession", "selloff", "liquidat", "cratered", "crater", "tumble", "tumbles", "dumping", "sell-off", "sell off", "rug", "rugpull", "rug pull", "liquidation", "liquidations", "bear", "downside", "slump", "slumps"
]

def classify_news_sentiment(headline: str) -> int:
    """Very simple headline sentiment: +1 bullish, -1 bearish, 0 neutral."""
    try:
        h = (headline or "").lower()
        if not h:
            return 0
        bull = sum(1 for w in _BULL_KW if w in h)
        bear = sum(1 for w in _BEAR_KW if w in h)
        if bull == 0 and bear == 0:
            return 0
        if bull > bear:
            return 1
        if bear > bull:
            return -1
        return 0
    except Exception:
        return 0

def news_conf_weight(conf: str) -> float:
    c = (conf or "").upper().strip()
    # STALE news should have ZERO impact (no boost, no contradiction blocks).
    if c == "STALE":
        return 0.0
    return 1.0 if c == "HIGH" else 0.7 if c == "MED" else 0.4 if c == "LOW" else 0.15

def compute_symbol_news_boost(*, conf: str, age_m: int, sentiment: int, max_abs: float = 25.0) -> float:
    """Bounded boost for symbol-specific news; decays with age."""
    try:
        if sentiment == 0:
            return 0.0
        w = float(news_conf_weight(conf))
        age = max(0.0, float(age_m))
        # decay: 0-15m ~1.0, 60m ~0.6, 240m ~0.25, >6h ~0.1
        decay = 1.0 / (1.0 + (age / 60.0))
        boost = float(sentiment) * max_abs * w * decay
        # clamp
        if boost > max_abs:
            boost = max_abs
        if boost < -max_abs:
            boost = -max_abs
        return boost
    except Exception:
        return 0.0

# --- SECTION: PERSISTENCE & RECEIPT HELPERS (Phase 3.2) ---

def generate_verbose_receipt(trade_ctx: dict) -> str:
    """Standardized, CSV-safe Phase 3.2 receipt (pipe-separated, fixed field order).

    IMPORTANT: must stay single-line (no embedded newlines) so Excel/ONLYOFFICE doesn't split cells.
    """
    fields = [
        ("ID","id"),
        ("Symbol","symbol"),
        ("Side","side"),
        ("ScoreTotal","score_total"),
        ("ScoreBase","score_base"),
        ("MacroAdj","macro_adj"),
        ("NewsBoost","news_boost"),
        ("Dir","dir"),
        ("RSI","rsi"),
        ("ATR","atr"),
        ("Spread","spread"),
        ("Risk","risk"),
        ("Qty","qty"),
        ("Entry","entry"),
        ("Stop","stop"),
        ("StopDist","stopdist"),
        ("Notional","notional"),
        ("Equity","equity"),
        ("Gates","gates"),
        ("News","news"),
        ("CloseLeg","close_leg"),
        ("CloseReason","close_reason"),
        ("Exit","exit"),
        ("PNL","pnl"),
        ("PNLPct","pnl_pct"),
        ("Cooldown","cooldown"),
        ("ClosedET","closed_et"),
    ]
    parts = []
    for label, key in fields:
        val = trade_ctx.get(key, "n/a")
        if val is None:
            val = "n/a"
        try:
            if isinstance(val, float):
                sval = f"{val:.6f}".rstrip("0").rstrip(".")
            else:
                sval = str(val)
        except Exception:
            sval = "n/a"
        sval = (sval or "").replace("|", ";").replace("\n", " ").replace("\r", " ").replace(",", ";").strip()
        parts.append(f"{label}: {sval if sval else 'n/a'}")
    return " | ".join(parts)

def _build_trade_receipt_ctx_from_trade(t) -> dict:
    """Best-effort build of receipt context from a ManagedTrade (for recovery/edge cases)."""
    try:
        sym = getattr(t, "symbol", "") or ""
        side = getattr(t, "side", "") or ""
        base_ctx = {
            "id": getattr(t, "trade_id", "") or "",
            "symbol": sym,
            "side": side,
            "score_total": "n/a",
            "score_base": "n/a",
            "macro_adj": getattr(t, "macro_adj", "n/a") if hasattr(t, "macro_adj") else "n/a",
            "news_boost": getattr(t, "news_boost", "n/a") if hasattr(t, "news_boost") else "n/a",
            "dir": "BULL" if side == "buy" else ("BEAR" if side == "sell" else "n/a"),
            "rsi": "n/a",
            "atr": getattr(t, "atr", "n/a") if hasattr(t, "atr") else "n/a",
            "spread": "n/a",
            "risk": "n/a",
            "qty": getattr(t, "qty", "n/a"),
            "entry": getattr(t, "entry_px", "n/a"),
            "stop": getattr(t, "stop_px", "n/a"),
            "stopdist": "n/a",
            "notional": "n/a",
            "equity": "n/a",
            "gates": "n/a",
            "news": (getattr(t, "news", "") or "").strip() or "n/a",
        }
        return base_ctx
    except Exception:
        return {}

def build_final_why_verbose(t, *, close_leg: str, close_reason: str, exit_price: float, pnl: float,
                           cooldown: str = "", closed_et: str = "") -> str:
    """Create a Phase 3.2/3.3 compliant final WHY_VERBOSE with close receipt fields."""
    try:
        ctx = {}
        try:
            ctx = dict(getattr(t, "receipt_ctx", {}) or {})
        except Exception:
            ctx = {}
        if not ctx:
            ctx = _build_trade_receipt_ctx_from_trade(t)
        # Close fields
        ctx["close_leg"] = str(close_leg or "n/a")
        ctx["close_reason"] = str(close_reason or "n/a")
        ctx["exit"] = float(exit_price or 0.0)
        ctx["pnl"] = float(pnl or 0.0)
        try:
            notional = abs(float(ctx.get("qty") or 0.0) * float(ctx.get("entry") or 0.0))
            ctx["pnl_pct"] = (float(pnl or 0.0) / notional * 100.0) if notional > 0 else 0.0
        except Exception:
            ctx["pnl_pct"] = "n/a"
        ctx["cooldown"] = str(cooldown or "")
        if not closed_et:
            try:
                closed_et = dt.datetime.now(tz=ET_TZ).strftime("%Y-%m-%d %H:%M:%S ET")
            except Exception:
                closed_et = ""
        ctx["closed_et"] = str(closed_et or "")
        return generate_verbose_receipt(ctx)
    except Exception:
        return (getattr(t, "why_verbose", "") or getattr(t, "why", "") or "").replace("\n"," ").replace("\r"," ").strip()

def parse_available_qty(msg: str) -> Optional[float]:
    """Extract an 'available' quantity from broker error text.

    Alpaca sometimes rejects an order with a message that includes an
    'available' qty (reserved by other resting orders). We use this
    to safely retry with a floored qty, never rounding up.
    """
    try:
        if not msg:
            return None
        s = str(msg)
        # common patterns: "available: 0.123", "available qty: 0.123", "available=0.123"
        m = re.search(r"available(?:\s*qty)?\s*[:=]\s*([0-9]+(?:\.[0-9]+)?)", s, re.IGNORECASE)
        if m:
            return float(m.group(1))
        # looser: "... available 0.123 ..."
        m = re.search(r"available\s+([0-9]+(?:\.[0-9]+)?)", s, re.IGNORECASE)
        if m:
            return float(m.group(1))
        # JSON-ish: {'available': '0.123'} or "available":"0.123"
        m = re.search(r"[\"']available[\"']\s*[:=]\s*[\"']?([0-9]+(?:\.[0-9]+)?)", s, re.IGNORECASE)
        if m:
            return float(m.group(1))
        return None
    except Exception:
        return None


def is_insufficient_balance_err(e: Exception) -> bool:
    """Detect Alpaca crypto 403 'insufficient balance' / reserved qty errors."""
    try:
        s = str(e).lower()
    except Exception:
        return False
    if 'insufficient balance' in s:
        return True
    if 'requested' in s and 'available' in s and ('insufficient' in s or 'balance' in s):
        return True
    if 'available:' in s and 'requested:' in s:
        return True
    return False




def _ensure_utf8_bom_and_repair_csv(path: Path) -> None:
    """
    Ensure a CSV is UTF-8 with BOM (utf-8-sig) so Excel/OnlyOffice won't show mojibake.
    Also repairs common mojibake sequences left over from older builds.
    Safe to call repeatedly.
    """
    try:
        if not path.exists() or path.stat().st_size == 0:
            return
        data = path.read_bytes()
        bom = b"\xef\xbb\xbf"
        if not data.startswith(bom):
            # Prepend BOM so Windows apps reliably detect UTF-8.
            data = bom + data
            path.write_bytes(data)
        # Repair common mojibake text patterns (UTF-8 bytes previously mis-decoded as cp1252).
        try:
            s = path.read_text(encoding="utf-8-sig", errors="replace")
        except Exception:
            return
        fixes = {
            "â¢": "-",      # bullet
            "â": "-",      # en-dash
            "â": "-",      # em-dash
            "â¦": "...",    # ellipsis
            "â": "\"",
            "â": "\"",
            "â": "'",
            "â": "'",
            "ðŸ§": "",       # partial emoji mojibake
            "ðŸ°": "",
            "â": "WARN",    # warning sign mojibake fragments
        }
        changed = False
        for a,b in fixes.items():
            if a in s:
                s = s.replace(a,b)
                changed = True
        if changed:
            path.write_text(s, encoding="utf-8-sig", newline="")
    except Exception:
        pass


def _ensure_csv_header(path: Path, headers: list[str]) -> None:
    """Create CSV with header if missing/empty.
    Keep this FAST (called from UI actions). For existing files, only run expensive repairs
    on small files to avoid freezing the GUI.
    """
    try:
        _ensure_dir(path.parent)
        header_line = ",".join(headers)
        if (not path.exists()) or path.stat().st_size == 0:
            with open(path, "w", encoding="utf-8-sig", newline="") as f:
                f.write(header_line + "\n")
            return

        # Quick header sanity check (read only first line)
        try:
            with open(path, "r", encoding="utf-8-sig", errors="replace", newline="") as f:
                first = f.readline().strip("\r\n")
        except Exception:
            first = ""

        # If header already present, we're done.
        if first.startswith(headers[0]) and first.replace("	", ",").startswith(headers[0]):
            # still optionally repair tiny files (BOM/commas) without blocking on huge CSVs
            size = path.stat().st_size
            if size <= 2_000_000:  # 2MB
                _ensure_utf8_bom_and_repair_csv(path)
            return

        # If the file is small, attempt a safe repair (BOM + delimiter cleanup).
        # For large files, do NOT attempt to rewrite; just leave as-is.
        size = path.stat().st_size
        if size <= 2_000_000:
            _ensure_utf8_bom_and_repair_csv(path)
    except Exception:
        pass

def _read_csv_header(path: Path) -> list[str]:
    try:
        if not path.exists() or path.stat().st_size == 0:
            return []
        with path.open("r", encoding="utf-8-sig", errors="ignore", newline="") as f:
            r = csv.reader(f)
            return next(r, []) or []
    except Exception:
        return []

def _upgrade_trade_journal_schema_if_needed() -> None:
    """Best-effort upgrade of trade_journal.csv from older header to current JOURNAL_HEADERS."""
    try:
        path = JOURNAL_PATH
        if not path.exists() or path.stat().st_size == 0:
            return
        hdr = _read_csv_header(path)
        if not hdr:
            return
        if hdr == JOURNAL_HEADERS:
            return
        if hdr != JOURNAL_HEADERS_OLD:
            return

        tmp = path.with_suffix(".tmp")
        with path.open("r", encoding="utf-8-sig", errors="ignore", newline="") as fin, tmp.open("w", encoding="utf-8-sig", newline="") as fout:
            r = csv.DictReader(fin)
            w = csv.DictWriter(fout, fieldnames=JOURNAL_HEADERS)
            w.writeheader()
            for row in r:
                out = {k: (row.get(k, "") if row is not None else "") for k in JOURNAL_HEADERS}
                # Derive pnl_pct when missing
                if not out.get("pnl_pct"):
                    try:
                        qty = _safe_float(out.get("qty")) or 0.0
                        entry = _safe_float(out.get("entry_price")) or 0.0
                        pnl = _safe_float(out.get("pnl")) or 0.0
                        notional = abs(qty * entry)
                        if notional > 0:
                            out["pnl_pct"] = f"{(pnl / notional) * 100.0:.4f}"
                    except Exception:
                        pass
                w.writerow(out)

        try:
            path.replace(path.with_suffix(".bak"))
        except Exception:
            try:
                bak = path.with_suffix(".bak")
                if bak.exists():
                    bak.unlink()
                path.replace(bak)
            except Exception:
                pass
        tmp.replace(path)
    except Exception:
        return

def parse_news_fields(news_text: str) -> dict:
    """Parse our formatted NEWS line into structured fields."""
    out = {
        "news_conf": "",
        "news_pub_et": "",
        "news_age_m": "",
        "news_source": "",
        "news_headline": "",
    }
    try:
        s = (news_text or "").strip()
        if not s:
            return out
        # Expect: [ALPACA:CONF pub=YYYY-MM-DD HH:MM ET age=Nm] Headline (source)
        m = re.search(r"\[ALPACA:([A-Z]+)\s+pub=([^\]]+?)\s+age=([0-9]+)m\]\s*(.*)$", s)
        if not m:
            return out
        out["news_conf"] = (m.group(1) or "").strip()
        out["news_pub_et"] = (m.group(2) or "").strip()
        out["news_age_m"] = (m.group(3) or "").strip()
        rest = (m.group(4) or "").strip()
        # Try split trailing "(source)"
        m2 = re.search(r"^(.*)\s+\(([^\)]+)\)\s*$", rest)
        if m2:
            out["news_headline"] = (m2.group(1) or "").strip()
            out["news_source"] = (m2.group(2) or "").strip()
        else:
            out["news_headline"] = rest
        return out
    except Exception:
        return out



def _open_path(p: Path) -> bool:
    """Best-effort open of a file/folder on the host OS. Returns True if launched."""
    try:
        # Prefer Qt (more reliable than os.startfile in some environments)
        from PySide6 import QtCore, QtGui
        url = QtCore.QUrl.fromLocalFile(str(p))
        if QtGui.QDesktopServices.openUrl(url):
            return True
    except Exception:
        pass

    try:
        if os.name == "nt":
            os.startfile(str(p))  # type: ignore[attr-defined]
            return True
    except Exception:
        pass

    try:
        import subprocess
        if sys.platform == "darwin":
            subprocess.Popen(["open", str(p)])
        else:
            subprocess.Popen(["xdg-open", str(p)])
        return True
    except Exception:
        return False



def _open_path_qt_only(p: Path) -> bool:
    """Qt-only open (non-blocking). Avoids os.startfile() which can sometimes block the UI."""
    try:
        from PySide6 import QtCore, QtGui
        url = QtCore.QUrl.fromLocalFile(str(p))
        return bool(QtGui.QDesktopServices.openUrl(url))
    except Exception:
        return False


def _open_path_async(p: Path) -> None:
    '''Open a file or folder without blocking the Qt UI thread.'''
    try:
        import threading, os, sys

        p_str = str(p)

        def _worker():
            try:
                if sys.platform.startswith('win'):
                    os.startfile(p_str)  # type: ignore[attr-defined]
                else:
                    _open_path(p)
            except Exception as e:
                try:
                    _log('WARN', f'Open path failed: {e}')
                except Exception:
                    pass

        threading.Thread(target=_worker, daemon=True).start()
    except Exception:
        # Best-effort fallback
        try:
            _open_path(p)
        except Exception:
            pass



def export_diagnostics_zip(reason: str = "manual", diag_dir: Path | None = None) -> Path:
    """Create a diagnostics zip in diag_dir (no raw keys). Returns zip path."""
    if diag_dir is None:
        d = globals().get("DIAG_DIR")
        diag_dir = d if isinstance(d, Path) else (Path.cwd() / "diagnostics")
    _ensure_dir(diag_dir)
    dt = now_et()
    ts = dt.strftime('%Y-%m-%d_%H%M%S_ET')
    out_zip = diag_dir / f"diagnostics_{reason}_{ts}.zip"
    # Collect known files if they exist (best-effort)
    candidates: list[tuple[Path, str]] = []
    for var, arc in [
        ("LOG_PATH", "logs/app.log"),
        ("PERF_PATH", "data/perf.json"),
        ("JOURNAL_PATH", "data/trade_journal.csv"),
        ("TRADE_EVENTS_CSV_PATH", "data/trade_events.csv"),
        ("HEARTBEAT_PATH", "data/heartbeat.json"),
        ("SETTINGS_PATH", "data/settings.json"),
    ]:
        p = globals().get(var)
        if isinstance(p, Path):
            candidates.append((p, arc))
    # Also include run_app/build logs if present in the working folder
    try:
        wd = Path(__file__).resolve().parent
        candidates.extend([
            (wd / "run_app.log", "logs/run_app.log"),
            (wd / "build_exe.log", "logs/build_exe.log"),
        ])
    except Exception:
        pass

    # Ensure CSV headers exist so the zip always has usable files
    try:
        jp = globals().get("JOURNAL_PATH")
        tep = globals().get("TRADE_EVENTS_CSV_PATH")
        if isinstance(jp, Path):
            _ensure_csv_header(jp, ["ts","event","symbol","side","qty","price","note"])
        if isinstance(tep, Path):
            _ensure_csv_header(tep, ["ts","trade_id","symbol","event","qty","price","info"])
    except Exception:
        pass

    import zipfile
    with zipfile.ZipFile(out_zip, "w", compression=zipfile.ZIP_DEFLATED) as zf:
        for p, arc in candidates:
            try:
                if p.exists():
                    zf.write(p, arcname=arc)
            except Exception:
                continue
    return out_zip

APP_NAME = f"Relentless Execution v{APP_VERSION} - Qt UI (Stocks + Crypto, PAPER/LIVE Toggle, Loop A/B, Watchdog)"

# --------------------------------------------------------------------------------------

# --------------------------------------------------------------------------------------
# Phase 3.3: EngineState (consolidated runtime flags to reduce mystery globals)
# --------------------------------------------------------------------------------------
from dataclasses import dataclass

@dataclass
class EngineState:
    connected: bool = False
    connecting: bool = False
    running: bool = False
    paused: bool = False
    warmup_until_ts: float = 0.0  # entry suppression window after connect/resume
    recent_stop_guard_until: Dict[str, float] = field(default_factory=dict)  # symbol -> ts; recovery stop race-guard
    crypto_close_retry_until: Dict[str, float] = field(default_factory=dict)  # symbol -> ts; retry window for close_position on 403 reserved/insufficient
    clear_local_trades_pending: bool = False  # set by UI (e.g., after PANIC confirms broker flat)
    clear_local_trades_reason: str = ""
    last_equity: float = 0.0
    last_dtd_pl: float = 0.0
    last_wtd_pl: float = 0.0
    last_hb_ts: float = 0.0
    last_status: str = ""

    last_recovery_stop_log_ts: Dict[str, float] = field(default_factory=dict)  # per-symbol throttle for RECOVERY stop logs
    last_crypto_protect_ts: Dict[str, float] = field(default_factory=dict)  # per-symbol ts for last crypto protective-stop activity
    last_existing_stop_ts: Dict[str, float] = field(default_factory=dict)  # nsym -> ts when existing STOP observed
    last_existing_stop_log_ts: Dict[str, float] = field(default_factory=dict)  # throttle INFO logs
    last_recovery_stop_action_ts: Dict[str, float] = field(default_factory=dict)  # throttle recovery stop place/cancel churn
    last_recovery_stop_snapshot: Dict[str, str] = field(default_factory=dict)  # symbol -> compact existing stop signature

# Launch-safe defaults
#
# We have repeatedly hit "NameError: <CONST> is not defined" during startup.
# To make the app robust against missing globals during refactors, we define the
# critical runtime constants here and we also access them via globals().get(...) in
# the few hot paths that previously crashed.


def _defconst(name: str, value):
    """Define a global constant if it doesn't already exist."""
    if name not in globals():
        globals()[name] = value

# Watchdog / Heartbeat defaults (locked behavior: 1s heartbeat, ~5s stale restart)
_defconst("WATCHDOG_CHECK_SEC", 1.0)
_defconst("WATCHDOG_TIMEOUT_SEC", 5.0)
_defconst("HEARTBEAT_SEC", 1.0)
_defconst("HEARTBEAT_PATH", None)  # set properly after APPDATA_DIR is defined
_defconst("AUTO_START_ON_LAUNCH", True)
_defconst("RESUME_WARMUP_SEC", 20.0)
_defconst("LIVE_CONFIRM_WORD", "LIVE")
_defconst("LIVE_CONFIRM_TEXT", "LIVE")

# Phase 2 runtime defaults (prevent NameError chains)
_defconst("BROKER_SYNC_SEC", 15.0)  # broker positions/orders refresh cadence
_defconst("CIRCUIT_BREAKER_SEC", 60)  # minimum pause after severe connectivity/error burst
_defconst("CIRCUIT_BREAKER_REASON", "")  # minimum pause after severe connectivity/error burst
_defconst("TIME_STOP_SEC", 45*60)  # 45 min max hold default
_defconst("MAX_CRYPTO_POSITIONS", 3)
_defconst("CRYPTO_DUST_QTY", 1e-5)
_defconst("CRYPTO_DUST_NOTIONAL", 1.0)
_defconst("MAX_CRYPTO_EXPOSURE_PCT", 25.0)
_defconst("MAX_TOTAL_EXPOSURE_PCT", 50.0)
_defconst("CRYPTO_TRADE_COOLDOWN_SEC", 10*60)  # loss-only per-symbol cooldown default
_defconst("TRADES_PER_HOUR_TARGET", 4)
_defconst("MAX_DAILY_TRADES", 40)
_defconst("APPSTATE_MAX_EVENTS", 5000)
_defconst("NEWS_RSS", [])  # optional list of RSS/Atom feed URLs
_defconst("RISK_ON_WORDS", ["beats","surge","upgrade","bullish","record"])
_defconst("RISK_OFF_WORDS", ["miss","downgrade","lawsuit","probe","war","inflation"])
_defconst("DRAWDOWN_SOFT1_PCT", 1.0)
_defconst("DRAWDOWN_SOFT2_PCT", 2.0)
_defconst("DRAWDOWN_HARD_PCT", 3.5)
# Engine/loop cadence + guardrails (Phase 2 defaults)
_defconst("SCAN_SEC", 1.0)
_defconst("LOOPA_SEC", 1.0)
_defconst("LOOPB_SEC", 5.0)
_defconst("LOOPB_TOPN", 25)
_defconst("LOOPB_RR", 2)
_defconst("TP1_FRACTION", 0.5)
_defconst("TP1_ATR_MULT", 1.0)
_defconst("TRAIL_ATR_MULT", 2.0)
_defconst("ATR_MULT_STOP", 1.5)

_defconst("NEWS_POLL_SEC", 30.0)
_defconst("ORDER_POLL_SEC", 1.0)
_defconst("ORDER_REPRICE_SEC", 5.0)
_defconst("MAX_REPRICE_BPS_STOCK", 50.0)  # cap limit chasing for stocks
_defconst("MAX_REPRICE_BPS_CRYPTO", 150.0)  # cap limit chasing for crypto
_defconst("TRAIL_UPDATE_SEC", 5.0)
_defconst("MARKET_CLOSED_LOG_SEC", 60.0)
_defconst("FEED_SCAN_LOG_SEC", 30.0)
_defconst("FEED_ORDER_LOG_SEC", 2.0)
_defconst("SEEK_BLINK_MS", 350)
_defconst("THEME_ACCENT", "#00D1FF")  # UI accent

# Trade sizing / limits (Phase 2 defaults)
_defconst("TIME_STOP_MINUTES", 45)
_defconst("LOSS_ONLY_COOLDOWN_SEC", 10*60)
_defconst("MAX_TRADES_PER_HOUR", 4)
_defconst("MAX_TRADES_PER_DAY", 40)
_defconst("MAX_POSITIONS", 5)
_defconst("MAX_SYMBOL_EXPOSURE_PCT", 10.0)
_defconst("MAX_CRYPTO_POSITIONS", 3)  # keep in sync with Phase 2 prefs

# Seatbelts: circuit breaker + drawdown guard (Phase 2 defaults)
_defconst("CB_FAIL_WINDOW_SEC", 120.0)
_defconst("CB_MAX_CONSEC_API_FAILS", 5)
_defconst("CB_MAX_ORDER_REJECTS", 5)
_defconst("CB_STALE_DATA_SEC", 30.0)
_defconst("CB_RECOVERY_OK_STREAK", 10)

_defconst("DD_SOFT1_PCT", 1.0)
_defconst("DD_SOFT1_RISK_MULT", 0.7)
_defconst("DD_SOFT2_PCT", 2.0)
_defconst("DD_SOFT2_RISK_MULT", 0.4)
_defconst("DD_HARD_PCT", 3.5)
_defconst("DD_HARD_PAUSE_SEC", 30*60)
_defconst("DD_HARD_RECOVER_PCT", 2.5)

# News helpers (Phase 2 defaults)
_defconst("MACRO_WORDS", ["cpi","pce","ppi","jobs","payrolls","fomc","rate","inflation","gdp","fed","yield","treasury","recession"])
_defconst("RISK_ON", ["risk-on","bullish","rally","surge","beats","upgrade","record"])
_defconst("RISK_OFF", ["risk-off","selloff","downgrade","miss","lawsuit","probe","war","inflation"])



class NonRetryableError(RuntimeError):
    """Marker exception for HTTP errors we should NOT retry (auth/validation)."""
    pass

ROOT = (Path(sys.executable).resolve().parent if getattr(sys, "frozen", False) else Path(__file__).resolve().parent)
RES_RUNTIME = ROOT / "runtime"  # packaged resources (may be read-only)
RES_RUNTIME.mkdir(exist_ok=True)

# Persist user data across updates in AppData (Windows). Falls back to ROOT if APPDATA missing.
APPDATA_DIR = Path(os.getenv("APPDATA") or str(ROOT)) / "RelentlessExecution"
APPDATA_DIR.mkdir(parents=True, exist_ok=True)
# --- Launch-safe persistent paths (avoid NameError chains) ---
_defconst("ET_TZ", ZoneInfo("America/New_York"))
_defconst("KEYS_PATH", APPDATA_DIR / "keys.json")


def load_keys():
    # Return (key_id, secret, trade_base, data_base) from KEYS_PATH.
    # Used by SELF_TEST and emergency PANIC client creation.
    if not KEYS_PATH.exists():
        raise RuntimeError(f"Missing keys file: {KEYS_PATH}. Use Tools -> Edit Alpaca Keys...")
    cfg = json.loads(KEYS_PATH.read_text(encoding='utf-8-sig', errors='ignore') or '{}')
    key = str(cfg.get('key_id') or cfg.get('key') or '').strip()
    sec = str(cfg.get('secret') or cfg.get('secret_key') or '').strip()
    trade = str(cfg.get('trade_base') or cfg.get('trade') or 'https://paper-api.alpaca.markets').strip()
    data = str(cfg.get('data_base') or cfg.get('data') or 'https://data.alpaca.markets').strip()
    if not key or not sec:
        raise RuntimeError('Missing Alpaca key_id/secret in keys.json')
    return key, sec, trade, data
_defconst("APPSTATE_PATH", APPDATA_DIR / "app_state.json")
_defconst("SETTINGS_PATH", APPDATA_DIR / "settings.json")
_defconst("LOG_PATH", APPDATA_DIR / "app.log")
_defconst("PERF_PATH", APPDATA_DIR / "perf.json")
_defconst("JOURNAL_PATH", APPDATA_DIR / "trade_journal.csv")
_defconst("JOURNAL_SPOOL_PATH", APPDATA_DIR / "trade_journal_spool.csv")
_defconst("TRADE_EVENTS_CSV_PATH", APPDATA_DIR / "trade_events.csv")
_defconst("REPLAY_EVENTS_PATH", APPDATA_DIR / "replay_events.jsonl")
_defconst("ANALYTICS_PATH", APPDATA_DIR / "analytics.json")
_defconst("DIAG_DIR", APPDATA_DIR / "diagnostics")
# keep backward-compatible equity path names used elsewhere
_defconst("EQUITY_CSV_PATH_PAPER", APPDATA_DIR / "equity_history_paper.csv")
_defconst("EQUITY_CSV_PATH_LIVE",  APPDATA_DIR / "equity_history_live.csv")


# finalize heartbeat path after APPDATA_DIR exists
if globals().get("HEARTBEAT_PATH") is None:
    HEARTBEAT_PATH = APPDATA_DIR / "heartbeat.json"

# --- Data mode constants (used by Performance tab + equity history) ---
DATA_MODE_PAPER = "PAPER"
DATA_MODE_LIVE  = "LIVE"

def _normalize_data_mode(mode: str) -> str:
    m = (mode or DATA_MODE_PAPER).strip().upper()
    return DATA_MODE_LIVE if m.startswith("LIVE") else DATA_MODE_PAPER

def equity_csv_path(mode: str = DATA_MODE_PAPER) -> Path:
    """Return the per-mode equity history CSV path in %APPDATA%/RelentlessExecution."""
    m = _normalize_data_mode(mode)
    fname = "equity_history_live.csv" if m == DATA_MODE_LIVE else "equity_history_paper.csv"
    return APPDATA_DIR / fname

# --- Default trading configuration (used by UI defaults) ---
DEFAULT_STOCKS = ["SPY", "QQQ"]
DEFAULT_CRYPTO = ["BTCUSD", "ETHUSD", "SOLUSD", "LTCUSD", "DOGEUSD"]
DEFAULT_RISK_PCT = 0.25
DEFAULT_SLIP_BPS_STOCK = 5
DEFAULT_SLIP_BPS_CRYPTO = 20
DEFAULT_MAX_SPREAD_BPS_STOCK = 20
DEFAULT_MAX_SPREAD_BPS_CRYPTO = 60





def _load_settings() -> dict:
    """Load persistent UI settings from SETTINGS_PATH (JSON). Always returns a dict."""
    try:
        p = SETTINGS_PATH  # set via _defconst
        if p.exists():
            return json.loads(p.read_text(encoding="utf-8-sig", errors="ignore") or "{}") or {}
    except Exception:
        pass
    return {}

def _save_settings(d: dict) -> None:
    """Persist UI settings to SETTINGS_PATH (JSON). Fail-silent (never crash launch/connect)."""
    try:
        p = SETTINGS_PATH
        p.parent.mkdir(parents=True, exist_ok=True)
        _write_json_atomic(p, d or {}, indent=2)
    except Exception:
        pass



def _write_json_atomic(path: Path, data: dict, indent: int = 2):
    """Write JSON atomically (temp file + replace) to avoid corruption on crash."""
    try:
        path.parent.mkdir(parents=True, exist_ok=True)
        import os, json, tempfile
        fd, tmp = tempfile.mkstemp(dir=str(path.parent), prefix=f".{path.name}.", suffix=".tmp")
        try:
            with os.fdopen(fd, "w", encoding="utf-8-sig") as f:
                json.dump(data or {}, f, indent=indent)
            os.replace(tmp, path)
        except Exception:
            try:
                os.unlink(tmp)
            except Exception:
                pass
            raise
    except Exception:
        pass

def _ensure_settings() -> dict:
    s = _load_settings()
    if not SETTINGS_PATH.exists():
        _save_settings(s)
    return s


def gen_trade_id(symbol: str) -> str:
    """Short, stable, human-readable Trade ID."""
    sym = (symbol or "SYM").upper().replace("/", "")
    token = f"{random.getrandbits(32):08X}"
    return f"{sym}-{token}"


def _write_csv_row(path: Path, header: list, row: list) -> None:
    """
    Append one CSV row safely.

    Hotfix v8.6.8:
      - Detect Windows file locks (Excel/ONLYOFFICE) and do NOT silently drop rows.
      - Retry briefly, then spool journal rows to JOURNAL_SPOOL_PATH.
      - Log any write/spool failures to app.log so RUN_APP shows the reason.
    """
    def _is_locked_exc(e: Exception) -> bool:
        try:
            # Windows: PermissionError / OSError with WinError 32/33 when file is in use
            if isinstance(e, PermissionError):
                return True
            if isinstance(e, OSError):
                win = getattr(e, "winerror", None)
                if win in (32, 33):
                    return True
            msg = str(e).lower()
            if "being used by another process" in msg or "process cannot access the file" in msg:
                return True
        except Exception:
            pass
        return False

    def _log(line: str) -> None:
        try:
            append_log_line(line)
        except Exception:
            pass
        try:
            print(line)
        except Exception:
            pass

    def _append_row(p: Path) -> None:
        p.parent.mkdir(parents=True, exist_ok=True)
        write_header = (not p.exists()) or (p.stat().st_size == 0)
        with p.open("a", encoding="utf-8-sig", errors="ignore", newline="") as f:
            w = csv.writer(f)
            if write_header:
                w.writerow(header)
            w.writerow(row)

    # Best-effort journal schema upgrades (non-fatal)
    try:
        if path == JOURNAL_PATH:
            _upgrade_trade_journal_schema_if_needed()
    except Exception:
        pass

    # If we have a journal spool, try to flush it first (best-effort)
    try:
        if path == JOURNAL_PATH and "JOURNAL_SPOOL_PATH" in globals():
            sp = JOURNAL_SPOOL_PATH
            if isinstance(sp, Path) and sp.exists() and sp.stat().st_size > 0:
                try:
                    # Attempt to append spool contents into the main journal
                    with sp.open("r", encoding="utf-8-sig", errors="ignore", newline="") as fin:
                        lines = fin.read()
                    # If journal is locked, this will throw and we'll keep the spool
                    with path.open("a", encoding="utf-8-sig", errors="ignore", newline="") as fout:
                        fout.write(lines)
                    sp.unlink(missing_ok=True)  # type: ignore[arg-type]
                    _log(f"{dt.datetime.now().strftime('%H:%M:%S')}  Journal: flushed spool rows into {path}")
                except Exception as e:
                    if _is_locked_exc(e):
                        # keep spool, do not spam
                        pass
    except Exception:
        pass

    # Try a few times in case ONLYOFFICE/Excel is momentarily saving
    for attempt in range(5):
        try:
            _append_row(path)
            return
        except Exception as e:
            if _is_locked_exc(e):
                try:
                    time.sleep(0.2)
                except Exception:
                    pass
                continue
            _log(f"{dt.datetime.now().strftime('%H:%M:%S')} ERR CSV write failed: {path} ({e})")
            return

    # Still locked after retries: spool journal rows (only for trade_journal)
    try:
        if path == JOURNAL_PATH and "JOURNAL_SPOOL_PATH" in globals():
            sp = JOURNAL_SPOOL_PATH
            if isinstance(sp, Path):
                try:
                    _append_row(sp)
                    _log(f"{dt.datetime.now().strftime('%H:%M:%S')} WARN  Journal locked by another app; wrote row to spool: {sp}")
                except Exception as e:
                    _log(f"{dt.datetime.now().strftime('%H:%M:%S')} ERR Journal spool write failed: {sp} ({e})")
            return
    except Exception:
        pass

    # Fallback: log once (do not raise)
    _log(f"{dt.datetime.now().strftime('%H:%M:%S')} ERR CSV write dropped after retries: {path}")



def write_replay_event(*, kind: str, payload: dict) -> None:
    """Layer 7: JSONL event stream for deterministic replay/tuning."""
    try:
        REPLAY_EVENTS_PATH.parent.mkdir(parents=True, exist_ok=True)
        rec = {
            "kind": kind,
            "ts": payload.get("ts") or dt.datetime.now(tz=ET_TZ).isoformat(),
            "payload": payload,
        }
        with REPLAY_EVENTS_PATH.open("a", encoding="utf-8-sig", errors="ignore") as f:
            f.write(json.dumps(rec, ensure_ascii=False) + "\n")
    except Exception:
        pass


def write_trade_event(*, trade_id: str, event: str, symbol: str, side: str = "", qty: float = 0.0,
                     price: float = 0.0, pnl: float = 0.0, state: str = "", why: str = "", news: str = "",
                     meta: Optional[dict] = None) -> None:
    """Layer 4: canonical audit trail row."""
    try:
        ts = dt.datetime.now(tz=ET_TZ).isoformat()
        header = ["ts","trade_id","event","symbol","side","qty","price","pnl","state","why","news","meta_json"]
        row = [
            ts,
            trade_id or "",
            event or "",
            symbol or "",
            side or "",
            f"{float(qty or 0.0):.8f}",
            f"{float(price or 0.0):.8f}",
            f"{float(pnl or 0.0):.8f}",
            state or "",
            why or "",
            news or "",
            json.dumps(meta or {}, ensure_ascii=False),
        ]
        _write_csv_row(TRADE_EVENTS_CSV_PATH, header, row)
        write_replay_event(kind=event or "EVENT", payload={
            "ts": ts,
            "trade_id": trade_id,
            "symbol": symbol,
            "side": side,
            "qty": qty,
            "price": price,
            "pnl": pnl,
            "state": state,
            "why": why,
            "news": news,
            "meta": meta or {},
        })
    except Exception:
        pass



def write_trade_journal_row(*, trade_id: str, symbol: str, side: str, qty: float,
                           entry_price: float, exit_price: Optional[float], pnl: Optional[float],
                           stop_price: Optional[float] = None,
                           why: str = "",
                           why_verbose: str = "",
                           news: str = "",
                           notes: str = "") -> None:
    """Append a trade row to trade_journal.csv.

    - WHY stays compact (feed line).
    - WHY_VERBOSE stores the longer receipt (single-line separators for clean CSV).
    - NEWS fields are parsed from our standardized format_news_confidence output.
    """
    try:
        ts = dt.datetime.now(tz=ET_TZ).isoformat()

        # Keep CSV clean in Excel/ONLYOFFICE
        why = (why or "").replace("\r", " ").replace("\n", " ").strip()
        why_verbose = (why_verbose or "").replace("\r", " ").replace("\n", " ").strip()
        notes = (notes or "").replace("\r", " ").replace("\n", " ").strip()

        notional = abs((qty or 0.0) * (entry_price or 0.0))
        pnl_pct = (float(pnl) / notional * 100.0) if (pnl is not None and notional > 0) else 0.0

        nf = parse_news_fields(news or "")
        row = [
            ts,
            trade_id,
            symbol,
            side,
            f"{qty:.8f}",
            f"{entry_price:.8f}",
            (f"{float(exit_price):.8f}" if exit_price and float(exit_price) > 0 else ""),
            (f"{float(pnl):.4f}" if pnl is not None else ""),
            (f"{float(pnl_pct):.4f}" if (pnl is not None and notional > 0) else ""),
            (f"{float(stop_price):.8f}" if (stop_price is not None and float(stop_price) > 0) else ""),
            why,
            why_verbose,
            nf.get("news_conf",""),
            nf.get("news_pub_et",""),
            nf.get("news_age_m",""),
            nf.get("news_source",""),
            nf.get("news_headline",""),
            notes,
        ]
        _write_csv_row(JOURNAL_PATH, JOURNAL_HEADERS, row)
    except Exception:
        pass




def write_trade_receipt(*, trade_id: str, stage: str, receipt: dict) -> None:
    """Write per-trade JSON receipt(s) capturing WHY circumstances.

    New format:
      %APPDATA%\\RelentlessExecution\\trade_receipts\\<trade_id>\\<ts>_<stage>.json
      %APPDATA%\\RelentlessExecution\\trade_receipts\\<trade_id>\\latest.json

    We also keep a legacy append-only list at:
      %APPDATA%\\RelentlessExecution\\trade_receipts\\<trade_id>.json
    """
    try:
        if not trade_id:
            return
        safe_id = re.sub(r"[^A-Za-z0-9_\-\.]+", "_", str(trade_id))[:120]
        safe_stage = re.sub(r"[^A-Za-z0-9_\-\.]+", "_", str(stage or "stage"))[:64]
        TRADE_RECEIPTS_DIR.mkdir(parents=True, exist_ok=True)

        payload = {
            "app_version": APP_VERSION,
            "trade_id": safe_id,
            "stage": safe_stage,
            "ts": time.time(),
            "receipt": receipt if isinstance(receipt, dict) else {"value": str(receipt)},
        }

        # New folder-per-trade snapshots
        tdir = TRADE_RECEIPTS_DIR / safe_id
        tdir.mkdir(parents=True, exist_ok=True)
        ts_i = int(payload["ts"])
        snap_path = tdir / f"{ts_i}_{safe_stage}.json"
        snap_path.write_text(json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8-sig")
        (tdir / "latest.json").write_text(json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8-sig")

        # Legacy append-only list (best-effort)
        try:
            legacy_path = TRADE_RECEIPTS_DIR / f"{safe_id}.json"
            items = []
            if legacy_path.exists():
                try:
                    items = json.loads(legacy_path.read_text(encoding="utf-8-sig", errors="ignore")) or []
                except Exception:
                    items = []
            if not isinstance(items, list):
                items = []
            items.append(payload)
            legacy_path.write_text(json.dumps(items, indent=2, sort_keys=True), encoding="utf-8-sig")
        except Exception:
            pass
    except Exception:
        pass




def _max_drawdown_from_equity(rows) -> float:
    try:
        peak = None
        max_dd = 0.0
        for _, eq in rows:
            if eq is None:
                continue
            e = float(eq)
            if peak is None or e > peak:
                peak = e
            if peak and peak > 0:
                dd = (peak - e) / peak
                if dd > max_dd:
                    max_dd = dd
        return float(max_dd)
    except Exception:
        return 0.0


def compute_analytics() -> dict:
    """Layer 6: compute analytics from trade events + equity history."""
    out = {
        "updated_ts": dt.datetime.now(tz=ET_TZ).isoformat(),
        "trades": 0,
        "wins": 0,
        "losses": 0,
        "win_rate": 0.0,
        "avg_win": 0.0,
        "avg_loss": 0.0,
        "profit_factor": 0.0,
        "expectancy": 0.0,
        "net_pnl": 0.0,
        "max_drawdown_paper": 0.0,
        "max_drawdown_live": 0.0,
        "per_symbol": {},
    }

    try:
        pnl_by_id = {}
        sym_by_id = {}
        if TRADE_EVENTS_CSV_PATH.exists():
            with TRADE_EVENTS_CSV_PATH.open("r", encoding="utf-8-sig", errors="ignore") as f:
                r = csv.DictReader(f)
                for d in r:
                    tid = (d.get("trade_id") or "").strip()
                    ev = (d.get("event") or "").strip().upper()
                    sym = (d.get("symbol") or "").strip().upper()
                    pnl = _safe_float(d.get("pnl"), 0.0)
                    if tid:
                        sym_by_id.setdefault(tid, sym)
                        # Only count realized pnl events
                        if ev in ("TP1_FILLED","EXIT_FILLED","CLOSED"):
                            pnl_by_id[tid] = pnl_by_id.get(tid, 0.0) + float(pnl)

        total_pnls = [float(v) for v in pnl_by_id.values()]
        out["net_pnl"] = float(sum(total_pnls))
        out["trades"] = int(len(total_pnls))
        wins = [p for p in total_pnls if p > 0]
        losses = [p for p in total_pnls if p < 0]
        out["wins"] = int(len(wins))
        out["losses"] = int(len(losses))
        out["win_rate"] = float(len(wins) / max(1, len(total_pnls)))
        out["avg_win"] = float(sum(wins) / max(1, len(wins))) if wins else 0.0
        out["avg_loss"] = float(sum(losses) / max(1, len(losses))) if losses else 0.0
        gross_win = float(sum(wins))
        gross_loss = float(abs(sum(losses)))
        out["profit_factor"] = float((gross_win / gross_loss) if gross_loss > 0 else (float("inf") if gross_win > 0 else 0.0))
        out["expectancy"] = float(out["win_rate"] * out["avg_win"] + (1.0 - out["win_rate"]) * out["avg_loss"])

        # per-symbol summary
        per_sym = {}
        for tid, pnl in pnl_by_id.items():
            sym = sym_by_id.get(tid, "")
            if not sym:
                continue
            s = per_sym.setdefault(sym, {"trades": 0, "net_pnl": 0.0, "wins": 0, "losses": 0})
            s["trades"] += 1
            s["net_pnl"] += float(pnl)
            if pnl > 0:
                s["wins"] += 1
            elif pnl < 0:
                s["losses"] += 1
        out["per_symbol"] = per_sym

        # drawdowns
        out["max_drawdown_paper"] = _max_drawdown_from_equity(_load_equity_rows(DATA_MODE_PAPER))
        out["max_drawdown_live"] = _max_drawdown_from_equity(_load_equity_rows(DATA_MODE_LIVE))

    except Exception as e:
        out["error"] = str(e)

    try:
        ANALYTICS_PATH.write_text(json.dumps(out, indent=2), encoding="utf-8-sig")
    except Exception:
        pass
    return out


def export_diagnostics(reason: str = "manual") -> Optional[Path]:
    """Layer 8: Export a diagnostics zip (logs, journal, events, equity, settings) with keys redacted."""
    try:
        DIAG_DIR.mkdir(parents=True, exist_ok=True)
        ts = dt.datetime.now(tz=ET_TZ).strftime("%Y%m%d_%H%M%S")
        out_path = DIAG_DIR / f"diagnostics_{ts}_{reason}.zip"

        # Redact keys
        redacted = {}
        try:
            if KEYS_PATH.exists():
                cfg = json.loads(KEYS_PATH.read_text(encoding="utf-8-sig", errors="ignore") or "{}")
                if isinstance(cfg, dict):
                    redacted = json.loads(json.dumps(cfg))
                    alp = redacted.get("alpaca", {}) if isinstance(redacted.get("alpaca"), dict) else {}
                    if alp:
                        if "key_id" in alp:
                            alp["key_id"] = "REDACTED"
                        if "secret_key" in alp:
                            alp["secret_key"] = "REDACTED"
                        redacted["alpaca"] = alp
        except Exception:
            pass

        def add_file(z: zipfile.ZipFile, path: Path, arcname: str):
            try:
                if path and path.exists():
                    z.write(path, arcname)
            except Exception:
                pass

        with zipfile.ZipFile(out_path, "w", compression=zipfile.ZIP_DEFLATED) as z:
            add_file(z, LOG_PATH, "app.log")
            add_file(z, PERF_PATH, "perf.json")
            add_file(z, JOURNAL_PATH, "trade_journal.csv")
            add_file(z, TRADE_EVENTS_CSV_PATH, "trade_events.csv")
            add_file(z, REPLAY_EVENTS_PATH, "replay_events.jsonl")
            add_file(z, ANALYTICS_PATH, "analytics.json")
            add_file(z, APPDATA_DIR / "heartbeat.json", "heartbeat.json")
            add_file(z, Path.cwd() / "run_app.log", "run_app.log")
            add_file(z, Path.cwd() / "build_exe.log", "build_exe.log")
            add_file(z, EQUITY_CSV_PATH_PAPER, "equity_history_paper.csv")
            add_file(z, EQUITY_CSV_PATH_LIVE, "equity_history_live.csv")
            add_file(z, SETTINGS_PATH, "settings.json")
            # include redacted keys + environment snapshot
            try:
                z.writestr("keys_redacted.json", json.dumps(redacted or {}, indent=2))
            except Exception:
                pass
            env = {
                "app": APP_NAME,
                "python": sys.version,
                "platform": platform.platform(),
                "frozen": bool(getattr(sys, "frozen", False)),
                "root": str(ROOT),
                "appdata": str(APPDATA_DIR),
            }
            z.writestr("env.json", json.dumps(env, indent=2))

        # keep only the most recent N diagnostics
        try:
            keep = int(_load_settings().get("diagnostics_keep_last", 10))
            zips = sorted(DIAG_DIR.glob("diagnostics_*.zip"), key=lambda p: p.stat().st_mtime, reverse=True)
            for p in zips[keep:]:
                try:
                    p.unlink()
                except Exception:
                    pass
        except Exception:
            pass

        return out_path
    except Exception:
        return None


def install_crash_hook() -> None:
    """Install a crash hook that writes a diagnostics zip on unhandled exceptions."""
    prev = sys.excepthook

    def _hook(exctype, value, tb):
        try:
            msg = "".join(traceback.format_exception(exctype, value, tb))
            append_log_line("CRASH:\n" + msg)
            s = _load_settings()
            if s.get("auto_export_diagnostics_on_crash", True):
                export_diagnostics("crash")
        except Exception:
            pass
        try:
            prev(exctype, value, tb)
        except Exception:
            pass

    sys.excepthook = _hook

def append_log_line(line: str):
    try:
        LOG_PATH.parent.mkdir(exist_ok=True)

        # Prevent runaway multi-GB logs from causing sluggish IO / "Not Responding".
        try:
            if LOG_PATH.exists() and LOG_PATH.stat().st_size > 50 * 1024 * 1024:
                ts = dt.datetime.now().strftime("%Y%m%d_%H%M%S")
                rotated = LOG_PATH.with_name(f"app_{ts}.log")
                try:
                    LOG_PATH.rename(rotated)
                except Exception:
                    # If rename fails (file locked), fall back to truncation.
                    with LOG_PATH.open("w", encoding="utf-8-sig", errors="ignore") as f_trunc:
                        f_trunc.write("")
        except Exception:
            pass

        with LOG_PATH.open("a", encoding="utf-8-sig", errors="ignore") as f:
            f.write(line.rstrip("\n") + "\n")
    except Exception:
        pass
def record_equity_snapshot(acct: dict, mode: str = DATA_MODE_PAPER):
    """Append one snapshot per minute to a CSV for 24h/WTD/MTD/All-time and charts."""
    try:
        ts = time.time()
        # bucket to minute
        minute_bucket = int(ts // 60)
        equity = _safe_float(acct.get("equity"))
        bp = _safe_float(acct.get("buying_power") or acct.get("regt_buying_power") or acct.get("cash"))
        upl = _safe_float(acct.get("unrealized_pl"))
        row = [str(ts), str(minute_bucket), f"{equity:.6f}", f"{bp:.6f}", f"{upl:.6f}"]

        # avoid duplicate minute buckets
        last_bucket = None
        path = equity_csv_path(mode)
        if path.exists():
            try:
                with path.open("rb") as f:
                    f.seek(0, 2)
                    size = f.tell()
                    f.seek(max(0, size - 4096), 0)
                    tail = f.read().decode("utf-8", "ignore").splitlines()
                for ln in reversed(tail):
                    parts = ln.split(",")
                    if len(parts) >= 2 and parts[1].isdigit():
                        last_bucket = int(parts[1]); break
            except Exception:
                last_bucket = None

        if last_bucket == minute_bucket:
            return

        header_needed = not path.exists()
        with path.open("a", encoding="utf-8-sig", errors="ignore", newline="") as f:
            w = csv.writer(f)
            if header_needed:
                w.writerow(["ts", "minute_bucket", "equity", "buying_power", "unrealized_pl"])
            w.writerow(row)
    except Exception:
        pass

def _load_equity_rows(mode: str = DATA_MODE_PAPER, limit_rows: int = 50000):
    """Load equity history (ts, equity). Limits rows for safety."""
    path = equity_csv_path(mode)
    if not path.exists():
        return []
    rows = []
    try:
        with path.open("r", encoding="utf-8-sig", errors="ignore") as f:
            r = csv.DictReader(f)
            for d in r:
                ts = _safe_float(d.get("ts"))
                eq = _safe_float(d.get("equity"))
                if ts > 0:
                    rows.append((ts, eq))
        if len(rows) > limit_rows:
            rows = rows[-limit_rows:]
    except Exception:
        return []
    return rows

def _equity_at_or_before(rows, target_ts: float):
    """Return equity from the last row at/before target_ts."""
    best = None
    for ts, eq in rows:
        if ts <= target_ts:
            best = eq
        else:
            break
    return best

def compute_period_pls(now_equity: float, mode: str = DATA_MODE_PAPER):
    """Returns dict for 24h, wtd, mtd, all using equity deltas."""
    rows = _load_equity_rows(mode)
    if not rows or now_equity is None:
        return {"24h": None, "wtd": None, "mtd": None, "all": None}

    now_ts = time.time()

    # 24h
    eq_24 = _equity_at_or_before(rows, now_ts - 86400)

    # WTD (Monday 00:00 ET)
    now_dt = dt.datetime.fromtimestamp(now_ts, tz=ET_TZ)
    week_start = (now_dt - dt.timedelta(days=now_dt.weekday())).replace(hour=0, minute=0, second=0, microsecond=0)
    eq_wtd = _equity_at_or_before(rows, week_start.timestamp())

    # MTD
    month_start = now_dt.replace(day=1, hour=0, minute=0, second=0, microsecond=0)
    eq_mtd = _equity_at_or_before(rows, month_start.timestamp())

    # All time
    eq_all = rows[0][1] if rows else None

    def d(a):
        return (now_equity - a) if a is not None else None

    return {"24h": d(eq_24), "wtd": d(eq_wtd), "mtd": d(eq_mtd), "all": d(eq_all)}

def compute_dtd_pl(now_equity: float, mode: str = DATA_MODE_PAPER):
    """Day-to-date P/L (since 00:00 ET). Returns (pl, day_start_equity)."""
    rows = _load_equity_rows(mode)
    if not rows or now_equity is None:
        return (None, None)
    now_ts = time.time()
    now_dt = dt.datetime.fromtimestamp(now_ts, tz=ET_TZ)
    day_start = now_dt.replace(hour=0, minute=0, second=0, microsecond=0)
    eq0 = _equity_at_or_before(rows, day_start.timestamp())
    if eq0 is None:
        return (None, None)
    return (float(now_equity) - float(eq0), float(eq0))

def compute_wtd_pl(now_equity: float, mode: str = DATA_MODE_PAPER):
    """Week-to-date P/L (since Monday 00:00 ET). Returns (pl, week_start_equity)."""
    rows = _load_equity_rows(mode)
    if not rows or now_equity is None:
        return (None, None)
    now_ts = time.time()
    now_dt = dt.datetime.fromtimestamp(now_ts, tz=ET_TZ)
    week_start = (now_dt - dt.timedelta(days=now_dt.weekday())).replace(hour=0, minute=0, second=0, microsecond=0)
    eq0 = _equity_at_or_before(rows, week_start.timestamp())
    if eq0 is None:
        return (None, None)
    return (float(now_equity) - float(eq0), float(eq0))

def fmt_pct(pct: Optional[float]):
    try:
        if pct is None:
            return "--"
        return f"{pct:+.2f}%"
    except Exception:
        return "--"

def fmt_money(x, signed: bool = False):
    """Format a float-like value as dollars.

    signed=True -> prefixes + / - and formats absolute value (e.g., +$12.34, -$12.34).
    """
    try:
        if x is None:
            return "--"
        v = float(x)
        if signed:
            sign = "+" if v > 0 else "-" if v < 0 else ""
            s = f"${abs(v):,.2f}"
            return f"{sign}{s}" if sign else s
        return f"${v:,.2f}"
    except Exception:
        return "--"

def stocks_market_open() -> bool:
    t = now_et()
    if t.weekday() >= 5:
        return False
    open_t = t.replace(hour=9, minute=30, second=0, microsecond=0)
    close_t = t.replace(hour=16, minute=0, second=0, microsecond=0)
    return open_t <= t <= close_t



def stocks_extended_session() -> str:
    """REGULAR, PRE, AFTER, OVERNIGHT, CLOSED (ET)."""
    t = now_et()
    wd = t.weekday()  # Mon=0..Sun=6
    h, m = t.hour, t.minute
    if wd >= 5:
        if wd == 6 and h >= 20:
            return "OVERNIGHT"
        return "CLOSED"
    if h < 4:
        return "OVERNIGHT"
    if h < 9 or (h == 9 and m < 30):
        return "PRE"
    if (h == 9 and m >= 30) or (9 < h < 16) or (h == 16 and m == 0):
        return "REGULAR"
    if (h == 16 and m > 0) or (16 < h < 20) or (h == 20 and m == 0):
        return "AFTER"
    if h > 20:
        return "OVERNIGHT"
    return "CLOSED"

def is_extended_stock_session(sess: str) -> bool:
    return sess in ("PRE", "AFTER", "OVERNIGHT")



def is_crypto_symbol(sym: str) -> bool:
    s = (sym or "").upper().strip()
    return ("/" in s) or (s.endswith("USD") and len(s) >= 6)

def _pos_float(p: dict, key: str, default: float = 0.0) -> float:
    try:
        return float(p.get(key, default))
    except Exception:
        return default

def is_dust_crypto_position(p: dict, min_notional: float = 1.0) -> bool:
    """True if a crypto position is so small Alpaca likely won't allow a closing order (min notional/qty)."
    This prevents thrash and user-visible 'stuck' dust positions.
    """
    try:
        sym = str(p.get("symbol",""))
        if not is_crypto_symbol(sym):
            return False
        qty = abs(_pos_float(p, "qty", 0.0))
        price = abs(_pos_float(p, "current_price", 0.0))
        notional = qty * price
        return notional < float(min_notional)
    except Exception:
        return False


def crypto_data_symbol(sym: str) -> str:
    """Prefer BTC/USD style for Alpaca crypto market-data endpoints."""
    s = (sym or "").upper().strip()
    if "/" in s:
        return s
    if s.endswith("USD") and len(s) >= 6:
        return f"{s[:-3]}/USD"
    return s


def norm_symbol(sym: str) -> str:
    """Normalize symbols for internal comparisons.

    Alpaca crypto positions often arrive as BTCUSD while market-data uses BTC/USD.
    We normalize to BTCUSD-style (remove '/'), keep stocks unchanged.
    """
    s = (sym or "").upper().strip()
    if "/" in s:
        s = s.replace("/", "")
    return s




def normalize_symbol(sym: str) -> str:
    """Normalize symbols for comparing broker symbols (DOGE/USD vs DOGEUSD)."""
    return norm_symbol(sym)
class AlpacaClient:
    def __init__(self, key_id: str, secret: str, trade_base: str, data_base: str):
        self.key_id = key_id
        self.secret = secret
        self.trade_base = trade_base.rstrip("/")
        self.data_base = data_base.rstrip("/")

        self.session = requests.Session()
        try:
            adapter = requests.adapters.HTTPAdapter(pool_connections=20, pool_maxsize=50)
            self.session.mount("https://", adapter)
        except Exception:
            pass
        self._max_attempts = 6

    def _sleep_backoff(self, attempt: int):
        # exponential backoff with jitter, capped
        base = min(8.0, 0.25 * (2 ** max(0, attempt-1)))
        time.sleep(base + random.random() * 0.25)

    def _request(self, method: str, url: str, *, params=None, json_payload=None, timeout: float = 6.0):
        """Resilient REST helper.

        Notes:
        - 401/403 are NOT retried. They include response body details.
        - 429/5xx/timeouts are retried with backoff.
        - Default timeout is intentionally short to avoid watchdog false positives.
        """
        last_err = None
        for attempt in range(1, self._max_attempts + 1):
            try:
                r = self.session.request(
                    method,
                    url,
                    headers=self._headers(),
                    params=params,
                    json=json_payload,
                    timeout=timeout,
                )

                # Fail fast on auth/permission (do not retry)
                if r.status_code in (401, 403):
                    body = ''
                    try:
                        j = r.json()
                        body = j.get('message') or j.get('error') or str(j)
                    except Exception:
                        try:
                            body = (r.text or '').strip()
                        except Exception:
                            body = ''
                    body = (body or '').strip()
                    if len(body) > 300:
                        body = body[:297] + '...'
                    raise NonRetryableError(f"HTTP {r.status_code} Forbidden/Auth: {body or 'Request not permitted'}")

                # Fail fast on validation errors (common on /v2/orders): include response body + short payload
                if r.status_code in (400, 422):
                    body = ''
                    code = r.status_code
                    try:
                        j = r.json()
                        # Alpaca usually returns {"code":..., "message":...}
                        body = j.get('message') or j.get('error') or str(j)
                    except Exception:
                        try:
                            body = (r.text or '').strip()
                        except Exception:
                            body = ''
                    body = (body or '').strip()
                    if len(body) > 500:
                        body = body[:497] + '...'
                    p = json_payload if isinstance(json_payload, dict) else None
                    p_txt = ''
                    if p:
                        # keep compact + safe
                        keys_keep = [
                            'symbol','side','type','time_in_force','qty','notional',
                            'limit_price','stop_price','trail_price','trail_percent','extended_hours'
                        ]
                        p_slim = {k: p.get(k) for k in keys_keep if k in p}
                        p_txt = f" payload={p_slim}"
                    raise NonRetryableError(f"HTTP {code} Unprocessable Entity: {body}{p_txt}")

                # Retry transient / rate limit
                if r.status_code in (408, 425, 429, 500, 502, 503, 504):
                    last_err = RuntimeError(f"HTTP {r.status_code}: transient")
                    self._sleep_backoff(attempt)
                    continue

                r.raise_for_status()
                return r

            except Exception as e:
                # Do not retry non-retryable failures (auth/validation)
                if isinstance(e, NonRetryableError):
                    raise
                last_err = e
                if attempt < self._max_attempts:
                    self._sleep_backoff(attempt)
                    continue
                raise

        if last_err:
            raise last_err
        raise RuntimeError('Request failed')


    def cancel_all_orders(self):
        # DELETE /v2/orders
        r = self._request('DELETE', f"{self.trade_base}/v2/orders")
        return True

    def close_all_positions(self):
        # DELETE /v2/positions
        r = self._request('DELETE', f"{self.trade_base}/v2/positions")
        return r.json() if r is not None else True

    def close_position(self, symbol: str, qty: Optional[float] = None):
        """Close an open position. Alpaca returns 404 if the position is already flat; treat as success."""
        # Positions endpoint uses "BTCUSD" style symbols (no slash)
        sym = norm_symbol(symbol)
        params: Dict[str, str] = {}
        if qty is not None:
            params["qty"] = str(qty)
        try:
            # IMPORTANT: use full base URL (trade_base); relative URLs will break requests
            r = self._request("DELETE", f"{self.trade_base}/v2/positions/{sym}", params=params)
            try:
                return r.json() if r is not None and getattr(r, "content", b"") else True
            except Exception:
                return True
        except requests.HTTPError as e:
            resp = getattr(e, "response", None)
            if resp is not None and getattr(resp, "status_code", None) == 404:
                return True
            raise
        except Exception as e:
            code = getattr(getattr(e, "response", None), "status_code", None)
            if code == 404:
                return True
            raise


    def _headers(self):
        return {
            "APCA-API-KEY-ID": self.key_id,
            "APCA-API-SECRET-KEY": self.secret,
            "Content-Type": "application/json",
        }

    def get_account(self):
        r = self._request("GET", f"{self.trade_base}/v2/account", timeout=4)
        if r.status_code == 401:
            raise RuntimeError("401 Unauthorized: Alpaca rejected your API key/secret (wrong, disabled, or pasted incorrectly).")
        r.raise_for_status()
        return r.json()

    def get_clock(self):
        """Get market clock (primarily for stock market open/closed).

        Uses /v2/clock.
        """
        r = self._request("GET", f"{self.trade_base}/v2/clock", timeout=4)
        r.raise_for_status()
        return r.json()

    def get_positions(self):
        r = self._request("GET", f"{self.trade_base}/v2/positions", timeout=4)
        r.raise_for_status()
        return r.json()

    def list_orders(self, status: str = "open", limit: int = 500, nested: bool = True):
        """Return orders from /v2/orders (default: open orders)."""
        params = {"status": status, "limit": int(limit)}
        if nested:
            params["nested"] = "true"
        r = self._request("GET", f"{self.trade_base}/v2/orders", params=params, timeout=4)
        r.raise_for_status()
        return r.json()

    def get_order(self, order_id: str):
        r = self._request("GET", f"{self.trade_base}/v2/orders/{order_id}", timeout=4)
        r.raise_for_status()
        return r.json()

    def cancel_order(self, order_id: str):
        r = self._request("DELETE", f"{self.trade_base}/v2/orders/{order_id}", timeout=4)
        if r.status_code in (204, 404):
            return True
        r.raise_for_status()
        return True

    def _fmt_price_str(self, symbol: str, price: float) -> str:
        """Format prices to valid tick sizes.

        - Stocks: pennies (2 decimals)
        - Crypto: allow 6 decimals
        """
        try:
            p = float(price)
        except Exception:
            return str(price)
        if is_crypto_symbol(symbol):
            return str(round(p, 6))
        return f"{round(p, 2):.2f}"

    def replace_order(self, order_id: str, symbol: Optional[str] = None, limit_price: Optional[float] = None, qty: Optional[float] = None):
        payload = {}
        if limit_price is not None:
            if symbol:
                payload["limit_price"] = self._fmt_price_str(symbol, float(limit_price))
            else:
                payload["limit_price"] = str(round(float(limit_price), 6))
        if qty is not None:
            payload["qty"] = str(qty)
        r = self._request("PATCH", f"{self.trade_base}/v2/orders/{order_id}", json_payload=payload, timeout=4)
        r.raise_for_status()
        return r.json()

    def get_asset(self, symbol: str):
        r = self._request("GET", f"{self.trade_base}/v2/assets/{symbol}", timeout=4)
        r.raise_for_status()
        return r.json()

    def submit_order_market(self, symbol: str, side: str, qty: float, tif: str):
        payload = {"symbol": symbol, "qty": str(qty), "side": side.lower(), "type": "market", "time_in_force": tif}
        r = self._request("POST", f"{self.trade_base}/v2/orders", json_payload=payload, timeout=4)
        r.raise_for_status()
        return r.json()

    def submit_order_limit(self, symbol: str, side: str, qty: float, tif: str, limit_price: float, extended_hours: bool = False):
        payload = {
            "symbol": symbol,
            "qty": str(qty),
            "side": side.lower(),
            "type": "limit",
            "time_in_force": tif,
            "limit_price": self._fmt_price_str(symbol, float(limit_price)),
        }
        # Extended hours eligibility: limit + DAY only
        if extended_hours:
            payload["extended_hours"] = True
            payload["time_in_force"] = "day"
        r = self._request("POST", f"{self.trade_base}/v2/orders", json_payload=payload, timeout=4)
        r.raise_for_status()
        return r.json()

    def submit_order_stop(self, symbol: str, side: str, qty: float, tif: str, stop_price: float):
        """Stock stop order (stop -> market).

        Crypto does not support 'stop' (only stop_limit). Caller should use submit_order_stop_limit for crypto.
        """
        payload = {
            "symbol": symbol,
            "qty": str(qty),
            "side": side.lower(),
            "type": "stop",
            "time_in_force": tif,
            "stop_price": self._fmt_price_str(symbol, float(stop_price)),
        }
        r = self._request("POST", f"{self.trade_base}/v2/orders", json_payload=payload, timeout=4)
        r.raise_for_status()
        return r.json()

    def submit_order_stop_limit(self, symbol: str, side: str, qty: float, tif: str, stop_price: float, limit_price: float):
        """Stop limit order (needed for crypto; also valid for stocks)."""
        payload = {
            "symbol": symbol,
            "qty": str(qty),
            "side": side.lower(),
            "type": "stop_limit",
            "time_in_force": tif,
            "stop_price": self._fmt_price_str(symbol, float(stop_price)),
            "limit_price": self._fmt_price_str(symbol, float(limit_price)),
        }
        r = self._request("POST", f"{self.trade_base}/v2/orders", json_payload=payload, timeout=4)
        r.raise_for_status()
        return r.json()

    def submit_order_trailing_stop(self, symbol: str, side: str, qty: float, tif: str, *, trail_price: Optional[float] = None, trail_percent: Optional[float] = None):
        """Trailing stop order (stocks).

        Alpaca supports trailing stop as a single order; it is not currently supported as a bracket leg.
        Use either trail_price or trail_percent.
        """
        payload = {
            "symbol": symbol,
            "qty": str(qty),
            "side": side.lower(),
            "type": "trailing_stop",
            "time_in_force": tif,
        }
        if trail_price is not None:
            payload["trail_price"] = self._fmt_price_str(symbol, float(trail_price))
        if trail_percent is not None:
            payload["trail_percent"] = str(round(float(trail_percent), 6))
        r = self._request("POST", f"{self.trade_base}/v2/orders", json_payload=payload, timeout=4)
        r.raise_for_status()
        return r.json()

    def get_bars(self, symbol: str, timeframe: str, limit: int = 200):
        hdr = self._headers()
        if not is_crypto_symbol(symbol):
            url = f"{self.data_base}/v2/stocks/{symbol}/bars"
            r = self._request("GET", url, params={"timeframe": timeframe, "limit": limit}, timeout=4)
            r.raise_for_status()
            return r.json().get("bars", [])
        else:
            pair = crypto_data_symbol(symbol)
            url = f"{self.data_base}/v1beta3/crypto/us/bars"
            tf_delta = _tf_to_timedelta(timeframe)
            end = dt.datetime.now(dt.timezone.utc)
            # add buffer so broker has enough history
            start = end - (tf_delta * int(limit + 50))
            params = {"symbols": pair, "timeframe": timeframe, "limit": limit, "start": _utc_rfc3339(start), "end": _utc_rfc3339(end)}
            r = self._request("GET", url, params=params, timeout=4)
            if r.status_code in (400, 404):
                url2 = f"{self.data_base}/v1beta2/crypto/bars"
                r2 = requests.get(url2, headers=hdr, params={"symbols": pair, "timeframe": timeframe, "limit": limit}, timeout=4)
                r2.raise_for_status()
                data = r2.json().get("bars", {})
                return data.get(pair, data.get(symbol, []))
            r.raise_for_status()
            data = r.json().get("bars", {})
            return data.get(pair, data.get(symbol, []))

    def get_latest_quote(self, symbol: str):
        hdr = self._headers()
        try:
            if not is_crypto_symbol(symbol):
                url = f"{self.data_base}/v2/stocks/{symbol}/quotes/latest"
                r = requests.get(url, headers=hdr, timeout=4)
                r.raise_for_status()
                q = r.json().get("quote", {})
                return (float(q["bp"]) if q.get("bp") else None, float(q["ap"]) if q.get("ap") else None)
            else:
                pair = crypto_data_symbol(symbol)
                url = f"{self.data_base}/v1beta3/crypto/us/latest/quotes"
                r = self._request("GET", url, params={"symbols": pair}, timeout=4)
                if r.status_code == 404:
                    return (None, None)
                r.raise_for_status()
                js = r.json()
                q = js.get("quotes", {}).get(pair, {}) or js.get("quotes", {}).get(symbol, {})
                return (float(q["bp"]) if q.get("bp") else None, float(q["ap"]) if q.get("ap") else None)
        except Exception:
            return (None, None)


    def get_latest_quotes_bulk(self, symbols, chunk: int = 200):
        """Return dict key->(bid,ask).
        Stocks keys use symbol. Crypto keys use BTC/USD format.
        """
        out = {}
        syms = [s for s in (symbols or []) if s]
        # stocks bulk
        stocks = [s.upper() for s in syms if not is_crypto_symbol(s)]
        for i in range(0, len(stocks), chunk):
            part = stocks[i:i+chunk]
            if not part:
                continue
            url = f"{self.data_base}/v2/stocks/quotes/latest"
            r = self._request("GET", url, params={"symbols": ",".join(part)}, timeout=4)
            r.raise_for_status()
            data = r.json().get("quotes", {})
            for sym,q in data.items():
                bid = float(q.get("bp") or 0) or None
                ask = float(q.get("ap") or 0) or None
                out[sym] = (bid, ask)

        # crypto bulk
        csyms = [crypto_data_symbol(s) for s in syms if is_crypto_symbol(s)]
        for i in range(0, len(csyms), chunk):
            part = csyms[i:i+chunk]
            if not part:
                continue
            url = f"{self.data_base}/v1beta3/crypto/us/latest/quotes"
            r = self._request("GET", url, params={"symbols": ",".join(part)}, timeout=4)
            if r.status_code in (401,403):
                # caller can handle
                raise RuntimeError(f"Crypto quotes forbidden ({r.status_code})")
            r.raise_for_status()
            data = r.json().get("quotes", {})
            for sym,q in data.items():
                bid = float(q.get("bp") or 0) or None
                ask = float(q.get("ap") or 0) or None
                out[sym] = (bid, ask)

        return out

    def list_assets(self):
        """List active US equities. Used to build large universes."""
        r = requests.get(f"{self.trade_base}/v2/assets", headers=self._headers(), params={"status":"active", "asset_class":"us_equity"}, timeout=4)
        r.raise_for_status()
        return r.json()

    def get_news(self, symbols, limit: int = 5):
        """Market Data news (stocks + crypto).

        Endpoint per Alpaca docs: GET https://data.alpaca.markets/v1beta1/news with `symbols` comma list.
        Some subscriptions may return 403 ("Subscription does not permit querying news").
        """
        syms = [s.strip().upper() for s in (symbols or []) if s and str(s).strip()]
        if not syms:
            return []
        limit = int(max(1, min(50, int(limit or 5))))
        url = f"{self.data_base}/v1beta1/news"
        r = self._request("GET", url, params={"symbols": ",".join(syms), "limit": limit}, timeout=4)
        # Provide a predictable error string for subscription-gated responses.
        if r.status_code == 403:
            msg = ""
            try:
                j = r.json()
                msg = str(j.get("message") or j.get("error") or j)
            except Exception:
                msg = (r.text or "").strip()
            raise RuntimeError(f"403 Forbidden (news): {msg}")
        r.raise_for_status()
        try:
            j = r.json()
        except Exception:
            return []
        return j.get('news', []) or j.get('data', []) or []


def _parse_iso_ts(s: str) -> Optional[dt.datetime]:
    """Parse common ISO timestamps from Alpaca news into timezone-aware UTC datetimes."""
    if not s:
        return None
    s = str(s).strip()
    if not s:
        return None
    try:
        # handle trailing 'Z'
        if s.endswith('Z'):
            s = s[:-1] + '+00:00'
        d = dt.datetime.fromisoformat(s)
        if d.tzinfo is None:
            d = d.replace(tzinfo=dt.timezone.utc)
        return d.astimezone(dt.timezone.utc)
    except Exception:
        return None


def format_news_confidence(news: dict) -> str:
    """Return a standardized NEWS string with confidence + publish time + age.

    Output example:
      [ALPACA:MED pub=2026-01-23 15:32 ET age=29m] Headline (source)
    """
    try:
        if not isinstance(news, dict):
            return ""
        headline = str(news.get("headline") or "").strip()
        source = str(news.get("source") or news.get("author") or "alpaca").strip()

        pub = None
        for k in ("created_at", "updated_at", "time", "timestamp"):
            v = news.get(k)
            if v:
                pub = _parse_iso_ts(str(v))
                if pub:
                    break

        now_utc = dt.datetime.now(dt.timezone.utc)
        age_m = 0
        pub_et_str = "n/a"
        if pub:
            try:
                if pub.tzinfo is None:
                    pub = pub.replace(tzinfo=dt.timezone.utc)
                age_m = int(max(0, (now_utc - pub.astimezone(dt.timezone.utc)).total_seconds() // 60))
                pub_et_str = pub.astimezone(ET_TZ).strftime("%Y-%m-%d %H:%M ET")
            except Exception:
                age_m = 0
                pub_et_str = "n/a"

        if pub is None:
            conf = "STALE"
        elif age_m <= 15:
            conf = "HIGH"
        elif age_m <= 60:
            conf = "MED"
        elif age_m <= 240:
            conf = "LOW"
        else:
            conf = "STALE"

        if not headline:
            headline = "(no headline)"
        return f"[ALPACA:{conf} pub={pub_et_str} age={age_m}m] {headline} ({source})"
    except Exception:
        return ""




def journal_row(kind: str, symbol: str, side: str, qty: float, price: float, pnl: float, tag: str, reason: str, votes: int = 0):
    """Append a simple trade journal row. Safe/no-throw."""
    try:
        JOURNAL_PATH.parent.mkdir(parents=True, exist_ok=True)
        header = ["ts","kind","symbol","side","qty","price","pnl","tag","reason","votes"]
        row = [dt.datetime.now(tz=ET_TZ).isoformat(), kind, symbol, side, f"{qty:.6f}", f"{price:.6f}", f"{pnl:.6f}", tag, reason, str(int(votes))]
        write_header = not JOURNAL_PATH.exists()
        with JOURNAL_PATH.open('a', encoding='utf-8-sig', errors='ignore', newline='') as f:
            w = csv.writer(f)
            if write_header:
                w.writerow(header)
            w.writerow(row)
    except Exception:
        pass


def perf_update(perf: dict, pnl: float):
    """Update simple win/loss counters."""
    try:
        perf.setdefault('trades', 0)
        perf.setdefault('wins', 0)
        perf.setdefault('losses', 0)
        perf['trades'] += 1
        if pnl >= 0:
            perf['wins'] += 1
        else:
            perf['losses'] += 1
        PERF_PATH.write_text(json.dumps(perf, indent=2), encoding='utf-8-sig')
    except Exception:
        pass


def _tf_to_timedelta(timeframe: str) -> dt.timedelta:
    tf = (timeframe or '').strip()
    # Accept: '1Min','5Min','15Min','1Hour','1Day' + also lowercase like '1m'
    m = re.match(r'^(\d+)(Min|Hour|Day|Week|Month)$', tf, re.I)
    if m:
        n = int(m.group(1))
        unit = m.group(2).lower()
        if unit == 'min':
            return dt.timedelta(minutes=n)
        if unit == 'hour':
            return dt.timedelta(hours=n)
        if unit == 'day':
            return dt.timedelta(days=n)
        if unit == 'week':
            return dt.timedelta(weeks=n)
        if unit == 'month':
            return dt.timedelta(days=30*n)
    m2 = re.match(r'^(\d+)(m|h|d)$', tf, re.I)
    if m2:
        n = int(m2.group(1))
        unit = m2.group(2).lower()
        if unit == 'm':
            return dt.timedelta(minutes=n)
        if unit == 'h':
            return dt.timedelta(hours=n)
        if unit == 'd':
            return dt.timedelta(days=n)
    # default 1 minute
    return dt.timedelta(minutes=1)


def _utc_rfc3339(ts: dt.datetime) -> str:
    if ts.tzinfo is None:
        ts = ts.replace(tzinfo=dt.timezone.utc)
    ts = ts.astimezone(dt.timezone.utc)
    return ts.replace(microsecond=0).isoformat().replace('+00:00', 'Z')



# ---------------- Indicators (minimal, dependency-free) ----------------

def _bars_to_ohlcv(bars):
    """Convert Alpaca bars list to arrays. Supports both v2 and v1beta crypto shapes."""
    o=h=l=c=v=None
    opens=[]; highs=[]; lows=[]; closes=[]; vols=[]
    for b in (bars or []):
        if not isinstance(b, dict):
            continue
        def g(*keys, default=None):
            for k in keys:
                if k in b and b[k] is not None:
                    return b[k]
            return default
        o = g('o','open'); h = g('h','high'); l = g('l','low'); c = g('c','close'); v = g('v','volume', default=0)
        try:
            opens.append(float(o)); highs.append(float(h)); lows.append(float(l)); closes.append(float(c)); vols.append(float(v or 0))
        except Exception:
            continue
    return opens, highs, lows, closes, vols


def ema(series, period: int):
    period = int(period)
    if not series or period <= 1:
        return None
    k = 2.0 / (period + 1.0)
    e = float(series[0])
    for x in series[1:]:
        e = (float(x) * k) + (e * (1.0 - k))
    return e


def rsi(series, period: int = 14):
    period = int(period)
    if not series or len(series) < period + 1:
        return None
    gains = 0.0
    losses = 0.0
    for i in range(1, period + 1):
        d = float(series[i]) - float(series[i-1])
        if d >= 0:
            gains += d
        else:
            losses -= d
    avg_gain = gains / period
    avg_loss = losses / period
    for i in range(period + 1, len(series)):
        d = float(series[i]) - float(series[i-1])
        g = d if d > 0 else 0.0
        l = (-d) if d < 0 else 0.0
        avg_gain = (avg_gain * (period - 1) + g) / period
        avg_loss = (avg_loss * (period - 1) + l) / period
    if avg_loss <= 1e-12:
        return 100.0
    rs = avg_gain / avg_loss
    return 100.0 - (100.0 / (1.0 + rs))


def atr(highs, lows, closes, period: int = 14):
    period = int(period)
    if not highs or not lows or not closes or len(closes) < period + 1:
        return None
    trs = []
    for i in range(1, len(closes)):
        h = float(highs[i]); l = float(lows[i]); pc = float(closes[i-1])
        tr = max(h - l, abs(h - pc), abs(l - pc))
        trs.append(tr)
    if len(trs) < period:
        return None
    a = sum(trs[:period]) / period
    for tr in trs[period:]:
        a = (a * (period - 1) + tr) / period
    return a


def vwap(highs, lows, closes, vols, lookback: int = 60):
    if not closes or not vols:
        return None
    n = min(int(lookback), len(closes))
    if n <= 1:
        return None
    pv = 0.0
    vv = 0.0
    for i in range(-n, 0):
        tp = (float(highs[i]) + float(lows[i]) + float(closes[i])) / 3.0
        vol = float(vols[i] or 0.0)
        pv += tp * vol
        vv += vol
    if vv <= 0:
        return None
    return pv / vv


# --------------------------------------------------------------------------------------
# Phase 3.3: Support classes (News/Trade state/CircuitBreaker)
# (Restored/required for v8.6.x runtime)
# --------------------------------------------------------------------------------------

class NewsContext:
    def __init__(self):
        self.mode = "CLEAR"
        self.headline = ""
        self.ts = 0.0

    def decay_if_old(self, max_age_sec=1800):
        if self.mode != "CLEAR" and (time.time() - self.ts) > max_age_sec:
            self.mode = "CLEAR"; self.headline = ""; self.ts = 0.0

    def is_macro(self) -> bool:
        s = (self.headline or "").lower()
        return any(w in s for w in MACRO_WORDS)

class NewsMonitor(threading.Thread):
    def __init__(self, ctx: NewsContext, out_q: queue.Queue):
        super().__init__(daemon=True)
        self._hb_ts = time.time()
        self.ctx = ctx
        self.out_q = out_q
        self.stop_ev = threading.Event()
        self.seen = set()

    def stop(self):
        self.stop_ev.set()

    def run(self):
        """Lightweight RSS poller to classify macro/news tone.
        Sets ctx.mode in {CLEAR,RISK_ON,RISK_OFF}.
        """
        self.out_q.put(("INFO", "NewsMonitor started."))
        while not self.stop_ev.is_set():
            try:
                for url in NEWS_RSS:
                    if self.stop_ev.is_set():
                        break
                    try:
                        r = requests.get(url, timeout=4)
                        if r.status_code >= 400:
                            continue
                        root = ET.fromstring(r.text)
                        # Try RSS 2.0 then Atom
                        titles = []
                        for it in root.findall('.//item'):
                            t = (it.findtext('title') or '').strip()
                            if t:
                                titles.append(t)
                        if not titles:
                            for ent in root.findall('.//{http://www.w3.org/2005/Atom}entry'):
                                t = (ent.findtext('{http://www.w3.org/2005/Atom}title') or '').strip()
                                if t:
                                    titles.append(t)
                        for t in titles[:25]:
                            key = (url + '|' + t)
                            if key in self.seen:
                                continue
                            self.seen.add(key)
                            s = t.lower()
                            mode = None
                            if any(w in s for w in RISK_OFF):
                                mode = 'RISK_OFF'
                            elif any(w in s for w in RISK_ON):
                                mode = 'RISK_ON'
                            if mode:
                                self.ctx.mode = mode
                                self.ctx.headline = t
                                self.ctx.ts = time.time()
                                self.out_q.put(("NEWS", f"{mode}: {t}"))
                    except Exception:
                        continue
            except Exception:
                pass
            # wait
            self.stop_ev.wait(NEWS_POLL_SEC)
        self.out_q.put(("INFO", "NewsMonitor stopped."))


@dataclass
class PositionState:
    symbol: str
    side: str  # 'long' or 'short'
    qty: float
    entry: float
    best: float
    stop: float
    opened_ts: float
    tag: str = ""
    reason: str = ""


@dataclass
class ManagedTrade:
    """Layer 1 trade lifecycle state (engine-owned).

    We manage exits ourselves to support Option C:
      - TP1 on part of the position
      - after TP1, trail the remainder

    Notes:
      - Stocks: we can use trailing_stop orders.
      - Crypto: trailing_stop is not supported; we emulate trailing via stop_limit refresh.
    """
    trade_id: str
    symbol: str
    side: str               # 'buy' or 'sell' (entry side)
    qty: float
    is_crypto: bool = False
    entry_px: Optional[float] = None
    entry_ts: Optional[float] = None
    entry_order_id: str = ""
    tp1_order_id: str = ""
    stop_order_id: str = ""
    trail_order_id: str = ""
    flatten_order_id: str = ""
    time_stop_fired: bool = False
    opened_ts: float = 0.0
    state: str = "SIGNAL"    # SIGNAL, ENTRY_SUBMITTED, ENTRY_FILLED, TP1_WORKING, TRAIL_WORKING, FLATTEN_WORKING, CLOSED

    # planning values
    atr: float = 0.0
    stop_px: float = 0.0
    tp1_px: float = 0.0
    trail_amt: float = 0.0
    tp1_qty: float = 0.0
    rem_qty: float = 0.0

    # tracking
    best_px: float = 0.0
    last_px: float = 0.0
    last_trail_update_ts: float = 0.0
    why: str = ""
    why_verbose: str = ""
    news: str = ""
    receipt_ctx: dict = field(default_factory=dict)
    realized_pnl: float = 0.0
    realized_qty: float = 0.0



@dataclass
class CircuitBreaker:
    enabled: bool = False
    reason: str = ""
    tripped_ts: float = 0.0
    consec_api_fails: int = 0
    consec_order_rejects: int = 0
    last_ok_ts: float = 0.0
    ok_streak: int = 0
    last_data_ok_ts: float = 0.0


def journal_row(kind: str, symbol: str, side: str, qty: float, price: float, pnl: float, tag: str, reason: str, votes: int = 0):
    """Append a simple trade journal row. Safe/no-throw."""
    try:
        JOURNAL_PATH.parent.mkdir(parents=True, exist_ok=True)
        header = ["ts","kind","symbol","side","qty","price","pnl","tag","reason","votes"]
        row = [dt.datetime.now(tz=ET_TZ).isoformat(), kind, symbol, side, f"{qty:.6f}", f"{price:.6f}", f"{pnl:.6f}", tag, reason, str(int(votes))]
        write_header = not JOURNAL_PATH.exists()
        with JOURNAL_PATH.open('a', encoding='utf-8-sig', errors='ignore', newline='') as f:
            w = csv.writer(f)
            if write_header:
                w.writerow(header)
            w.writerow(row)
    except Exception:
        pass


def perf_update(perf: dict, pnl: float):
    """Update simple win/loss counters."""
    try:
        perf.setdefault('trades', 0)
        perf.setdefault('wins', 0)
        perf.setdefault('losses', 0)
        perf['trades'] += 1
        if pnl >= 0:
            perf['wins'] += 1
        else:
            perf['losses'] += 1
        PERF_PATH.write_text(json.dumps(perf, indent=2), encoding='utf-8-sig')
    except Exception:
        pass


def _tf_to_timedelta(timeframe: str) -> dt.timedelta:
    tf = (timeframe or '').strip()
    # Accept: '1Min','5Min','15Min','1Hour','1Day' + also lowercase like '1m'
    m = re.match(r'^(\d+)(Min|Hour|Day|Week|Month)$', tf, re.I)
    if m:
        n = int(m.group(1))
        unit = m.group(2).lower()
        if unit == 'min':
            return dt.timedelta(minutes=n)
        if unit == 'hour':
            return dt.timedelta(hours=n)
        if unit == 'day':
            return dt.timedelta(days=n)
        if unit == 'week':
            return dt.timedelta(weeks=n)
        if unit == 'month':
            return dt.timedelta(days=30*n)
    m2 = re.match(r'^(\d+)(m|h|d)$', tf, re.I)
    if m2:
        n = int(m2.group(1))
        unit = m2.group(2).lower()
        if unit == 'm':
            return dt.timedelta(minutes=n)
        if unit == 'h':
            return dt.timedelta(hours=n)
        if unit == 'd':
            return dt.timedelta(days=n)
    # default 1 minute
    return dt.timedelta(minutes=1)


def _utc_rfc3339(ts: dt.datetime) -> str:
    if ts.tzinfo is None:
        ts = ts.replace(tzinfo=dt.timezone.utc)
    ts = ts.astimezone(dt.timezone.utc)
    return ts.replace(microsecond=0).isoformat().replace('+00:00', 'Z')



# ---------------- Indicators (minimal, dependency-free) ----------------

def _bars_to_ohlcv(bars):
    """Convert Alpaca bars list to arrays. Supports both v2 and v1beta crypto shapes."""
    o=h=l=c=v=None
    opens=[]; highs=[]; lows=[]; closes=[]; vols=[]
    for b in (bars or []):
        if not isinstance(b, dict):
            continue
        def g(*keys, default=None):
            for k in keys:
                if k in b and b[k] is not None:
                    return b[k]
            return default
        o = g('o','open'); h = g('h','high'); l = g('l','low'); c = g('c','close'); v = g('v','volume', default=0)
        try:
            opens.append(float(o)); highs.append(float(h)); lows.append(float(l)); closes.append(float(c)); vols.append(float(v or 0))
        except Exception:
            continue
    return opens, highs, lows, closes, vols


def ema(series, period: int):
    period = int(period)
    if not series or period <= 1:
        return None
    k = 2.0 / (period + 1.0)
    e = float(series[0])
    for x in series[1:]:
        e = (float(x) * k) + (e * (1.0 - k))
    return e


def rsi(series, period: int = 14):
    period = int(period)
    if not series or len(series) < period + 1:
        return None
    gains = 0.0
    losses = 0.0
    for i in range(1, period + 1):
        d = float(series[i]) - float(series[i-1])
        if d >= 0:
            gains += d
        else:
            losses -= d
    avg_gain = gains / period
    avg_loss = losses / period
    for i in range(period + 1, len(series)):
        d = float(series[i]) - float(series[i-1])
        g = d if d > 0 else 0.0
        l = (-d) if d < 0 else 0.0
        avg_gain = (avg_gain * (period - 1) + g) / period
        avg_loss = (avg_loss * (period - 1) + l) / period
    if avg_loss <= 1e-12:
        return 100.0
    rs = avg_gain / avg_loss
    return 100.0 - (100.0 / (1.0 + rs))


def atr(highs, lows, closes, period: int = 14):
    period = int(period)
    if not highs or not lows or not closes or len(closes) < period + 1:
        return None
    trs = []
    for i in range(1, len(closes)):
        h = float(highs[i]); l = float(lows[i]); pc = float(closes[i-1])
        tr = max(h - l, abs(h - pc), abs(l - pc))
        trs.append(tr)
    if len(trs) < period:
        return None
    a = sum(trs[:period]) / period
    for tr in trs[period:]:
        a = (a * (period - 1) + tr) / period
    return a


def vwap(highs, lows, closes, vols, lookback: int = 60):
    if not closes or not vols:
        return None
    n = min(int(lookback), len(closes))
    if n <= 1:
        return None
    pv = 0.0
    vv = 0.0
    for i in range(-n, 0):
        tp = (float(highs[i]) + float(lows[i]) + float(closes[i])) / 3.0
        vol = float(vols[i] or 0.0)
        pv += tp * vol
        vv += vol
    if vv <= 0:
        return None
    return pv / vv


class Engine(threading.Thread):
    """Resilient scanning engine.

    Focus of v7.6.x: connection stability + independent heartbeat + Loop A/B scheduling.
    Auto-ordering is enabled with strict guardrails (spread caps, notional caps, cooldowns).
    Full trade lifecycle management (brackets/trailing/managed exits) is the next layer.
    """

    def __init__(
        self,
        client: 'AlpacaClient',
        symbols,
        news_ctx: NewsContext,
        out_q: queue.Queue,
        state: Optional[EngineState],
        risk_pct: float,
        max_spread_bps_stock: int,
        max_spread_bps_crypto: int,
        use_limits: bool,
        slip_bps_stock: float,
        slip_bps_crypto: float,
        allow_shorts: bool = False,
        aggressive_on_aligned: bool = False,
        exec_mode: str = DATA_MODE_PAPER,
        settings: dict | None = None,
    ):
        super().__init__(daemon=True)
        self.client = client
        # de-dupe while preserving order
        seen = set()
        self.symbols = []
        for s in (symbols or []):
            s = (s or '').strip().upper()
            if not s or s in seen:
                continue
            seen.add(s)
            self.symbols.append(s)
        self.news_ctx = news_ctx
        self.out_q = out_q
        self.state = state
        if self.state is not None:
            self.state.running = True
            self.state.paused = False

        self.risk_pct = float(risk_pct)
        self.max_spread_bps_stock = int(max_spread_bps_stock)
        self.max_spread_bps_crypto = int(max_spread_bps_crypto)
        self.use_limits = bool(use_limits)
        self.slip_bps_stock = float(slip_bps_stock)
        self.slip_bps_crypto = float(slip_bps_crypto)
        self.allow_shorts = bool(allow_shorts)
        self.aggressive = bool(aggressive_on_aligned)
        # Exec mode + settings (Layers 4-8 + paper test relaxations)
        self.exec_mode = (exec_mode or DATA_MODE_PAPER).upper()
        self.settings = dict(settings) if isinstance(settings, dict) else _ensure_settings()
        self.canary_mode = bool(self.settings.get("canary_mode", False))
        # PAPER relax mode (for testing): enables PAPER-only min score gates + probe trades.
        # Can be enabled via settings.json (paper_relax_for_testing=true) OR env var RELENTLESS_PAPER_RELAX=1.
        _env_paper_relax = str(os.environ.get('RELENTLESS_PAPER_RELAX', '') or '').strip().lower()
        if _env_paper_relax in ('1','true','on','yes'):
            self.paper_relax = (self.exec_mode == DATA_MODE_PAPER)
        elif _env_paper_relax in ('0','false','off','no'):
            self.paper_relax = False
        else:
            self.paper_relax = bool(self.settings.get('paper_relax_for_testing', False)) and (self.exec_mode == DATA_MODE_PAPER)
        self._probe_enable = bool(self.settings.get("paper_probe_enable", True)) and self.paper_relax and (not self.canary_mode)
        self._probe_cd_sec = float(self.settings.get("paper_probe_cooldown_sec", 300) or 300)
        self._last_probe_ts = 0.0
        self._last_analytics_ts = 0.0


        # Optional PAPER-only signal relax (increases entry frequency for testing).
        # Default is STRICT. Enable by setting settings.json:
        #   "paper_relax_for_testing": true,
        #   "paper_relax_signal": true,
        # Optional tuning:
        #   "paper_ema_tol_bps": 2.0,
        #   "paper_rsi_bull": 52.0,
        #   "paper_rsi_bear": 48.0
        # Or set env var RELENTLESS_RELAX_SIGNAL=1 (PAPER only).
        env_relax = str(os.environ.get("RELENTLESS_RELAX_SIGNAL", "") or "").strip().lower()
        env_relax_on = env_relax in ("1", "true", "on", "yes")

        # Signal relax (ema tolerance + RSI thresholds)
        # Can be enabled via settings.json "paper_relax_signal": true or env RELENTLESS_RELAX_SIGNAL=1
        self.paper_relax_signal = (bool(self.settings.get('paper_relax_signal', False)) or env_relax_on) and self.paper_relax
        # Defaults match STRICT mode unless relax is enabled
        self.signal_ema_tol_bps = 0.0
        self.signal_rsi_bull = 55.0
        self.signal_rsi_bear = 45.0
        if self.paper_relax_signal:
            try:
                self.signal_ema_tol_bps = float(self.settings.get("paper_ema_tol_bps", 2.0) or 2.0)
            except Exception:
                self.signal_ema_tol_bps = 2.0
            try:
                self.signal_rsi_bull = float(self.settings.get("paper_rsi_bull", 52.0) or 52.0)
            except Exception:
                self.signal_rsi_bull = 52.0
            try:
                self.signal_rsi_bear = float(self.settings.get("paper_rsi_bear", 48.0) or 48.0)
            except Exception:
                self.signal_rsi_bear = 48.0
            try:
                self.out_q.put(("INFO", f"Entry signal: RELAX (ema_tol={self.signal_ema_tol_bps:.2f}bps bull_rsi>={self.signal_rsi_bull:.1f} bear_rsi<={self.signal_rsi_bear:.1f})"))
            except Exception:
                pass
        else:
            try:
                self.out_q.put(("INFO", "Entry signal: STRICT (bull: ef>es, rsi>=55, vwap ok; bear: ef<es, rsi<=45, vwap ok)"))
            except Exception:
                pass

        self.stop_ev = threading.Event()
        self._quote_cache = {}  # sym -> (ts,bid,ask,mid,score)
        self._rr_idx = 0
        self._loopA_errors = 0
        self._last_broker_sync = 0.0
        self._last_orders_sync = 0.0
        self._open_orders_cache = []
        self._open_orders_ts = 0.0
        # pending entry protection: broker positions can appear before our fill handler fires
        # which can trigger RECOVERY to fight with our normal entry/stop logic.
        self._pending_entries = {}  # ns -> ts
        self._pending_entry_ttl = 90.0
        self._recovery_logged = set()
        self._last_acct_poll = 0.0
        self._last_account = None
        self._last_equity = None
        self._last_scan_log_ts = 0.0  # throttle scan chatter to keep UI responsive
        self._last_scan_log_kept = ""
        # Last broker account snapshot (for fast KPI updates)
        self._acct_eq = None
        self._acct_upl = 0.0
        self._acct_bp = None
        self._kpi_cached_pls = {"24h": None, "wtd": None, "mtd": None, "all": None}
        self._kpi_cached_ts = 0.0
        self._last_buying_power = None
        self._last_cash = None

        # Stock market clock (to avoid attempting stock orders when market is closed)
        self._stock_market_open = True
        self._last_clock_poll = 0.0
        self._last_market_closed_notice = 0.0

        # Rejection diagnostics
        self._last_reject_log_ts = 0.0
        self.pos = {}  # sym -> PositionState (snapshot only for now)

        # throttle scan spam in the UI feed
        self._last_scan_feed_ts = 0.0

        # heartbeat timestamp (read directly by UI watchdog to avoid queue lag)
        self.hb_ts = time.time()
        self.trade_enabled = True

        # Layer 1: trade lifecycle state
        self.trades: dict[str, ManagedTrade] = {}
        # order_id -> (trade_id, leg)
        self._oid_to_leg: dict[str, tuple[str, str]] = {}

        # Layer 2: circuit breaker + recovery
        self.cb = CircuitBreaker()
        self._cb_window = []  # list[(ts, kind)]
        self._trade_ts_hour = []  # entry timestamps for activity caps
        self._trade_ts_day = []
        self._last_data_stale_notice = 0.0

        # Phase 2: loss-only cooldown + drawdown hard-pause state
        self._sym_cooldowns: dict[str, float] = {}   # norm_symbol -> cooldown_until_ts
        self._dd_halt_until: float = 0.0
        self._last_dd_halt_warn_ts: float = 0.0

        # Layer 3: symbol news cache
        self._news_cache = {}  # sym -> (ts, headline)
        self._news_disabled = False


    def _clear_local_trades(self, reason: str = "") -> None:
        """Clear local trade/order bookkeeping without touching broker positions."""
        try:
            n_trades = len(getattr(self, "trades", {}) or {})
        except Exception:
            n_trades = 0
        try:
            self.trades.clear()
        except Exception:
            self.trades = {}
        # legacy map may not exist in this build; clear only if present
        try:
            m = getattr(self, "_symbol_to_trade", None)
            if isinstance(m, dict):
                m.clear()
        except Exception:
            pass
        try:
            self._oid_to_leg.clear()
        except Exception:
            self._oid_to_leg = {}
        try:
            self.out_q.put(("WARN", f"WARN  LOCAL STATE: cleared {n_trades} trades (reason={reason or 'n/a'})."))
        except Exception:
            pass


    def _find_active_trade_id_for_symbol(self, sym: str) -> Optional[str]:
        """Return active trade_id for symbol from self.trades (legacy _symbol_to_trade is optional)."""
        ns = normalize_symbol(sym)
        for tid, t in list((getattr(self, "trades", {}) or {}).items()):
            try:
                if normalize_symbol(getattr(t, "symbol", "")) != ns:
                    continue
                st = str(getattr(t, "state", "") or "").upper()
                if st in ("CLOSED", "CANCELED", "REJECTED", "DONE"):
                    continue
                return tid
            except Exception:
                continue
        return None



    def _clear_trade_for_symbol(self, sym: str, note: str = "") -> None:
        """Clear ONLY the local trade state for a single symbol.
        Used for dust/edge cases so we don't get stuck in SYMBOL BUSY."""
        try:
            ns = normalize_symbol(sym)
            tid = self._find_active_trade_id_for_symbol(ns)
            if tid and tid in self.trades:
                self.trades.pop(tid, None)
            try:
                m = getattr(self, "_symbol_to_trade", None)
                if isinstance(m, dict):
                    m.pop(ns, None)
            except Exception:
                pass
            try:
                self.state.last_existing_stop_ts.pop(ns, None)
                self.state.last_existing_stop_log_ts.pop(ns, None)
            except Exception:
                pass
            self.out_q.put(("WARN", f"RECOVERY: cleared local trade state for {sym} {('('+note+')') if note else ''}"))
        except Exception as _e:
            try:
                self.out_q.put(("WARN", f"RECOVERY: failed to clear local trade state for {sym}: {_e}"))
            except Exception:
                pass
    def _cancel_open_orders_for_symbol(self, symbol: str, reason: str = "", cancel_stops: bool = True) -> None:
        """Best-effort: cancel open orders for this symbol.

        Alpaca (especially crypto) can reserve qty for resting orders. If exits
        fail and we attempt a PANIC close, we must cancel open orders first or
        the broker may reject with "insufficient balance".
        """
        try:
            def _ns(x: str) -> str:
                return str(x or "").replace("/", "").upper()

            target = _ns(symbol)
            orders = self.client.list_orders(status="open", limit=500)
            for o in orders or []:
                sym = _ns(o.get("symbol", ""))
                if sym != target:
                    continue
                otype = (o.get("type") or "").lower()
                if (not cancel_stops) and (otype in ("stop", "stop_limit", "trailing_stop")):
                    continue
                oid = o.get("id")
                if oid:
                    try:
                        self.client.cancel_order(oid)
                    except Exception:
                        pass
        except Exception:
            # never fail loudly here
            return

    def _close_position_with_unreserve(self, symbol: str, qty: Optional[float] = None, reason: str = ""):
        """Close position with crypto-safe unreserve retries."""
        if not is_crypto_symbol(symbol):
            return self.client.close_position(symbol) if qty is None else self.client.close_position(symbol, qty=qty)

        last_err = None
        for attempt in range(3):
            try:
                self._cancel_open_orders_for_symbol(symbol, cancel_stops=False, reason=(reason or 'close_pre') + f"_ns_{attempt}")
            except Exception:
                pass
            try:
                return self.client.close_position(symbol) if qty is None else self.client.close_position(symbol, qty=qty)
            except Exception as e:
                last_err = e
                if not is_insufficient_balance_err(e):
                    raise
                try:
                    self._cancel_open_orders_for_symbol(symbol, cancel_stops=True, reason=(reason or 'close_retry') + f"_all_{attempt}")
                except Exception:
                    pass
                time.sleep(0.35)
        if last_err is not None:
            raise last_err
        return None

    def _hb_loop(self):
        """Heartbeat loop runs independently so slow API calls don't trigger false watchdog restarts."""
        while not self.stop_ev.is_set():
            now = time.time()
            self.hb_ts = now
            try:
                self.out_q.put(("HEARTBEAT", {"ts": now, "pos": len(self.pos)}))
            except Exception:
                pass

            # Write a simple heartbeat file for an out-of-process guardian.
            # Best-effort only (never crash the engine if disk write fails).
            try:
                hb = {
                    "ts": now,
                    "pid": os.getpid(),
                    "version": APP_VERSION,
                    "pos_count": int(len(self.pos) if self.pos else 0),
                    "has_positions": bool(self.pos),
                }
                _write_json_atomic(HEARTBEAT_PATH, hb)
            except Exception:
                pass
            self.stop_ev.wait(HEARTBEAT_SEC)

    def stop(self):
        self.stop_ev.set()
        try:
            self.join(timeout=2.0)
        except Exception:
            pass

    # ---------------- Layer 2: Circuit breaker ----------------
    def _cb_record(self, kind: str, msg: str = ""):
        """Record failures/signal events used by the circuit breaker.

        kind: 'api_fail' | 'order_reject' | 'data_stale' | 'ok'
        """
        now = time.time()
        # trim window
        self._cb_window = [(t,k) for (t,k) in self._cb_window if (now - t) <= CB_FAIL_WINDOW_SEC]
        self._cb_window.append((now, kind))

        if kind == 'api_fail':
            self.cb.consec_api_fails += 1
            self.cb.ok_streak = 0
        elif kind == 'order_reject':
            self.cb.consec_order_rejects += 1
            self.cb.ok_streak = 0
        elif kind == 'data_stale':
            self.cb.ok_streak = 0
            # treat repeated stale data as API failure for protection
            self.cb.consec_api_fails += 1
        elif kind == 'ok':
            self.cb.consec_api_fails = 0
            self.cb.consec_order_rejects = 0
            self.cb.ok_streak += 1
            self.cb.last_ok_ts = now

        if (not self.cb.enabled) and (
            self.cb.consec_api_fails >= CB_MAX_CONSEC_API_FAILS or
            self.cb.consec_order_rejects >= CB_MAX_ORDER_REJECTS
        ):
            reason = msg or (f"api_fails={self.cb.consec_api_fails}, order_rejects={self.cb.consec_order_rejects}")
            self._cb_trip(reason)

    def _cb_trip(self, reason: str):
        self.cb.enabled = True
        self.cb.reason = reason
        self.cb.tripped_ts = time.time()
        self.trade_enabled = False
        self.out_q.put(('WARN', f"CIRCUIT BREAKER TRIPPED: {reason}. Trading paused; diagnosing + attempting recovery."))

    def _cb_recovery_tick(self):
        """Try to self-heal and resume trading.

        We keep scanning and managing exits while CB is enabled.
        To clear, we need CB_RECOVERY_OK_STREAK successful health checks.
        """
        if not self.cb.enabled:
            return
        now = time.time()
        # throttle recovery work
        if (now - self.cb.last_ok_ts) < 2.5:
            return
        try:
            # minimal health check: account + a small quote sample
            _ = self.client.get_account()
            sample = []
            for s in self.symbols[:6]:
                if s:
                    sample.append(s)
            if sample:
                _ = self.client.get_latest_quotes_bulk(sample)
            self._cb_record('ok', '')
            if self.cb.ok_streak >= CB_RECOVERY_OK_STREAK:
                self.cb.enabled = False
                self.cb.reason = ''
                self.trade_enabled = True
                self.cb.ok_streak = 0
                self.out_q.put(('INFO', 'Circuit breaker cleared (health checks OK). Trading re-enabled.'))
        except Exception as e:
            self._cb_record('api_fail', f"recovery: {e}")
            self.out_q.put(('WARN', f"Recovery attempt failed: {e}"))

    # ---------------- Layer 3: Symbol news ----------------

    # ---------------- Layer 3: Symbol news ----------------
    def _get_symbol_news_info(self, sym: str) -> dict:
        """Return cached symbol news info dict:
        {formatted, conf, pub_et, age_m, source, headline, sentiment}
        """
        if not sym:
            return {}
        if getattr(self, "_news_disabled", False):
            return {}
        now = time.time()
        if not hasattr(self, "_news_cache_info"):
            self._news_cache_info = {}
        ts_h = self._news_cache_info.get(sym)
        if ts_h and (now - ts_h[0]) < 180:
            return ts_h[1] or {}
        try:
            items = self.client.get_news([sym], limit=1)
            info = {}
            if items:
                it = items[0] or {}
                formatted = format_news_confidence(it) or (it.get('headline') or it.get('title') or '').strip()
                nf = parse_news_fields(formatted or "")
                conf = (nf.get("news_conf") or "").strip() or "STALE"
                pub_et = (nf.get("news_pub_et") or "").strip()
                age_m = int(float(nf.get("news_age_m") or 9999))
                src = (nf.get("news_source") or "").strip()
                head = (nf.get("news_headline") or "").strip() or formatted
                sent = classify_news_sentiment(head)
                info = {
                    "formatted": (formatted or "").strip(),
                    "conf": conf,
                    "pub_et": pub_et,
                    "age_m": age_m,
                    "source": src,
                    "headline": head,
                    "sentiment": sent,
                }
            if info.get("formatted"):
                self._news_cache_info[sym] = (now, info)
            return info
        except Exception as e:
            msg = str(e)
            if ('403' in msg) and ('news' in msg.lower()) and ('subscription' in msg.lower() or 'permit' in msg.lower()):
                self._news_disabled = True
                self.out_q.put(('WARN', 'Symbol news disabled: Alpaca subscription does not permit querying news.'))
            return {}

    def _get_symbol_news(self, sym: str) -> str:
        info = self._get_symbol_news_info(sym)
        return (info.get("formatted") or "").strip()

    # ---------------- Layer 2: Risk gates ----------------
    def _risk_can_open(self, sym: str, est_notional: float) -> tuple[bool, str]:
        """Account-level risk gating.

        This does NOT cap profit; it prevents blowups.
        """
        now = time.time()
        # trim trade timestamps
        self._trade_ts_hour = [t for t in self._trade_ts_hour if (now - t) <= 3600]
        self._trade_ts_day = [t for t in self._trade_ts_day if (now - t) <= 86400]
        if len(self._trade_ts_hour) >= MAX_TRADES_PER_HOUR:
            return False, f"max trades/hour ({MAX_TRADES_PER_HOUR})"
        if len(self._trade_ts_day) >= MAX_TRADES_PER_DAY:
            return False, f"max trades/day ({MAX_TRADES_PER_DAY})"

        # Phase 2: hard drawdown pause (entries only; exits still managed)
        try:
            if float(getattr(self, '_dd_halt_until', 0.0) or 0.0) and now < float(self._dd_halt_until):
                mins = int(max(0.0, float(self._dd_halt_until) - now) // 60)
                return False, f"hard drawdown pause ({mins}m)"
        except Exception:
            pass

        # Phase 2: loss-only per-symbol cooldown (only after losing trades)
        try:
            ns = norm_symbol(sym)
            # if we just submitted an entry, let the normal fill handler own this symbol
            try:
                ts = self._pending_entries.get(ns)
                if ts is not None and (now - float(ts)) <= float(self._pending_entry_ttl):
                    return False, 'pending entry (await fill)'
            except Exception:
                pass
            until = float(self._sym_cooldowns.get(ns, 0.0) or 0.0)
            if until and now < until:
                mins = int(max(0.0, until - now) // 60)
                return False, f"cooldown after loss ({mins}m)"
        except Exception:
            pass
        # max positions
        if len(self.pos) >= max(1, int(MAX_POSITIONS)):
            return False, f"max positions ({MAX_POSITIONS})"

        # max crypto positions (Phase 2A)
        if is_crypto_symbol(sym):
            try:
                crypto_open = 0
                for ps in self.pos.values():
                    try:
                        if is_crypto_symbol(ps.symbol) and abs(float(ps.qty or 0.0)) >= CRYPTO_DUST_QTY:
                            crypto_open += 1
                    except Exception:
                        continue
                if crypto_open >= int(MAX_CRYPTO_POSITIONS):
                    return False, f"max crypto positions ({MAX_CRYPTO_POSITIONS})"
            except Exception:
                pass


        eq = float(self._last_equity or 0.0)
        if eq <= 0:
            return True, ''
        # Resolve caps (paper relax overrides)
        total_cap = MAX_TOTAL_EXPOSURE_PCT
        crypto_cap = MAX_CRYPTO_EXPOSURE_PCT
        sym_cap = MAX_SYMBOL_EXPOSURE_PCT
        if self.paper_relax:
            try:
                total_cap = float(self.settings.get("paper_max_total_exposure_pct", total_cap) or total_cap)
                crypto_cap = float(self.settings.get("paper_max_crypto_exposure_pct", crypto_cap) or crypto_cap)
                sym_cap = float(self.settings.get("paper_max_symbol_exposure_pct", sym_cap) or sym_cap)
            except Exception:
                pass

        # symbol exposure cap
        if est_notional > (eq * sym_cap):
            return False, f"symbol exposure cap ({sym_cap*100:.0f}% eq)"

        # total exposure rough estimate: sum positions notional using cached mids (best effort)
        total = 0.0
        crypto = 0.0
        for ps in self.pos.values():
            try:
                px = float(ps.best or ps.entry or 0.0)
                total += abs(float(ps.qty) * px)
                if is_crypto_symbol(ps.symbol):
                    crypto += abs(float(ps.qty) * px)
            except Exception:
                continue
        total_after = total + abs(est_notional)
        crypto_after = crypto + (abs(est_notional) if is_crypto_symbol(sym) else 0.0)
        if total_after > (eq * total_cap):
            return False, f"total exposure cap ({total_cap*100:.0f}% eq)"
        # Crypto exposure cap should prevent ADDING crypto risk; it should not block stock entries
        # just because existing crypto exposure is elevated.
        if is_crypto_symbol(sym) and (crypto_after > (eq * crypto_cap)):
            return False, f"crypto exposure cap ({crypto_cap*100:.0f}% eq)"
        return True, ''

    def _maybe_set_loss_cooldown(self, symbol: str, pnl: float):
        """Apply a per-symbol cooldown only after losing trades.

        Prevents stop-out churn in choppy regimes without blocking winners.
        """
        try:
            if float(pnl) >= 0.0:
                return
            ns = norm_symbol(symbol)
            now = time.time()
            until = now + float(LOSS_ONLY_COOLDOWN_SEC)
            prev = float(self._sym_cooldowns.get(ns, 0.0) or 0.0)
            self._sym_cooldowns[ns] = max(prev, until)
            # Throttle notices per symbol (1/min)
            key = f'_cooldown_note_{ns}'
            if (now - float(getattr(self, key, 0.0))) > 60.0:
                setattr(self, key, now)
                mins = int(max(0.0, self._sym_cooldowns[ns] - now) // 60)
                self.out_q.put(('INFO', f'Loss cooldown applied for {symbol}: {mins}m'))
        except Exception:
            return


    def _symbol_busy_for_entry(self, sym: str):
        """Return (busy, reason) if a symbol already has exposure/orders.

        This prevents duplicate entries on the same symbol (common cause of Alpaca wash-trade 403 when
        opposite-side stop/market orders exist).
        """
        ns = norm_symbol(sym)

        # Existing broker position snapshot
        try:
            ps = self.pos.get(ns)
            if ps and float(getattr(ps, 'qty', 0.0) or 0.0) != 0.0:
                return True, 'open position'
        except Exception:
            pass

        # Any tracked open orders for this symbol
        try:
            oo = getattr(self, '_open_orders', None) or {}
            for meta in oo.values():
                ms = norm_symbol(str(meta.get('symbol', '') or ''))
                if ms == ns:
                    leg = str(meta.get('leg', '?') or '?')
                    return True, f'open order ({leg})'
        except Exception:
            pass

        # Any in-flight managed trade not yet closed
        try:
            for t in (self.trades or {}).values():
                ts = norm_symbol(str(getattr(t, 'symbol', '') or ''))
                if ts != ns:
                    continue
                st = str(getattr(t, 'state', '') or '')
                if st and st.upper() not in ('CLOSED', 'CANCELED', 'DONE'):
                    return True, f'active trade ({st})'
        except Exception:
            pass

        return False, ''


    def _broker_position_qty(self, symbol: str) -> float:
        """Best-effort broker position qty (can be fractional for crypto). Returns 0.0 if flat/unknown."""
        try:
            sym = normalize_symbol(symbol)
            poss = self.client.get_positions() or []
            for p in poss:
                ps = normalize_symbol(str(p.get("symbol", "")))
                if ps == sym:
                    return float(p.get("qty") or 0.0)
        except Exception:
            return 0.0
        return 0.0
    
    
    def run(self):
        self.out_q.put(("INFO", "Engine started. Seeking setups..."))
        self.hb_ts = time.time()  # immediate heartbeat on thread start
        if self.paper_relax:
            try:
                total_cap = float(self.settings.get("paper_max_total_exposure_pct", MAX_TOTAL_EXPOSURE_PCT) or MAX_TOTAL_EXPOSURE_PCT)
                crypto_cap = float(self.settings.get("paper_max_crypto_exposure_pct", MAX_CRYPTO_EXPOSURE_PCT) or MAX_CRYPTO_EXPOSURE_PCT)
                sym_cap = float(self.settings.get("paper_max_symbol_exposure_pct", MAX_SYMBOL_EXPOSURE_PCT) or MAX_SYMBOL_EXPOSURE_PCT)
                base_score = float(self.settings.get("paper_min_entry_score", 120.0) or 120.0)
                test_score = float(self.settings.get("paper_test_min_entry_score", base_score) or base_score)
                min_score = min(base_score, test_score)
                self.out_q.put(("INFO", f"PAPER relax enabled (testing): caps total={total_cap*100:.0f}% crypto={crypto_cap*100:.0f}% symbol={sym_cap*100:.0f}% min_score={min_score:.0f} (base={base_score:.0f}, test={test_score:.0f})"))
            except Exception:
                self.out_q.put(("INFO", "PAPER relax enabled (testing)"))
        hb_thread = threading.Thread(target=self._hb_loop, daemon=True)
        hb_thread.start()
        last_loopA = 0.0
        last_loopB = 0.0
        last_hb = 0.0

        while not self.stop_ev.is_set():
            now = time.time()

            # Local-state clear (requested by UI/state, e.g., after PANIC confirms broker flat)
            try:
                if getattr(self.state, "clear_local_trades_pending", False):
                    self._clear_local_trades(reason=getattr(self.state, "clear_local_trades_reason", "") or "requested")
                    self.state.clear_local_trades_pending = False
                    self.state.clear_local_trades_reason = ""
            except Exception:
                pass
            try:
                # Poll market clock occasionally (stocks only).
                if (now - self._last_clock_poll) > 300.0:
                    self._last_clock_poll = now
                    try:
                        clk = self.client.get_clock()
                        self._stock_market_open = bool(clk.get('is_open', True))
                    except Exception:
                        # If clock fails, assume open to avoid disabling stock trading unnecessarily
                        self._stock_market_open = True

                if (not self._stock_market_open) and ((now - self._last_market_closed_notice) > 600.0):
                    self._last_market_closed_notice = now
                    self.out_q.put(('INFO', 'Market appears CLOSED; stock entries suppressed. Crypto entries still allowed.'))
                # Layer 2: circuit breaker recovery attempts
                if self.cb.enabled:
                    self._cb_recovery_tick()

                # Layer 2: data staleness protection (don't trade blind)
                if self.cb.last_data_ok_ts and (now - self.cb.last_data_ok_ts) > CB_STALE_DATA_SEC:
                    if (now - self._last_data_stale_notice) > 5.0:
                        self._last_data_stale_notice = now
                        self._cb_record('data_stale', 'stale quotes')
                        self.out_q.put(('WARN', 'Data appears stale; circuit breaker may pause trading until feed recovers.'))

                # keep news from going stale
                try:
                    self.news_ctx.decay_if_old()
                except Exception:
                    pass

                # periodic broker sync
                if (now - self._last_broker_sync) >= BROKER_SYNC_SEC:
                    self._broker_sync()
                    self._last_broker_sync = now

                # periodic account poll (drives equity chart + proves connectivity)
                if (now - self._last_acct_poll) >= 20.0:
                    try:
                        acct = self.client.get_account()
                        # Cache for sizing safeguards
                        try:
                            self._last_account = acct
                            self._last_equity = _safe_float(acct.get('equity') or acct.get('portfolio_value'))
                            self._last_buying_power = _safe_float(acct.get('buying_power') or acct.get('regt_buying_power') or acct.get('cash'))
                            self._last_cash = _safe_float(acct.get('cash'))
                            # Phase 2A: very soft drawdown context (DTD from equity snapshots)
                            try:
                                dtd_pl, dtd_eq0 = compute_dtd_pl(float(self._last_equity or 0.0), mode=self.data_mode)
                                self._dtd_pl = dtd_pl
                                self._dtd_eq0 = dtd_eq0
                                if dtd_pl is not None and dtd_eq0:
                                    self._dtd_pl_pct = float(dtd_pl) / float(dtd_eq0)
                                else:
                                    self._dtd_pl_pct = None
                            except Exception:
                                self._dtd_pl = None; self._dtd_eq0 = None; self._dtd_pl_pct = None

                            # Phase 2: hard drawdown pause + auto-recovery (does not affect exit management)
                            try:
                                dd = getattr(self, '_dtd_pl_pct', None)
                                if dd is not None:
                                    dd = float(dd)
                                    if dd <= -float(DD_HARD_PCT):
                                        if float(getattr(self, '_dd_halt_until', 0.0) or 0.0) < now:
                                            self._dd_halt_until = now + float(DD_HARD_PAUSE_SEC)
                                        if (now - float(getattr(self, '_last_dd_halt_warn_ts', 0.0))) > 600.0:
                                            self._last_dd_halt_warn_ts = now
                                            mins = int(max(0.0, self._dd_halt_until - now) // 60)
                                            self.out_q.put(('WARN', f'Hard drawdown pause active (DTD {dd*100:.2f}%): pausing new entries ~{mins}m'))
                                    else:
                                        if float(getattr(self, '_dd_halt_until', 0.0) or 0.0) and now >= float(self._dd_halt_until):
                                            if dd <= -float(DD_HARD_RECOVER_PCT):
                                                self._dd_halt_until = now + 1800.0
                                                if (now - float(getattr(self, '_last_dd_halt_warn_ts', 0.0))) > 600.0:
                                                    self._last_dd_halt_warn_ts = now
                                                    self.out_q.put(('WARN', f'Hard drawdown still below recovery (DTD {dd*100:.2f}%): extending pause 30m'))
                                            else:
                                                self._dd_halt_until = 0.0
                                                self.out_q.put(('INFO', f'Drawdown recovered (DTD {dd*100:.2f}%): entries resumed.'))
                            except Exception:
                                pass
                        except Exception:
                            pass
                        self.out_q.put(("ACCT", acct))
                    except Exception as e:
                        self.out_q.put(("WARN", f"Account poll failed: {e}"))
                        self._cb_record('api_fail', f"acct: {e}")

                # Loop A: refresh quote cache (cheap)
                if (now - last_loopA) >= LOOPA_SEC:
                    self._loopA_refresh_quotes()
                    last_loopA = now

                # Loop B: deep scan subset (expensive)
                if (now - last_loopB) >= LOOPB_SEC:
                    self._loopB_scan()
                    last_loopB = now

            except Exception as e:
                self.out_q.put(("ERROR", f"Engine error: {e}"))

            # short sleep keeps CPU sane while still "constant"
            self.stop_ev.wait(0.05)

        self.stop_ev.set()
        self.out_q.put(("INFO", "Engine stopped."))

    def _broker_sync(self):
        try:
            broker_positions = self.client.get_positions() or []
            now = time.time()
            # Open orders are needed for symbol-busy + adopting existing protective stops on restart.
            open_orders = []
            if (now - self._last_orders_sync) > 15.0:
                try:
                    open_orders = self.client.list_orders(status="open", limit=500, nested=True) or []
                    self._open_orders_cache = open_orders
                    self._open_orders_ts = now
                    self._last_orders_sync = now
                except Exception as oe:
                    open_orders = self._open_orders_cache or []
                    self.out_q.put(("WARN", f"Open orders sync failed: {oe}"))
            else:
                open_orders = self._open_orders_cache or []

            stop_by_symbol = self._reconcile_from_broker(broker_positions, open_orders)

            new_pos = {}
            for p in broker_positions:
                sym = norm_symbol(p.get("symbol", ""))
                side = "LONG" if p.get("side") == "long" else "SHORT"
                qty = float(p.get("qty") or 0.0)
                entry = float(p.get("avg_entry_price") or 0.0)
                cur = float(p.get("current_price") or 0.0)
                upnl = float(p.get("unrealized_pl") or 0.0)
                stop_px = float(stop_by_symbol.get(sym) or 0.0)
                new_pos[sym] = PositionState(symbol=sym, side=side, qty=abs(qty), entry=entry, best=cur, stop=stop_px, opened_ts=now, tag="BROKER", reason=f"uPnL={upnl:.2f}")
            self.pos = new_pos
        except Exception as e:
            self.out_q.put(("WARN", f"Broker sync failed: {e}"))

    def _reconcile_from_broker(self, broker_positions, open_orders):
        """Rebuild/refresh in-app trade state from broker truth.

        Goal: after restart/crash/power loss, we *never forget* existing positions and we ensure a
        broker-side protective STOP exists (crypto: stop-limit safety seatbelt) so you stay protected
        even if the app is down.
        """
        stop_by_symbol = {}
        now = time.time()  # used for pending-entry TTL + reconciliation timing
        # Index positions by symbol (normalized)
        pos_by_sym = {}
        for p in (broker_positions or []):
            sym = norm_symbol(p.get("symbol", ""))
            if sym:
                pos_by_sym[sym] = p
        def find_active_trade(sym: str):
            ns = norm_symbol(sym)
            for _tid, t in self.trades.items():
                if norm_symbol(t.symbol) == ns and t.state not in ('CLOSED', 'CANCELED', 'REJECTED'):
                    return _tid, t
            return None, None


        # --- DUST handling (crypto): tiny residual positions can be below Alpaca minimum order size.
        # Attempt to close ONCE, then ignore to avoid thrash/spam.
        if not hasattr(self, "_dust_ignored"):
            self._dust_ignored = {}  # sym -> ignore_until_ts (or 0 for permanent)

        # 1) Ensure we have an in-app trade object for every live broker position.
        for sym, p in pos_by_sym.items():
            ts = self._pending_entries.get(sym)
            if ts and (now - ts) <= self._pending_entry_ttl:
                continue  # wait for our own fill handler

            # Detect dust crypto positions (notional near $0 or qty extremely tiny)
            try:
                qty_abs = abs(float(p.get("qty") or 0.0))
                cur_px = float(p.get("current_price") or 0.0)
                notional = qty_abs * cur_px
            except Exception:
                qty_abs, cur_px, notional = 0.0, 0.0, 0.0

            if is_crypto_symbol(sym):
                # If we've already decided to ignore dust, skip it unless it has grown.
                ign_until = 0.0
                try:
                    ign_until = float(getattr(self, "_dust_ignored", {}).get(sym, 0.0) or 0.0)
                except Exception:
                    ign_until = 0.0
                if ign_until and time.time() < ign_until:
                    # Still ignored for now
                    continue

                # Heuristics: very tiny qty or essentially zero notional.
                if qty_abs > 0 and (qty_abs < CRYPTO_DUST_QTY or notional < CRYPTO_DUST_NOTIONAL):
                    self.out_q.put(("WARN", f"RECOVERY: detected DUST position {crypto_data_symbol(sym)} qty={qty_abs:g} notional~${notional:.2f}. Attempting close once."))
                    try:
                        exit_side = "sell" if (p.get("side") == "long") else "buy"
                        # Try to close exactly the dust qty; Alpaca may reject if below minimum.
                        self.client.submit_order_market(sym, exit_side, qty_abs, "gtc")
                    except Exception as de:
                        msg = str(de)
                        # If Alpaca tells us the minimum qty, we accept and ignore to avoid thrash.
                        self.out_q.put(("WARN", f"RECOVERY: dust close failed for {sym}: {msg}. Will ignore dust to avoid thrash."))
                        try:
                            self._dust_ignored[sym] = time.time() + 3600.0  # ignore for 1 hour
                        except Exception:
                            pass
                    else:
                        # If accepted, give broker a moment; we still ignore for a short window.
                        try:
                            self._dust_ignored[sym] = time.time() + 120.0
                        except Exception:
                            pass
                    continue
            tid, t = find_active_trade(sym)
            if t is None:
                qty = abs(float(p.get("qty") or 0.0))
                entry = float(p.get("avg_entry_price") or 0.0)
                side = "buy" if p.get("side") == "long" else "sell"
                tid = f"RECOVERY-{sym}-{uuid4().hex[:8]}"
                t = ManagedTrade(
                    trade_id=tid,
                    symbol=sym,
                    is_crypto=is_crypto_symbol(sym),
                    side=side,
                    qty=qty,
                    entry_px=entry,
                    entry_ts=time.time(),
                    opened_ts=time.time(),
                    state="ENTRY_FILLED",
                )
                # Conservative synthetic TP marker (used for UI/logs; execution is broker STOP-first).
                tp_mult = 1.003 if side == "buy" else 0.997
                t.tp1_px = entry * tp_mult if entry else 0.0
                self.trades[tid] = t
                self.out_q.put(("WARN", f"RECOVERY: detected open broker position {sym} qty={qty:g}. Rebuilding trade state + ensuring protective stop."))

        # 2) Rebuild order-id -> leg mapping from broker open orders.
        self._oid_to_leg = {}
        # Track candidate stop orders by symbol to adopt them cleanly.
        stop_orders_by_sym = {}
        for o in (open_orders or []):
            sym = norm_symbol(o.get("symbol", ""))
            oid = o.get("id")
            if not sym or not oid:
                continue
            otype = (o.get("type") or "").lower()
            side = (o.get("side") or "").lower()
            if otype in ("stop", "stop_limit", "trailing_stop"):
                stop_orders_by_sym.setdefault(sym, []).append(o)

        # 3) Adopt existing stops where they match a live position; otherwise place a new protective stop.
        for sym, p in pos_by_sym.items():
            tid, t = find_active_trade(sym)
            if t is None:
                continue
            # Race-guard: if we *just* placed a protective STOP as part of a fresh entry,
            # broker order lists can lag for a few seconds. Avoid cancel/replace thrash.
            try:
                recent_ts = float(t.entry_ts or t.opened_ts or 0.0)
            except Exception:
                recent_ts = 0.0
            if t.stop_order_id and float(getattr(t, "stop_px", 0.0) or 0.0) > 0.0 and recent_ts and (now - recent_ts) < 30.0:
                try:
                    stop_by_symbol[sym] = float(t.stop_px or 0.0)
                    self._oid_to_leg[t.stop_order_id] = (tid, "stop")
                except Exception:
                    pass
                continue

            # Adopt an existing broker stop (preferred).
            adopted = False
            candidates = stop_orders_by_sym.get(sym, [])
            if candidates:
                # Pick the stop with the largest qty (usually the protective seatbelt).
                def _oq(o):
                    try:
                        return float(o.get("qty") or 0.0)
                    except Exception:
                        return 0.0
                candidates = sorted(candidates, key=_oq, reverse=True)
                for o in candidates:
                    otype = (o.get("type") or "").lower()
                    oside = (o.get("side") or "").lower()
                    # For LONG (buy) positions, protective stop is a SELL stop. For SHORT, it's a BUY stop.
                    want_side = "sell" if t.side == "buy" else "buy"
                    if oside != want_side:
                        continue
                    t.stop_order_id = o.get("id")
                    sp = o.get("stop_price") or o.get("stop_price")
                    try:
                        t.stop_px = float(sp) if sp is not None else 0.0
                    except Exception:
                        t.stop_px = 0.0
                    if t.stop_px:
                        stop_by_symbol[sym] = t.stop_px
                    self._oid_to_leg[t.stop_order_id] = (tid, "stop")
                    try:
                        snap = f"{str(o.get('id') or '')}|{otype}|{oside}|{float(o.get('qty') or 0.0):.8f}|{float(t.stop_px or 0.0):.8f}"
                        self.state.last_recovery_stop_snapshot[sym] = snap
                        self.state.last_recovery_stop_action_ts[sym] = now
                    except Exception:
                        pass
                    adopted = True
                    break

            if adopted:
                last_ts = self.state.last_recovery_stop_log_ts.get(sym, 0.0)
                # Also stamp a per-symbol protective-stop activity timestamp (seatbelt/grace window)
                try:
                    d2 = getattr(self.state, 'last_crypto_protect_ts', None)
                    if d2 is None:
                        self.state.last_crypto_protect_ts = {}
                        d2 = self.state.last_crypto_protect_ts
                    d2[sym] = time.time()
                except Exception:
                    pass
                if now - last_ts > 600.0:
                    self.state.last_recovery_stop_log_ts[sym] = now
                    self.out_q.put(("WARN", f"WARN  RECOVERY: existing protective STOP detected for {sym}: STOP {getattr(t, 'stop_px', 0.0)} (id={getattr(t, 'stop_order_id', '')}) qty={p.get('qty')}"))
                    try:
                        _ns = normalize_symbol(sym)
                        _now = time.time()
                        self.state.last_crypto_protect_ts[sym] = _now
                        self.state.last_crypto_protect_ts[_ns] = _now
                        self.state.last_existing_stop_ts[_ns] = _now
                    except Exception:
                        pass
                continue

            # No existing stop found -> place one now (STOP-first seatbelt).
            # Recovery safety: cancel any leftover open orders for this symbol first (they can reserve qty and cause 403).
            # Recovery stop race-guard: if we just submitted/placed a stop for this symbol, don't clobber it here
            try:
                gmap = getattr(self.state, 'recent_stop_guard_until', {}) if self.state is not None else {}
                guard_until = float(gmap.get(sym, 0.0) or 0.0)
            except Exception:
                guard_until = 0.0
            if guard_until and now < guard_until:
                # Let the normal entry/stop lifecycle finish; recovery will revisit next cycle if needed
                continue

            # Per-symbol throttle: avoid cancel/replace STOP churn if no material change occurred.
            try:
                last_act = float(self.state.last_recovery_stop_action_ts.get(sym, 0.0) or 0.0)
            except Exception:
                last_act = 0.0
            if last_act and (now - last_act) < 45.0:
                continue

            self._cancel_open_orders_for_symbol(sym, reason='recovery_before_stop', cancel_stops=False)
            try:
                qty_abs = abs(float(p.get("qty") or 0.0))
                if qty_abs <= 0:
                    continue
                exit_side = "sell" if p.get("side") == "long" else "buy"
                entry = float(p.get("avg_entry_price") or 0.0)
                # Treat tiny "dust" as ignorable: do not try to place stops for it.
                if is_crypto_symbol(sym):
                    try:
                        cur_px = float(p.get("current_price") or 0.0) or entry or 0.0
                        notional = (qty_abs * cur_px) if cur_px else 0.0
                    except Exception:
                        notional = 0.0
                    if (qty_abs < CRYPTO_DUST_QTY) or (notional and notional < CRYPTO_DUST_NOTIONAL):
                        self.out_q.put(("WARN", f"WARN  RECOVERY: DUST position; skipping stop for {crypto_data_symbol(sym)} qty={qty_abs:g} notional~${notional:.2f}."))
                        try:
                            self._dust_ignored[sym] = time.time() + 3600
                        except Exception:
                            pass
                        continue
                # Fallback stop distance when indicators aren't available yet (startup recovery).
                # Keep it modest; the goal is *protection*, not perfect strategy.
                dist = 0.0035
                stop_px = entry * (1 - dist) if exit_side == "sell" else entry * (1 + dist)
                stop_px = float(self.client._fmt_price_str(sym, stop_px))

                if is_crypto_symbol(sym):
                    stop_qty = floor_crypto_qty(qty_abs)
                    if stop_qty <= 0:
                        continue
                    _cfg = getattr(self, 'cfg', None)
                    slip_bps = getattr(_cfg, 'slip_bps_crypto', 0.0) if _cfg is not None else 0.0
                    slip = float(slip_bps or 0.0) / 10000.0
                    limit_px = stop_px * (1 - slip) if exit_side == "sell" else stop_px * (1 + slip)
                    limit_px = float(self.client._fmt_price_str(sym, limit_px))
                    o = self.client.submit_order_stop_limit(sym, exit_side, stop_qty, "gtc", stop_px, limit_px)
                else:
                    # Stocks: use a regular stop order (market stop).
                    stop_qty = float(int(qty_abs)) if qty_abs >= 1 else qty_abs
                    o = self.client.submit_order_stop(sym, exit_side, stop_qty, "gtc", stop_px)

                oid = o.get("id") if isinstance(o, dict) else None
                if oid:
                    t.stop_order_id = oid
                    t.stop_px = stop_px
                    stop_by_symbol[sym] = stop_px
                    self._oid_to_leg[oid] = (tid, "stop")
                    try:
                        if is_crypto_symbol(sym):
                            self.state.last_crypto_protect_ts[sym] = time.time()
                        self.state.last_recovery_stop_action_ts[sym] = now
                        self.state.last_recovery_stop_snapshot[sym] = f"{oid}|placed|{exit_side}|{float(stop_qty or 0.0):.8f}|{float(stop_px or 0.0):.8f}"
                    except Exception:
                        pass
                    self.out_q.put(("WARN", f"RECOVERY: placed protective STOP for {sym}: STOP {self.client._fmt_price_str(sym, stop_px)} ({stop_qty})"))
            except Exception as se:
                try:
                    self.state.last_recovery_stop_action_ts[sym] = now
                except Exception:
                    pass
                # If we cannot place a protective stop, flatten immediately (safety first).
                try:
                    qty_abs = abs(float(p.get("qty") or 0.0))
                    if qty_abs > 0:
                        exit_side = "sell" if p.get("side") == "long" else "buy"
                        qty_to_close = floor_crypto_qty(qty_abs) if is_crypto_symbol(sym) else qty_abs
                        # Guard: if we recently detected an existing protective STOP, do NOT flatten just because a duplicate STOP placement failed.
                        try:
                            _ns = normalize_symbol(sym)
                            _now = time.time()
                            _last = None
                            try:
                                _last = self.state.last_existing_stop_ts.get(_ns)
                            except Exception:
                                _last = None
                            if _last is not None and (_now - float(_last)) < 600.0:
                                self.out_q.put(("WARN", f"RECOVERY: STOP place failed for {sym} but existing STOP detected recently; skipping flatten."))
                                continue
                        except Exception:
                            pass
                        self.out_q.put(("WARN", f"RECOVERY: STOP placement failed for {sym} ({se}). Flattening immediately."))
                        try:
                            if is_crypto_symbol(sym):
                                # Crypto: cancel any resting orders that reserve qty, then close full position (no qty).
                                self._cancel_open_orders_for_symbol(sym, reason="recovery_flatten_crypto")
                                self._close_position_with_unreserve(sym, reason='retry_close')
                            else:
                                self.client.submit_order_market(sym, exit_side, qty_to_close, "gtc")
                        except Exception as e2:
                            self.out_q.put(("ERROR", f"RECOVERY: flatten failed for {sym}: {e2}"))
                except Exception:
                    pass

        # Ghost-trade purge: if broker has no position AND no open orders for a symbol, but local state still shows an active trade,
        # clear it so the symbol isn't stuck "busy" forever (common after PANIC / manual closes / restarts).
        try:
            pos_syms = set((pos_by_symbol or {}).keys())
            ord_syms = set()
            for o in (open_orders or []):
                try:
                    osym = normalize_symbol((o or {}).get("symbol") or "")
                    if osym:
                        ord_syms.add(osym)
                except Exception:
                    pass

            now2 = time.time()
            drop_ids = []
            for tid, t in list((self.trades or {}).items()):
                try:
                    sym = normalize_symbol(getattr(t, "symbol", "") or "")
                    if not sym:
                        continue
                    if sym in pos_syms or sym in ord_syms:
                        continue
                    st = str(getattr(t, "state", "") or "")
                    if st.upper() == "CLOSED":
                        drop_ids.append(tid)
                        continue
                    opened_ts = float(getattr(t, "opened_ts", 0.0) or 0.0)
                    if opened_ts and (now2 - opened_ts) < 15.0:
                        continue

                    # Write a reconcile note to journal for forensic clarity (best-effort).
                    try:
                        whyv = (getattr(t, "why_verbose", "") or getattr(t, "why", "") or "n/a").replace("\n"," ").replace("\r"," ").strip()
                        notes = f"reconcile_flat_no_pos_orders | state={st}"
                        write_trade_journal_row(
                            trade_id=str(getattr(t, "trade_id", tid)),
                            symbol=str(getattr(t, "symbol", "")),
                            side=str(getattr(t, "side", "")),
                            qty=float(getattr(t, "qty", 0.0) or 0.0),
                            entry_price=float(getattr(t, "entry_px", 0.0) or 0.0),
                            exit_price=0.0,
                            pnl=0.0,
                            stop_price=float(getattr(t, "stop_px", 0.0) or 0.0),
                            why=str(getattr(t, "why", "") or "reconcile"),
                            why_verbose=whyv,
                            news=str(getattr(t, "news", "") or ""),
                            notes=notes,
                        )
                    except Exception:
                        pass

                    self.out_q.put(("WARN", f"WARN  RECONCILE: clearing ghost trade for {sym} (local={st}) - broker flat/no orders."))
                    drop_ids.append(tid)
                except Exception:
                    pass

            for tid in drop_ids:
                try:
                    self.trades.pop(tid, None)
                except Exception:
                    pass
            try:
                m = getattr(self, '_symbol_to_trade', None)
                if isinstance(m, dict):
                    for sym, tid in list(m.items()):
                        if tid not in (self.trades or {}):
                            m.pop(sym, None)
            except Exception:
                pass
            try:
                for oid, leg in list((self._oid_to_leg or {}).items()):
                    if leg and leg.get("trade_id") and (leg.get("trade_id") not in (self.trades or {})):
                        self._oid_to_leg.pop(oid, None)
            except Exception:
                pass
        except Exception:
            pass

        return stop_by_symbol

    def _loopA_refresh_quotes(self):
        try:
            q = self.client.get_latest_quotes_bulk(self.symbols)
            now = time.time()
            for sym, (bid, ask) in (q or {}).items():
                if not bid or not ask:
                    continue
                mid = (bid + ask) / 2.0
                spread_bps = ((ask - bid) / mid) * 10000.0 if mid else 999999.0
                score = max(0.0, 200.0 - spread_bps)
                prev = self._quote_cache.get(sym)
                if prev and len(prev) >= 4 and prev[3] and mid:
                    pmid = float(prev[3])
                    if pmid > 0:
                        score += min(50.0, abs(mid - pmid) / pmid * 10000.0)
                self._quote_cache[sym] = (now, bid, ask, mid, score)
            self._loopA_errors = 0
            # mark data OK for recovery logic
            self.cb.last_data_ok_ts = time.time()
            if self.cb.enabled:
                self._cb_record('ok', '')
        except Exception as e:
            self._loopA_errors += 1
            self.out_q.put(("WARN", f"LoopA quotes failed: {e}"))
            self._cb_record('api_fail', f"LoopA: {e}")

    def _deep_slice(self):
        # top attention + round robin; always include positions first
        pinned = list(self.pos.keys())
        scored = []
        for sym, rec in self._quote_cache.items():
            try:
                scored.append((float(rec[4]), sym))
            except Exception:
                continue
        scored.sort(reverse=True)
        top = [sym for _, sym in scored[:LOOPB_TOPN] if sym not in pinned]

        rr = []
        rest = [s for s in self.symbols if (s not in pinned and s not in top)]
        if rest:
            start = self._rr_idx % len(rest)
            take = rest[start:start+LOOPB_RR]
            if len(take) < LOOPB_RR:
                take += rest[:(LOOPB_RR-len(take))]
            rr = take
            self._rr_idx = (self._rr_idx + LOOPB_RR) % max(1, len(rest))

        out = []
        seen = set()
        for s in pinned + top + rr:
            if s and s not in seen:
                seen.add(s)
                out.append(s)
        return out


    def _loopB_scan(self):
        """Deep scan selective slice.

        v7.5.8 adds back:
          - indicators
          - deep analysis (limited to a small candidate set to avoid rate limits)
          - safe paper/live order submission
          - fill tracking (REST polling)

        Feed behavior:
          - scan summaries throttled (FEED_SCAN_LOG_SEC)
          - trades always posted immediately as a 3-line block (Option B)
        """
        syms = self._deep_slice()
        if not syms:
            return

        # --- Build attention-ranked list from Loop A quote cache ---
        ranked = []
        for s in syms:
            rec = self._quote_cache.get(s)
            if rec:
                try:
                    ranked.append((float(rec[4]), s))
                except Exception:
                    continue
        ranked.sort(reverse=True)
        top_syms = [s for _, s in ranked[:8]] if ranked else syms[:8]

        # --- Throttle scan chatter ---
        now = time.time()
        if (now - self._last_scan_feed_ts) >= FEED_SCAN_LOG_SEC:
            mode = getattr(self.news_ctx, 'mode', 'CLEAR')
            try:
                mode = str(mode)
            except Exception:
                mode = 'CLEAR'
            top = ','.join(top_syms[:5])
            self.out_q.put(("INFO", f"Scanning: evaluated {len(syms)} symbols. Top attention: {top} (news_mode={mode})"))
            headline = getattr(self.news_ctx, 'headline', '')
            if headline:
                h = headline.strip()
                if len(h) > 160:
                    h = h[:157] + '...'
                self.out_q.put(('DECISION', f"Macro news: {h}"))
            self._last_scan_feed_ts = now

        # --- Trade decision / execution ---
        # Conservative guardrails to avoid runaway trading:
        # - 1 new entry at a time
        # - cooldown per symbol
        # - only trade if we have equity info
        if getattr(self, '_open_orders', None) is None:
            self._open_orders = {}
            self._cooldown = {}
            self._last_order_poll = 0.0
            self._last_equity = None

        # Poll existing orders for updates (Layer 1 lifecycle)
        if self._open_orders and (now - self._last_order_poll) >= max(ORDER_POLL_SEC, 0.5):
            self._last_order_poll = now
            done = []
            for oid, meta in list(self._open_orders.items()):
                trade_id = meta.get('trade_id') or ''
                leg = meta.get('leg') or ''
                sym = meta.get('symbol')
                try:
                    od = self.client.get_order(oid)
                except Exception as e:
                    # transient failures are common; count for CB but don't kill
                    self._cb_record('api_fail', f"order_poll: {e}")
                    continue

                st = str(od.get('status','')).lower()
                filled_qty = float(od.get('filled_qty') or 0.0)
                avg_fill = od.get('filled_avg_price') or od.get('avg_fill_price')
                try:
                    avg_fill = float(avg_fill) if avg_fill is not None else None
                except Exception:
                    avg_fill = None

                # Entry repricing: if limit order is stuck, step it toward market within slip constraints
                if leg == 'entry' and st in ('new','accepted','pending_new','partially_filled'):
                    lp = meta.get('limit_price')
                    last_rp = float(meta.get('last_reprice_ts') or 0.0)
                    if lp is not None and (now - last_rp) >= ORDER_REPRICE_SEC:
                        try:
                            rec = self._quote_cache.get(sym) if sym else None
                            if rec:
                                _, bid, ask, mid, _ = rec
                                slip_bps = self.slip_bps_crypto if is_crypto_symbol(sym) else self.slip_bps_stock
                                if meta.get('side') == 'buy':
                                    new_lp = float(ask) * (1.0 + (slip_bps/10000.0))
                                else:
                                    new_lp = float(bid) * (1.0 - (slip_bps/10000.0))
                                # Cap repricing so we never chase beyond a sane distance from the original mid
                                cap_bps = meta.get('max_reprice_bps')
                                orig_mid = meta.get('orig_mid')
                                if cap_bps and orig_mid and float(orig_mid) > 0:
                                    cap_bps = float(cap_bps)
                                    orig_mid = float(orig_mid)
                                    if meta.get('side') == 'buy':
                                        new_lp = min(new_lp, orig_mid * (1.0 + cap_bps/10000.0))
                                    else:
                                        new_lp = max(new_lp, orig_mid * (1.0 - cap_bps/10000.0))
                                # Normalize decimals
                                new_lp = round(float(new_lp), 6 if is_crypto_symbol(sym) else 2)
                                cur_lp = float(lp)
                                # Only reprice if it improves (buy: higher, sell: lower) and is meaningfully different
                                improve = (new_lp > cur_lp + (1e-9 if is_crypto_symbol(sym) else 1e-6)) if meta.get('side') == 'buy' else (new_lp < cur_lp - (1e-9 if is_crypto_symbol(sym) else 1e-6))
                                if improve:
                                    self.client.replace_order(oid, symbol=sym, limit_price=str(new_lp))
                                    meta['limit_price'] = new_lp
                                    meta['last_reprice_ts'] = now
                                    self.log(f"Repriced {sym} entry limit to {new_lp}")
                        except Exception:
                            pass

                # Terminal states
                if st in ('filled', 'canceled', 'rejected', 'expired', 'done_for_day') or filled_qty > 0:
                    done.append(oid)

                # Handle rejects
                if st in ('rejected',):
                    self.out_q.put(('ERROR', f"Order {oid} rejected ({leg}): {od.get('rejection_reason') or od.get('status') or ''}"))
                    self._cb_record('order_reject', f"{leg} reject")

                if st == 'filled' or filled_qty > 0:
                    # Update trade lifecycle
                    t = self.trades.get(trade_id) if trade_id else None
                    px = avg_fill if avg_fill is not None else meta.get('limit_price')
                    if t is None:
                        # fall back to legacy trade print
                        side = meta.get('side')
                        qty = meta.get('qty')
                        px_s = fmt_price(px, is_crypto=is_crypto_symbol(sym))
                        summary = f"{side.upper()} {sym} qty={qty} @ {px_s} (filled)"
                        self.out_q.put(('TRADE', {'summary': summary, 'why': meta.get('why',''), 'news': meta.get('news','')}))
                        continue

                    if leg == 'entry':
                        t.entry_px = float(px or 0.0)
                        t.entry_order_id = oid
                        t.opened_ts = t.opened_ts or now
                        t.state = 'ENTRY_FILLED'
                        self._pending_entries.pop(norm_symbol(t.symbol), None)

                        # CRYPTO SAFETY: if we got a partial fill, cancel the remaining entry order
                        # before placing a protective STOP. This avoids Alpaca crypto 403 wash-trade rejections
                        # caused by having an open BUY while submitting a SELL stop on the same symbol.
                        if is_crypto_symbol(t.symbol) and filled_qty > 0 and st != 'filled':
                            try:
                                self.out_q.put(('INFO', f'Partial fill on {t.symbol}: canceling remaining entry to allow STOP protectionow'))
                                self.client.cancel_order(oid)
                            except Exception:
                                pass
                            # Prefer broker-reported filled_qty over submitted qty (important for partial crypto fills)
                        inferred_qty = 0.0
                        try:
                            inferred_qty = float(filled_qty or 0.0)
                        except Exception:
                            inferred_qty = 0.0
                        if inferred_qty <= 0:
                            try:
                                inferred_qty = float(meta.get('qty') or 0.0)
                            except Exception:
                                inferred_qty = 0.0
                        # Backstop: if broker position qty disagrees materially, trust the broker
                        live_qty = 0.0
                        try:
                            live_qty = float(self._broker_position_qty(symbol) or 0.0)
                        except Exception:
                            live_qty = 0.0
                        qty_final = inferred_qty
                        if live_qty > 0 and (qty_final <= 0 or qty_final > live_qty * 1.2 or qty_final < live_qty * 0.8):
                            qty_final = live_qty
                        if qty_final > 0:
                            t.qty = float(qty_final)
    
                        # Layer 4: audit entry fill
                        write_trade_event(trade_id=t.trade_id, event="ENTRY_FILLED", symbol=t.symbol, side=t.side, qty=float(t.qty), price=float(t.entry_px or 0.0), state=t.state, why=t.why, news=t.news, meta={"entry_order_id": t.entry_order_id})
    
                        # Plan exits
                        is_c = is_crypto_symbol(t.symbol)
                        qty_full = t.qty
                        # TP1 qty
                        if is_c:
                            # Floor (never round up) so we don't oversubscribe reserved qty on exits
                            _raw = float(qty_full) * float(TP1_FRACTION)
                            _raw = max(_raw, 0.000001)
                            _scale = 1000000
                            tp1_qty = float(int(_raw * _scale)) / _scale
                            tp1_qty = max(tp1_qty, 0.000001)
                        else:
                            tp1_qty = int(max(1, round(qty_full * TP1_FRACTION)))
                        tp1_qty = min(tp1_qty, qty_full)
                        rem = float(qty_full) - float(tp1_qty)
                        t.tp1_qty = float(tp1_qty)
                        t.rem_qty = float(max(0.0, rem))
    
                        # Compute stop / tp1 prices
                        entry = float(t.entry_px or 0.0)
                        atrv = float(t.atr or 0.0)
                        stop_dist = max(atrv * ATR_MULT_STOP, entry * 0.002)
                        tp1_dist = max(atrv * TP1_ATR_MULT, entry * 0.002)
                        if t.side == 'buy':
                            t.stop_px = entry - stop_dist
                            t.tp1_px = entry + tp1_dist
                        else:
                            t.stop_px = entry + stop_dist
                            t.tp1_px = entry - tp1_dist
                        t.trail_amt = max(atrv * TRAIL_ATR_MULT, entry * 0.0015)
    
                        # Build a detailed WHY receipt (circumstances + sizing + gates)
                        try:
                            m = dict(meta or {})
                            eq0 = float(m.get('eq') or 0.0) or float(getattr(self, '_last_equity', 0.0) or 0.0)
                            # Exposure snapshot (best effort from cached positions)
                            total = 0.0
                            crypto = 0.0
                            for ps in self.pos.values():
                                try:
                                    px0 = float(ps.best or ps.entry or 0.0)
                                    n0 = abs(float(ps.qty) * px0)
                                    total += n0
                                    if is_crypto_symbol(ps.symbol):
                                        crypto += n0
                                except Exception:
                                    continue
                            notional = abs(float(t.qty) * float(t.entry_px or 0.0))
                            total_after = total + notional
                            crypto_after = crypto + (notional if is_crypto_symbol(t.symbol) else 0.0)
                            total_pct = (total / eq0) if eq0 else 0.0
                            crypto_pct = (crypto / eq0) if eq0 else 0.0
                            total_after_pct = (total_after / eq0) if eq0 else 0.0
                            crypto_after_pct = (crypto_after / eq0) if eq0 else 0.0
    
                            stop_dist_act = abs(float(t.entry_px or 0.0) - float(t.stop_px or 0.0))
                            risk_budget = float(m.get('risk_budget') or 0.0)
                            est_risk = stop_dist_act * abs(float(t.qty))
    
                            dd = getattr(self, '_dtd_pl_pct', None)
                            dd_pct = (float(dd) * 100.0) if dd is not None else None
    
                            def _pct(x: float) -> str:
                                try:
                                    return f"{float(x)*100.0:.1f}%"
                                except Exception:
                                    return "n/a"
    
                            # Add a compact circumstances receipt under the standard WHY header line
                            size_line = (
                                f"- size: qty={float(t.qty):.6f} notional={fmt_money(notional)} ({_pct(notional/eq0) if eq0 else 'n/a'} eq); "
                                f"stop={fmt_price(t.stop_px, is_crypto=is_c)} dist={fmt_money(stop_dist_act)}; "
                                f"risk_budget={fmt_money(risk_budget)} est_risk={fmt_money(est_risk)}"
                            )
                            gates_line = (
                                f"- gates: crypto_pos_cap={int(MAX_CRYPTO_POSITIONS)}; "
                                f"crypto_exp {_pct(crypto_pct)}->{_pct(crypto_after_pct)}/25%; "
                                f"total_exp {_pct(total_pct)}->{_pct(total_after_pct)}/50%; "
                                f"trades_hr {len(self._trade_ts_hour)}/{int(MAX_TRADES_PER_HOUR)}; "
                                f"dd={dd_pct:.2f}%" if dd_pct is not None else f"- gates: trades_hr {len(self._trade_ts_hour)}/{int(MAX_TRADES_PER_HOUR)}"
                            )
    
                            # Preserve existing summary WHY as first line (already contains indicators/news_align)
                            t.why = (t.why or '').replace("\r"," ").replace("\n"," ").strip()
                            # Phase 3.2: standardized receipt (single-line, CSV-safe)
                            try:
                                nf = parse_news_fields(t.news or "")
                                news_conf = (nf.get("news_conf") or "").strip() or "STALE"
                                news_pub_et = (nf.get("news_pub_et") or "").strip()
                                news_age_m = (nf.get("news_age_m") or "").strip()
                                news_src = (nf.get("news_source") or "").strip()
                                news_head = (nf.get("news_headline") or "").strip()
                            except Exception:
                                news_conf, news_pub_et, news_age_m, news_src, news_head = ("STALE", "", "", "", (t.news or ""))
                            gates_clean = (gates_line or "").replace("\n"," ").replace("\r"," ").strip()
                            size_clean = (size_line or "").replace("\n"," ").replace("\r"," ").strip()
                            ctx = {
                                "id": t.trade_id,
                                "symbol": t.symbol,
                                "side": t.side,
                                "score_total": m.get("score_total", m.get("score", "n/a")),
                                "score_base": m.get("score_base", m.get("base_score", "n/a")),
                                "macro_adj": m.get("macro_adj", m.get("news_macro_adj", 0.0)),
                                "news_boost": m.get("news_boost", m.get("news_sym_boost", 0.0)),
                                "score": m.get("score_total", m.get("score", "n/a")),
                                "dir": m.get("direction", ("BULL" if t.side == "buy" else "BEAR")),
                                "rsi": m.get("rsi", "n/a"),
                                "atr": m.get("atr", getattr(t, "atr", 0.0) or 0.0),
                                "spread": m.get("spread_bps", "n/a"),
                                "risk": m.get("eff_risk_pct", m.get("base_risk_pct", "n/a")),
                                "qty": t.qty,
                                "entry": getattr(t, "entry_px", "n/a"),
                                "stop": getattr(t, "stop_px", "n/a"),
                                "stopdist": locals().get("stop_dist_act", "n/a"),
                                "notional": locals().get("notional", "n/a"),
                                "equity": locals().get("eq0", "n/a"),
                                "gates": (gates_clean + (" ; " + size_clean if size_clean else "")).strip(),
                                "news": f"{news_conf} {news_pub_et} age={news_age_m}m {news_src} {news_head}".strip(),
                            }
                            try:
                                t.receipt_ctx = dict(ctx)
                            except Exception:
                                t.receipt_ctx = {}
                            t.why_verbose = generate_verbose_receipt(ctx)
                            # Keep compact feed WHY accurate for later legs
                            try:
                                t.news_boost = float(ctx.get('news_boost', 0.0) or 0.0)
                                t.macro_adj = float(ctx.get('macro_adj', 0.0) or 0.0)
                            except Exception:
                                pass
                            # Phase 3: journal an ENTRY row (exit blank) for full trade traceability
                            try:
                                write_trade_journal_row(trade_id=t.trade_id, symbol=t.symbol, side=t.side,
                                    qty=float(t.qty or 0.0), entry_price=float(t.entry_px or 0.0), exit_price=None, pnl=0.0,
                                    why=t.why, why_verbose=(getattr(t,'why_verbose','') or '').strip(), news=t.news,
                                    stop_price=float(getattr(t,'stop_px',0.0) or 0.0), notes="entry_filled")
                            except Exception:
                                pass
                            write_trade_receipt(trade_id=t.trade_id, stage='ENTRY_FILLED', receipt={
                                'symbol': t.symbol,
                                'side': t.side,
                                'score': m.get('score'),
                                'news_mode': m.get('news_mode'),
                                'entry_px': float(t.entry_px or 0.0),
                                'qty': float(t.qty or 0.0),
                                'notional': float(notional),
                                'stop_px': float(t.stop_px or 0.0),
                                'tp1_px': float(t.tp1_px or 0.0),
                                'stop_dist': float(stop_dist_act),
                                'risk_budget': float(risk_budget),
                                'est_risk': float(est_risk),
                                'equity': float(eq0),
                                'exposure_total_pct_before': float(total_pct),
                                'exposure_total_pct_after': float(total_after_pct),
                                'exposure_crypto_pct_before': float(crypto_pct),
                                'exposure_crypto_pct_after': float(crypto_after_pct),
                                'trades_hour': int(len(self._trade_ts_hour)),
                                'trades_day': int(len(self._trade_ts_day)),
                                'dtd_pl_pct': float(dd) if dd is not None else None,
                                'time_stop_min': int(TIME_STOP_MINUTES),
                            })
                        except Exception:
                            pass
    
                        # Submit exit orders: TP1 + STOP
                        # NOTE: Alpaca will reject multiple exit orders whose combined qty exceeds position qty.
                        # To keep TP1 + STOP compatible without broker-side OCO/bracket, we size the STOP to the
                        # remaining qty (qty_full - tp1_qty). This preserves lifecycle testing and prevents
                        # "insufficient balance/position" rejects. For LIVE hardening, we can upgrade to a
                        # managed-OCO approach (cancel/replace stop when TP1 triggers) so the full position
                        # remains protected.
                        exit_side = 'sell' if t.side == 'buy' else 'buy'
                        tif_exit = 'gtc' if is_c else 'day'
                        try:
                            def _floor_pos(x, decimals=6):
                                x = float(x or 0.0)
                                if x <= 0.0:
                                    return 0.0
                                s = 10 ** int(decimals)
                                return float(int(x * s)) / s
    
                            def _parse_available(msg: str):
                                try:
                                    m2 = re.search(r"available:\s*([0-9]*\.?[0-9]+)", msg or "")
                                except Exception:
                                    m2 = None
                                if not m2:
                                    return None
                                try:
                                    return float(m2.group(1))
                                except Exception:
                                    return None
    
                            # CRYPTO NOTE (Alpaca): placing TP1 + STOP as separate orders can be rejected
                            # with a 403 "wash trade detected / use complex orders". Safety-first behavior:
                            # place a protective STOP first, and keep TP1 as a *synthetic* target (no broker
                            # TP1 order) until we implement a fully managed OCO.

                            if is_c:
                                # STOP qty: full position, floored (never rounded up), with tiny epsilon.
                                stop_qty = _floor_pos(max(float(qty_full) - 0.000001, 0.0), 6)
                            else:
                                # Stocks: STOP protects the *remainder* after TP1.
                                stop_qty = float(qty_full) - float(tp1_qty)
                                stop_qty = int(max(0, round(stop_qty)))
    
                            def _submit_stop(_qty):
                                if not _qty:
                                    return None
                                if is_c:
                                    slip_bps = self.slip_bps_crypto
                                    if exit_side == 'sell':
                                        lim = float(t.stop_px) * (1.0 - (slip_bps/10000.0))
                                    else:
                                        lim = float(t.stop_px) * (1.0 + (slip_bps/10000.0))
                                    return self.client.submit_order_stop_limit(t.symbol, exit_side, _qty, tif_exit, t.stop_px, lim)
                                else:
                                    return self.client.submit_order_stop(t.symbol, exit_side, _qty, 'gtc', t.stop_px)
    
                            od_st = None
                            _stop_err = None

                            # First attempt
                            try:
                                if is_c:
                                    if float(stop_qty) > 0:
                                        od_st = _submit_stop(stop_qty)
                                else:
                                    if int(stop_qty) > 0:
                                        od_st = _submit_stop(stop_qty)
                            except Exception as _e:
                                _stop_err = _e

                                # Crypto STOP placement can sometimes fail immediately after an entry with
                                # HTTP 403 'insufficient balance' because the position/available qty isn't
                                # visible yet or qty is temporarily reserved. Treat as transient and retry
                                # a few times after short sleeps, using broker position qty if available.
                                if is_c and is_insufficient_balance_err(_e):
                                    last = _e
                                    for delay in (0.5, 1.0, 2.0):
                                        try:
                                            time.sleep(delay)
                                            try:
                                                # Release any non-stop working orders that could reserve qty
                                                self._cancel_open_orders_for_symbol(t.symbol, cancel_stops=False, reason='stop_retry')
                                            except Exception:
                                                pass
                                            # Prefer broker position qty if we can fetch it
                                            qty_try = None
                                            try:
                                                pos = self.client.get_position(t.symbol)
                                                qty_try = abs(float(getattr(pos, 'qty', 0.0) or 0.0))
                                            except Exception:
                                                qty_try = None
                                            q = qty_try if (qty_try and qty_try > 0) else float(stop_qty)
                                            q = max(0.0, q - 0.000001)
                                            q = _floor_pos(q, 6)
                                            if q > 0:
                                                od_st = _submit_stop(q)
                                                stop_qty = q
                                                _stop_err = None
                                                break
                                        except Exception as _e2:
                                            last = _e2
                                            _stop_err = _e2
                                    # If still failing, fall through to the older 'available qty' parse retry below.

                                # Retry once using broker-reported available qty (crypto only)
                                _av = _parse_available(str(_stop_err)) if _stop_err is not None else None
                                if _av is not None and is_c and _stop_err is not None:
                                    _safe = _floor_pos(max(_av - 0.000001, 0.0), 6)
                                    if _safe > 0:
                                        try:
                                            od_st = _submit_stop(_safe)
                                            stop_qty = _safe
                                            _stop_err = None
                                        except Exception as _e2:
                                            _stop_err = _e2

                            if _stop_err is not None:
                                raise _stop_err
    
                            oid_st = str((od_st or {}).get('id') or '')
                            if oid_st:
                                t.stop_order_id = oid_st
                                self._open_orders[oid_st] = {'trade_id': t.trade_id, 'leg':'stop', 'symbol':t.symbol, 'side': exit_side, 'qty': stop_qty, 'stop_price': t.stop_px, 'ts': now, 'why': feed_why_for_trade(t), 'news': t.news}

                            if is_c:
                                # Keep TP1 as a synthetic target for now (no broker TP1 order).
                                t.tp1_order_id = ''
                                t.state = 'PROTECT_ONLY'
                                write_trade_event(trade_id=t.trade_id, event="EXITS_PLACED", symbol=t.symbol, side=t.side, qty=float(t.qty), price=float(t.entry_px or 0.0), state=t.state, why=t.why, news=t.news, meta={"tp1_px": float(t.tp1_px or 0.0), "tp1_qty": float(t.tp1_qty or 0.0), "stop_px": float(t.stop_px or 0.0), "stop_qty": float(stop_qty or 0.0), "tp1_active": False, "mode": "CRYPTO_STOP_ONLY"})
                                try:
                                    if is_c:
                                        self.state.last_crypto_protect_ts[t.symbol] = time.time()
                                except Exception:
                                    pass
                                self.out_q.put(('INFO', f"Placed protective STOP for {t.symbol}: STOP {fmt_price(t.stop_px, is_crypto=True)} ({stop_qty}) (TP1 synthetic target {fmt_price(t.tp1_px, is_crypto=True)})"))
                                # Stop placed: extend race-guard so broker-recovery won't cancel/replace this stop immediately
                                try:
                                    if self.state is not None:
                                        d = getattr(self.state, 'recent_stop_guard_until', None)
                                        if d is None:
                                            self.state.recent_stop_guard_until = {}
                                            d = self.state.recent_stop_guard_until
                                        d[t.symbol] = time.time() + 30.0
                                except Exception:
                                    pass
                            else:
                                # Stocks: submit TP1 then STOP remainder (existing behavior).
                                od_tp = self.client.submit_order_limit(t.symbol, exit_side, tp1_qty, tif_exit, t.tp1_px, extended_hours=False)
                                oid_tp = str(od_tp.get('id') or '')
                                if oid_tp:
                                    t.tp1_order_id = oid_tp
                                    self._open_orders[oid_tp] = {'trade_id': t.trade_id, 'leg':'tp1', 'symbol':t.symbol, 'side': exit_side, 'qty': tp1_qty, 'limit_price': t.tp1_px, 'ts': now, 'why': feed_why_for_trade(t), 'news': t.news}
                                t.state = 'TP1_WORKING' if getattr(t, 'tp1_order_id', '') else 'PROTECT_ONLY'
                                write_trade_event(trade_id=t.trade_id, event="EXITS_PLACED", symbol=t.symbol, side=t.side, qty=float(t.qty), price=float(t.entry_px or 0.0), state=t.state, why=t.why, news=t.news, meta={"tp1_px": float(t.tp1_px or 0.0), "tp1_qty": float(t.tp1_qty or 0.0), "stop_px": float(t.stop_px or 0.0), "stop_qty": float(stop_qty or 0.0), "tp1_active": bool(getattr(t, 'tp1_order_id', ''))})
                                if getattr(t, 'tp1_order_id', ''):
                                    self.out_q.put(('INFO', f"Placed exits for {t.symbol}: TP1 {fmt_price(t.tp1_px, is_crypto=False)} ({tp1_qty}) + STOP {fmt_price(t.stop_px, is_crypto=False)} ({stop_qty})"))
                                else:
                                    self.out_q.put(('INFO', f"Placed protective STOP for {t.symbol}: STOP {fmt_price(t.stop_px, is_crypto=False)} ({stop_qty})"))
                        except Exception as e:
                            self.out_q.put(('ERROR', f"Exit placement failed for {t.symbol}: {e}"))
                            self._cb_record('api_fail', f"exit_place: {e}")

                            # Safety-first: if we couldn't place a protective STOP for crypto,
                            # immediately attempt to flatten that position so we never leave
                            # an unprotected remainder.
                            if is_crypto_symbol(t.symbol):
                                # Seatbelt: avoid false panic-closes when a protective STOP already exists (or was just placed).
                                try:
                                    _sym = t.symbol
                                    _now = time.time()
                                    _grace = 20.0  # seconds
                                    _last = None
                                    try:
                                        _d = getattr(self.state, "last_crypto_protect_ts", {})
                                        _last = _d.get(_sym)
                                        if _last is None:
                                            _last = _d.get(normalize_symbol_for_orders(_sym))
                                    except Exception:
                                        _last = None
                                    if getattr(t, "stop_order_id", "") or (_last is not None and (_now - float(_last)) < _grace):
                                        self.out_q.put(("WARN", f"WARN  Seatbelt: skip immediate close for {_sym} (protective STOP present/recent)"))
                                    else:
                                        # Check broker open orders for an existing SELL stop/stop_limit on this symbol.
                                        _has_stop = False
                                        try:
                                            _orders = self.client.list_orders(status="open", limit=500)
                                            _sym_norm = normalize_symbol_for_orders(_sym)
                                            for _o in (_orders or []):
                                                if str(_o.get("symbol") or "") != _sym_norm:
                                                    continue
                                                if str(_o.get("side") or "").lower() != "sell":
                                                    continue
                                                _t = str(_o.get("type") or "").lower()
                                                if _t in ("stop", "stop_limit"):
                                                    _has_stop = True
                                                    break
                                        except Exception:
                                            _has_stop = False
                                        if _has_stop:
                                            self.out_q.put(("WARN", f"WARN  Seatbelt: skip immediate close for {_sym} (broker protective STOP exists)"))
                                        else:
                                            self.out_q.put(("WARN", f"WARN  Unprotected crypto risk: attempting immediate close for {_sym}..."))
                                            # Cancel any open orders first (they can reserve qty and cause "insufficient balance" on the close call).
                                            self._cancel_open_orders_for_symbol(_sym)
                                            self.client.close_position(_sym)
                                            self.out_q.put(("WARN", f"WARN  Submitted close for {_sym} after exit placement failure."))
                                except Exception as e2:
                                    self.out_q.put(("ERROR", f"PANIC close failed for {t.symbol}: {e2}"))
                        # Print Option B trade block for entry fill
                        px_s = fmt_price(t.entry_px, is_crypto=is_crypto_symbol(t.symbol))
                        self.out_q.put(('TRADE', {'summary': f"{t.side.upper()} {t.symbol} qty={t.qty} @ {px_s} (filled)", 'why': feed_why_for_trade(t), 'news': t.news}))
    
                    elif leg == 'tp1':
                        # TP1 filled: move to trailing on remainder
                        self.out_q.put(('INFO', f"TP1 filled for {t.symbol}. Preparing trailing exit on remainder..."))
                        # Layer 4: audit TP1 fill realized PnL
                        _tpq = float(meta.get("qty") or filled_qty or t.tp1_qty or 0.0)
                        _ex = float(px or 0.0)
                        _en = float(t.entry_px or 0.0)
                        _pnl = ((_ex - _en) * _tpq) if t.side == "buy" else ((_en - _ex) * _tpq)
                        write_trade_event(trade_id=t.trade_id, event="TP1_FILLED", symbol=t.symbol, side=t.side, qty=_tpq, price=_ex, pnl=_pnl, state=t.state, why=t.why, news=t.news, meta={"tp1_qty": _tpq})
                        try:
                            t.realized_pnl = float(getattr(t, "realized_pnl", 0.0)) + float(_pnl)
                            t.realized_qty = float(getattr(t, "realized_qty", 0.0)) + float(_tpq)
                        except Exception:
                            pass


                        # Cancel stop and replace with trailing for remaining qty, or close if no remainder
                        if t.rem_qty <= 0.0:
                            # closed in full
                            if t.stop_order_id:
                                try: self.client.cancel_order(t.stop_order_id)
                                except Exception: pass
                            t.state = 'CLOSED'
                            write_trade_event(trade_id=t.trade_id, event="CLOSED", symbol=t.symbol, side=t.side, qty=float(getattr(t, "realized_qty", 0.0)), price=float(_ex), pnl=float(getattr(t, "realized_pnl", 0.0)), state="CLOSED", why=t.why, news=t.news, meta={"closed_leg": "tp1_full"})
                            try:
                                _why_v = (getattr(t, 'why_verbose', '') or '').strip() or (t.why or '')
                                _notes = "closed_leg=tp1_full | close_reason=tp1_full"
                                final_whyv = build_final_why_verbose(t, close_leg="tp1_full", close_reason="tp1_full", exit_price=float(_ex or 0.0), pnl=float(getattr(t,'realized_pnl',0.0) or 0.0), cooldown=str(getattr(t,'cooldown_note','') or ''))
                                write_trade_journal_row(trade_id=t.trade_id, symbol=t.symbol, side=t.side, qty=float(getattr(t,'realized_qty',0.0) or t.qty or 0.0), entry_price=float(t.entry_px or 0.0), exit_price=float(_ex or 0.0), pnl=float(getattr(t,'realized_pnl',0.0) or 0.0), why=t.why, why_verbose=final_whyv, news=t.news, stop_price=float(getattr(t,'stop_px',0.0) or 0.0), notes=_notes)
                                try:
                                    write_trade_receipt(trade_id=t.trade_id, stage="CLOSED", receipt={
                                        "event": "CLOSED",
                                        "symbol": t.symbol,
                                        "side": t.side,
                                        "qty": float(getattr(t,'realized_qty',0.0) or t.qty or 0.0),
                                        "entry_price": float(t.entry_px or 0.0),
                                        "exit_price": float(_ex or 0.0),
                                        "pnl": float(getattr(t,'realized_pnl',0.0) or 0.0),
                                        "stop_price": float(getattr(t,'stop_px',0.0) or 0.0),
                                        "why": t.why,
                                        "why_verbose": (getattr(t,'why_verbose','') or '').strip(),
                                        "news": t.news,
                                        "news_fields": parse_news_fields(t.news or ""),
                                    })
                                except Exception:
                                    pass

                            except Exception:
                                pass
                            _pxs = fmt_price(_ex, is_crypto=is_crypto_symbol(t.symbol))
                            self.out_q.put(("TRADE", {"summary": f"CLOSED TP1 {t.symbol} qty={_tpq} @ {_pxs} (filled)", "why": feed_why_for_trade(t), "news": t.news}))
                            try: compute_analytics()
                            except Exception: pass

                        else:
                            # Start trailing on remainder WITHOUT ever dropping the protective STOP.
                            exit_side = 'sell' if t.side == 'buy' else 'buy'
                            is_c = is_crypto_symbol(t.symbol)

                            # Refresh remainder from broker (authoritative) to avoid over-requesting.
                            try:
                                rp = self._broker_position_qty(t.symbol)
                                if rp is not None and rp > 0:
                                    t.rem_qty = floor_crypto_qty(rp) if is_c else int(max(0, round(rp)))
                            except Exception:
                                pass

                            if float(t.rem_qty or 0.0) <= 1e-6:
                                t.state = 'CLOSED'
                                write_trade_event(trade_id=t.trade_id, event='CLOSED', symbol=t.symbol, side=t.side, qty=float(getattr(t, 'realized_qty', 0.0)), price=float(_ex), pnl=float(getattr(t, 'realized_pnl', 0.0)), state='CLOSED', why=t.why, news=t.news, meta={'closed_leg': 'tp1'})
                                try:
                                    _why_v = (getattr(t, 'why_verbose', '') or '').strip() or (t.why or '')
                                    _notes = "closed_leg=" + str(leg) + " | close_reason=" + str(leg)
                                    final_whyv = build_final_why_verbose(t, close_leg=str(leg), close_reason=str(leg), exit_price=float(_ex or 0.0), pnl=float(getattr(t,'realized_pnl',0.0) or 0.0), cooldown=str(getattr(t,'cooldown_note','') or ''))
                                    write_trade_journal_row(trade_id=t.trade_id, symbol=t.symbol, side=t.side, qty=float(getattr(t,'realized_qty',0.0) or t.qty or 0.0), entry_price=float(t.entry_px or 0.0), exit_price=float(_ex or 0.0), pnl=float(getattr(t,'realized_pnl',0.0) or 0.0), why=t.why, why_verbose=final_whyv, news=t.news, stop_price=float(getattr(t,'stop_px',0.0) or 0.0), notes=_notes)
                                    try:
                                        write_trade_receipt(trade_id=t.trade_id, stage="CLOSED", receipt={
                                            "event": "CLOSED",
                                            "symbol": t.symbol,
                                            "side": t.side,
                                            "qty": float(getattr(t,'realized_qty',0.0) or t.qty or 0.0),
                                            "entry_price": float(t.entry_px or 0.0),
                                            "exit_price": float(_ex or 0.0),
                                            "pnl": float(getattr(t,'realized_pnl',0.0) or 0.0),
                                            "stop_price": float(getattr(t,'stop_px',0.0) or 0.0),
                                            "why": t.why,
                                            "why_verbose": (getattr(t,'why_verbose','') or '').strip(),
                                            "news": t.news,
                                            "news_fields": parse_news_fields(t.news or ""),
                                        })
                                    except Exception:
                                        pass

                                except Exception:
                                    pass
                                try:
                                    compute_analytics()
                                except Exception:
                                    pass
                            else:
                                old_stop_id = getattr(t, 'stop_order_id', '')
                                old_stop_px = float(getattr(t, 'stop_px', 0.0) or 0.0)

                                # If we recently failed trailing on this symbol, don't keep hammering.
                                try:
                                    if getattr(t, 'trail_disabled_until_ts', 0.0) and now < float(getattr(t, 'trail_disabled_until_ts', 0.0)):
                                        # stay protected by old stop
                                        t.state = 'PROTECT_ONLY'
                                        raise RuntimeError('trail_disabled_cooldown')
                                except Exception:
                                    # ignore
                                    pass

                                try:
                                    if not is_c:
                                        # STOCKS: converting STOP -> TRAILING requires freeing reserved qty.
                                        # Approach (safety-first):
                                        # 1) cancel existing protective STOP (qty reservation)
                                        # 2) place trailing stop for remainder
                                        # 3) if trailing fails, immediately restore protective STOP (or flatten if even that fails)

                                        # Step 1: cancel existing stop to free qty
                                        if old_stop_id:
                                            try:
                                                self.client.cancel_order(old_stop_id)
                                            except Exception:
                                                pass
                                            try:
                                                self._open_orders.pop(old_stop_id, None)
                                            except Exception:
                                                pass
                                        t.stop_order_id = ''

                                        # Step 2: submit trailing stop
                                        # Submit trailing stop (retry once if cancellation propagation is laggy)
                                        try:
                                            od_tr = self.client.submit_order_trailing_stop(t.symbol, exit_side, t.rem_qty, 'gtc', trail_price=t.trail_amt)
                                        except Exception as _te1:
                                            msg = str(_te1)
                                            if ('insufficient qty' in msg) or ('available' in msg):
                                                try:
                                                    import time as _time
                                                    _time.sleep(0.25)
                                                except Exception:
                                                    pass
                                                od_tr = self.client.submit_order_trailing_stop(t.symbol, exit_side, t.rem_qty, 'gtc', trail_price=t.trail_amt)
                                            else:
                                                raise

                                        oid_tr = str((od_tr or {}).get('id') or '')
                                        if oid_tr:
                                            t.trail_order_id = oid_tr
                                            self._open_orders[oid_tr] = {'trade_id': t.trade_id, 'leg':'trail', 'symbol':t.symbol, 'side': exit_side, 'qty': float(t.rem_qty), 'trail_price': t.trail_amt, 'ts': now, 'why': feed_why_for_trade(t), 'news': t.news}
                                            t.state = 'TRAIL_WORKING'
                                            write_trade_event(trade_id=t.trade_id, event='TRAIL_STARTED', symbol=t.symbol, side=t.side, qty=float(t.rem_qty), price=float(px or 0.0), state=t.state, why=t.why, news=t.news, meta={'trail_amt': float(t.trail_amt or 0.0), 'mode':'stock_trailing'})
                                        else:
                                            raise RuntimeError('trail_order_no_id')
                                    else:
                                        # crypto: emulate trailing via stop_limit refresh; place NEW stop first, then cancel old
                                        write_trade_event(trade_id=t.trade_id, event='TRAIL_STARTED', symbol=t.symbol, side=t.side, qty=float(t.rem_qty), price=float(px or 0.0), state='TRAIL_WORKING', why=t.why, news=t.news, meta={'trail_amt': float(t.trail_amt or 0.0), 'mode': 'crypto_emulated'})
                                        t.state = 'TRAIL_WORKING'
                                        t.last_trail_update_ts = 0.0
                                        t.best_px = float(t.entry_px or 0.0)

                                        stop_px = float(old_stop_px or t.stop_px or 0.0)
                                        if stop_px <= 0:
                                            stop_px = float(_ex) * 0.995

                                        slip_bps = self.slip_bps_crypto
                                        def _submit(qty_use: float):
                                            lim = stop_px * (1.0 - (slip_bps/10000.0)) if exit_side=='sell' else stop_px * (1.0 + (slip_bps/10000.0))
                                            return self.client.submit_order_stop_limit(t.symbol, exit_side, qty_use, 'gtc', stop_px, lim)

                                        q0 = floor_crypto_qty(float(t.rem_qty))
                                        try:
                                            od_st = _submit(q0)
                                        except Exception as e1:
                                            av = parse_available_qty(str(e1))
                                            if av is not None:
                                                q1 = floor_crypto_qty(av)
                                                if q1 > 0:
                                                    od_st = _submit(q1)
                                                    q0 = q1
                                                else:
                                                    raise
                                            else:
                                                raise

                                        oid_st = str((od_st or {}).get('id') or '')
                                        if oid_st:
                                            t.stop_order_id = oid_st
                                            t.stop_px = stop_px
                                            self._open_orders[oid_st] = {'trade_id': t.trade_id, 'leg':'stop', 'symbol':t.symbol, 'side': exit_side, 'qty': float(q0), 'stop_price': stop_px, 'ts': now, 'why': feed_why_for_trade(t), 'news': t.news}
                                            if old_stop_id:
                                                try:
                                                    self.client.cancel_order(old_stop_id)
                                                except Exception:
                                                    pass
                                        else:
                                            raise RuntimeError('trail_stop_no_id')
                                except Exception as e:
                                    # STOCKS NOTE: we may have canceled the protective stop to free reserved qty.
                                    # Ensure we end this block with protection in place.
                                    t.state = 'PROTECT_ONLY'
                                    # Cooldown trailing attempts on this symbol for a while
                                    try:
                                        t.trail_disabled_until_ts = now + 30*60
                                    except Exception:
                                        pass

                                    try:
                                        if not is_c:
                                            # Restore protective STOP immediately (or flatten if that also fails)
                                            # Refresh remaining qty authoritatively
                                            rp2 = None
                                            try:
                                                rp2 = self._broker_position_qty(t.symbol)
                                            except Exception:
                                                rp2 = None
                                            rem_int = int(max(0, round(rp2))) if rp2 is not None else int(max(0, round(float(t.rem_qty or 0.0))))
                                            if rem_int <= 0:
                                                # nothing left to protect
                                                t.stop_order_id = ''
                                                t.stop_px = old_stop_px
                                            else:
                                                stop_px_use = float(old_stop_px or t.stop_px or 0.0)
                                                if stop_px_use <= 0:
                                                    stop_px_use = float(t.entry_px or 0.0) * 0.995
                                                try:
                                                    od_rs = self.client.submit_order_stop(t.symbol, exit_side, rem_int, 'gtc', stop_px_use)
                                                    oid_rs = str((od_rs or {}).get('id') or '')
                                                    if oid_rs:
                                                        t.stop_order_id = oid_rs
                                                        t.stop_px = stop_px_use
                                                        self._open_orders[oid_rs] = {'trade_id': t.trade_id, 'leg':'stop', 'symbol':t.symbol, 'side': exit_side, 'qty': rem_int, 'stop_price': stop_px_use, 'ts': now, 'why': feed_why_for_trade(t), 'news': t.news}
                                                        write_trade_event(trade_id=t.trade_id, event='TRAIL_SETUP_FAILED_RESTORED_STOP', symbol=t.symbol, side=t.side, qty=float(rem_int), price=float(px or 0.0), state='PROTECT_ONLY', why=t.why, news=t.news, meta={'err': str(e)[:180]})
                                                    else:
                                                        raise RuntimeError('restore_stop_no_id')
                                                except Exception as e2:
                                                    # Last resort: flatten remainder to remove unmanaged risk
                                                    self.out_q.put(('WARN', f"Trailing setup failed and STOP restore failed for {t.symbol}; flattening remainder. {e2}"))
                                                    try:
                                                        od_m = self.client.submit_order_market(t.symbol, exit_side, rem_int, 'day')
                                                        oid_m = str((od_m or {}).get('id') or '')
                                                        if oid_m:
                                                            t.flatten_order_id = oid_m
                                                            self._open_orders[oid_m] = {'trade_id': t.trade_id, 'leg':'flatten', 'symbol':t.symbol, 'side': exit_side, 'qty': rem_int, 'ts': now, 'why': feed_why_for_trade(t), 'news': t.news}
                                                    except Exception:
                                                        pass
                                        else:
                                            # Crypto path: we did not cancel the stop unless replacement succeeded.
                                            t.stop_order_id = old_stop_id
                                            t.stop_px = old_stop_px
                                    except Exception:
                                        # ultra defensive: keep old stop reference
                                        t.stop_order_id = old_stop_id
                                        t.stop_px = old_stop_px

                                    self.out_q.put(('ERROR', f"Trailing setup failed for {t.symbol}; protective STOP preserved/restored. {e}"))
                                    # Do NOT trip the global circuit breaker for trailing failures.


                    elif leg in ('stop','trail'):
                        # IMPORTANT: do NOT flatten on PARTIAL stop/trail fills.
                        # If the protective order is only partially filled, the remaining position is still protected
                        # by the remaining stop quantity. Flattening here would close the remainder at market and can
                        # cause oversized losses.
                        try:
                            _status = str(meta.get('status') or meta.get('order_status') or '').lower().strip()
                            _oqty = float(meta.get('qty') or meta.get('order_qty') or 0.0)
                            _fqty = float(filled_qty or meta.get('filled_qty') or meta.get('filled') or 0.0)
                            _is_full = (_status == 'filled') or (_oqty > 0 and _fqty >= (_oqty - max(1e-6, _oqty*1e-6)))
                            _is_partial = (_status in ('partially_filled','partial_fill','partially-filled')) or (_oqty > 0 and _fqty > 0 and not _is_full)
                        except Exception:
                            _is_full = True
                            _is_partial = False
                        if _is_partial:
                            # record the partial fill and keep the stop/trail working
                            self.out_q.put(('INFO', f"Exit PARTIAL ({leg}) for {t.symbol}: filled={_fqty:g} of {_oqty:g}. Keeping protective order active (no flatten)."))
                            _exq = float(filled_qty or meta.get('qty') or 0.0)
                            _expx = float(px or 0.0)
                            _enpx = float(t.entry_px or 0.0)
                            _pnl2 = ((_expx - _enpx) * _exq) if t.side == 'buy' else ((_enpx - _expx) * _exq)
                            try:
                                t.realized_pnl = float(getattr(t, 'realized_pnl', 0.0)) + float(_pnl2)
                                t.realized_qty = float(getattr(t, 'realized_qty', 0.0)) + float(_exq)
                            except Exception:
                                pass
                            write_trade_event(trade_id=t.trade_id, event='EXIT_PARTIAL', symbol=t.symbol, side=t.side, qty=_exq, price=_expx, pnl=_pnl2, state=t.state, why=t.why, news=t.news, meta={'leg': leg, 'status': meta.get('status', '')})
                            _pxs = fmt_price(_expx, is_crypto=is_crypto_symbol(t.symbol))
                            self.out_q.put(('TRADE', {'summary': f"EXIT {leg.upper()} PARTIAL {t.symbol} qty={_exq} @ {_pxs} (filled)", 'why': feed_why_for_trade(t), 'news': t.news}))
                            continue

                        # Protective exit filled. If this stop/trail was sized for the *remainder* (to avoid broker rejects),
                        # the position may still have TP1-size leftover. Safety-first behavior:
                        # - cancel any remaining exit legs
                        # - immediately FLATTEN the remaining position (seatbelt first)
                        self.out_q.put(('INFO', f"Exit filled ({leg}) for {t.symbol}. Canceling remaining legs + flattening any leftover qty."))

                        # Layer 4: audit exit fill realized PnL (this leg)
                        _exq = float(filled_qty or meta.get("qty") or 0.0)
                        _expx = float(px or 0.0)
                        _enpx = float(t.entry_px or 0.0)
                        _pnl2 = ((_expx - _enpx) * _exq) if t.side == "buy" else ((_enpx - _expx) * _exq)
                        try:
                            t.realized_pnl = float(getattr(t, "realized_pnl", 0.0)) + float(_pnl2)
                            t.realized_qty = float(getattr(t, "realized_qty", 0.0)) + float(_exq)
                        except Exception:
                            pass
                        write_trade_event(trade_id=t.trade_id, event="EXIT_FILLED", symbol=t.symbol, side=t.side, qty=_exq, price=_expx, pnl=_pnl2, state=t.state, why=t.why, news=t.news, meta={"leg": leg})

                        # Option B exit block (this leg)
                        _pxs = fmt_price(_expx, is_crypto=is_crypto_symbol(t.symbol))
                        self.out_q.put(("TRADE", {"summary": f"EXIT {leg.upper()} {t.symbol} qty={_exq} @ {_pxs} (filled)", "why": feed_why_for_trade(t), "news": t.news}))

                        # Cancel known remaining legs
                        for other in [getattr(t, 'tp1_order_id', ''), getattr(t, 'stop_order_id', ''), getattr(t, 'trail_order_id', ''), getattr(t, 'flatten_order_id', '')]:
                            if other and other != oid:
                                try:
                                    self.client.cancel_order(other)
                                except Exception:
                                    pass

                        # Estimate remaining qty still open and flatten it (do NOT assume CLOSED yet)
                        try:
                            _full = float(getattr(t, 'qty', 0.0) or 0.0)
                            _real = float(getattr(t, 'realized_qty', 0.0) or 0.0)
                            _rem = max(0.0, _full - _real)
                        except Exception:
                            _rem = 0.0                        # Override remainder using broker position qty when possible (more reliable than realized_qty math)
                        try:
                            _pos_qty = abs(self._broker_position_qty(t.symbol))
                            if _pos_qty > 0.0:
                                _rem = _pos_qty
                        except Exception:
                            pass
                        # If remainder is tiny, treat as closed
                        if _rem <= 1e-6:
                            t.state = 'CLOSED'
                            write_trade_event(trade_id=t.trade_id, event="CLOSED", symbol=t.symbol, side=t.side, qty=float(getattr(t, "realized_qty", 0.0)), price=float(_expx), pnl=float(getattr(t, "realized_pnl", 0.0)), state="CLOSED", why=t.why, news=t.news, meta={"closed_leg": leg, "note": "no remainder"})
                            try:
                                _why_v = (getattr(t, 'why_verbose', '') or '').strip() or (t.why or '')
                                _notes = "closed_leg=" + str(leg) + " | close_reason=" + str(leg)
                                final_whyv = build_final_why_verbose(t, close_leg=str(leg), close_reason=str(leg), exit_price=float(_expx or 0.0), pnl=float(getattr(t,'realized_pnl',0.0) or 0.0), cooldown=str(getattr(t,'cooldown_note','') or ''))
                                write_trade_journal_row(trade_id=t.trade_id, symbol=t.symbol, side=t.side, qty=float(getattr(t,'realized_qty',0.0) or t.qty or 0.0), entry_price=float(t.entry_px or 0.0), exit_price=float(_expx or 0.0), pnl=float(getattr(t,'realized_pnl',0.0) or 0.0), why=t.why, why_verbose=final_whyv, news=t.news, stop_price=float(getattr(t,'stop_px',0.0) or 0.0), notes=_notes)
                                try:
                                    write_trade_receipt(trade_id=t.trade_id, stage="CLOSED", receipt={
                                        "event": "CLOSED",
                                        "symbol": t.symbol,
                                        "side": t.side,
                                        "qty": float(getattr(t,'realized_qty',0.0) or t.qty or 0.0),
                                        "entry_price": float(t.entry_px or 0.0),
                                        "exit_price": float(_ex or 0.0),
                                        "pnl": float(getattr(t,'realized_pnl',0.0) or 0.0),
                                        "stop_price": float(getattr(t,'stop_px',0.0) or 0.0),
                                        "why": t.why,
                                        "why_verbose": (getattr(t,'why_verbose','') or '').strip(),
                                        "news": t.news,
                                        "news_fields": parse_news_fields(t.news or ""),
                                    })
                                except Exception:
                                    pass

                            except Exception:
                                pass
                            try:
                                self._maybe_set_loss_cooldown(t.symbol, float(getattr(t, 'realized_pnl', 0.0) or 0.0))
                            except Exception:
                                pass
                            try:
                                compute_analytics()
                            except Exception:
                                pass
                        else:
                            # Submit a broker-side close for the remaining qty
                            try:
                                # Prefer broker-reported position qty to avoid over-requesting
                                try:
                                    rp = self._broker_position_qty(t.symbol)
                                    if rp is not None and rp > 0:
                                        _rem = rp
                                except Exception:
                                    pass                                # Refresh remainder from broker position qty to avoid '1e-06' ghost remainders
                                try:
                                    _pos_qty2 = abs(self._broker_position_qty(t.symbol))
                                    if _pos_qty2 > 0.0:
                                        _rem = _pos_qty2
                                except Exception:
                                    pass
                                qty_close = float(_rem or 0.0)
                                if is_crypto_symbol(t.symbol):
                                    qty_close = floor_crypto_qty(qty_close)
                                else:
                                    qty_close = int(max(0, round(qty_close)))

                                if qty_close and float(qty_close) > 0:
                                    # First try close_position (broker-side). For crypto, prefer closing the full position
                                    # after canceling open orders (avoids slash-symbol mismatches and qty/precision ghosts).
                                    try:
                                        if is_crypto_symbol(t.symbol):
                                            try:
                                                self._cancel_open_orders_for_symbol(t.symbol, reason="flatten_after_exit", cancel_stops=True)
                                            except Exception:
                                                pass
                                            resp = self._close_position_with_unreserve(t.symbol, qty=None, reason='flatten_after_exit')
                                        else:
                                            resp = self._close_position_with_unreserve(t.symbol, qty=qty_close, reason='flatten_after_exit')
                                    except Exception as _e1:
                                        av = parse_available_qty(str(_e1))
                                        if av is not None and is_crypto_symbol(t.symbol):
                                            # One more try: cancel orders then close full position again.
                                            try:
                                                self._cancel_open_orders_for_symbol(t.symbol, reason="flatten_after_exit_retry", cancel_stops=True)
                                            except Exception:
                                                pass
                                            try:
                                                resp = self._close_position_with_unreserve(t.symbol, qty=None, reason='flatten_after_exit')
                                            except Exception:
                                                safe = floor_crypto_qty(av)
                                                if safe > 0:
                                                    qty_close = safe
                                                    resp = self._close_position_with_unreserve(t.symbol, qty=qty_close, reason='flatten_after_exit')
                                                else:
                                                    raise
                                        else:
                                            raise

                                    oid_flat = ''
                                    try:
                                        oid_flat = str((resp or {}).get('id') or (resp or {}).get('order_id') or '')
                                    except Exception:
                                        oid_flat = ''

                                    if not oid_flat:
                                        side_close = 'sell' if t.side == 'buy' else 'buy'
                                        tif = 'gtc' if is_crypto_symbol(t.symbol) else 'day'
                                        try:
                                            od = self.client.submit_order_market(t.symbol, side_close, qty_close, tif)
                                            oid_flat = str((od or {}).get('id') or '')
                                        except Exception as _e2:
                                            av = parse_available_qty(str(_e2))
                                            if av is not None and is_crypto_symbol(t.symbol):
                                                safe = floor_crypto_qty(av)
                                                if safe > 0:
                                                    qty_close = safe
                                                    od = self.client.submit_order_market(t.symbol, side_close, qty_close, tif)
                                                    oid_flat = str((od or {}).get('id') or '')
                                                else:
                                                    raise
                                            else:
                                                raise

                                    if oid_flat:
                                        qty_for_log = float(_rem) if is_crypto_symbol(t.symbol) else float(qty_close)
                                        t.flatten_order_id = oid_flat
                                        self._open_orders[oid_flat] = {'trade_id': t.trade_id, 'leg':'flatten', 'symbol':t.symbol, 'side': ('sell' if t.side == 'buy' else 'buy'), 'qty': float(qty_for_log), 'ts': now, 'why': feed_why_for_trade(t), 'news': t.news}
                                        t.state = 'FLATTEN_WORKING'
                                        write_trade_event(trade_id=t.trade_id, event="FLATTEN_SUBMITTED", symbol=t.symbol, side=t.side, qty=float(qty_for_log), price=float(_expx), state=t.state, why=t.why, news=t.news, meta={"after_leg": leg})
                                        self.out_q.put(('WARN', f"FLATTEN: closing remaining {t.symbol} qty={qty_for_log} after {leg} fill"))
                                    else:
                                        raise RuntimeError('close_position/market returned no order id')
                                else:
                                    t.state = 'CLOSED'
                                    write_trade_event(trade_id=t.trade_id, event="CLOSED", symbol=t.symbol, side=t.side, qty=float(getattr(t, "realized_qty", 0.0)), price=float(_expx), pnl=float(getattr(t, "realized_pnl", 0.0)), state="CLOSED", why=t.why, news=t.news, meta={"closed_leg": leg, "note": "qty_close<=0"})
                                    try:
                                        _why_v = (getattr(t, 'why_verbose', '') or '').strip() or (t.why or '')
                                        _notes = "closed_leg=" + str(leg) + " | close_reason=" + str(leg)
                                        final_whyv = build_final_why_verbose(t, close_leg=str(leg), close_reason=str(leg), exit_price=float(_expx or 0.0), pnl=float(getattr(t,'realized_pnl',0.0) or 0.0), cooldown=str(getattr(t,'cooldown_note','') or ''))
                                        write_trade_journal_row(trade_id=t.trade_id, symbol=t.symbol, side=t.side, qty=float(getattr(t,'realized_qty',0.0) or t.qty or 0.0), entry_price=float(t.entry_px or 0.0), exit_price=float(_expx or 0.0), pnl=float(getattr(t,'realized_pnl',0.0) or 0.0), why=t.why, why_verbose=final_whyv, news=t.news, stop_price=float(getattr(t,'stop_px',0.0) or 0.0), notes=_notes)
                                        try:
                                            write_trade_receipt(trade_id=t.trade_id, stage="CLOSED", receipt={
                                                "event": "CLOSED",
                                                "symbol": t.symbol,
                                                "side": t.side,
                                                "qty": float(getattr(t,'realized_qty',0.0) or t.qty or 0.0),
                                                "entry_price": float(t.entry_px or 0.0),
                                                "exit_price": float(_ex or 0.0),
                                                "pnl": float(getattr(t,'realized_pnl',0.0) or 0.0),
                                                "stop_price": float(getattr(t,'stop_px',0.0) or 0.0),
                                                "why": t.why,
                                                "why_verbose": (getattr(t,'why_verbose','') or '').strip(),
                                                "news": t.news,
                                                "news_fields": parse_news_fields(t.news or ""),
                                            })
                                        except Exception:
                                            pass

                                    except Exception:
                                        pass

                                try:
                                    compute_analytics()
                                except Exception:
                                    pass

                            except Exception as e:
                                self.out_q.put(('ERROR', f"Flatten-after-exit failed for {t.symbol}: {e}"))
                                # If broker says "insufficient balance" on a tiny remainder, treat it as dust and clear local state.
                                try:
                                    _rem = self._broker_position_qty(sym)
                                    if _rem is not None and abs(float(_rem)) <= 1e-6:
                                        self.out_q.put(("WARN", f"RECOVERY: flatten-after-exit remainder is dust for {sym} qty={_rem}; clearing local trade."))
                                        self._clear_trade_for_symbol(sym, note="dust_remainder")
                                        continue
                                except Exception:
                                    pass
                                # Safety-first: if we still hold a remainder, place a protective STOP.
                                try:
                                    rp2 = self._broker_position_qty(t.symbol)
                                    remq = rp2 if (rp2 is not None and rp2 > 0) else float(_rem or 0.0)
                                    if is_crypto_symbol(t.symbol):
                                        prot_qty = floor_crypto_qty(remq)
                                        if prot_qty > 0:
                                            stop_px = float(getattr(t, 'stop_px', 0.0) or 0.0)
                                            rec = self._quote_cache.get(t.symbol)
                                            mid = float(rec[3]) if rec else 0.0
                                            if mid > 0:
                                                # Put stop slightly below current mid (for longs) as emergency protection
                                                stop_px = stop_px if stop_px > 0 else mid * 0.995
                                                stop_px = min(stop_px, mid * 0.995)
                                            if stop_px > 0:
                                                slip_bps = self.slip_bps_crypto
                                                lim = stop_px * (1.0 - (slip_bps/10000.0))
                                                try:
                                                    odp = self.client.submit_order_stop_limit(t.symbol, 'sell' if t.side=='buy' else 'buy', prot_qty, 'gtc', stop_px, lim)
                                                except Exception as ee:
                                                    av = parse_available_qty(str(ee))
                                                    if av is not None:
                                                        prot_qty2 = floor_crypto_qty(av)
                                                        if prot_qty2 > 0:
                                                            prot_qty = prot_qty2
                                                            odp = self.client.submit_order_stop_limit(t.symbol, 'sell' if t.side=='buy' else 'buy', prot_qty, 'gtc', stop_px, lim)
                                                        else:
                                                            raise
                                                    else:
                                                        raise
                                                oidp = str((odp or {}).get('id') or '')
                                                if oidp:
                                                    t.stop_order_id = oidp
                                                    self._open_orders[oidp] = {'trade_id': t.trade_id, 'leg':'stop', 'symbol':t.symbol, 'side': ('sell' if t.side=='buy' else 'buy'), 'qty': float(prot_qty), 'stop_price': stop_px, 'ts': now, 'why': feed_why_for_trade(t), 'news': t.news}
                                                    write_trade_event(trade_id=t.trade_id, event='PROTECTIVE_STOP_PLACED_AFTER_FLATTEN_FAIL', symbol=t.symbol, side=t.side, qty=float(prot_qty), price=float(stop_px), state='PROTECT_ONLY', why=t.why, news=t.news, meta={'reason': str(e)[:160]})
                                                    self.out_q.put(('WARN', f'Protective STOP placed for {t.symbol} qty={prot_qty} after flatten failure'))
                                                    t.state = 'PROTECT_ONLY'
                                except Exception:
                                    pass
                                # Treat as order reject; do not immediately trip global CB.
                                try:
                                    self._cb_record('order_reject', f"flatten_after_exit: {e}")
                                except Exception:
                                    pass
                                t.state = 'EXIT_PARTIAL'
                                write_trade_event(trade_id=t.trade_id, event="EXIT_PARTIAL", symbol=t.symbol, side=t.side, qty=float(_rem), price=float(_expx), state=t.state, why=t.why, news=t.news, meta={"after_leg": leg, "reason": str(e)[:200]})

                    if leg == 'flatten':
                        # Flatten order filled -> trade is truly closed
                        self.out_q.put(('INFO', f"Flatten filled for {t.symbol}. Marking trade CLOSED."))
                        _exq = float(filled_qty or meta.get("qty") or 0.0)
                        _expx = float(px or 0.0)
                        _enpx = float(t.entry_px or 0.0)
                        _pnl2 = ((_expx - _enpx) * _exq) if t.side == "buy" else ((_enpx - _expx) * _exq)
                        try:
                            t.realized_pnl = float(getattr(t, "realized_pnl", 0.0)) + float(_pnl2)
                            t.realized_qty = float(getattr(t, "realized_qty", 0.0)) + float(_exq)
                        except Exception:
                            pass
                        write_trade_event(trade_id=t.trade_id, event="FLATTEN_FILLED", symbol=t.symbol, side=t.side, qty=_exq, price=_expx, pnl=_pnl2, state=t.state, why=t.why, news=t.news, meta={"leg": "flatten"})
                        _pxs = fmt_price(_expx, is_crypto=is_crypto_symbol(t.symbol))
                        self.out_q.put(("TRADE", {"summary": f"FLATTEN {t.symbol} qty={_exq} @ {_pxs} (filled)", "why": feed_why_for_trade(t), "news": t.news}))

                        # Cancel any leftover legs we know about
                        for other in [getattr(t, 'tp1_order_id', ''), getattr(t, 'stop_order_id', ''), getattr(t, 'trail_order_id', ''), getattr(t, 'flatten_order_id', '')]:
                            if other and other != oid:
                                try:
                                    self.client.cancel_order(other)
                                except Exception:
                                    pass

                        t.state = 'CLOSED'
                        write_trade_event(trade_id=t.trade_id, event="CLOSED", symbol=t.symbol, side=t.side, qty=float(getattr(t, "realized_qty", 0.0)), price=float(_expx), pnl=float(getattr(t, "realized_pnl", 0.0)), state="CLOSED", why=t.why, news=t.news, meta={"closed_leg": "flatten"})
                        try:
                            _why_v = (getattr(t, 'why_verbose', '') or '').strip() or (t.why or '')
                            _notes = "closed_leg=flatten | close_reason=flatten"
                            final_whyv = build_final_why_verbose(t, close_leg="flatten", close_reason="flatten", exit_price=float(_expx or 0.0), pnl=float(getattr(t,'realized_pnl',0.0) or 0.0), cooldown=str(getattr(t,'cooldown_note','') or ''))
                            write_trade_journal_row(trade_id=t.trade_id, symbol=t.symbol, side=t.side, qty=float(getattr(t,'realized_qty',0.0) or t.qty or 0.0), entry_price=float(t.entry_px or 0.0), exit_price=float(_expx or 0.0), pnl=float(getattr(t,'realized_pnl',0.0) or 0.0), why=t.why, why_verbose=final_whyv, news=t.news, stop_price=float(getattr(t,'stop_px',0.0) or 0.0), notes=_notes)
                            try:
                                write_trade_receipt(trade_id=t.trade_id, stage="CLOSED", receipt={
                                    "event": "CLOSED",
                                    "symbol": t.symbol,
                                    "side": t.side,
                                    "qty": float(getattr(t,'realized_qty',0.0) or t.qty or 0.0),
                                    "entry_price": float(t.entry_px or 0.0),
                                    "exit_price": float(_ex or 0.0),
                                    "pnl": float(getattr(t,'realized_pnl',0.0) or 0.0),
                                    "stop_price": float(getattr(t,'stop_px',0.0) or 0.0),
                                    "why": t.why,
                                    "why_verbose": (getattr(t,'why_verbose','') or '').strip(),
                                    "news": t.news,
                                    "news_fields": parse_news_fields(t.news or ""),
                                })
                            except Exception:
                                pass

                        except Exception:
                            pass
                        try:
                            self._maybe_set_loss_cooldown(t.symbol, float(getattr(t, 'realized_pnl', 0.0) or 0.0))
                        except Exception:
                            pass
                        try:
                            compute_analytics()
                        except Exception:
                            pass



                    # Remove closed trades from active sets periodically (kept for audit/logs)

                # Terminal non-fill states
                if st in ('canceled','expired','done_for_day') and filled_qty <= 0:
                    self.out_q.put(('WARN', f"Order {oid} {st} ({leg})"))

            for oid in done:
                self._open_orders.pop(oid, None)

        # Layer 1: crypto trailing emulation refresh
        for t in list(self.trades.values()):
            if t.state != 'TRAIL_WORKING' or not is_crypto_symbol(t.symbol):
                continue
            if t.rem_qty <= 0.0:
                continue
            if (now - float(t.last_trail_update_ts or 0.0)) < TRAIL_UPDATE_SEC:
                continue
            rec = self._quote_cache.get(t.symbol)
            if not rec:
                continue
            _, bid, ask, mid, _ = rec
            px = float(mid or (ask if t.side == 'buy' else bid) or 0.0)
            if px <= 0:
                continue
            t.last_px = px
            # update best favorable price
            if t.side == 'buy':
                t.best_px = max(float(t.best_px or px), px)
                new_stop = t.best_px - float(t.trail_amt or 0.0)
            else:
                t.best_px = min(float(t.best_px or px), px)
                new_stop = t.best_px + float(t.trail_amt or 0.0)
            # Don't move stop in wrong direction
            if t.side == 'buy' and new_stop <= float(t.stop_px or 0.0):
                continue
            if t.side == 'sell' and new_stop >= float(t.stop_px or 0.0):
                continue
            # Refresh stop_limit safely: submit NEW first, then cancel old. Never leave the position unprotected.
            exit_side = 'sell' if t.side == 'buy' else 'buy'
            try:
                old_stop_id = getattr(t, 'stop_order_id', '')
                old_stop_px = float(getattr(t, 'stop_px', 0.0) or 0.0)

                # Respect a trailing-disable cooldown if we recently had order rejects.
                if getattr(t, 'trail_disabled_until_ts', 0.0) and now < float(getattr(t, 'trail_disabled_until_ts', 0.0)):
                    continue

                # Use authoritative remaining qty (broker positions) to avoid over-requesting.
                remq = None
                try:
                    rp = self._broker_position_qty(t.symbol)
                    if rp is not None and rp > 0:
                        remq = rp
                except Exception:
                    remq = None
                if remq is None:
                    remq = float(t.rem_qty or 0.0)

                q0 = floor_crypto_qty(remq)
                if q0 <= 0:
                    continue

                slip_bps = self.slip_bps_crypto
                if exit_side == 'sell':
                    lim = new_stop * (1.0 - (slip_bps/10000.0))
                else:
                    lim = new_stop * (1.0 + (slip_bps/10000.0))

                def _submit(qty_use: float):
                    return self.client.submit_order_stop_limit(t.symbol, exit_side, qty_use, 'gtc', new_stop, lim)

                try:
                    od_st = _submit(q0)
                except Exception as e1:
                    av = parse_available_qty(str(e1))
                    if av is not None:
                        q1 = floor_crypto_qty(av)
                        if q1 > 0:
                            od_st = _submit(q1)
                            q0 = q1
                        else:
                            raise
                    else:
                        raise

                oid_st = str((od_st or {}).get('id') or '')
                if oid_st:
                    # New stop is live; now cancel the old one.
                    if old_stop_id:
                        try:
                            self.client.cancel_order(old_stop_id)
                        except Exception:
                            pass
                    t.stop_order_id = oid_st
                    t.stop_px = new_stop
                    t.last_trail_update_ts = now
                    self._open_orders[oid_st] = {'trade_id': t.trade_id, 'leg':'stop', 'symbol':t.symbol, 'side': exit_side, 'qty': float(q0), 'stop_price': new_stop, 'ts': now, 'why': feed_why_for_trade(t), 'news': t.news}
                    self.out_q.put(('INFO', f"Trailed crypto stop {t.symbol} -> {fmt_price(new_stop, is_crypto=True)}"))
            except Exception as e:
                # Keep old stop; disable trailing for this symbol temporarily.
                try:
                    t.stop_order_id = old_stop_id
                    t.stop_px = old_stop_px
                    t.trail_disabled_until_ts = now + 30*60
                except Exception:
                    pass
                # Do not trip global circuit breaker for this. Log once.
                self.out_q.put(('WARN', f"Trail refresh failed for {t.symbol}; keeping existing STOP. {e}"))
                # Do NOT count trailing refresh failures toward the global circuit breaker.
                # We keep the old protective STOP and disable trailing for this symbol, which is the safe fallback.
                continue


        
        # Phase 2A (support): CRYPTO CLOSE RETRY WINDOW
        # If we previously hit a transient Alpaca 403 'insufficient balance' while trying to close/flatten crypto,
        # keep retrying for a short window without tripping the circuit breaker.
        try:
            for sym, until in list(getattr(self.state, 'crypto_close_retry_until', {}).items()):
                try:
                    if float(until or 0.0) <= float(now):
                        self.state.crypto_close_retry_until.pop(sym, None)
                        continue
                except Exception:
                    continue
                # Only retry if we actually have a broker position
                try:
                    pos = self.client.get_position(sym)
                    qty_pos = abs(float(getattr(pos, 'qty', 0.0) or 0.0))
                except Exception:
                    qty_pos = 0.0
                if qty_pos <= 0:
                    self.state.crypto_close_retry_until.pop(sym, None)
                    continue
                try:
                    self.out_q.put(('WARN', f"RETRY CLOSE: attempting close_position for {sym} (qty~{qty_pos})"))
                    try:
                        self._cancel_open_orders_for_symbol(sym, cancel_stops=True, reason='retry_close')
                    except Exception:
                        pass
                    self._close_position_with_unreserve(sym, reason='retry_close')
                except Exception as e:
                    # Keep window alive only for the transient insufficient balance case
                    if not is_insufficient_balance_err(e):
                        self.state.crypto_close_retry_until.pop(sym, None)
        except Exception:
            pass

# Phase 2A: TIME STOP (max hold) - if a trade has been open too long without exiting,
        # flatten it safely to prevent "hanging" trades from hogging exposure.
        try:
            for t in list(self.trades.values()):
                if getattr(t, "time_stop_fired", False):
                    continue
                if t.state not in ("ENTRY_FILLED", "TP1_WORKING", "TRAIL_WORKING"):
                    continue
                # If opened_ts is missing (e.g., recovered trade without timestamp), initialize it and do NOT time-stop immediately.
                if not getattr(t, "opened_ts", 0.0):
                    t.opened_ts = now
                    continue
                if t.opened_ts and (now - float(t.opened_ts)) < float(TIME_STOP_SEC):
                    continue
                # Don't time-stop while already closing
                if t.state in ("FLATTEN_WORKING", "CLOSED", "EXIT_PARTIAL"):
                    continue
                # Determine remaining qty (best-effort)
                try:
                    _full = float(getattr(t, "qty", 0.0) or 0.0)
                    _real = float(getattr(t, "realized_qty", 0.0) or 0.0)
                    rem = max(0.0, _full - _real)
                except Exception:
                    rem = 0.0
                if rem <= 1e-6:
                    t.time_stop_fired = True
                    continue
                t.time_stop_fired = True
                self.out_q.put(("WARN", f"TIME STOP: flattening {t.symbol} after {int((now - float(t.opened_ts))//60)}m open"))
                write_trade_event(trade_id=t.trade_id, event="TIME_STOP_TRIGGERED", symbol=t.symbol, side=t.side, qty=float(rem), price=float(t.last_px or t.entry_px or 0.0), state=t.state, why=t.why, news=t.news, meta={"minutes": int((now - float(t.opened_ts))//60)})
                # Cancel any working exit legs we know about
                for other in [getattr(t, "tp1_order_id", ""), getattr(t, "stop_order_id", ""), getattr(t, "trail_order_id", "")]:
                    if other:
                        try:
                            self.client.cancel_order(other)
                        except Exception:
                            pass
                # Submit a flatten order for the remainder
                try:
                    qty_close = rem
                    if is_crypto_symbol(t.symbol):
                        # For crypto, close the full position (no qty) after canceling all open orders for the symbol.
                        # This avoids 403 'insufficient balance' from reserved qty and timing mismatches.
                        try:
                            self._cancel_open_orders_for_symbol(t.symbol, cancel_stops=True, reason='time_stop')
                        except Exception:
                            pass
                        qty_close = None
                    else:
                        qty_close = int(max(0, round(qty_close)))
                    if (qty_close is None) or (qty_close and float(qty_close) > 0):
                        resp = self._close_position_with_unreserve(t.symbol, qty=qty_close, reason='time_stop_flatten')
                        oid_flat = ""
                        try:
                            oid_flat = str((resp or {}).get("id") or (resp or {}).get("order_id") or "")
                        except Exception:
                            oid_flat = ""
                        if (not oid_flat) and (qty_close is not None):
                            side_close = "sell" if t.side == "buy" else "buy"
                            tif = "gtc" if is_crypto_symbol(t.symbol) else "day"
                            od = self.client.submit_order_market(t.symbol, side_close, qty_close, tif)
                            oid_flat = str((od or {}).get("id") or "")
                        if oid_flat:
                            qty_for_log = float(rem) if (qty_close is None) else float(qty_close)
                            t.flatten_order_id = oid_flat
                            self._open_orders[oid_flat] = {"trade_id": t.trade_id, "leg": "flatten", "symbol": t.symbol, "side": ("sell" if t.side == "buy" else "buy"), "qty": float(qty_for_log), "ts": now, "why": feed_why_for_trade(t), "news": t.news}
                            t.state = "FLATTEN_WORKING"
                            write_trade_event(trade_id=t.trade_id, event="FLATTEN_SUBMITTED", symbol=t.symbol, side=t.side, qty=float(qty_for_log), price=float(t.last_px or t.entry_px or 0.0), state=t.state, why=t.why, news=t.news, meta={"after_leg": "time_stop"})
                except Exception as e:
                    self.out_q.put(("ERROR", f"TIME STOP flatten failed for {t.symbol}: {e}"))
                    # Crypto can throw transient 403 'insufficient balance' if qty is reserved or broker position visibility lags.
                    # Do NOT trip global circuit breaker for that; schedule a retry window instead.
                    if is_crypto_symbol(t.symbol) and is_insufficient_balance_err(e):
                        try:
                            until = float(now) + 90.0
                            cur = float(self.state.crypto_close_retry_until.get(t.symbol, 0.0) or 0.0)
                            self.state.crypto_close_retry_until[t.symbol] = max(cur, until)
                        except Exception:
                            pass
                        self.out_q.put(("WARN", f"TIME STOP: will retry close for {t.symbol} (transient insufficient balance/reserved qty)"))
                    else:
                        self._cb_record("api_fail", f"time_stop_flatten: {e}")
        except Exception:
            pass

        # If circuit breaker is enabled, do not open new entries.
        if self.cb.enabled or (not getattr(self, 'trade_enabled', True)):
            return

        # If any entry is working, don't open another entry. (We still manage exits above.)
        if any((m.get('leg') == 'entry') for m in self._open_orders.values()):
            return

        # Need equity to size risk; try to fetch once if missing
        if self._last_equity is None:
            try:
                acct = self.client.get_account()
                self._last_equity = float(acct.get('equity') or acct.get('portfolio_value') or 0.0) or None
            except Exception:
                self._last_equity = None
        if not self._last_equity:
            return

        # Max positions guard (use configured cap)
        if len(self.pos) >= max(1, int(MAX_POSITIONS)):
            return

        # Candidate evaluation (small set)
        best = None
        best_score = -1e9
        best_meta = None

        # PAPER probe selection (used only if no trades occur for a while)
        best_probe = None
        best_probe_score = -1e9
        best_probe_meta = None
        # Rejection diagnostics
        top_reject = None  # (sym, detail)
        top_reject_score = -1e9
        # Rejection counters for transparency (Phase 3 trust layer)
        rej = {'spread': 0, 'bars': 0, 'data': 0, 'signal': 0, 'score': 0, 'short': 0, 'news': 0}
        last_bars_err = None
        is_probe_trade = False

        news_mode = str(getattr(self.news_ctx, 'mode', 'CLEAR'))
        news_headline = (getattr(self.news_ctx, 'headline', '') or '').strip()

        # Avoid re-entering symbols we already hold (crypto symbol format varies: BTCUSD vs BTC/USD)
        pos_norm = {norm_symbol(k) for k in (self.pos.keys() or [])}
        for sym in top_syms[:5]:
            if norm_symbol(sym) in pos_norm:
                continue
            # cooldown 5 minutes
            cd = self._cooldown.get(sym, 0.0)
            if now < cd:
                continue

            rec = self._quote_cache.get(sym)
            if not rec:
                continue
            _, bid, ask, mid, _ = rec
            if not bid or not ask or not mid:
                continue
            spread_bps = ((ask - bid) / mid) * 10000.0 if mid else 999999.0
            max_spread = self.max_spread_bps_crypto if is_crypto_symbol(sym) else self.max_spread_bps_stock
            if spread_bps > max_spread:
                # Track closest spread failure for diagnostics (higher is "closer")
                rej['spread'] += 1
                gap = float(spread_bps) - float(max_spread)
                rej_metric = -gap
                if rej_metric > top_reject_score:
                    top_reject_score = rej_metric
                    top_reject = (sym, f"spread too wide: {spread_bps:.1f}bps > max={max_spread:.1f}bps")
                continue

            # Fetch bars (1Min). Keep limits reasonable to avoid rate limits.
            try:
                bars = self.client.get_bars(sym, '1Min', limit=180)
            except Exception as e:
                rej['bars'] += 1
                last_bars_err = str(e)
                # Track top bars error (throttle logging later)
                if 0.0 > top_reject_score and top_reject is None:
                    top_reject_score = 0.0
                    top_reject = (sym, f"bars fetch failed: {last_bars_err}")
                continue
            o, h, l, c, v = _bars_to_ohlcv(bars)
            if len(c) < 60:
                rej['data'] += 1
                if 0.0 > top_reject_score and top_reject is None:
                    top_reject_score = 0.0
                    top_reject = (sym, f"insufficient bars: {len(c)}")
                continue
            close = float(c[-1])
            ef = ema(c[-60:], 12)
            es = ema(c[-80:], 26)
            rv = rsi(c, 14)
            av = atr(h, l, c, 14)
            vw = vwap(h, l, c, v, 60)
            if ef is None or es is None or rv is None or av is None:
                rej['data'] += 1
                if 0.0 > top_reject_score and top_reject is None:
                    top_reject_score = 0.0
                    top_reject = (sym, "indicator calc failed")
                continue

            ema_tol = 0.0
            try:
                ema_tol = float(getattr(self, 'signal_ema_tol_bps', 0.0) or 0.0) * close / 10000.0
            except Exception:
                ema_tol = 0.0

            bull = (ef >= (es - ema_tol)) and (rv >= float(getattr(self, 'signal_rsi_bull', 55.0))) and (self.paper_relax_signal or vw is None or close >= vw)
            bear = (ef <= (es + ema_tol)) and (rv <= float(getattr(self, 'signal_rsi_bear', 45.0))) and (self.paper_relax_signal or vw is None or close <= vw)

            # News alignment tilt
            aligned = False
            if 'RISK_ON' in news_mode and bull:
                aligned = True
            if 'RISK_OFF' in news_mode and bear:
                aligned = True

            side = None
            if bull:
                side = 'buy'
            elif bear and self.allow_shorts:
                side = 'sell'

            if side == 'sell' and is_crypto_symbol(sym):
                # Alpaca crypto is not shortable; block any attempted short.
                # (We also skip symbols we already hold above, so any sell here is a short attempt.)
                rej_score = abs(ef - es) / close * 10000.0
                if rej_score > top_reject_score:
                    top_reject = (sym, 'crypto not shortable (shorts disabled for crypto)')
                    rej['short'] += 1
                    top_reject_score = rej_score
                continue

            if not side:
                # Track "no directional signal" cases for transparency
                rej['signal'] += 1
                rej_metric = float(abs(ef - es) / close * 10000.0) + float(abs(rv - 50.0))
                if rej_metric > top_reject_score:
                    top_reject_score = rej_metric
                    trend_bps_tmp = abs(ef - es) / close * 10000.0
                    top_reject = (sym, f"no signal: ef={'>' if ef>es else '<='}es rsi={rv:.1f} trend={trend_bps_tmp:.1f}bps spread={spread_bps:.1f}bps")
                continue

            # score: trend separation + momentum + attention + alignment bonus (+ news boosts)
            trend_bps = abs(ef - es) / close * 10000.0
            mom = (rv - 50.0) if side == 'buy' else (50.0 - rv)
            base_score = trend_bps + (mom * 2.0) + (200.0 - spread_bps)

            # Macro mode tilt: aligned gets a bonus; contradictory macro gets a *penalty only* (no hard blocks).
            macro_adj = 0.0
            if aligned:
                macro_adj += 30.0
                if self.aggressive:
                    macro_adj += 15.0
            else:
                if ('RISK_ON' in news_mode and bear) or ('RISK_OFF' in news_mode and bull):
                    macro_adj -= 10.0
                    if self.aggressive:
                        macro_adj -= 5.0

            # Symbol-specific news: can boost, but contradictions are a hard block (Phase 3 news edits).
            sym_news_boost = 0.0
            sym_news_head = ""
            sym_news_conf = ""
            sym_news_age_m = 9999
            sym_news_sent = 0
            try:
                info = self._get_symbol_news_info(sym)
                sym_news_head = (info.get("headline") or "")
                sym_news_conf = (info.get("conf") or "")
                sym_news_age_m = int(info.get("age_m") or 9999)
                sym_news_sent = int(info.get("sentiment") or 0)
                if sym_news_sent != 0 and news_conf_weight(sym_news_conf) > 0.0:
                    # contradictions are a hard block when the headline is for this symbol
                    if (sym_news_sent < 0 and side == 'buy') or (sym_news_sent > 0 and side == 'sell'):
                        rej['news'] += 1
                        # Track top rejection
                        if 0.0 > top_reject_score:
                            top_reject_score = 0.0
                            top_reject = (sym, f"symbol news contradiction: {sym_news_conf} age={sym_news_age_m}m {sym_news_head[:120]}")
                        continue
                    sym_news_boost = compute_symbol_news_boost(conf=sym_news_conf, age_m=sym_news_age_m, sentiment=sym_news_sent)
            except Exception:
                pass

            score = base_score + macro_adj + sym_news_boost

            meta_local = {
                'side': side,
                'close': close,
                'bid': bid,
                'ask': ask,
                'mid': mid,
                'spread_bps': spread_bps,
                'atr': av,
                'rsi': rv,
                'ema_fast': ef,
                'ema_slow': es,
                'vwap': vw,
                'aligned': aligned,
                'base_score': float(base_score),
                'macro_adj': float(macro_adj),
                'news_boost': float(sym_news_boost),
                'news_conf': str(sym_news_conf or ''),
                'news_age_m': int(sym_news_age_m) if 'sym_news_age_m' in locals() else 9999,
                'news_headline': str(sym_news_head or ''),
                'news_sentiment': int(sym_news_sent) if 'sym_news_sent' in locals() else 0,
            }
            # require a minimum quality bar (paper relax can lower this for testing)
            min_score = 120.0
            probe_min_score = 60.0
            if self.paper_relax:
                try:
                    base = float(self.settings.get("paper_min_entry_score", min_score) or min_score)
                except Exception:
                    base = min_score
                try:
                    test = float(self.settings.get("paper_test_min_entry_score", base) or base)
                except Exception:
                    test = base
                min_score = min(base, test)
                try:
                    probe_min_score = float(self.settings.get("paper_probe_min_score", probe_min_score) or probe_min_score)
                except Exception:
                    probe_min_score = probe_min_score

            if score < min_score:
                rej['score'] += 1
                # Track top rejection (closest to threshold) for diagnostics
                if score > top_reject_score:
                    top_reject_score = score
                    top_reject = (sym, f"score={score:.1f} < min_score={min_score:.1f} spread={spread_bps:.1f}bps rsi={rv:.1f} trend={trend_bps:.1f}bps")
                # Track best probe candidate (still requires a directional signal + spread checks)
                if self.paper_relax and self._probe_enable and score >= probe_min_score and score > best_probe_score and (self._stock_market_open or is_crypto_symbol(sym)):
                    best_probe = sym
                    best_probe_score = score
                    best_probe_meta = dict(meta_local)
                continue

            if score > best_score:
                best_score = score
                best = sym
                best_meta = dict(meta_local)

        if not best or not best_meta:
            # Rejection diagnostics (throttled)
            try:
                if top_reject and (now - float(getattr(self, '_last_reject_log_ts', 0.0))) > 120.0:
                    self._last_reject_log_ts = now
                    self.out_q.put(('INFO', f"No entries this cycle. reasons=spread:{rej.get('spread',0)} bars:{rej.get('bars',0)} data:{rej.get('data',0)} signal:{rej.get('signal',0)} score:{rej.get('score',0)} short:{rej.get('short',0)} warmup:{rej.get('warmup',0)}. Top reject: {top_reject[0]} ({top_reject[1]})"))
            except Exception:
                pass

            # PAPER probe: if we haven't opened any trades for a while, place a tiny trade to validate lifecycle.
            try:
                last_entry = (self._trade_ts_day[-1] if self._trade_ts_day else 0.0)
                force_after = float(self.settings.get('paper_probe_force_after_sec', 600) or 600)
                if (best_probe and best_probe_meta and self._probe_enable and (now - self._last_probe_ts) > self._probe_cd_sec and (now - last_entry) > force_after):
                    best = best_probe
                    best_score = best_probe_score
                    best_meta = best_probe_meta
                    is_probe_trade = True
                    self._last_probe_ts = now
                    self.out_q.put(('WARN', f"PAPER PROBE: forcing tiny test trade on {best} score={best_score:.1f} (to validate lifecycle)"))
            except Exception:
                pass

            if not best or not best_meta:
                return

        sym = best
        side = best_meta['side']
        close = best_meta['close']
        av = best_meta['atr']


        # Size position (risk model)
        base_risk_pct = float(self.risk_pct)
        eff_risk_pct = float(base_risk_pct)

        # Phase 2: drawdown seatbelt (soft tiers). Never blocks exits; only reduces risk-per-trade.
        try:
            dd = getattr(self, "_dtd_pl_pct", None)
            if dd is not None:
                dd = float(dd)
                if dd <= -float(DD_SOFT2_PCT):
                    eff_risk_pct = min(eff_risk_pct, base_risk_pct * float(DD_SOFT2_RISK_MULT))
                    if (time.time() - float(getattr(self, "_last_dd_warn_ts", 0.0))) > 600.0:
                        self._last_dd_warn_ts = time.time()
                        self.out_q.put(("WARN", f"Soft drawdown tier-2 (DTD {dd*100:.2f}%): risk/trade reduced to {eff_risk_pct:.3f}%"))
                elif dd <= -float(DD_SOFT1_PCT):
                    eff_risk_pct = min(eff_risk_pct, base_risk_pct * float(DD_SOFT1_RISK_MULT))
                    if (time.time() - float(getattr(self, "_last_dd_warn_ts", 0.0))) > 600.0:
                        self._last_dd_warn_ts = time.time()
                        self.out_q.put(("WARN", f"Soft drawdown tier-1 (DTD {dd*100:.2f}%): risk/trade reduced to {eff_risk_pct:.3f}%"))
        except Exception:
            pass

        risk_dollars = float(self._last_equity) * (eff_risk_pct / 100.0)
        stop_dist = max(av * 1.8, close * 0.002)  # ATR-based, with floor
        qty = risk_dollars / stop_dist if stop_dist > 0 else 0.0

        # Hard cap by available buying power/cash so we never request more than the account can afford.
        try:
            est_px = float(best_meta['ask'] if side == 'buy' else best_meta['bid']) or float(best_meta.get('mid') or close)
        except Exception:
            est_px = float(best_meta.get('mid') or close)

        eq = float(self._last_equity or 0.0)
        bp = float(self._last_buying_power or 0.0)
        cash = float(self._last_cash or 0.0)
        available = (cash if is_crypto_symbol(sym) else bp) or (bp or cash or eq)

        # also cap per-position notional as a percent of equity (prevents huge positions from tiny stops)
        max_notional_pct = 0.25
        max_notional = max(0.0, min(available * 0.95, eq * max_notional_pct if eq else available * 0.95))
        max_qty_by_funds = (max_notional / est_px) if (est_px and max_notional) else 0.0

        if max_qty_by_funds > 0:
            qty = min(qty, max_qty_by_funds)
        if is_crypto_symbol(sym):
            qty = round(max(qty, 0.000001), 6)
        else:
            qty = int(max(1.0, qty))
        if not qty:
            return

        # If this is a PAPER probe trade, force a tiny size so it can fill and validate the lifecycle.
        if is_probe_trade:
            # If stock market is closed, don't place stock probes.
            if (not is_crypto_symbol(sym)) and (not getattr(self, '_stock_market_open', True)):
                try:
                    
                    if not hasattr(self, '_last_stock_closed_log'): self._last_stock_closed_log = {}
                    last = float(self._last_stock_closed_log.get(sym+'_probe', 0.0) or 0.0)
                    if (time.time() - last) > 300:
                        self._last_stock_closed_log[sym+'_probe'] = time.time()
                        self.out_q.put(('INFO', 'Probe skipped for %s: market appears closed.' % sym))

                except Exception:
                    pass
                return
            if is_crypto_symbol(sym):
                try:
                    # ~$10 notional, with sane minimum
                    qty = max(0.0001, round(10.0 / float(est_px or 1.0), 6))
                except Exception:
                    qty = 0.0001
            else:
                qty = 1

        # Build WHY + NEWS text (Option B block formatting happens in UI)
        # Phase 3: keep WHY compact in the live feed. Store verbose WHY/receipts separately.
        why_parts = []
        if is_probe_trade:
            why_parts.append("PROBE")
        why_parts.append(f"score={best_score:.1f}")
        try:
            nb = float(best_meta.get("news_boost") or 0.0)
            if abs(nb) >= 0.05:
                why_parts.append(f"nboost={nb:+.1f}")
        except Exception:
            pass
        try:
            ma = float(best_meta.get("macro_adj") or 0.0)
            if abs(ma) >= 0.05:
                why_parts.append(f"macro={ma:+.0f}")
        except Exception:
            pass
        why_parts.append("BULL" if side=='buy' else "BEAR")
        why_parts.append(f"RSI={best_meta['rsi']:.1f}")
        why_parts.append(f"ATR={av:.4f}")
        why_parts.append(f"spr={best_meta['spread_bps']:.1f}bps")
        why_parts.append(f"risk={eff_risk_pct:.2f}%")
        if best_meta.get('aligned'):
            why_parts.append(f"news={news_mode}")
        why = " | ".join(why_parts)

        # Layer 3: prefer symbol-linked headline; fall back to macro mode
        sym_head = self._get_symbol_news(sym)
        news_line = sym_head or (news_headline if news_headline else f"mode={news_mode} (no headline)")

        # Submit order (Layer 1 lifecycle + Layer 2 risk gate)
        if not getattr(self, "trade_enabled", True):
            return
        # Avoid stock order submits when market is closed.
        if (not is_crypto_symbol(sym)) and (not getattr(self, '_stock_market_open', True)):
            
            if not hasattr(self, '_last_stock_closed_log'): self._last_stock_closed_log = {}
            last = float(self._last_stock_closed_log.get(sym, 0.0) or 0.0)
            if (time.time() - last) > 300:
                self._last_stock_closed_log[sym] = time.time()
                self.out_q.put(('INFO', 'Skipped stock entry for %s: market appears closed.' % sym))

            return
        tif = 'gtc' if is_crypto_symbol(sym) else 'day'

        # Prevent duplicate entries on the same symbol when a position/exits already exist.
        busy, busy_reason = self._symbol_busy_for_entry(sym)
        if busy:
            if getattr(self, '_busy_notice_ts', None) is None:
                self._busy_notice_ts = {}
            last = float(self._busy_notice_ts.get(sym, 0.0) or 0.0)
            if (now - last) >= 60.0:
                self._busy_notice_ts[sym] = now
                self.out_q.put(('INFO', f"Skip entry for {sym}: {busy_reason} (symbol busy)"))
            return
        limit_px = None
        try:
            # Layer 2 risk gate BEFORE submitting
            est_notional = float(qty) * float(est_px or close or 0.0)
            ok, reason = self._risk_can_open(sym, est_notional)
            if not ok:
                # no normal per-symbol cooldown (Phase 2A)
                self.out_q.put(('WARN', f"Risk gate blocked entry for {sym}: {reason}"))
                return

            # Layer 8: canary mode (scan + log only, no orders)
            if getattr(self, "canary_mode", False):
                tid = gen_trade_id(sym)
                self.out_q.put(("DECISION", f"CANARY: would {side.upper()} {sym} qty={qty} est_px={fmt_price(est_px, is_crypto=is_crypto_symbol(sym))} score={best_score:.1f} trade_id={tid}"))
                write_trade_event(trade_id=tid, event="WOULD_TRADE", symbol=sym, side=side, qty=float(qty), price=float(est_px or 0.0), state="CANARY", why=why, news=news_line, meta={"tif": tif, "score": float(best_score)})
                # no normal per-symbol cooldown (Phase 2A)                return

            # Warmup guard: do not enter immediately after a connect/resume.
            try:
                wu = float(getattr(self.state, "warmup_until_ts", 0.0) or 0.0)
                if wu and time.time() < wu:
                    try:
                        rej["warmup"] = int(rej.get("warmup", 0)) + 1
                    except Exception:
                        pass
                    try:
                        last = float(getattr(self, "_last_warmup_log_ts", 0.0) or 0.0)
                        if time.time() - last > 30.0:
                            self._last_warmup_log_ts = time.time()
                            self.out_q.put(("INFO", f"Warmup active ({int(wu - time.time())}s left): suppressing entries this cycle."))
                    except Exception:
                        pass
                    return
            except Exception:
                pass

            if self.use_limits:
                slip_bps = self.slip_bps_crypto if is_crypto_symbol(sym) else self.slip_bps_stock
                if side == 'buy':
                    limit_px = float(best_meta['ask']) * (1.0 + (slip_bps / 10000.0))
                else:
                    limit_px = float(best_meta['bid']) * (1.0 - (slip_bps / 10000.0))
                od = self.client.submit_order_limit(sym, side, qty, tif, limit_px, extended_hours=False)
            else:
                od = self.client.submit_order_market(sym, side, qty, tif)
            oid = str(od.get('id') or '')
            if not oid:
                raise RuntimeError('Order returned no id')
                # Recovery/stop race-guard: after submitting an entry, do not let broker-recovery clobber stops for a brief window
                try:
                    if self.state is not None:
                        d = getattr(self.state, 'recent_stop_guard_until', None)
                        if d is None:
                            self.state.recent_stop_guard_until = {}
                            d = self.state.recent_stop_guard_until
                        d[sym] = time.time() + 30.0
                except Exception:
                    pass
            # Create trade lifecycle record
            trade_id = gen_trade_id(sym)
            t = ManagedTrade(
                trade_id=trade_id,
                symbol=sym,
                side=side,
                qty=float(qty),
                entry_order_id=oid,
                opened_ts=now,
                atr=float(av or 0.0),
                why=why,
                news=news_line,
                state='ENTRY_SUBMITTED',
            )
            self.trades[trade_id] = t
            # Layer 4: audit trail + replay
            write_trade_event(trade_id=trade_id, event="ENTRY_SUBMITTED", symbol=sym, side=side, qty=float(qty), price=float(limit_px or est_px or 0.0), state=t.state, why=why, news=news_line, meta={"tif": tif, "use_limits": bool(self.use_limits), "score": float(best_score)})


            # Snapshot some decision-time context for later WHY receipts.
            orig_mid = float(best_meta.get('mid') or ((float(best_meta.get('bid') or 0.0) + float(best_meta.get('ask') or 0.0)) / 2.0))
            is_crypto = is_crypto_symbol(sym)
            max_reprice_bps = float(MAX_REPRICE_BPS_CRYPTO if is_crypto else MAX_REPRICE_BPS_STOCK)
            self._open_orders[oid] = {
                'trade_id': trade_id,
                'leg': 'entry',
                'symbol': sym,
                'side': side,
                'qty': qty,
                'limit_price': (round(float(limit_px), 6) if limit_px is not None else None),
                'why': why,
                'news': news_line,
                'ts': now,
                'orig_mid': orig_mid,
                'orig_limit_price': (round(float(limit_px), 6) if is_crypto else round(float(limit_px), 2)) if limit_px is not None else None,
                'max_reprice_bps': max_reprice_bps,
                'last_reprice_ts': 0.0,
                'score': float(best_score),
                'direction': ('BULL' if side == 'buy' else 'BEAR'),
                'rsi': float(best_meta.get('rsi') or 0.0),
                'spread_bps': float(best_meta.get('spread_bps') or 0.0),
                'atr': float(av or 0.0),

                'est_px': float(est_px or close or 0.0),
                'est_notional': float(est_notional or 0.0),
                'eff_risk_pct': float(eff_risk_pct),
                'base_risk_pct': float(base_risk_pct),
                'risk_budget': float(risk_dollars),
                'stop_dist_est': float(stop_dist),
                'eq': float(eq),
                'bp': float(bp),
                'cash': float(cash),
                'available': float(available),
                'paper_relax': bool(self.paper_relax),
                'news_mode': str(news_mode),
                'score': float(best_score),
                'score_total': float(best_score),
                'score_base': float(best_meta.get('base_score') or 0.0),
                'macro_adj': float(best_meta.get('macro_adj') or 0.0),
                'news_boost': float(best_meta.get('news_boost') or 0.0),
                'direction': ('BULL' if side=='buy' else 'BEAR'),
                'news_macro_adj': float(best_meta.get('macro_adj') or 0.0),
                'news_sym_boost': float(best_meta.get('news_boost') or 0.0),
                'sym_news_conf': str(best_meta.get('news_conf') or ''),
                'sym_news_age_m': int(best_meta.get('news_age_m') or 9999),
                'sym_news_headline': str(best_meta.get('news_headline') or ''),
            }

            self._pending_entries[norm_symbol(sym)] = now
            # count entry for activity caps
            self._trade_ts_hour.append(now)
            self._trade_ts_day.append(now)
            # cooldown per symbol to avoid churn
                # no normal per-symbol cooldown (Phase 2A)
            px_txt = (f"limit={fmt_price(limit_px, is_crypto=is_crypto_symbol(sym))}" if limit_px is not None else "market")
            self.out_q.put(('ORDERING', f"{side.upper()} {sym} qty={qty} {px_txt} tif={tif}"))
            # Post a decision line immediately (trade will post on fill)
            self.out_q.put(('DECISION', f"Queued trade candidate: {sym} score={best_score:.1f} trade_id={trade_id}"))
        except Exception as e:
            msg = str(e)
            # Do not stop the engine on order rejection; surface details and continue scanning.
            self.out_q.put(('ERROR', f"Order submit failed: {msg}"))
            mlow = (msg or '').lower()

            # Validation failures (HTTP 400/422) are not auth issues; do NOT trip the global circuit breaker.
            # Treat as a per-symbol reject and cool down briefly so we don't hammer the same invalid payload.
            if ('http 422' in mlow) or ('unprocessable entity' in mlow) or ('http 400' in mlow) or ('bad request' in mlow):
                self._cooldown[sym] = now + 600.0
                self.out_q.put(('WARN', f"Order rejected for {sym} (validation). Cooling down 10m. Details: {msg}"))
                try:
                    write_trade_event(trade_id=gen_trade_id(sym), event="ORDER_REJECT_VALIDATION", symbol=sym, side=side, qty=float(qty), price=float(limit_px or est_px or 0.0), state="REJECTED", why=why, news=news_line, meta={"err": msg})
                except Exception:
                    pass
                return

            if 'rejected' in mlow or 'order' in mlow:
                self._cb_record('order_reject', msg)
            # Alpaca wash-trade protection (403) can trigger if opposite-side orders exist.
            # Crypto does NOT support complex OCO/bracket orders, so we avoid the condition instead of disabling trading.
            if ('wash trade' in mlow) or ('complex orders' in mlow):
                self._cooldown[sym] = now + 600.0
                self.out_q.put(('WARN', f"Wash-trade protection triggered for {sym}. Skipping symbol 10m (opposite-side open orders/position)."))
                try:
                    self._cb_record('wash_trade', msg)
                except Exception:
                    pass
                return

            # If it's just buying power / cash sizing, cool down the symbol and keep trading enabled.

            if 'insufficient' in mlow and ('balance' in mlow or 'buying power' in mlow):
                self._cooldown[sym] = now + 600.0
                self.out_q.put(('WARN', f"Sizing/cash guard hit for {sym}. Cooling down 10m."))
                return

            # Only disable trading if it looks like a true auth/scope issue.
            if ('http 401' in mlow) or ('unauthorized' in mlow) or ('invalid api key' in mlow) or ('forbidden/auth' in mlow and ('wash trade' not in mlow) and ('complex orders' not in mlow) and 'insufficient' not in mlow):
                self.out_q.put(('WARN', 'Trading disabled: Alpaca rejected the request as unauthorized/forbidden. Open Tools -> Edit Alpaca Keys and verify keys + base URL.'))
                self.trade_enabled = False
            return


def group_for(sym: str) -> str:
    if sym in ("SPY","QQQ","IWM","DIA"): return "EQUITY_INDEX"
    if sym in ("BTCUSD","ETHUSD"): return "CRYPTO_MAJOR"
    return "OTHER"

# ---------------- Clipboard helpers ----------------
# Qt widgets already provide a built-in context menu for Cut/Copy/Paste.
# (We previously had a Tk helper here; removed to avoid tk dependency.)

QT_QSS = """
QWidget { background: #0f1115; color: #e6e8eb; font-family: Segoe UI; font-size: 10pt; }
QMainWindow::separator { background: #1f2630; width: 1px; height: 1px; }
QFrame#Card { background: #161a20; border: 1px solid #2a3240; border-radius: 12px; }
QLabel#Title { font-size: 16pt; font-weight: 700; }
QLabel#Subtle { color: #a7b0ba; }
QPushButton { background: #1f2630; border: 1px solid #2a3240; padding: 8px 12px; border-radius: 10px; }
QPushButton:hover { background: #243041; }
QPushButton:pressed { background: #1b2432; }
QLineEdit, QDoubleSpinBox, QSpinBox { background: #0c0f14; border: 1px solid #2a3240; padding: 6px 8px; border-radius: 10px; }
QLineEdit:focus, QDoubleSpinBox:focus, QSpinBox:focus { border: 1px solid #4da3ff; }
QCheckBox { spacing: 8px; }
QCheckBox::indicator { width: 16px; height: 16px; border-radius: 4px; border: 1px solid #2a3240; background: #0c0f14; }
QCheckBox::indicator:checked { background: #4da3ff; border: 1px solid #4da3ff; }
QTextEdit { background: #0b0e12; border: 1px solid #2a3240; border-radius: 12px; padding: 10px; }
QMenuBar { background: #0f1115; border-bottom: 1px solid #1f2630; }
QMenuBar::item:selected { background: #1f2630; border-radius: 8px; }
QMenu { background: #11151b; border: 1px solid #2a3240; }
QMenu::item:selected { background: #1f2630; }
QWidget#Pill { background: #1f2630; border: 1px solid #2a3240; border-radius: 999px; }
QLabel#Dot { font-size: 11pt; }
QLabel#PillText { color: #a7b0ba; font-weight: 600; font-size: 9pt; }
QLabel#Kpi { color: #a7b0ba; }
QLabel#StatusPill { background: #1f2630; border: 1px solid #2a3240; border-radius: 999px; padding: 6px 10px; color: #a7b0ba; }
QLabel#MarketPill { background: #1f2630; border: 1px solid #2a3240; border-radius: 999px; padding: 6px 10px; color: #a7b0ba; }
"""



def _status_dot(color: str) -> str:
    # Unicode circle
    return "●"  # color handled via stylesheet on label

class KeysDialog(QtWidgets.QDialog):
    def __init__(self, parent=None):
        super().__init__(parent)
        self.setWindowTitle("Edit Alpaca Keys")
        self.setModal(True)
        self.resize(640, 360)

        form = QtWidgets.QFormLayout()
        self.key_id = QtWidgets.QLineEdit()
        self.secret = QtWidgets.QLineEdit()
        self.secret.setEchoMode(QtWidgets.QLineEdit.Password)
        self.trade = QtWidgets.QLineEdit()
        self.data = QtWidgets.QLineEdit()

        form.addRow("Key ID", self.key_id)
        form.addRow("Secret", self.secret)
        form.addRow("Paper Trade URL", self.trade)
        form.addRow("Market Data URL", self.data)

        btn_row = QtWidgets.QHBoxLayout()
        btn_row.addStretch(1)
        save = QtWidgets.QPushButton("Save")
        cancel = QtWidgets.QPushButton("Cancel")
        btn_row.addWidget(save)
        btn_row.addWidget(cancel)

        save.clicked.connect(self.accept)
        cancel.clicked.connect(self.reject)

        root = QtWidgets.QVBoxLayout()
        root.addLayout(form)
        root.addSpacing(8)
        root.addLayout(btn_row)

        wrap = QtWidgets.QWidget()
        wrap.setLayout(root)
        outer = QtWidgets.QVBoxLayout()
        card = QtWidgets.QFrame(objectName="Card")
        card.setLayout(root)
        outer.addWidget(card)
        self.setLayout(outer)

        self._load()

    def _load(self):
        try:
            if KEYS_PATH.exists():
                cfg = json.loads(KEYS_PATH.read_text(encoding='utf-8-sig', errors='ignore') or "{}")
            else:
                cfg = {}
        except Exception:
            cfg = {}
        alp = cfg.get('alpaca', {})
        self.key_id.setText(str(alp.get('key_id','') or ''))
        self.secret.setText(str(alp.get('secret_key','') or ''))
        self.trade.setText(str(alp.get('paper_base_url','https://paper-api.alpaca.markets') or ''))
        self.live = QtWidgets.QLineEdit()
        self.live.setPlaceholderText('https://api.alpaca.markets')
        
        self.data.setText(str(alp.get('data_base_url','https://data.alpaca.markets') or ''))
        # live_base_url is optional; used for charts toggle
        self._live_base_url = str(alp.get('live_base_url','https://api.alpaca.markets') or 'https://api.alpaca.markets')

    def get_payload(self):
        return {
            'alpaca': {
                'key_id': self.key_id.text().strip(),
                'secret_key': self.secret.text().strip(),
                'paper_base_url': self.trade.text().strip(),
                'data_base_url': self.data.text().strip(),
                'live_base_url': getattr(self, '_live_base_url', 'https://api.alpaca.markets'),
            }
        }

class PerformanceWidget(QtWidgets.QWidget):
    """Equity curve + P/L bar chart."""
    def __init__(self, parent=None):
        super().__init__(parent)
        self._rows = []
        self.mode = DATA_MODE_PAPER

        top = QtWidgets.QFrame(objectName="Card")
        top_l = QtWidgets.QHBoxLayout(top)
        top_l.setContentsMargins(14, 10, 14, 10)

        self.range_box = QtWidgets.QComboBox()
        self.range_box.addItems(["1D","1W","1M","1Y","ALL"])
        self.tf_box = QtWidgets.QComboBox()
        self.tf_box.addItems(["1m","5m","10m","30m","1h","4h","1d"])

        # Data source toggle (charts only)
        self.mode_box = QtWidgets.QComboBox()
        self.mode_box.addItems([DATA_MODE_PAPER, DATA_MODE_LIVE])
        top_l.insertWidget(0, QtWidgets.QLabel("Data:", objectName="Subtle"))
        top_l.insertWidget(1, self.mode_box)

        top_l.addWidget(QtWidgets.QLabel("Range:", objectName="Subtle"))
        top_l.addWidget(self.range_box)
        top_l.addSpacing(16)
        top_l.addWidget(QtWidgets.QLabel("Timeframe:", objectName="Subtle"))
        top_l.addWidget(self.tf_box)
        top_l.addStretch(1)

        # KPI (Equity/DTD/WTD) shown on Performance tab
        self.kpi_lbl_perf = ElidedLabel("Eq: -- | DTD: -- | WTD: --")
        self.kpi_lbl_perf.setObjectName("KPI")
        self.kpi_lbl_perf.setAlignment(Qt.AlignRight | Qt.AlignVCenter)
        top_l.addWidget(self.kpi_lbl_perf)

        self.pl_lbl = QtWidgets.QLabel("24h: --   WTD: --   MTD: --   All: --")
        self.pl_lbl.setObjectName("Kpi")
        top_l.addWidget(self.pl_lbl)

        # Line chart (equity curve)
        self.line_chart = QChart()
        self.line_chart.legend().hide()
        self.line_series = QLineSeries()
        self.line_chart.addSeries(self.line_series)
        self.line_axis_x = QValueAxis(); self.line_axis_y = QValueAxis()
        self.line_axis_x.setLabelFormat("%d")
        self.line_chart.addAxis(self.line_axis_x, QtCore.Qt.AlignBottom)
        self.line_chart.addAxis(self.line_axis_y, QtCore.Qt.AlignLeft)
        self.line_series.attachAxis(self.line_axis_x)
        self.line_series.attachAxis(self.line_axis_y)
        self.line_view = QChartView(self.line_chart)
        self.line_view.setRenderHint(QtGui.QPainter.Antialiasing)

        # Bar chart (bucketed P/L)
        self.bar_chart = QChart()
        self.bar_chart.legend().hide()
        self.bar_series = QBarSeries()
        self.bar_chart.addSeries(self.bar_series)
        self.bar_axis_x = QBarCategoryAxis()
        self.bar_axis_y = QValueAxis()
        self.bar_chart.addAxis(self.bar_axis_x, QtCore.Qt.AlignBottom)
        self.bar_chart.addAxis(self.bar_axis_y, QtCore.Qt.AlignLeft)
        self.bar_series.attachAxis(self.bar_axis_x)
        self.bar_series.attachAxis(self.bar_axis_y)
        self.bar_view = QChartView(self.bar_chart)
        self.bar_view.setRenderHint(QtGui.QPainter.Antialiasing)

        split = QtWidgets.QSplitter(QtCore.Qt.Vertical)
        split.addWidget(self.line_view)
        split.addWidget(self.bar_view)
        split.setStretchFactor(0, 3)
        split.setStretchFactor(1, 2)

        layout = QtWidgets.QVBoxLayout(self)
        layout.setContentsMargins(14, 14, 14, 14)
        layout.setSpacing(12)
        layout.addWidget(top)
        layout.addWidget(split, 1)

        self.range_box.currentTextChanged.connect(lambda _: self.refresh())
        self.tf_box.currentTextChanged.connect(lambda _: self.refresh())
        self.mode_box.currentTextChanged.connect(self._on_mode)

    

    def _on_mode(self, m: str):
        self.mode = (m or DATA_MODE_PAPER).upper()
        self.refresh()
    def _range_to_seconds(self, rng: str):
        return {
            "1D": 86400,
            "1W": 86400*7,
            "1M": 86400*30,
            "1Y": 86400*365,
            "ALL": None,
        }.get(rng, 86400*7)

    def _tf_to_seconds(self, tf: str):
        return {
            "1m": 60,
            "5m": 300,
            "10m": 600,
            "30m": 1800,
            "1h": 3600,
            "4h": 14400,
            "1d": 86400,
        }.get(tf, 300)

    def load_rows(self):
        self._rows = _load_equity_rows(self.mode)

    def refresh(self, now_equity: Optional[float] = None):
        self.load_rows()
        rows = self._rows
        if not rows:
            self.pl_lbl.setText("24h: --   WTD: --   MTD: --   All: --")
            self.line_series.clear()
            self.bar_series.clear()
            return

        # Summary P/Ls
        if now_equity is None:
            now_equity = rows[-1][1]
        pls = compute_period_pls(now_equity, self.mode)
        def fmt(x):
            return fmt_money(x, signed=True)
        self.pl_lbl.setText(f"24h: {fmt(pls['24h'])}   WTD: {fmt(pls['wtd'])}   MTD: {fmt(pls['mtd'])}   All: {fmt(pls['all'])}")

        # Filter range
        rng = self.range_box.currentText()
        sec = self._range_to_seconds(rng)
        now_ts = time.time()
        if sec is not None:
            start_ts = now_ts - sec
            rows = [(ts, eq) for ts, eq in rows if ts >= start_ts]

        if not rows:
            self.line_series.clear()
            self.bar_series.clear()
            return

        # Resample for line chart: last equity per bucket
        tf = self.tf_box.currentText()
        bucket = self._tf_to_seconds(tf)
        series = []
        last_bucket = None
        last_val = None
        for ts, eq in rows:
            b = int(ts // bucket)
            if last_bucket is None:
                last_bucket = b
                last_val = eq
            elif b == last_bucket:
                last_val = eq
            else:
                series.append((last_bucket, last_val))
                last_bucket = b
                last_val = eq
        if last_bucket is not None:
            series.append((last_bucket, last_val))

        self.line_series.clear()
        # X axis is just index for simplicity (fast, stable); labels are implied by range.
        y_vals = [v for _, v in series]
        for i, (_, v) in enumerate(series):
            self.line_series.append(i, v)

        if y_vals:
            self.line_axis_x.setRange(0, max(1, len(series)-1))
            mn, mx = min(y_vals), max(y_vals)
            pad = (mx-mn)*0.05 if mx>mn else (mn*0.01 if mn else 1.0)
            self.line_axis_y.setRange(mn-pad, mx+pad)

        # Bar chart: profit per bucket (auto bucket by range)
        # 1D -> hourly, up to 1M -> daily, up to 1Y -> weekly, ALL -> monthly (YYYY-MM)
        if rng == "1D":
            bar_bucket = 3600
            label_fmt = "%%H:00"
        elif rng in ("1W","1M"):
            bar_bucket = 86400
            label_fmt = "%%m/%%d"
        elif rng == "1Y":
            bar_bucket = 86400*7
            label_fmt = "Wk %%W"
        else:
            bar_bucket = None  # monthly calendar

        buckets = []
        if bar_bucket is not None:
            last_b = None
            last_close = None
            for ts, eq in rows:
                b = int(ts // bar_bucket)
                if last_b is None:
                    last_b = b; last_close = eq
                elif b == last_b:
                    last_close = eq
                else:
                    buckets.append((last_b, last_close))
                    last_b = b; last_close = eq
            if last_b is not None:
                buckets.append((last_b, last_close))

            # profits: current bucket close - prev bucket close
            cats = []
            vals = []
            colors = []
            prev = None
            for b, close in buckets:
                if prev is None:
                    prev = close
                    continue
                profit = close - prev
                prev = close
                dt_lab = dt.datetime.fromtimestamp(b*bar_bucket, tz=ET_TZ).strftime(label_fmt)
                cats.append(dt_lab)
                vals.append(profit)
                colors.append(profit >= 0)
        else:
            # monthly by YYYY-MM
            month_map = {}
            for ts, eq in rows:
                d = dt.datetime.fromtimestamp(ts, tz=ET_TZ)
                key = f"{d.year:04d}-{d.month:02d}"
                month_map[key] = eq  # last close in month
            keys = sorted(month_map.keys())
            cats = []
            vals = []
            colors = []
            prev = None
            for k in keys:
                close = month_map[k]
                if prev is None:
                    prev = close
                    continue
                profit = close - prev
                prev = close
                cats.append(k)
                vals.append(profit)
                colors.append(profit >= 0)

        self.bar_series.clear()
        self.bar_axis_x.clear()
        if cats:
            # Two sets so we can color green/red
            set_green = QBarSet("Profit"); set_green.setColor(QtGui.QColor("#22c55e"))
            set_red = QBarSet("Loss"); set_red.setColor(QtGui.QColor("#ef4444"))

            for v, is_pos in zip(vals, colors):
                if is_pos:
                    set_green.append(v); set_red.append(0)
                else:
                    set_green.append(0); set_red.append(v)

            self.bar_series.append(set_green)
            self.bar_series.append(set_red)
            self.bar_axis_x.append(cats)
            self.bar_axis_y.setRange(min(vals + [0]) * 1.05, max(vals + [0]) * 1.05 if max(vals+[0]) != 0 else 1.0)


class ElidedLabel(QtWidgets.QLabel):
    """QLabel that elides long text so the window can shrink without forcing a huge minimum width."""
    def __init__(self, text: str = "", parent=None):
        super().__init__(text, parent)
        self.setSizePolicy(QtWidgets.QSizePolicy.Expanding, QtWidgets.QSizePolicy.Preferred)
        self.setMinimumWidth(10)

    def paintEvent(self, event):
        painter = QtGui.QPainter(self)
        fm = QtGui.QFontMetrics(self.font())
        elided = fm.elidedText(self.text(), QtCore.Qt.ElideRight, max(0, self.width() - 2))
        painter.setPen(self.palette().color(QtGui.QPalette.Text))
        painter.drawText(self.rect(), self.alignment() or (QtCore.Qt.AlignVCenter | QtCore.Qt.AlignLeft), elided)

    def sizeHint(self):
        # Small-ish hint so layouts don't insist on full text width.
        sh = super().sizeHint()
        sh.setWidth(min(sh.width(), 520))
        return sh


class MainWindow(QtWidgets.QMainWindow):
    sig_apply_acct = QtCore.Signal(object)
    sig_apply_acct = QtCore.Signal(object)
    def __init__(self):
        super().__init__()
        self.setWindowTitle(APP_NAME)
        self.resize(1040, 720)
        self.setMinimumSize(860, 620)

        self.client = None
        self.client_live = None
        self.data_mode = DATA_MODE_PAPER
        self._exec_mode = DATA_MODE_PAPER  # execution account: PAPER/LIVE
        self.engine = None
        self.news = None
        self.news_ctx = None
        self.q = queue.Queue()
        self._connected = False
        self._connecting = False

        try:
            self._paused = bool(_ensure_settings().get('paused', False))
        except Exception:
            self._paused = False
        # Phase 3.3: consolidated runtime flags
        self.state = EngineState(connected=self._connected, connecting=self._connecting, running=False, paused=self._paused)


        self._last_positions_pull = 0.0
        self._pos_refresh_inflight = False
        self._pos_refresh_last_req = 0.0
        self._last_hb_ts = 0.0
        self._trade_flash_until = 0.0
        self._health_flash_until = 0.0
        self._trade_flash_color = "#a855f7"
        self._health_flash_color = "#f97316"
        self._last_equity = None
        # Positions snapshot (broker pull) + fast UI refresh (quote-cache driven)
        self._pos_snapshot = []
        self._pos_snapshot_ts = 0.0

        self._build_ui()
        try:
            self.sig_apply_acct.connect(self._apply_account_to_ui)
        except Exception:
            pass

        self._apply_theme()

        # Main UI drain timer
        self.timer = QtCore.QTimer(self)
        self.timer.timeout.connect(self._drain)
        self.timer.start(200)

        # Apply ACCT immediately (avoid queue starvation)
        try:
            self.sig_apply_acct.connect(self._apply_account_to_ui)
        except Exception:
            pass

        # Periodic account refresh (for KPIs + equity history)
        self.acct_timer = QtCore.QTimer(self)
        self.acct_timer.timeout.connect(self._request_account_refresh)
        self.acct_timer.start(5000)
        try:
            self._request_account_refresh()
        except Exception:
            pass

        self._last_hb_ts = time.time()
        self.wd_timer = QtCore.QTimer(self)
        self.wd_timer.timeout.connect(self._watchdog_tick)
        wd_check = float(globals().get("WATCHDOG_CHECK_SEC", 1.0) or 1.0)
        self.wd_timer.start(int(wd_check * 1000))

        # Fast positions refresh (does NOT hit broker; updates last/uPnL from quote cache)
        self.pos_fast_timer = QtCore.QTimer(self)
        self.pos_fast_timer.timeout.connect(self._refresh_positions_fast)
        self.pos_fast_timer.start(1000)




    def _current_data_client(self):
        """Return a REST client for UI-side refreshes based on execution mode.

        Execution mode may be stored as a string or (for backward compat) as the exec_mode QComboBox.
        This must never raise on the UI thread.
        """
        try:
            mode = getattr(self, '_exec_mode', DATA_MODE_PAPER)
            if hasattr(mode, 'currentText'):
                mode = mode.currentText()
            mode = (str(mode) if mode is not None else DATA_MODE_PAPER).upper().strip()
            if mode == DATA_MODE_LIVE:
                return getattr(self, 'client_live', None) or getattr(self, 'client', None)
            return getattr(self, 'client', None) or getattr(self, 'client_live', None)
        except Exception:
            try:
                return getattr(self, 'client', None)
            except Exception:
                return None

    def _watchdog_tick(self):
        """UI-side watchdog (non-blocking).

        Hard rules:
        - Never call Alpaca REST here (UI thread).
        - Only restart the Engine thread if it is dead or heartbeat is stale.
        """
        try:
            import time
            now = time.time()
            if getattr(self, '_connect_inflight', False):
                return

            # UI heartbeat (so we can detect a frozen UI elsewhere if needed)
            try:
                self._ui_hb_ts = now
            except Exception:
                pass

            eng = getattr(self, "engine", None)
            # Prefer engine heartbeat; fallback to UI hb
            hb = 0.0
            try:
                if eng is not None:
                    hb = float(getattr(eng, "hb_ts", 0.0) or 0.0)
            except Exception:
                hb = 0.0
            try:
                hb = max(hb, float(getattr(self, "_ui_hb_ts", 0.0) or 0.0))
            except Exception:
                pass

            stale_sec = float(globals().get("WATCHDOG_TIMEOUT_SEC", 5.0) or 5.0)
            cooldown = 2.0  # throttle restarts/log spam
            last = float(getattr(self, "_last_wd_restart_ts", 0.0) or 0.0)

            # Case 1: engine thread is dead
            if eng is not None:
                alive = False
                try:
                    alive = bool(eng.is_alive())
                except Exception:
                    alive = False
                if not alive:
                    if now - last > cooldown:
                        self._last_wd_restart_ts = now
                        try:
                            self._log("WARN", "WARN  Watchdog: engine thread not alive. Restarting...")
                        except Exception:
                            pass
                        self._restart_engine_thread()
                    return

            # Case 2: heartbeat is stale
            if hb > 0 and (now - hb) > stale_sec:
                if now - last > cooldown:
                    self._last_wd_restart_ts = now
                    try:
                        self._log("WARN", f"WARN  Watchdog: heartbeat stale > {stale_sec:.1f}s ({now-hb:.1f}s). Restarting engine...")
                    except Exception:
                        pass
                    self._restart_engine_thread()
                return
        except Exception:
            return

    def _restart_engine_thread(self):
        """Restart Engine safely from UI watchdog. Never blocks UI with REST calls."""
        try:
            import time
            # Stop old engine if present
            try:
                if getattr(self, "engine", None) is not None:
                    try:
                        self.engine.stop()
                    except Exception:
                        pass
            except Exception:
                pass

            kwargs = dict(getattr(self, "_engine_kwargs", {}) or {})
            if not kwargs:
                return

            # Preserve shared EngineState if available
            try:
                if getattr(self, "state", None) is not None:
                    kwargs["state"] = self.state
            except Exception:
                pass

            new_eng = Engine(**kwargs)
            self.engine = new_eng
            try:
                self.engine.hb_ts = time.time()
            except Exception:
                pass
            new_eng.start()
        except Exception as e:
            try:
                self._log("WARN", f"WARN  Watchdog: restart failed: {e}")
            except Exception:
                pass
    def _apply_theme(self):
        self.setStyleSheet(QT_QSS)


    def _set_kpi_text(self, compact: str, full: str, color: Optional[str] = None):
        """Set KPI text on Trading + Performance tabs (no header duplicate)."""
        try:
            # Trading tab KPI (top-right)
            if hasattr(self, 'kpi_lbl_trade') and self.kpi_lbl_trade is not None:
                self.kpi_lbl_trade.setText(compact)
                self.kpi_lbl_trade.setToolTip(full)
                if color is not None:
                    self.kpi_lbl_trade.setStyleSheet(f"color: {color};")
                else:
                    self.kpi_lbl_trade.setStyleSheet("")
            # Performance tab KPI (top-right)
            if hasattr(self, 'perf_widget') and self.perf_widget is not None and hasattr(self.perf_widget, 'kpi_lbl_perf'):
                lbl = getattr(self.perf_widget, 'kpi_lbl_perf', None)
                if lbl is not None:
                    lbl.setText(compact)
                    lbl.setToolTip(full)
                    if color is not None:
                        lbl.setStyleSheet(f"color: {color};")
                    else:
                        lbl.setStyleSheet("")
        except Exception:
            pass

    def _build_ui(self):
        tools = self.menuBar().addMenu("Tools")
        act_keys = QtGui.QAction("Edit Alpaca Keys...", self)
        act_test = QtGui.QAction("Test Keys", self)
        tools.addAction(act_keys); tools.addAction(act_test)
        act_keys.triggered.connect(self.open_keys)
        act_test.triggered.connect(self.test_keys)

        # Header (title + indicator lights + KPIs)
        header = QtWidgets.QFrame(objectName="Card")
        hbox = QtWidgets.QHBoxLayout(header)
        hbox.setContentsMargins(14, 10, 14, 10)
        hbox.setSpacing(10)

        title = ElidedLabel(APP_NAME); title.setToolTip(APP_NAME)
        title.setObjectName("Title")
        hbox.addWidget(title)

        # Execution toggle (PAPER/LIVE) - affects actual trading
        exec_lbl = QtWidgets.QLabel("Exec:")
        exec_lbl.setObjectName("KpiLabel")
        self.exec_mode = QtWidgets.QComboBox()
        self.exec_mode.addItems([DATA_MODE_PAPER, DATA_MODE_LIVE])
        self.exec_mode.setFixedWidth(90)
        self.exec_mode.currentTextChanged.connect(self._on_exec_mode_changed)
        self._exec_mode = self.exec_mode  # backward compat: some code expects _exec_mode widget
        hbox.addWidget(exec_lbl)
        hbox.addWidget(self.exec_mode)

        # Charts/graphs data source toggle (PAPER/LIVE) - affects charts only
        data_lbl = QtWidgets.QLabel("Charts:")
        data_lbl.setObjectName("KpiLabel")
        self.data_mode_box = QtWidgets.QComboBox()
        self.data_mode_box.addItems([DATA_MODE_PAPER, DATA_MODE_LIVE])
        self.data_mode_box.setFixedWidth(90)
        self.data_mode_box.currentTextChanged.connect(self._on_data_mode)
        hbox.addWidget(data_lbl)
        hbox.addWidget(self.data_mode_box)

        # indicator pills
        lights = QtWidgets.QWidget()
        lrow = QtWidgets.QHBoxLayout(lights); lrow.setContentsMargins(0,0,0,0); lrow.setSpacing(10)

        def _mk_light(txt):
            w = QtWidgets.QWidget()
            r = QtWidgets.QHBoxLayout(w); r.setContentsMargins(10,4,10,4); r.setSpacing(6)
            dot = QtWidgets.QLabel("●"); dot.setObjectName("Dot")
            lab = QtWidgets.QLabel(txt); lab.setObjectName("PillText")
            r.addWidget(dot); r.addWidget(lab)
            w.setObjectName("Pill")
            return w, dot

        self.light_conn_w, self.light_conn_dot = _mk_light("CONN")
        self.light_seek_w, self.light_seek_dot = _mk_light("SEEK")
        self.light_trade_w, self.light_trade_dot = _mk_light("TRADE")
        self.light_health_w, self.light_health_dot = _mk_light("HEALTH")
        for w in [self.light_conn_w, self.light_seek_w, self.light_trade_w, self.light_health_w]:
            lrow.addWidget(w)
        hbox.addWidget(lights)

        hbox.addStretch(1)

        # NOTE: keep this ASCII-only to avoid Windows encoding issues
        self.market_lbl = QtWidgets.QLabel("MKT: --")
        self.market_lbl.setObjectName("MarketPill")
        hbox.addWidget(self.market_lbl)

        self.status_lbl = QtWidgets.QLabel("Disconnected")
        self.status_lbl.setObjectName("StatusPill")
        hbox.addWidget(self.status_lbl)

        self._market_clock_started = False
        self._ensure_market_clock_thread()

        # Trading tab contents
        trading = QtWidgets.QWidget()
        t_layout = QtWidgets.QVBoxLayout(trading)
        t_layout.setContentsMargins(14,14,14,14)
        t_layout.setSpacing(12)

        # Trading tab KPI mirror (same KPIs shown in header / performance)
        trade_kpi_row = QtWidgets.QWidget()
        trade_kpi_l = QtWidgets.QHBoxLayout(trade_kpi_row); trade_kpi_l.setContentsMargins(0,0,0,0); trade_kpi_l.setSpacing(6)
        trade_kpi_l.addStretch(1)
        self.kpi_lbl_trade = ElidedLabel("Eq: -- | DTD: -- | WTD: --"); self.kpi_lbl_trade.setToolTip("KPIs (hover for full)")
        self.kpi_lbl_trade.setObjectName("Kpi")
        trade_kpi_l.addWidget(self.kpi_lbl_trade)
        t_layout.addWidget(trade_kpi_row)

        cfg = QtWidgets.QFrame(objectName="Card")
        grid = QtWidgets.QGridLayout(cfg)
        grid.setHorizontalSpacing(18)
        grid.setVerticalSpacing(10)

        self.stocks_edit = QtWidgets.QLineEdit(",".join(DEFAULT_STOCKS))
        self.crypto_edit = QtWidgets.QLineEdit(",".join(DEFAULT_CRYPTO))
        self.aggr_chk = QtWidgets.QCheckBox("Trade aggressively when news aligns"); self.aggr_chk.setChecked(True)
        self.shorts_chk = QtWidgets.QCheckBox("Allow shorts (stocks only)"); self.shorts_chk.setChecked(False)
        self.use_limits_chk = QtWidgets.QCheckBox("Use marketable LIMIT orders"); self.use_limits_chk.setChecked(True)

        self.risk_spin = QtWidgets.QDoubleSpinBox(); self.risk_spin.setDecimals(2); self.risk_spin.setRange(0.01, 5.0); self.risk_spin.setValue(DEFAULT_RISK_PCT)
        self.spread_stock = QtWidgets.QSpinBox(); self.spread_stock.setRange(1, 500); self.spread_stock.setValue(DEFAULT_MAX_SPREAD_BPS_STOCK)
        self.spread_crypto = QtWidgets.QSpinBox(); self.spread_crypto.setRange(1, 5000); self.spread_crypto.setValue(DEFAULT_MAX_SPREAD_BPS_CRYPTO)
        self.slip_stock = QtWidgets.QSpinBox(); self.slip_stock.setRange(0, 200); self.slip_stock.setValue(DEFAULT_SLIP_BPS_STOCK)
        self.slip_crypto = QtWidgets.QSpinBox(); self.slip_crypto.setRange(0, 2000); self.slip_crypto.setValue(DEFAULT_SLIP_BPS_CRYPTO)

        grid.addWidget(QtWidgets.QLabel("Stocks"), 0, 0); grid.addWidget(self.stocks_edit, 0, 1)
        grid.addWidget(QtWidgets.QLabel("Crypto"), 0, 2); grid.addWidget(self.crypto_edit, 0, 3)
        grid.addWidget(self.aggr_chk, 1, 0, 1, 2); grid.addWidget(self.shorts_chk, 1, 2, 1, 2)
        grid.addWidget(QtWidgets.QLabel("Risk % per trade"), 2, 0); grid.addWidget(self.risk_spin, 2, 1)
        grid.addWidget(QtWidgets.QLabel("Max spread bps (stocks)"), 2, 2); grid.addWidget(self.spread_stock, 2, 3)
        grid.addWidget(QtWidgets.QLabel("Max spread bps (crypto)"), 3, 2); grid.addWidget(self.spread_crypto, 3, 3)
        grid.addWidget(self.use_limits_chk, 3, 0, 1, 2)
        grid.addWidget(QtWidgets.QLabel("Slip bps stocks"), 4, 2); grid.addWidget(self.slip_stock, 4, 3)
        grid.addWidget(QtWidgets.QLabel("Slip bps crypto"), 5, 2); grid.addWidget(self.slip_crypto, 5, 3)

        # Buttons
        btn_row = QtWidgets.QHBoxLayout()
        self.btn_stop = QtWidgets.QPushButton("Stop / Disconnect")
        self.btn_flatten = QtWidgets.QPushButton("PANIC: Flatten All")
        self.btn_journal = QtWidgets.QPushButton("Open Journal")
        self.btn_export = QtWidgets.QPushButton("Export Logs")
        btn_row.addWidget(self.btn_stop); btn_row.addWidget(self.btn_flatten)
        btn_row.addStretch(1); btn_row.addWidget(self.btn_journal); btn_row.addWidget(self.btn_export)
        self.btn_stop.clicked.connect(self.stop_or_resume)
        self.btn_flatten.clicked.connect(self.flatten_all)
        self.btn_journal.clicked.connect(self.open_journal)
        self.btn_export.clicked.connect(self.export_logs)

        panes = QtWidgets.QSplitter()
        left = QtWidgets.QWidget()
        left_l = QtWidgets.QVBoxLayout(left)
        left_l.addWidget(QtWidgets.QLabel("Live Feed (Trades / Orders / News)", objectName="Subtle"))
        self.log_box = QtWidgets.QTextEdit(); self.log_box.setReadOnly(True)
        left_l.addWidget(self.log_box)

        right = QtWidgets.QWidget()
        right_l = QtWidgets.QVBoxLayout(right)
        right_l.addWidget(QtWidgets.QLabel("Positions", objectName="Subtle"))
        self.pos_table = QtWidgets.QTableWidget(0, 8)
        self.pos_table.setHorizontalHeaderLabels(["Symbol","Side","Qty","Entry","Last","uPnL","Stop","Tag"])
        self.pos_table.horizontalHeader().setStretchLastSection(True)
        self.pos_table.setEditTriggers(QtWidgets.QAbstractItemView.NoEditTriggers)
        self.pos_table.setSelectionBehavior(QtWidgets.QAbstractItemView.SelectRows)
        self.pos_table.setAlternatingRowColors(True)
        right_l.addWidget(self.pos_table)

        panes.addWidget(left); panes.addWidget(right)
        panes.setStretchFactor(0, 3); panes.setStretchFactor(1, 2)

        t_layout.addWidget(header)
        t_layout.addWidget(cfg)
        t_layout.addLayout(btn_row)
        t_layout.addWidget(panes, 1)

        # Performance tab
        self.perf_widget = PerformanceWidget()

        tabs = QtWidgets.QTabWidget()
        tabs.addTab(trading, "Trading")
        tabs.addTab(self.perf_widget, "Performance")

        central = QtWidgets.QWidget()
        outer = QtWidgets.QVBoxLayout(central)
        outer.setContentsMargins(0,0,0,0)
        outer.setSpacing(0)
        outer.addWidget(tabs)

        self.setCentralWidget(central)

        # init lights
        self._set_dot(self.light_conn_dot, "#ef4444")
        self._set_dot(self.light_seek_dot, "#1f2630")
        self._set_dot(self.light_trade_dot, "#1f2630")
        self._set_dot(self.light_health_dot, "#1f2630")

    def _log(self, *args):
        '''Append a line to the in-app Live Feed.

        Accepts:
          - _log('message')
          - _log('WARN','message')
          - _log('message','WARN')

        Also supports message prefixes like '[TRADE] ...', '[WHY] ...', '[NEWS] ...'.
        '''
        if not args:
            return

                # Normalize (level, msg) — preserve dict payloads (e.g., level='TRADE', msg={...})
        level = 'INFO'
        msg = ''
        if len(args) == 1:
            msg = args[0]
        else:
            a0, a1 = args[0], args[1]
            known = {'INFO','WARN','ERROR','DEBUG','TRADE','WHY','NEWS'}
            if isinstance(a0, str) and a0.strip().upper() in known:
                level = a0.strip().upper()
                msg = a1
            elif isinstance(a1, str) and a1.strip().upper() in known:
                level = a1.strip().upper()
                msg = a0
            else:
                msg = ' '.join(str(x) for x in args)

        # Tag prefixes
        tag_map = {
            '[TRADE]': 'TRADE',
            '[WHY]': 'WHY',
            '[NEWS]': 'NEWS',
        }
        tag = None
        if isinstance(msg, str):
            msg_stripped = msg.lstrip()
            for prefix, t in tag_map.items():
                if msg_stripped.upper().startswith(prefix):
                    tag = t
                    msg_stripped = msg_stripped[len(prefix):].lstrip()
                    msg = msg_stripped
                    break

        icon_map = {
            'INFO': 'ℹ️',
            'WARN': '⚠️',
            'ERROR': '❌',
            'DEBUG': '·',
            'TRADE': '✅',
            'WHY': '🧠',
            'NEWS': '📰',
        }
        # Special case: structured trade payloads → render locked 3-line feed format.
        if level == 'TRADE' and isinstance(msg, dict):
            payload = msg
            summary = str(payload.get('summary') or payload.get('msg') or '').strip()
            why = str(payload.get('why') or '').strip()
            news = str(payload.get('news') or payload.get('news_text') or '').strip()

            def _news_color(n: str) -> str:
                n2 = (n or '').lower()
                if not n2 or n2 in {'n/a','na','none'}:
                    return '#999999'
                if 'hard-block' in n2 or 'contradict' in n2 or 'bearish' in n2:
                    return '#ff6666'
                if 'bullish' in n2 or 'boost' in n2:
                    return '#66ff99'
                if 'neutral' in n2:
                    return '#999999'
                return '#bbbbbb'

            lines = []
            if summary:
                lines.append(('TRADE', summary, None))
            lines.append(('WHY', f"WHY: {why}" if why else "WHY: n/a", None))
            lines.append(('NEWS', f"NEWS: {news}" if news else "NEWS: n/a", _news_color(news)))

            try:
                te = self.log_box
                ts = dt.datetime.now().strftime('%H:%M:%S')
                for sublevel, body, color in lines:
                    icon = icon_map.get(sublevel, '')
                    safe_body = html.escape(body)
                    if color:
                        html_line = f"{ts} {icon} <span style='color:{color}'>{safe_body}</span>"
                    else:
                        html_line = f"{ts} {icon} {safe_body}"
                    te.append(html_line)

                # Trim to avoid unbounded QTextDocument growth (keeps UI responsive)
                try:
                    doc = te.document()
                    if doc is not None and doc.blockCount() > 4000:
                        now = time.time()
                        if now - getattr(self, '_last_log_trim_ts', 0.0) > 2.0:
                            self._last_log_trim_ts = now
                            remove_blocks = doc.blockCount() - 3000
                            if remove_blocks > 0:
                                cursor = QtGui.QTextCursor(doc)
                                cursor.movePosition(QtGui.QTextCursor.Start)
                                for _ in range(remove_blocks):
                                    cursor.select(QtGui.QTextCursor.BlockUnderCursor)
                                    cursor.removeSelectedText()
                                    cursor.deleteChar()
                except Exception:
                    pass
            except Exception:
                pass
            return

        color_map = {
            'ERROR': '#ff6666',
            'WARN':  '#ffcc66',
            'TRADE': '#66ff99',
            'WHY':   '#a3a3ff',
            'NEWS':  '#66b3ff',
            'INFO':  '#d0d0d0',
            'DEBUG': '#a0a0a0',
        }

        icon = icon_map.get(level, '.')
        color = color_map.get(level, '#d0d0d0')
        ts = dt.datetime.now().strftime('%H:%M:%S')

        # --- UI safety: prevent huge/dirty lines from freezing the Qt text widget ---
        try:
            # Replace tabs/newlines (these can come from CSV receipts / spool flushes)
            msg = str(msg).replace('\t',' ').replace('\r',' ').replace('\n',' ')
            # Hard cap line length to keep QTextEdit rendering fast
            _MAX = 900
            if len(msg) > _MAX:
                msg = msg[:_MAX] + ' ... (truncated)'
        except Exception:
            pass


        # Always render as rich HTML in the QTextEdit (so news can be colored).
        safe = html.escape(str(msg))
        html_line = f'<span style="color:{color}">{ts} {icon} {safe}</span>'
        plain_line = f'{ts} {icon} {msg}'.strip()

        te = getattr(self, 'log_box', None)
        if te is None:
            # Back-compat name
            te = getattr(self, 'log_box_text', None)

        try:
            if te is not None:
                # append() is significantly cheaper than manual cursor moves + insertHtml under heavy output
                te.append(html_line)
                # Trim to avoid unbounded QTextDocument growth (keeps UI responsive)
                try:
                    doc = te.document()
                    if doc is not None and doc.blockCount() > 4000:
                        now = time.time()
                        if now - getattr(self, '_last_log_trim_ts', 0.0) > 2.0:
                            self._last_log_trim_ts = now
                            remove_blocks = doc.blockCount() - 3000
                            # Remove in one anchored delete (much cheaper than per-block loops)
                            cur = QtGui.QTextCursor(doc)
                            cur.movePosition(QtGui.QTextCursor.Start)
                            # Move down N blocks while keeping an anchor
                            cur.movePosition(QtGui.QTextCursor.Down, QtGui.QTextCursor.KeepAnchor, max(0, remove_blocks))
                            cur.removeSelectedText()
                            cur.deleteChar()
                except Exception:
                    pass
            else:
                # Fallback
                print(plain_line)
        except Exception:
            try:
                te.append(plain_line)
            except Exception:
                pass


    def _set_dot(self, lbl: QtWidgets.QLabel, color: str):
        """Set dot color efficiently.
        Avoid repeated setStyleSheet calls (can cause UI churn / 'Not Responding').
        """
        try:
            if getattr(lbl, '_last_dot_color', None) == color:
                return
            lbl._last_dot_color = color
        except Exception:
            pass
        lbl.setStyleSheet(f"QLabel#Dot {{ color: {color}; }}")


    def _set_status(self, text: str):
        try:
            if getattr(self, '_last_status_text', None) == text:
                return
            self._last_status_text = text
        except Exception:
            pass
        try:
            self.status_lbl.setText(text)
        except Exception:
            pass

    def _update_indicator_lights(self):
        now = time.time()

        if self._connected:
            self._set_dot(self.light_conn_dot, "#22c55e")
            self._connecting = False
            self._set_status("Connected")
        elif self._connecting:
            self._set_dot(self.light_conn_dot, "#f59e0b")
            self._set_status("Connecting")
        else:
            self._set_dot(self.light_conn_dot, "#ef4444")
            self._set_status("Disconnected")

        hb_src = getattr(self, '_last_hb_ts', 0.0)
        try:
            if self.engine is not None:
                hb_src = float(getattr(self.engine, 'hb_ts', hb_src))
        except Exception:
            pass
        hb_age = now - float(hb_src)
        if self._connected and hb_age < (SCAN_SEC * 2.5):
            phase = int((now * 1000) / SEEK_BLINK_MS) % 2
            self._set_dot(self.light_seek_dot, THEME_ACCENT if phase == 0 else "#1f2630")
        else:
            self._set_dot(self.light_seek_dot, "#1f2630")

        if now < self._trade_flash_until:
            self._set_dot(self.light_trade_dot, self._trade_flash_color)
        else:
            self._set_dot(self.light_trade_dot, "#1f2630")

        if now < self._health_flash_until:
            self._set_dot(self.light_health_dot, self._health_flash_color)
        else:
            self._set_dot(self.light_health_dot, "#1f2630")


    def _fmt_clock_et(self, iso: str) -> str:
        if not iso:
            return "--"
        try:
            d = dt.datetime.fromisoformat(str(iso).replace("Z", "+00:00"))
        except Exception:
            return "--"
        try:
            ny = ZoneInfo("America/New_York")
            d = d.astimezone(ny)
            return d.strftime("%a %H:%M ET")
        except Exception:
            # Fallback: show UTC
            try:
                d = d.astimezone(dt.timezone.utc)
            except Exception:
                pass
            return d.strftime("%a %H:%M UTC")

    def _market_clock_loop(self):
        """Background loop to keep an accurate market open/closed status (incl holidays/weekends).

        Uses Alpaca /v2/clock so holiday/weekend logic stays correct without hardcoding calendars.
        Updates the header pill without spamming the feed.
        """
        last_txt = None
        while True:
            txt = "MKT: -"
            try:
                c = getattr(self, "client", None)
                if c and getattr(self, "_connected", False):
                    ck = c.get_clock()
                    is_open = bool(ck.get("is_open"))

                    def _parse_iso(v):
                        if not v:
                            return None
                        try:
                            return dt.datetime.fromisoformat(str(v).replace("Z", "+00:00"))
                        except Exception:
                            return None

                    def _fmt_delta(seconds: float) -> str:
                        try:
                            s = int(max(0, seconds))
                        except Exception:
                            return ""
                        m = s // 60
                        h = m // 60
                        m = m % 60
                        if h <= 0 and m <= 0:
                            return ""
                        if h <= 0:
                            return f" in {m}m"
                        return f" in {h}h {m}m"

                    next_open_raw = ck.get("next_open")
                    next_close_raw = ck.get("next_close")
                    next_open_dt = _parse_iso(next_open_raw)
                    next_close_dt = _parse_iso(next_close_raw)

                    next_open = self._fmt_clock_et(next_open_raw)
                    next_close = self._fmt_clock_et(next_close_raw)

                    # best-effort session label (PRE/REG/AFTER/WEEKEND-ish)
                    try:
                        sess = stocks_extended_session()
                    except Exception:
                        sess = ""

                    if is_open:
                        delta = ""
                        if next_close_dt:
                            try:
                                now_et = dt.datetime.now(ET_TZ)
                                delta = _fmt_delta((next_close_dt.astimezone(ET_TZ) - now_et).total_seconds())
                            except Exception:
                                delta = ""
                        txt = f"MKT: OPEN (closes {next_close}{delta})"
                    else:
                        delta = ""
                        if next_open_dt:
                            try:
                                now_et = dt.datetime.now(ET_TZ)
                                delta = _fmt_delta((next_open_dt.astimezone(ET_TZ) - now_et).total_seconds())
                            except Exception:
                                delta = ""
                        if sess in ("PRE", "AFTER"):
                            txt = f"MKT: CLOSED ({sess}, opens {next_open}{delta})"
                        else:
                            txt = f"MKT: CLOSED (opens {next_open}{delta})"
            except Exception:
                txt = "MKT: ?"
            if txt != last_txt:
                try:
                    QtCore.QMetaObject.invokeMethod(
                        self.market_lbl,
                        "setText",
                        QtCore.Qt.QueuedConnection,
                        QtCore.Q_ARG(str, txt),
                    )
                except Exception:
                    pass
                last_txt = txt
            time.sleep(60)

    def _ensure_market_clock_thread(self):
        if getattr(self, "_market_clock_started", False):
            return
        self._market_clock_started = True
        t = threading.Thread(target=self._market_clock_loop, daemon=True)
        t.start()

    def _flash_trade(self, color: str, ms: int = 600):
        self._trade_flash_color = color
        self._trade_flash_until = time.time() + (ms / 1000.0)

    def _flash_health(self, color: str, ms: int = 2000):
        now = time.time()
        until = now + (max(500, int(ms)) / 1000.0)
        # Don't shorten an existing flash window.
        if until > float(getattr(self, "_health_flash_until", 0.0) or 0.0):
            self._health_flash_until = until
            self._health_flash_color = color
        else:
            # If extending the same color slightly, keep it.
            if color:
                self._health_flash_color = color

    def open_keys(self):
        dlg = KeysDialog(self)
        if dlg.exec() == QtWidgets.QDialog.Accepted:
            payload = dlg.get_payload()
            try:
                KEYS_PATH.write_text(json.dumps(payload, indent=2), encoding='utf-8-sig')
                self._log(f"Keys saved: {KEYS_PATH}")
            except Exception as e:
                QtWidgets.QMessageBox.critical(self, "Keys", str(e))

    def _load_keys(self):
        if not KEYS_PATH.exists():
            raise RuntimeError(f"Missing keys file: {KEYS_PATH}. Use Tools -> Edit Alpaca Keys...")
        cfg = json.loads(KEYS_PATH.read_text(encoding='utf-8-sig', errors='ignore') or "{}")
        alp = cfg.get('alpaca', {})
        key = (alp.get('key_id') or '').strip()
        sec = (alp.get('secret_key') or '').strip()
        trade = (alp.get('paper_base_url') or '').strip()
        data = (alp.get('data_base_url') or '').strip()
        if not (key and sec and trade and data):
            raise RuntimeError("Alpaca keys incomplete. Use Tools -> Edit Alpaca Keys...")
        return key, sec, trade, data

    def test_keys(self):
        try:
            key, sec, trade, data = self._load_keys()
            c = AlpacaClient(key, sec, trade, data)
        except Exception as e:
            QtWidgets.QMessageBox.critical(self, "Keys", str(e))
            return

        # Run the network call off the UI thread to avoid Windows "Not Responding".
        try:
            self._log("Testing Alpaca keys...")
        except Exception:
            pass

        def _worker():
            ok = False
            msg = ""
            try:
                acct = c.get_account()
                ok = True
                msg = f"OK. Account: {acct.get('account_number','?')}"
            except Exception as e:
                ok = False
                msg = str(e)

            def _ui():
                try:
                    if ok:
                        QtWidgets.QMessageBox.information(self, "Keys", msg)
                    else:
                        QtWidgets.QMessageBox.critical(self, "Keys", msg)
                except Exception:
                    pass

            try:
                QtCore.QTimer.singleShot(0, _ui)
            except Exception:
                try:
                    _ui()
                except Exception:
                    pass

        try:
            threading.Thread(target=_worker, daemon=True).start()
        except Exception as e:
            QtWidgets.QMessageBox.critical(self, "Keys", str(e))

    def _on_exec_mode_changed(self, mode: str):
        mode = (mode or '').upper()
        if mode == DATA_MODE_LIVE:
            # Confirmation dialog to prevent accidental live trading
            txt, ok = QtWidgets.QInputDialog.getText(self, 'Enable LIVE Trading', 'Type LIVE to confirm:', QtWidgets.QLineEdit.Normal, '')
            if (not ok) or (txt.strip().upper() != 'LIVE'):
                # revert
                self.exec_mode.blockSignals(True)
                self.exec_mode.setCurrentText(DATA_MODE_PAPER)
                self.exec_mode.blockSignals(False)
                return
            self._log('WARN  LIVE EXECUTION ARMED')
        else:
            self._log('Execution set to PAPER')

        # Persist current execution mode so an external guardian can make the
        # correct broker calls if the UI dies.
        try:
            _write_json_atomic(APPSTATE_PATH, {
                "ts": time.time(),
                "pid": os.getpid(),
                "version": APP_VERSION,
                "exec_mode": mode,
            })
        except Exception:
            pass


    def _on_data_mode(self, mode: str):
        """Charts-only data mode (PAPER/LIVE). Never affects execution mode."""
        mode = (mode or '').upper().strip()
        if mode not in (DATA_MODE_PAPER, DATA_MODE_LIVE):
            mode = DATA_MODE_PAPER
        self.data_mode = mode

        # Persist UI preference (charts only). Fail-silent.
        try:
            s = _ensure_settings()
            s['data_mode'] = mode
            _save_settings(s)
        except Exception:
            pass

        # Refresh performance widget to reflect the selected data mode.
        try:
            if hasattr(self, 'perf_widget') and self.perf_widget:
                self.perf_widget.mode = self.data_mode
                self.perf_widget.refresh(now_equity=getattr(self, "_last_equity", None))
        except Exception:
            pass

        try:
            self._log(f"Charts data set to {mode}")
        except Exception:
            pass

    def start(self):
        if self._connected:
            self._log("Already connected (auto-connect is enabled). Use Stop / Disconnect to reconnect.")
            try:
                self._request_account_refresh()
            except Exception:
                pass
            return
        if self._connecting:
            return
        try:
            key, sec, trade, data = self._load_keys()
        except Exception as e:
            QtWidgets.QMessageBox.critical(self, "Keys", str(e))
            return

        self._connecting = True
        self.status_lbl.setText("Connecting...")
        mode_txt = DATA_MODE_PAPER
        try:
            w = getattr(self, "exec_mode", None)
            mode_txt = (w.currentText() if w and hasattr(w,"currentText") else str(getattr(self,"_exec_mode",DATA_MODE_PAPER))).upper()
        except Exception:
            mode_txt = DATA_MODE_PAPER
        self._log(f"Connecting to Alpaca {mode_txt}...")

        cfg = json.loads(KEYS_PATH.read_text(encoding='utf-8-sig', errors='ignore') or "{}")

        def worker():
            try:
                exec_mode = DATA_MODE_PAPER
                try:
                    w = getattr(self, 'exec_mode', None)
                    if w is not None and hasattr(w, 'currentText'):
                        exec_mode = (w.currentText() or DATA_MODE_PAPER).upper()
                    else:
                        ex = getattr(self, '_exec_mode', DATA_MODE_PAPER)
                        exec_mode = (ex.currentText() if hasattr(ex, 'currentText') else str(ex)).upper()
                except Exception:
                    exec_mode = DATA_MODE_PAPER
                paper_trade = (cfg.get('alpaca',{}) or {}).get('paper_base_url', trade)
                live_trade = (cfg.get('alpaca',{}) or {}).get('live_base_url', 'https://api.alpaca.markets')
                trade_url = live_trade if exec_mode==DATA_MODE_LIVE else paper_trade
                client = AlpacaClient(key, sec, trade_url, data)
                # optional live client for charts
                try:
                    live_trade = (cfg.get('alpaca',{}) or {}).get('live_base_url','https://api.alpaca.markets')
                except Exception:
                    live_trade = 'https://api.alpaca.markets'
                try:
                    self.client_live = AlpacaClient(key, sec, live_trade, data)
                except Exception:
                    self.client_live = None
                acct = client.get_account()
                self.client = client
                self.news_ctx = NewsContext()
                self.news = NewsMonitor(self.news_ctx, self.q)

                stocks = [s.strip().upper() for s in self.stocks_edit.text().split(',') if s.strip()]
                crypto = [s.strip().upper() for s in self.crypto_edit.text().split(',') if s.strip()]
                symbols = stocks + crypto

                settings = _ensure_settings()
                # PAPER testing: add extra symbols to ensure we can validate lifecycle even if the user already holds BTC/ETH or markets are quiet.
                try:
                    paper_relax = bool(settings.get('paper_relax_for_testing', False)) and (exec_mode == DATA_MODE_PAPER)
                    extras = (settings.get('paper_test_extra_symbols','') or '')
                    if paper_relax and extras:
                        extra_syms = [s.strip().upper() for s in str(extras).split(',') if s.strip()]
                        for s in extra_syms:
                            if s not in symbols:
                                symbols.append(s)
                except Exception:
                    pass
                # Save engine kwargs so the UI watchdog can rebuild Engine safely.
                self._engine_kwargs = dict(
                    client=client,
                    symbols=symbols,
                    news_ctx=self.news_ctx,
                    out_q=self.q,
                    state=self.state,
                    risk_pct=float(self.risk_spin.value()),
                    spread_stock=int(self.spread_stock.value()),
                    spread_crypto=int(self.spread_crypto.value()),
                    use_limits=bool(self.use_limits_chk.isChecked()),
                    slip_stock=float(self.slip_stock.value()),
                    slip_crypto=float(self.slip_crypto.value()),
                    allow_shorts=bool(self.shorts_chk.isChecked()),
                    aggressive_on_aligned=bool(self.aggr_chk.isChecked()),
                    exec_mode=exec_mode,
                    settings=settings,
                )

                self.engine = Engine(
                    client,
                    symbols,
                    self.news_ctx,
                    self.q,
                    self.state,
                    float(self.risk_spin.value()),
                    int(self.spread_stock.value()),
                    int(self.spread_crypto.value()),
                    bool(self.use_limits_chk.isChecked()),
                    float(self.slip_stock.value()),
                    float(self.slip_crypto.value()),
                    allow_shorts=bool(self.shorts_chk.isChecked()),
                    aggressive_on_aligned=bool(self.aggr_chk.isChecked()),
                    exec_mode=exec_mode,
                    settings=settings,
                )

                # Warmup guard: avoid instant entries immediately after connect/resume
                try:
                    if self.state is not None:
                        self.state.warmup_until_ts = time.time() + float(RESUME_WARMUP_SEC)
                        self.q.put(("INFO", f"Warmup: suppressing entries for {int(float(RESUME_WARMUP_SEC))}s after connect/resume."))
                except Exception:
                    pass

                self.news.start()
                self.engine.start()

                self.q.put(("INFO", f"Connected {exec_mode}. Account: {acct.get('account_number','?')}"))
                self.q.put(("UI", {"connected": True, "status": f"Connected - Autotrading ({exec_mode})"}))
                self.q.put(("INFO", f"Watching: {', '.join(symbols)}"))
                try:
                    self.sig_apply_acct.emit(acct)
                except Exception:
                    pass
                self.q.put(("ACCT", acct))
            except Exception as e:
                self.q.put(("ERROR", f"Connect failed: {e}"))
                self.q.put(("UI", {"connected": False, "status": "Disconnected"}))

        threading.Thread(target=worker, daemon=True).start()

    def _set_paused(self, val: bool):
        try:
            s = _ensure_settings()
            s['paused'] = bool(val)
            _save_settings(s)
            self._paused = bool(val)
        except Exception:
            self._paused = bool(val)

    def _resume_from_pause(self):
        # Resume/connect after persisted pause. No UI/layout changes.
        try:
            self._set_paused(False)
        except Exception:
            pass
        try:
            # Force reconnect path
            self._connected = False
            self._connecting = False
        except Exception:
            pass
        try:
            self._log('Resuming...')
        except Exception:
            pass
        # start() already spawns a background worker
        try:
            self.start()
        except Exception as e:
            try:
                self._log(f'Resume failed: {e}')
            except Exception:
                pass

    def stop_or_resume(self):
        # Stop if running; otherwise resume. Bound to the existing Stop/Disconnect button.
        try:
            if bool(getattr(self, '_paused', False)) or (not bool(getattr(self, '_connected', False))):
                return self._resume_from_pause()
        except Exception:
            pass
        # If currently running, stop and persist pause
        try:
            self.stop()
        finally:
            try:
                self._set_paused(True)
                self._log('PAUSED: auto-start suppressed. Click Stop/Disconnect again to resume.')
            except Exception:
                pass


    def stop(self):
        try:
            if self.engine:
                self.engine.stop()
            if self.news:
                self.news.stop()
        finally:
            self.engine = None
            self.news = None
            self.client = None
            self.client_live = None
            self.data_mode = DATA_MODE_PAPER
            self._exec_mode = DATA_MODE_PAPER
            try:
                if hasattr(self, 'exec_mode') and self.exec_mode is not None and hasattr(self.exec_mode,'setCurrentText'):
                    self.exec_mode.blockSignals(True)
                    self.exec_mode.setCurrentText(DATA_MODE_PAPER)
                    self.exec_mode.blockSignals(False)
            except Exception:
                pass
            self._connected = False
            self._connecting = False
            self._set_status("Disconnected")
            self._log("Stopped / disconnected.")
            try:
                self._set_paused(True)
            except Exception:
                pass
            self.pos_table.setRowCount(0)

    
    def _request_positions_refresh(self):
        """Fetch broker positions in a background thread and apply on UI thread via the queue.
        Prevents UI freezes if the REST call stalls."""
        try:
            now = time.time()
            if getattr(self, "_pos_refresh_inflight", False):
                return
            # avoid spam
            if now - getattr(self, "_pos_refresh_last_req", 0.0) < 3.0:
                return
            if not (self.engine and getattr(self.engine, "client", None) and getattr(self, "_connected", False)):
                return
            self._pos_refresh_inflight = True
            self._pos_refresh_last_req = now

            def _worker():
                try:
                    pos = self.engine.client.get_positions()
                    if pos is None:
                        pos = []
                    # send to UI
                    self.q.put(("POS", list(pos)))
                except Exception as e:
                    self.q.put(("WARN", f"Positions refresh failed: {e}"))
                finally:
                    self._pos_refresh_inflight = False

            threading.Thread(target=_worker, daemon=True).start()
        except Exception:
            # never let UI crash for a helper
            return

    def _apply_positions(self, pos):
        """Apply a fresh positions snapshot (list of dicts) to the Positions table."""
        try:
            # Hide dust crypto positions (below broker minimums). They can't be closed reliably, so we
            # keep them out of the table to prevent PANIC spam / confusion.
            try:
                pos = [
                    p for p in (pos or [])
                    if not (is_crypto_symbol(str(p.get("symbol",""))) and is_dust_crypto_position(p, min_notional=1.0))
                ]
            except Exception:
                pass
            if not pos:
                self._pos_snapshot = []
                self.pos_table.setRowCount(0)
                return

            # Snapshot for fast refresh (quotes can update 'Last' and uPnL quickly)
            self._pos_snapshot = pos

            # Render
            self.pos_table.setRowCount(len(pos))
            for i, p in enumerate(pos):
                sym = str(p.get("symbol", ""))
                side = str(p.get("side", ""))
                qty = str(p.get("qty", ""))
                entry = p.get("avg_entry_price")
                upnl = p.get("unrealized_pl")
                last = p.get("current_price")

                def _fmt(x):
                    try:
                        return f"{float(x):.2f}"
                    except Exception:
                        return str(x) if x is not None else ""

                self.pos_table.setItem(i, 0, QtWidgets.QTableWidgetItem(sym))
                self.pos_table.setItem(i, 1, QtWidgets.QTableWidgetItem(side))
                self.pos_table.setItem(i, 2, QtWidgets.QTableWidgetItem(qty))
                self.pos_table.setItem(i, 3, QtWidgets.QTableWidgetItem(_fmt(entry)))
                self.pos_table.setItem(i, 4, QtWidgets.QTableWidgetItem(_fmt(last)))
                self.pos_table.setItem(i, 5, QtWidgets.QTableWidgetItem(_fmt(upnl)))
                # cols 6/7 reserved for stop/tag (if available later)
        except Exception as e:
            self._append_feed(f"WARN  Positions UI update failed: {e}")

    def _refresh_positions_fast(self):
        """Fast timer hook for positions refresh.
        Kept for backward compatibility with the existing timer wiring.
        Routed through the async refresh path to avoid UI thread stalls."""
        try:
            self._request_positions_refresh()
        except Exception:
            # Never crash the UI because a timer tick failed
            try:
                self._log("WARN", "positions fast refresh error (ignored)")
            except Exception:
                pass


    def _refresh_positions(self):
        # Legacy synchronous refresh (kept for compatibility) – now routed through the async
        # refresher to avoid blocking the Qt UI thread with broker REST calls.
        if not self.client:
            try:
                self.pos_table.setRowCount(0)
            except Exception:
                pass
            return
        try:
            self._request_positions_refresh()
        except Exception:
            pass
        return

    def _request_account_refresh(self):
        c = self._current_data_client()
        if not c or not self._connected:
            return
        try:
            now = time.time()
            if getattr(self, "_acct_refresh_inflight", False):
                return
            # Avoid hammering REST (rate limits). Engine already polls too.
            if now - getattr(self, "_acct_refresh_last_req", 0.0) < 5.0:
                return
            self._acct_refresh_inflight = True
            self._acct_refresh_last_req = now

            def worker():
                try:
                    acct = c.get_account()
                    # Apply ACCT immediately (queued to UI thread) + keep queue copy
                    try:
                        self.sig_apply_acct.emit(acct)
                    except Exception:
                        pass
                    self.q.put(("ACCT", acct))
                except Exception as e:
                    self.q.put(("LOG", f"Account refresh failed: {e}"))
                finally:
                    self._acct_refresh_inflight = False

            threading.Thread(target=worker, daemon=True).start()
        except Exception:
            return

    def _apply_account_to_ui(self, acct: dict):
        try:
            eq = _safe_float(acct.get("equity"))
            upl = _safe_float(acct.get("unrealized_pl"))
            bp = _safe_float(acct.get("buying_power") or acct.get("regt_buying_power") or acct.get("cash"))
            # KPI estimate: default to broker equity/unrealized
            eq_est = eq
            upl_sum = upl
            record_equity_snapshot(acct, self.data_mode)
            self._last_equity = eq
            pls = compute_period_pls(eq, self.data_mode)
            # cache for fast KPI updates (equity estimate will adjust unrealized only)
            self._acct_eq = eq
            self._acct_upl = upl
            self._acct_bp = bp
            self._kpi_cached_pls = pls
            self._kpi_cached_ts = time.time()
            def fmt_pl(x):
                return fmt_money(x, signed=True)
            dtd_pl, dtd_base = compute_dtd_pl(eq, self.data_mode)
            wtd_pl, wtd_base = compute_wtd_pl(eq, self.data_mode)
            if dtd_pl is None: dtd_pl, dtd_base = 0.0, (dtd_base or eq or 0.0)
            if wtd_pl is None: wtd_pl, wtd_base = 0.0, (wtd_base or eq or 0.0)
            dtd_pct = (dtd_pl / dtd_base * 100.0) if (dtd_pl is not None and dtd_base not in (None, 0)) else 0.0
            wtd_pct = (wtd_pl / wtd_base * 100.0) if (wtd_pl is not None and wtd_base not in (None, 0)) else 0.0
            full = f"Equity: {fmt_money(eq)}   DTD: {fmt_money(dtd_pl, signed=True)} ({fmt_pct(dtd_pct)})   WTD: {fmt_money(wtd_pl, signed=True)} ({fmt_pct(wtd_pct)})   uPnL: {fmt_money(upl, signed=True)}   BP: {fmt_money(bp)}"
            compact = f"Eq {fmt_money(eq)} | DTD {fmt_money(dtd_pl, signed=True)} ({fmt_pct(dtd_pct)}) | WTD {fmt_money(wtd_pl, signed=True)} ({fmt_pct(wtd_pct)})"
            kpi_color = "#00c853" if (dtd_pl is not None and dtd_pl > 0) else "#ff1744" if (dtd_pl is not None and dtd_pl < 0) else None
            self._set_kpi_text(compact, full, kpi_color)
            # Update performance tab
            self.perf_widget.mode = self.data_mode
            self.perf_widget.refresh(now_equity=eq)
        except Exception:
            pass
    def flatten_all(self):
        if not self.client:
            return
        resp = QtWidgets.QMessageBox.question(
            self,
            "PANIC: Flatten All",
            "Close ALL open positions and cancel open orders?\n\nThis is for emergencies.",
            QtWidgets.QMessageBox.Yes | QtWidgets.QMessageBox.No
        )
        if resp != QtWidgets.QMessageBox.Yes:
            return

        def worker():
            try:
                c = self.client
                self.q.put(("WARN", "PANIC: flattening all positions..."))

                # 1) Cancel all open orders first (free reserved qty)
                try:
                    c.cancel_all_orders()
                except Exception as e:
                    self.q.put(("WARN", f"PANIC: cancel_all_orders failed: {e}"))

                # 2) Pull positions and attempt to close each with the best available method
                try:
                    positions = c.get_positions() or []
                except Exception as e:
                    positions = []
                    self.q.put(("ERROR", f"PANIC: could not fetch positions: {e}"))

                # Snapshot positions before flatten so we can journal PANIC closures
                positions_before = [dict(p) for p in (positions or [])]

                sess = stocks_extended_session()
                can_ext = (sess in ("PRE", "AFTER"))

                def _try_close_one(p: dict, slip_bps_override: float = None):
                    sym = (p.get('symbol') or '').upper().strip()
                    if not sym:
                        return
                    side = (p.get('side') or '').lower()  # long/short
                    qty_s = p.get('qty')
                    try:
                        qty = float(qty_s)
                    except Exception:
                        qty = None
                    if qty is None or qty <= 0:
                        return

                    # Determine asset class (fallback to symbol format)
                    asset_class = (p.get('asset_class') or '').lower()
                    is_crypto = (asset_class == 'crypto') or is_crypto_symbol(sym)

                    if is_crypto and is_dust_crypto_position(p, min_notional=1.0):
                        self.q.put(("WARN", f"PANIC: {sym} is dust (<$1 notional). Cannot reliably close via API; ignoring."))
                        return

                    # Crypto: cancel any resting orders first (they reserve qty), then close_position with retries
                    if is_crypto:
                        try:
                            # Cancel open orders for this symbol to free reserved qty
                            try:
                                for o in c.list_orders(status="open", symbols=[sym], limit=200):
                                    try:
                                        c.cancel_order_by_id(o.id)
                                    except Exception:
                                        pass
                                time.sleep(0.6)
                            except Exception:
                                pass

                            last_err = None
                            for attempt in range(3):
                                try:
                                    c.close_position(sym)
                                    self.q.put(("WARN", f"PANIC: submitted close for {sym} (crypto)"))
                                    return
                                except Exception as e:
                                    last_err = e
                                    es = str(e).lower()
                                    if ("insufficient balance" in es) or ("available" in es):
                                        time.sleep(0.8)
                                        continue
                                    raise

                            self.q.put(("ERROR", f"PANIC: close_position failed for {sym} (crypto): {last_err}"))
                            return
                        except Exception as e:
                            self.q.put(("ERROR", f"PANIC: close_position failed for {sym} (crypto): {e}"))
                            return

                    # Stocks / ETFs
                    if stocks_market_open():
                        # Regular hours: broker close_position is fine
                        try:
                            c.close_position(sym)
                            self.q.put(("WARN", f"PANIC: submitted close for {sym} (stock) qty={qty_s}"))
                            return
                        except Exception as e:
                            self.q.put(("ERROR", f"PANIC: close_position failed for {sym} (stock): {e}"))
                            # fall through to limit attempt

                    # Outside regular hours: only PRE/AFTER can actually fill using extended-hours limit orders
                    if not can_ext:
                        self.q.put(("WARN", f"PANIC: {sym} not closed - stock market is {sess}. Wait for REGULAR hours (or close manually in Alpaca)."))
                        return

                    # Extended hours: place a marketable LIMIT close using configured slippage bps.
                    slip_bps = float(slip_bps_override) if slip_bps_override is not None else (float(self.slip_stock.value()) if hasattr(self, 'slip_stock') else 5.0)
                    bid, ask = c.get_latest_quote(sym)
                    ref = None
                    # For SELL (closing long) use bid as reference; for BUY (cover short) use ask.
                    close_side = 'sell' if side != 'short' else 'buy'
                    if close_side == 'sell':
                        ref = bid or ((bid + ask) / 2.0 if bid and ask else None)
                    else:
                        ref = ask or ((bid + ask) / 2.0 if bid and ask else None)
                    if ref is None:
                        # fallback to current_price from broker position payload if present
                        try:
                            ref = float(p.get('current_price') or 0) or None
                        except Exception:
                            ref = None
                    if ref is None:
                        self.q.put(("WARN", f"PANIC: {sym} - no quote available to price an extended-hours limit close."))
                        return

                    if close_side == 'sell':
                        limit_px = float(ref) * (1.0 - (slip_bps / 10000.0))
                    else:
                        limit_px = float(ref) * (1.0 + (slip_bps / 10000.0))

                    try:
                        c.submit_order_limit(sym, close_side, qty, 'day', limit_px, extended_hours=True)
                        self.q.put(("WARN", f"PANIC: submitted EXT-hours limit close for {sym} qty={qty_s} @ {limit_px:.4f} (session={sess})"))
                    except Exception as e:
                        self.q.put(("ERROR", f"PANIC: EXT-hours limit close failed for {sym}: {e}"))

                for p in positions:
                    _try_close_one(p)

                # 3) Self-confirm + retry loop (fail-loud, best effort)
                base_slip = float(self.slip_stock.value()) if hasattr(self, 'slip_stock') else 5.0
                max_tries = 6
                for attempt in range(1, max_tries + 1):
                    try:
                        time.sleep(1.5 if attempt == 1 else 2.5)
                    except Exception:
                        pass
                    remain = []
                    try:
                        remain = c.get_positions() or []
                    except Exception:
                        remain = []

                    # Ignore tiny "dust" positions that Alpaca refuses to close (min order notional).
                    # This prevents PANIC from looking "broken" when the only remainder is < $1.
                    if remain:
                        remain_all = list(remain)
                        dust_syms = []
                        filtered = []
                        for p in remain_all:
                            try:
                                sym = str(p.get("symbol") or "")
                                qty = abs(_safe_float(p.get("qty") or p.get("quantity") or 0.0))
                                mv = abs(_safe_float(p.get("market_value") or p.get("notional") or 0.0))
                                if mv <= 0.0:
                                    mv = abs(_safe_float(p.get("current_price") or 0.0)) * qty
                                if (qty > 0.0) and (qty <= CRYPTO_DUST_QTY or mv <= CRYPTO_DUST_NOTIONAL):
                                    dust_syms.append(sym)
                                    continue
                                filtered.append(p)
                            except Exception:
                                filtered.append(p)
                        remain = filtered
                        if (not remain) and remain_all:
                            # Only dust is left; consider PANIC successful.
                            uniq = sorted({s for s in dust_syms if s})
                            if uniq:
                                self.q.put(("WARN", f"PANIC:  only dust positions remain (ignored): {','.join(uniq)}"))
                            else:
                                self.q.put(("WARN", "PANIC:  only dust positions remain (ignored)."))
                            break

                    if not remain:
                        self.q.put(("WARN", "PANIC:  all positions closed."))
                        # Tell Engine thread to clear any lingering local trade state now that broker is flat.
                        try:
                            if self.state is not None:
                                self.state.clear_local_trades_pending = True
                                self.state.clear_local_trades_reason = "panic_all_positions_closed"
                        except Exception:
                            pass
                        break

                    syms = ",".join([(r.get('symbol') or '?') for r in remain])
                    self.q.put(("WARN", f"PANIC: positions still open ({attempt}/{max_tries}): {syms}"))

                    # Cancel again to free reservations / replace ext-hours limits
                    try:
                        c.cancel_all_orders()
                    except Exception:
                        pass

                    # Re-attempt close; in PRE/AFTER, increase slippage each retry so we actually get flat.
                    slip_override = min(200.0, base_slip * (1.0 + attempt * 0.75))

                    for p in remain:
                        try:
                            _try_close_one(p, slip_bps_override=slip_override)
                        except Exception:
                            pass

                # Final report (don't silently fail)
                try:
                    time.sleep(1.0)
                    remain2 = c.get_positions() or []
                    if remain2:
                        syms2 = ",".join([(r.get('symbol') or '?') for r in remain2])
                        self.q.put(("ERROR", f"PANIC: WARN  still open after retries: {syms2}"))
                    else:
                        self.q.put(("WARN", "PANIC: flatten completed."))

                        # Journal PANIC closures even if they weren't managed trades (Phase 3 receipts start here).
                        try:
                            panic_tag = dt.datetime.now(tz=ET_TZ).strftime("PANIC_%Y%m%d_%H%M%S")
                            closed_orders = []
                            try:
                                closed_orders = c.list_orders(status="closed", limit=500) or []
                            except Exception:
                                closed_orders = []
                            def _parse_iso(s):
                                try:
                                    if not s:
                                        return None
                                    ss = str(s).replace("Z", "+00:00")
                                    return dt.datetime.fromisoformat(ss)
                                except Exception:
                                    return None
                            # Build a latest filled exit price lookup per symbol
                            latest_fill = {}
                            for o in (closed_orders or []):
                                try:
                                    if (o.get('status') or '').lower() != 'filled':
                                        continue
                                    sym = (o.get('symbol') or '').upper().strip()
                                    if not sym:
                                        continue
                                    fp = _safe_float(o.get('filled_avg_price') or o.get('filled_avg_price'))
                                    if fp <= 0:
                                        continue
                                    t = _parse_iso(o.get('filled_at') or o.get('filled_at') or o.get('updated_at') or o.get('submitted_at'))
                                    prev = latest_fill.get(sym)
                                    if (prev is None) or (t and prev[0] and t > prev[0]) or (t and not prev[0]):
                                        latest_fill[sym] = (t, fp)
                                except Exception:
                                    pass

                            for p0 in (positions_before or []):
                                try:
                                    sym = (p0.get('symbol') or '').upper().strip()
                                    if not sym:
                                        continue
                                    qty = _safe_float(p0.get('qty'))
                                    if qty <= 0:
                                        continue
                                    side = (p0.get('side') or '').lower()  # long/short
                                    entry = _safe_float(p0.get('avg_entry_price') or p0.get('avg_entry_price') or p0.get('avg_entry_price'))
                                    exit_price: Optional[float] = None
                                    if sym in latest_fill:
                                        try:
                                            fp = float(latest_fill[sym][1] or 0.0)
                                            if fp > 0:
                                                exit_price = fp
                                        except Exception:
                                            exit_price = None
                                    pnl: Optional[float] = None
                                    if entry > 0 and exit_price is not None and exit_price > 0:
                                        if side == 'short':
                                            pnl = (entry - exit_price) * qty
                                        else:
                                            pnl = (exit_price - entry) * qty

                                    why_compact = f"PANIC_FLATTEN ({sym})"
                                    exit_s = (f"{exit_price:.8f}" if (exit_price is not None and exit_price > 0) else "n/a")
                                    pnl_s = (f"{pnl:.4f}" if (pnl is not None) else "n/a")
                                    notes = (f"WHY: {why_compact} | " + f"SIZE: qty={qty:.8f} entry~{entry:.8f} exit~{exit_s} pnl~{pnl_s} | " + f"GATES: manual emergency flatten; orders canceled; position close attempted | " + f"NEWS: n/a (panic)")
                                    write_trade_journal_row(
                                        trade_id=f"{panic_tag}_{sym}",
                                        symbol=sym,
                                        side=side or "",
                                        qty=qty,
                                        entry_price=entry,
                                        exit_price=exit_price,
                                        pnl=pnl,
                                        stop_price=0.0,
                                        why=why_compact,
                                        why_verbose=generate_verbose_receipt({"id": f"{panic_tag}_{sym}", "symbol": sym, "side": side or "", "score_total": "n/a", "score_base": "n/a", "macro_adj": "n/a", "news_boost": "n/a", "dir": "n/a", "rsi": "n/a", "atr": "n/a", "spread": "n/a", "risk": "n/a", "qty": qty, "entry": entry, "stop": "n/a", "stopdist": "n/a", "notional": "n/a", "equity": "n/a", "gates": "panic_flatten", "news": "n/a", "close_leg": "panic_flatten", "close_reason": "panic", "exit": exit_price, "pnl": pnl, "pnl_pct": "n/a", "cooldown": "", "closed_et": dt.datetime.now(tz=ET_TZ).strftime('%Y-%m-%d %H:%M:%S ET')}) ,
                                        news="",
                                        notes=notes,
                                    )
                                    try:
                                        write_trade_receipt(trade_id=trade_id, stage="PANIC", receipt={
                                            "event": "PANIC",
                                            "symbol": symbol,
                                            "side": side,
                                            "qty": float(qty or 0.0),
                                            "entry_price": float(entry or 0.0),
                                            "exit_price": float(exit_price or 0.0),
                                            "pnl": float(pnl or 0.0),
                                            "stop_price": 0.0,
                                            "why": why_compact,
                                            "why_verbose": why_compact,
                                            "news": "",
                                            "notes": notes,
                                        })
                                    except Exception:
                                        pass

                                except Exception:
                                    pass
                        except Exception:
                            pass
                except Exception:
                    self.q.put(("WARN", "PANIC: flatten submitted."))
            except Exception as e:
                self.q.put(("ERROR", f"PANIC failed: {e}"))
        threading.Thread(target=worker, daemon=True).start()


    def open_journal(self):
        """Open the trade journal in a non-blocking way (never freeze the UI)."""
        self._log('INFO', 'Open Journal requested...')
        try:
            if hasattr(self, 'btn_journal'):
                self.btn_journal.setEnabled(False)
        except Exception:
            pass

        def _worker():
            err = ''
            try:
                # FAST: only create header if missing/empty. Do NOT run repairs here.
                def _fast_create(p: Path, headers: list[str]) -> None:
                    try:
                        _ensure_dir(p.parent)
                        if (not p.exists()) or p.stat().st_size == 0:
                            with open(p, 'w', encoding='utf-8-sig', newline='') as f:
                                f.write(','.join(headers) + '\n')
                    except Exception:
                        # If locked or unreadable, just skip.
                        pass

                _fast_create(JOURNAL_PATH, JOURNAL_HEADERS)
                _fast_create(TRADE_EVENTS_CSV_PATH, TRADE_EVENTS_HEADERS)
            except Exception as e:
                err = str(e)

            try:
                self.q.put(('BG', {'task': 'open_journal', 'ok': (err == ''), 'path': str(JOURNAL_PATH), 'err': err}))
            except Exception:
                pass

        threading.Thread(target=_worker, daemon=True).start()


    def export_logs(self):
        # Build diagnostics ZIP off the UI thread (zipping can take a few seconds)
        try:
            if hasattr(self, "btn_export_logs"):
                self.btn_export_logs.setEnabled(False)
        except Exception:
            pass

        self._log(" Export Logs: building diagnostics ZIP...")

        def _worker():
            try:
                out_zip = export_diagnostics_zip()
                self.q.put(("BG", {"task": "export_logs", "ok": True, "path": str(out_zip)}))
            except Exception as e:
                self.q.put(("BG", {"task": "export_logs", "ok": False, "err": str(e), "trace": traceback.format_exc()}))

        threading.Thread(target=_worker, daemon=True).start()


    def _drain(self):
        # Pull positions periodically
        if self._connected and self.client and (time.time() - self._last_positions_pull) > 3.0:
            self._last_positions_pull = time.time()
            self._request_positions_refresh()

        try:
            processed = 0
            t0 = time.time()
            qsize = 0
            try:
                qsize = int(self.q.qsize())
            except Exception:
                qsize = 0

            def _is_spammy_scan(msg: str) -> bool:
                m = (msg or "").strip()
                if not m:
                    return True
                if m.startswith("Scanning:"):
                    return True
                if m.startswith("LoopA") or m.startswith("Loop A"):
                    return True
                if m.startswith("Top attention"):
                    return True
                if m.startswith("Probe") or m.startswith("PROBE"):
                    return True
                return False

            while True:
                kind, msg = self.q.get_nowait()
                processed += 1
                if processed >= 50 or (time.time() - t0) > 0.03:
                    # keep UI responsive even if the engine is chatty
                    break

                if kind == "UI" and isinstance(msg, dict):
                    prev_conn = self._connected
                    self._connected = bool(msg.get('connected', self._connected))
                    self._connecting = False if self._connected else self._connecting
                    self._set_status(str(msg.get('status', self.status_lbl.text())))
                    # Once we become connected, force a KPI/account refresh immediately
                    if self._connected and not prev_conn:
                        try:
                            self._request_account_refresh()
                        except Exception:
                            pass
                    continue

                if kind == "HEARTBEAT":
                    if isinstance(msg, dict):
                        self._last_hb_ts = _safe_float(msg.get("ts"), time.time())
                    else:
                        self._last_hb_ts = time.time()
                    continue

                if kind == "BG" and isinstance(msg, dict):
                    task = msg.get("task")
                    if task == "export_logs":
                        try:
                            if hasattr(self, "btn_export_logs"):
                                self.btn_export_logs.setEnabled(True)
                        except Exception:
                            pass

                        if msg.get("ok"):
                            outp = msg.get("path")
                            self._log('INFO', f"Export Logs: {outp}")
                            try:
                                _open_path(Path(outp).parent)
                            except Exception:
                                pass
                        else:
                            self._log('ERROR', f"Export Logs failed: {msg.get('err')}")
                    elif task == "open_journal":
                        try:
                            if hasattr(self, 'btn_journal'):
                                self.btn_journal.setEnabled(True)
                        except Exception:
                            pass

                        if msg.get("ok"):
                            p = Path(str(msg.get("path", JOURNAL_PATH)))
                            self._log('INFO', f"Journal: {p}")
                            ok = _open_path_qt_only(p)
                            if not ok:
                                # Fallback (may block in rare cases, so keep last resort)
                                try:
                                    ok = _open_path(p)
                                except Exception:
                                    ok = False
                            if not ok:
                                self._log('WARN', "Open Journal could not launch automatically. Open it manually from %APPDATA%\\RelentlessExecution.")
                        else:
                            self._log('ERROR', f"Open Journal prep failed: {msg.get('err')}")
                    continue

                if kind == "ACCT" and isinstance(msg, dict):
                    self._apply_account_to_ui(msg)
                    continue

                if kind == "POS" and isinstance(msg, list):
                    self._apply_positions(msg)
                    continue

                if kind == "ORDERING":
                    self._flash_trade("#a855f7", ms=700)
                    self._log(f" ORDER -> {msg}")
                elif kind == "TRADE":
                    self._flash_trade("#4DA3FF", ms=900)
                    if isinstance(msg, dict):
                        summary = str(msg.get('summary','')).strip()
                        why = str(msg.get('why','')).strip()
                        news = str(msg.get('news','')).strip()
                        if summary:
                            self._log('TRADE', summary)
                        if why:
                            self._log('WHY', why)
                        if news:
                            self._log('NEWS', news)
                    else:
                        self._log(str(msg))
                elif kind == "NEWS":
                    self._log('NEWS', str(msg))
                elif kind == "DECISION":
                    self._log(f" {msg}")
                elif kind == "WARN":
                    self._flash_health("#f97316", ms=2500)
                    self._log('WARN', str(msg))
                elif kind == "ERROR":
                    self._flash_health("#ef4444", ms=3000)
                    self._log(f"ERR {msg}")
                else:
                    # Throttle spammy scan chatter to prevent UI lockups ("Not Responding")
                    try:
                        if isinstance(msg, str) and _is_spammy_scan(msg):
                            now2 = time.time()
                            # If backlog is building, drop scan spam aggressively
                            if qsize > 200:
                                continue
                            # Otherwise keep at most one scan-ish line every ~30s
                            if (now2 - float(getattr(self, "_last_scan_log_ts", 0.0))) < 30.0:
                                continue
                            self._last_scan_log_ts = now2
                    except Exception:
                        pass
                    self._log(str(msg))
        except queue.Empty:
            pass

        self._update_indicator_lights()


def replay_summary(path: str) -> bool:
    """MVP replay harness helper.

    For now, this is a *summary* tool (Layer 7) to validate that the
    event stream is being written and is parseable.
    """
    try:
        p = Path(path)
        if not p.exists():
            print(f"REPLAY: file not found: {p}")
            return False
        counts = {}
        total = 0
        with p.open("r", encoding="utf-8-sig", errors="ignore") as f:
            for line in f:
                line = line.strip()
                if not line:
                    continue
                total += 1
                try:
                    j = json.loads(line)
                except Exception:
                    counts["__parse_error__"] = counts.get("__parse_error__", 0) + 1
                    continue
                ev = str(j.get("event") or j.get("kind") or "").strip() or "__unknown__"
                counts[ev] = counts.get(ev, 0) + 1
        print(f"REPLAY: {p.name} total_lines={total}")
        for k in sorted(counts.keys()):
            print(f"  {k}: {counts[k]}")
        return True
    except Exception as e:
        print(f"REPLAY: error: {e}")
        return False


def run_self_test() -> bool:
    """Non-destructive self-test (Layer 8).

    Goal: quickly confirm that persistence paths work and that Alpaca connectivity
    is sane *if keys are present*.
    """
    ok = True
    print("SELF-TEST: starting...")
    try:
        APPDATA_DIR.mkdir(parents=True, exist_ok=True)
        test_path = APPDATA_DIR / "__self_test_write.tmp"
        test_path.write_text("ok", encoding="utf-8-sig")
        test_path.unlink(missing_ok=True)
        print(f"SELF-TEST: AppData writable: {APPDATA_DIR}")
    except Exception as e:
        print(f"SELF-TEST: AppData not writable: {e}")
        ok = False

    try:
        s = _load_settings()
        print(f"SELF-TEST: settings loaded (canary_mode={bool(s.get('canary_mode', False))})")
    except Exception as e:
        print(f"SELF-TEST: settings load failed: {e}")
        ok = False

    # If keys exist, attempt minimal Alpaca checks.
    if KEYS_PATH.exists():
        try:
            k = load_keys()
            c = AlpacaClient(k)
            a = c.get_account()
            eq = a.get("equity") or a.get("portfolio_value")
            bp = a.get("buying_power") or a.get("regt_buying_power")
            print(f"SELF-TEST: Alpaca account OK (equity={eq}, bp={bp})")
            # sample quotes
            sample = ["SPY","QQQ","BTCUSD","ETHUSD"]
            try:
                q = c.get_latest_quotes_bulk(sample)
                print(f"SELF-TEST: quotes OK (symbols={len(q)})")
            except Exception as e:
                print(f"SELF-TEST: quotes failed (non-fatal): {e}")
        except Exception as e:
            print(f"SELF-TEST: Alpaca check failed: {e}")
            ok = False
    else:
        print("SELF-TEST: keys.json not found (skipping Alpaca connectivity check)")

    # Diagnostics export sanity check (optional)
    try:
        p = export_diagnostics("self_test")
        if p:
            print(f"SELF-TEST: diagnostics zip created: {p.name}")
        else:
            print("SELF-TEST: diagnostics zip failed to create")
            ok = False
    except Exception as e:
        print(f"SELF-TEST: diagnostics export error: {e}")
        ok = False

    print("SELF-TEST:", "PASS" if ok else "FAIL")
    return ok


def parse_cli(argv: list[str]):
    ap = argparse.ArgumentParser(prog="RelentlessExecution", add_help=True)
    ap.add_argument("--self-test", action="store_true", help="Run non-destructive checks and exit.")
    ap.add_argument("--export-diagnostics", action="store_true", help="Create a diagnostics zip and exit.")
    ap.add_argument("--diagnostics-reason", default="manual", help="Reason tag for diagnostics zip name.")
    ap.add_argument("--replay", metavar="PATH", help="Summarize a replay_events.jsonl file and exit.")
    ap.add_argument("--set-paper-relax", choices=["on", "off"], help="Toggle PAPER relax testing gates and exit.")
    return ap.parse_args(argv)


def main_ui():
    app = QtWidgets.QApplication(sys.argv)
    app.setApplicationName("Relentless Execution")
    w = MainWindow()
    w.show()
    # Auto-start on launch if keys are present AND not paused
    try:
        _s = _ensure_settings()
        _paused = bool(_s.get('paused', False))
    except Exception:
        _paused = False
    if _paused:
        QtCore.QTimer.singleShot(700, lambda: getattr(w, '_log', print)("PAUSED: auto-start suppressed. Click Stop/Disconnect to resume."))
    elif AUTO_START_ON_LAUNCH and KEYS_PATH.exists():
        QtCore.QTimer.singleShot(600, w.start)
    return app.exec()


def entrypoint():
    install_crash_hook()
    args = parse_cli(sys.argv[1:])

    if getattr(args, "set_paper_relax", None):
        val = str(getattr(args, "set_paper_relax")).lower().strip()
        s = _ensure_settings()
        s["paper_relax_for_testing"] = (val == "on")
        _save_settings(s)
        print(f"Settings updated: paper_relax_for_testing={s['paper_relax_for_testing']}")
        return 0

    if getattr(args, "export_diagnostics", False):
        p = export_diagnostics(str(getattr(args, "diagnostics_reason", "manual") or "manual"))
        if p:
            print(f"Diagnostics created: {p}")
            return 0
        print("Diagnostics export failed")
        return 1

    if getattr(args, "self_test", False):
        return 0 if run_self_test() else 1

    if getattr(args, "replay", None):
        return 0 if replay_summary(str(args.replay)) else 1

    return int(main_ui())


if __name__ == '__main__':
    raise SystemExit(entrypoint())
