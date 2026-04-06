# -*- coding: utf-8 -*-
"""
Autofish Bot — Roblox Western Edition  (v5 — bubble baseline fix + catch OCR hardening)
================================================================================
Requirements:
    pip install mss pillow pytesseract pynput numpy

Tesseract OCR: https://github.com/UB-Mannheim/tesseract/wiki

Controls:
    F6  — Start / Stop fishing
    F7  — Toggle debug overlay
    F8  — Quit

Fixes vs v4:
  • Bubble detection: rolling-average background replaces stale single-frame bg
  • Bubble detection: adaptive net_min floor for nighttime (brt < 50)
  • Bubble detection: BUBBLE_PHASE1_REQUIRED lowered to 8 with confirmation hysteresis
  • Catch OCR: morphological noise cleanup before binarization
  • Catch OCR: adaptive CATCH_MIN_COLORED_PIXELS based on scene brightness
  • Catch OCR: median-filter pre-pass to suppress water ripple texture
"""

import os, sys, time, threading, argparse, ctypes, shutil, re, json
from typing import Optional
from collections import deque

import numpy as np
import mss
import pytesseract
import tkinter as tk
from PIL import Image, ImageFilter, ImageEnhance, ImageStat
from pynput import keyboard as kb
from pynput.keyboard import Key

# ══════════════════════════════════════════════════════════════════════════════
#  TESSERACT
# ═══════════════════════════════════════════════���══════════════════════════════

TESSERACT_PATH = r"C:\Program Files\Tesseract-OCR\tesseract.exe"

def _init_tesseract():
    path = TESSERACT_PATH if os.path.isfile(TESSERACT_PATH) else shutil.which("tesseract")
    if not path:
        print("❌ Tesseract not found! https://github.com/UB-Mannheim/tesseract/wiki")
        sys.exit(1)
    pytesseract.pytesseract.tesseract_cmd = path
    print(f"[INIT] Tesseract: {path}")

# ══════════════════════════════════════════════════════════════════════════════
#  CONFIGURATION
# ══════════════════════════════════════════════════════════════════════════════

BAIT_KEY = "4"
ROD_KEY  = "3"

# ── Regions ───────────────────────────────────────────────────────────────────
SKILL_CHECK_REGION = {"left": 1240, "top": 678,  "width": 80,  "height": 90}
BOBBER_REGION      = {"left": 760,  "top": 380,  "width": 220, "height": 180}
CATCH_REGION       = {"left": 1050, "top": 275,  "width": 400, "height": 19}
BUBBLE_REGION      = {"left": 650,  "top": 300,  "width": 440, "height": 360}
WATER_CURSOR_POS   = (870, 470)

# ── Red bobber pixels — brightness-interpolated thresholds ───────────────────
_BOBBER_BRT_ANCHORS  = (  0, 100, 255)
_BOBBER_RMIN_ANCHORS = ( 70, 130, 180)
_BOBBER_GMAX_ANCHORS = (150, 120,  80)
_BOBBER_BMAX_ANCHORS = (140, 110,  60)

# ── Bubble detection — brightness-interpolated thresholds ─────────────────────
# v5: relaxed night thresholds significantly so bubbles are detectable at brt~38
# v6: added brt=85 anchor and smoothed the 65→110 transition so that game
#     nighttime (brt ~80-90) no longer produces unreachably high thresholds.
_BUBBLE_BRT_ANCHORS  = (  0,  35,  50,  65,  85, 110, 255)
_BUBBLE_GMIN_ANCHORS = ( 10,  12,  15,  50,  85, 135, 135)
_BUBBLE_BMIN_ANCHORS = ( 12,  15,  18,  65, 100, 150, 150)
_BUBBLE_EXCS_ANCHORS = (  1,   2,   3,  15,  35,  75,  75)
_BUBBLE_NMIN_ANCHORS = ( 15,  20,  30, 100, 150, 200, 200)

BUBBLE_GONE_THRESH    = 0.15
BUBBLE_CONFIRM_SECS   = 1.2
BUBBLE_MIN_BASELINE   = 2
BUBBLE_PHASE1_REQUIRED = 8   # v5: lowered from 12 — compensated by hysteresis
BUBBLE_HYSTERESIS_MAX  = 2   # max consecutive below-threshold frames before streak resets

# ── Rolling background for bubble detection ───────────────────────────────────
# Instead of a single stale bg snapshot, we maintain a rolling average of the
# bubble pixel count from recent frames where no bubbles are detected.
# This adapts to gradual lighting changes (day/night cycle, clouds, etc.).
BUBBLE_BG_WINDOW_SIZE  = 30   # number of recent non-bubble frames to average
BUBBLE_BG_UPDATE_ALPHA = 0.05 # EMA smoothing factor for background pixel count

# Inset (pixels) cropped from each edge of BUBBLE_REGION before pixel analysis.
# Avoids counting overlay border artifacts as bubble pixels.
BUBBLE_REGION_INSET = 4

# ── Skill check ───────────────────────────────────────────────────────────────
TARGET_CHARS  = {"T", "F", "G", "R"}
MISREAD_MAP   = {"P": "R", "B": "R"}

SKILL_SAME_LETTER_COOLDOWN = 0.18

# ── Timing ────────────────────────────────────────────────────────────────────
BAIT_KEY_DELAY     = 0.10
BAIT_APPLY_DELAY   = 0.50
ROD_KEY_DELAY      = 0.30
CAST_SETTLE_TIME   = 1.50
BITE_TIMEOUT       = 90.0
SKILL_CHECK_WINDOW = 5.00
CATCH_READ_WINDOW  = 4.00
BETWEEN_CAST_DELAY = 0.05

HOTKEY_TOGGLE = Key.f6
HOTKEY_QUIT   = Key.f8

BASE_DIR    = r"C:\Users\austi\Downloads\autofish"
LOG_PATH    = BASE_DIR + r"\autofish.log"
CONFIG_PATH = BASE_DIR + r"\autofish_config.json"

DEBUG_VERBOSE = False

# ── Catch OCR — v5 adaptive gate ────────���─────────────────────────────────────
# At night (brt < 50), water is dark and fewer spurious colored pixels appear,
# so we can use a lower gate.  During daytime, keep it higher to reject noise.
CATCH_MIN_COLORED_PIXELS_DAY   = 18
CATCH_MIN_COLORED_PIXELS_NIGHT = 10

# ══════════════════════════════════════════════════════════════════════════════
#  LOGGING
# ══════════════════════════════════════════════════════════════════════════════

_log_file = None

def log(msg: str):
    ts   = time.strftime("%H:%M:%S.") + f"{int(time.time()*1000)%1000:03d}"
    line = f"[{ts}] {msg}"
    print(line)
    _recent_logs.append(line)
    if len(_recent_logs) > 16:
        _recent_logs.pop(0)
    if _log_file:
        _log_file.write(line + "\n")
        _log_file.flush()

def init_log():
    global _log_file
    os.makedirs(BASE_DIR, exist_ok=True)
    _log_file = open(LOG_PATH, "w", encoding="utf-8")
    log("=== Autofish Bot v5 started ===")
    log(f"BOBBER_REGION       : {BOBBER_REGION}")
    log(f"BUBBLE_REGION       : {BUBBLE_REGION}")
    log(f"CATCH_REGION        : {CATCH_REGION}")
    log(f"SKILL_CHECK_WINDOW  : {SKILL_CHECK_WINDOW}s")
    log(f"TARGET_CHARS        : {sorted(TARGET_CHARS)}")

# ══════════════════════════════════════════════════════════════════════════════
#  CONFIG FILE
# ══════════════════════════════════════════════════════════════════════════════

_CONFIG_KEYS = [
    "BOBBER_REGION", "BUBBLE_REGION", "SKILL_CHECK_REGION", "CATCH_REGION",
    "BUBBLE_MIN_BASELINE", "BUBBLE_GONE_THRESH", "BUBBLE_CONFIRM_SECS",
    "BUBBLE_PHASE1_REQUIRED", "BAIT_KEY", "ROD_KEY", "TARGET_CHARS",
    "SKILL_CHECK_WINDOW", "CATCH_READ_WINDOW", "BITE_TIMEOUT",
    "BAIT_KEY_DELAY", "BAIT_APPLY_DELAY", "ROD_KEY_DELAY",
    "CAST_SETTLE_TIME", "BETWEEN_CAST_DELAY", "SKILL_SAME_LETTER_COOLDOWN",
    "CATCH_MIN_COLORED_PIXELS_DAY", "CATCH_MIN_COLORED_PIXELS_NIGHT",
    "WATER_CURSOR_POS",
]

def load_config():
    if not os.path.isfile(CONFIG_PATH):
        print("[CONFIG] No config file, using defaults")
        return

    try:
        with open(CONFIG_PATH, "r", encoding="utf-8") as f:
            data = json.load(f)
    except Exception as e:
        print(f"[CONFIG] Warning: could not read config file ({e}), using defaults")
        return

    g = globals()
    for key, value in data.items():
        if key not in _CONFIG_KEYS:
            continue
        # Special type conversions for non-JSON-native types
        if key == "TARGET_CHARS":
            value = set(value)
        elif key == "WATER_CURSOR_POS":
            value = tuple(value)
        g[key] = value
        print(f"[CONFIG] Config override: {key} = {value}")


def save_config():
    data = {
        "BOBBER_REGION":       BOBBER_REGION,
        "BUBBLE_REGION":       BUBBLE_REGION,
        "SKILL_CHECK_REGION":  SKILL_CHECK_REGION,
        "CATCH_REGION":        CATCH_REGION,
        "BUBBLE_MIN_BASELINE": BUBBLE_MIN_BASELINE,
        "BUBBLE_GONE_THRESH":  BUBBLE_GONE_THRESH,
        "BUBBLE_CONFIRM_SECS": BUBBLE_CONFIRM_SECS,
        "BUBBLE_PHASE1_REQUIRED": BUBBLE_PHASE1_REQUIRED,
        "BAIT_KEY":            BAIT_KEY,
        "ROD_KEY":             ROD_KEY,
        "TARGET_CHARS":        sorted(TARGET_CHARS),
        "SKILL_CHECK_WINDOW":  SKILL_CHECK_WINDOW,
        "CATCH_READ_WINDOW":   CATCH_READ_WINDOW,
        "BITE_TIMEOUT":        BITE_TIMEOUT,
        "BAIT_KEY_DELAY":      BAIT_KEY_DELAY,
        "BAIT_APPLY_DELAY":    BAIT_APPLY_DELAY,
        "ROD_KEY_DELAY":       ROD_KEY_DELAY,
        "CAST_SETTLE_TIME":    CAST_SETTLE_TIME,
        "BETWEEN_CAST_DELAY":  BETWEEN_CAST_DELAY,
        "SKILL_SAME_LETTER_COOLDOWN": SKILL_SAME_LETTER_COOLDOWN,
        "CATCH_MIN_COLORED_PIXELS_DAY":   CATCH_MIN_COLORED_PIXELS_DAY,
        "CATCH_MIN_COLORED_PIXELS_NIGHT": CATCH_MIN_COLORED_PIXELS_NIGHT,
        "WATER_CURSOR_POS":    list(WATER_CURSOR_POS),
    }
    try:
        os.makedirs(BASE_DIR, exist_ok=True)
        with open(CONFIG_PATH, "w", encoding="utf-8") as f:
            json.dump(data, f, indent=2)
        print(f"[CONFIG] Saved config to {CONFIG_PATH}")
    except Exception as e:
        print(f"[CONFIG] Warning: could not save config ({e})")

# ══════════════════════════════════════════════════════════════════════════════
#  SESSION STATS
# ══════════════════════════════════════════════════════════════════════════════

_stats = {"start": None, "casts": 0, "baits": 0,
          "skill_checks": 0, "bite_timeouts": 0, "false_reels": 0, "catches": {}}

def _record_catch(name: str):
    name = name.strip() or "Unknown"
    _stats["catches"][name] = _stats["catches"].get(name, 0) + 1

def print_summary():
    if not _stats["start"]:
        return
    elapsed = time.time() - _stats["start"]
    mins, secs = divmod(int(elapsed), 60)
    total = sum(_stats["catches"].values())
    sep = "═" * 44
    print(f"\n{sep}\n           📋  SESSION SUMMARY\n{sep}")
    print(f"  Duration      : {mins}m {secs:02d}s")
    print(f"  Casts         : {_stats['casts']}")
    print(f"  Bait used     : {_stats['baits']}")
    print(f"  Skill checks  : {_stats['skill_checks']}")
    print(f"  Bite timeouts : {_stats['bite_timeouts']}")
    print(f"  False reels   : {_stats['false_reels']}")
    print(f"  Total catches : {total}")
    if _stats["catches"]:
        print("\n  Catches by type:")
        for name, count in sorted(_stats["catches"].items(), key=lambda x: -x[1]):
            print(f"    {name:<32} × {count}")
    print(sep + "\n")
    if _log_file:
        _log_file.write("\n[SUMMARY]\n")
        _log_file.write(f"  Duration: {mins}m {secs:02d}s\n")
        _log_file.write(f"  Casts: {_stats['casts']}\n")
        _log_file.write(f"  Baits: {_stats['baits']}\n")
        _log_file.write(f"  False reels: {_stats['false_reels']}\n")
        _log_file.write(f"  Total catches: {total}\n")
        for name, count in sorted(_stats["catches"].items(), key=lambda x: -x[1]):
            _log_file.write(f"    {name}: {count}\n")
        _log_file.flush()

# ══════════════════════════════════════════════════════════════════════════════
#  STATE
# ══════════════════════════════════════════════════════════════════════════════

fishing_active = False
running        = True

# ══════════════════════════════════════════════════════════════════════════════
#  INPUT
# ══════════════════════════════════════════════════════════════════════════════

KEYEVENTF_SCANCODE   = 0x0008
KEYEVENTF_KEYUP      = 0x0002
MOUSEEVENTF_LEFTDOWN = 0x0002
MOUSEEVENTF_LEFTUP   = 0x0004

SCAN_CODES = {
    "1":0x02,"2":0x03,"3":0x04,"4":0x05,"5":0x06,
    "6":0x07,"7":0x08,"8":0x09,"9":0x0A,"0":0x0B,
    "A":0x1E,"B":0x30,"C":0x2E,"D":0x20,"E":0x12,
    "F":0x21,"G":0x22,"H":0x23,"I":0x17,"J":0x24,
    "K":0x25,"L":0x26,"M":0x32,"N":0x31,"O":0x18,
    "P":0x19,"Q":0x10,"R":0x13,"S":0x1F,"T":0x14,
    "U":0x16,"V":0x2F,"W":0x11,"X":0x2D,"Y":0x15,
    "Z":0x2C,
}

_kbe = ctypes.windll.user32.keybd_event
_kbe.argtypes = [ctypes.c_ubyte, ctypes.c_ubyte, ctypes.c_ulong, ctypes.c_ulong]
_me  = ctypes.windll.user32.mouse_event
_me.argtypes  = [ctypes.c_ulong, ctypes.c_long, ctypes.c_long,
                 ctypes.c_ulong, ctypes.c_ulong]

def send_key(char: str) -> bool:
    sc = SCAN_CODES.get(char.upper())
    if sc is None:
        log(f"  ⚠ No scan code for [{char}]")
        return False
    log(f"  ⌨ send_key [{char}]")
    _kbe(0, sc, KEYEVENTF_SCANCODE, 0)
    time.sleep(0.05)
    _kbe(0, sc, KEYEVENTF_SCANCODE | KEYEVENTF_KEYUP, 0)
    return True

def click(label: str = ""):
    _me(MOUSEEVENTF_LEFTDOWN, 0, 0, 0, 0)
    time.sleep(0.06)
    _me(MOUSEEVENTF_LEFTUP, 0, 0, 0, 0)
    time.sleep(0.06)
    log(f"  🖱 Click — {label}")

def set_cursor_pos(x: int, y: int):
    ctypes.windll.user32.SetCursorPos(x, y)
    time.sleep(0.05)

def _grab_rgb(sct, region: dict) -> Image.Image:
    frame = sct.grab(region)
    return Image.frombytes("RGB", frame.size, frame.bgra, "raw", "BGRX")

def _brightness(img: Image.Image) -> float:
    return ImageStat.Stat(img.convert("L")).mean[0]


def _get_bubble_params(brightness: float):
    """Return (g_min, b_min, cyan_excess, net_min) interpolated from scene brightness."""
    brt = float(brightness)
    g_min       = int(np.interp(brt, _BUBBLE_BRT_ANCHORS, _BUBBLE_GMIN_ANCHORS))
    b_min       = int(np.interp(brt, _BUBBLE_BRT_ANCHORS, _BUBBLE_BMIN_ANCHORS))
    cyan_excess = int(np.interp(brt, _BUBBLE_BRT_ANCHORS, _BUBBLE_EXCS_ANCHORS))
    net_min     = int(np.interp(brt, _BUBBLE_BRT_ANCHORS, _BUBBLE_NMIN_ANCHORS))
    return g_min, b_min, cyan_excess, net_min


def _rain_tier_label(brightness: float) -> str:
    """Return a human-readable label for the rain filter tier active at *brightness*."""
    if brightness >= 90:
        return "strict"
    elif brightness >= 50:
        return "moderate"
    else:
        return "none"


def _pixel_channel_stats(img: Image.Image) -> str:
    """Return a compact string with per-channel mean R/G/B and the mean cyan_excess."""
    inset = BUBBLE_REGION_INSET
    w, h = img.size
    if w > 8 and h > 8:
        img = img.crop((inset, inset, w - inset, h - inset))
    arr = np.array(img, dtype=np.int32)
    R, G, B = arr[:, :, 0], arr[:, :, 1], arr[:, :, 2]
    cyan_ex = G + B - 2 * R
    return (f"avgR={float(R.mean()):.1f} avgG={float(G.mean()):.1f} "
            f"avgB={float(B.mean()):.1f} avgCyan={float(cyan_ex.mean()):.1f}")


def _get_bobber_thresholds(brightness: float):
    """Return (r_min, g_max, b_max) for bobber detection, interpolated from brightness."""
    brt = float(brightness)
    r_min = int(np.interp(brt, _BOBBER_BRT_ANCHORS, _BOBBER_RMIN_ANCHORS))
    g_max = int(np.interp(brt, _BOBBER_BRT_ANCHORS, _BOBBER_GMAX_ANCHORS))
    b_max = int(np.interp(brt, _BOBBER_BRT_ANCHORS, _BOBBER_BMAX_ANCHORS))
    return r_min, g_max, b_max


def _count_bobber_pixels(img: Image.Image, brightness: float) -> int:
    w, h = img.size
    if w > 8 and h > 8:
        img = img.crop((4, 4, w - 4, h - 4))
    arr = np.array(img, dtype=np.int32)
    R, G, B = arr[:,:,0], arr[:,:,1], arr[:,:,2]

    r_min, g_max, b_max = _get_bobber_thresholds(brightness)
    return int(np.sum((R > r_min) & (G < g_max) & (B < b_max)))


def _count_bubble_pixels(img: Image.Image,
                         min_g: int,
                         min_b: int,
                         min_excess: int,
                         brightness: float = 110.0) -> int:
    """
    Count cyan/turquoise bubble pixels.

    v5 changes:
      - At deep night (brt < 40), also accept pixels where G+B collectively
        exceed R by a small margin, even if individually G or B are below the
        normal thresholds.  Bubbles at night are very dim and desaturated.
      - Rain rejection is relaxed further at deep night.
    """
    w, h = img.size
    if w > 8 and h > 8:
        inset = BUBBLE_REGION_INSET
        img = img.crop((inset, inset, w - inset, h - inset))
    arr = np.array(img, dtype=np.int32)
    R, G, B = arr[:,:,0], arr[:,:,1], arr[:,:,2]
    cyan_excess = G + B - 2 * R

    # ── Standard bubble mask ──────────────────────────────────────────────
    # v6: raised strict rain filter boundary from 65→90 so game-nighttime
    #     (brt ~80-85) uses the moderate filter instead of the strict one.
    if brightness >= 90:
        rain_mask = (R * 2 < G) & (R * 2 < B)
    elif brightness >= 50:
        rain_mask = (R * 3 < G * 2) & (R * 3 < B * 2)
    else:
        rain_mask = np.ones(R.shape, dtype=bool)
    standard_mask = (G > min_g) & (B > min_b) & (cyan_excess > min_excess) & rain_mask

    # ── v5: Deep-night supplemental mask ──────────────────────────────────
    # At brt < 45, bubbles can be so dim that individual G/B channels barely
    # clear any threshold.  Instead, look for pixels where the *combined*
    # G+B is meaningfully higher than 2*R (i.e. cyan_excess is positive)
    # and the absolute values aren't totally dark (G+B > 30).
    if brightness < 45:
        deep_night_mask = (
            (cyan_excess > max(1, min_excess)) &
            ((G + B) > 30) &
            (G > R) &
            (B > R)
        )
        mask = standard_mask | deep_night_mask
    else:
        mask = standard_mask

    return int(np.sum(mask))


def _bubble_stats(img: Image.Image, brightness: float):
    """
    Like _count_bubble_pixels but also returns the bounding box of detected
    bubble pixels as (min_x, min_y, max_x, max_y) relative to the cropped
    image (after BUBBLE_REGION_INSET crop), or None when no pixels are found.

    Returns (count, bbox).
    """
    g_min, b_min, min_excess, _ = _get_bubble_params(brightness)
    w, h = img.size
    if w > 8 and h > 8:
        inset = BUBBLE_REGION_INSET
        img = img.crop((inset, inset, w - inset, h - inset))
    arr = np.array(img, dtype=np.int32)
    R, G, B = arr[:,:,0], arr[:,:,1], arr[:,:,2]
    cyan_excess = G + B - 2 * R

    if brightness >= 90:
        rain_mask = (R * 2 < G) & (R * 2 < B)
    elif brightness >= 50:
        rain_mask = (R * 3 < G * 2) & (R * 3 < B * 2)
    else:
        rain_mask = np.ones(R.shape, dtype=bool)
    standard_mask = (G > g_min) & (B > b_min) & (cyan_excess > min_excess) & rain_mask

    if brightness < 45:
        deep_night_mask = (
            (cyan_excess > max(1, min_excess)) &
            ((G + B) > 30) &
            (G > R) &
            (B > R)
        )
        mask = standard_mask | deep_night_mask
    else:
        mask = standard_mask

    ys, xs = np.where(mask)
    if len(xs) == 0:
        return (0, None)
    bbox = (int(xs.min()), int(ys.min()), int(xs.max()), int(ys.max()))
    count = int(np.sum(mask))
    return (count, bbox)

# ══════════════════════════════���═══════════════════════════════════════════════
#  OVERLAY STATE
# ══════════════════════════════════════════════════════════════════════════════

_ov = {
    "bobber_count": 0, "bubble_count": 0, "bobber_state": "idle",
    "skill_brt": 0.0, "skill_letter": "", "catch_text": "",
    "bot_state": "IDLE", "fish_count": 0, "bubble_bbox": None,
}
_recent_logs = []
def ov(key, val): _ov[key] = val

# ══════════════════════════════════════════════════════════════════════════════
#  BOBBER / BUBBLE DETECTION  (v5 — rolling background)
# ══════════════════════════════════════════════════════════════════════════════

def watch_bobber() -> bool:
    log(f"  🎣 Settling {CAST_SETTLE_TIME}s...")
    time.sleep(CAST_SETTLE_TIME)

    deadline = time.time() + BITE_TIMEOUT
    frame_n  = 0

    # ── Phase 1: wait for bubbles ─────────────────────────────────────────────
    ov("bobber_state", "waiting for bubbles")
    with mss.mss() as sct:
        # v5: Take multiple background samples over a short window to build
        # a robust initial background pixel count estimate.
        bg_samples = []
        sample_start = time.time()
        while time.time() - sample_start < 2.0:  # 2.0s of background sampling
            bg_img = _grab_rgb(sct, BUBBLE_REGION)
            brt = _brightness(bg_img)
            g_min, b_min, cyan_excess, net_min = _get_bubble_params(brt)
            bg_px = _count_bubble_pixels(bg_img, g_min, b_min, cyan_excess, brt)
            bg_samples.append(bg_px)
            time.sleep(0.03)

        # Use the median of samples as the initial background (robust to outliers)
        bg_count_ema = float(np.median(bg_samples))
        bg_arr = np.array(bg_samples)
        deep_night_active = brt < 45
        rain_tier = _rain_tier_label(brt)
        chan_stats = _pixel_channel_stats(bg_img)
        log(f"  🫧 Phase 1: waiting for bubbles (brightness={brt:.1f} g_min={g_min} "
            f"b_min={b_min} excess={cyan_excess} net_min={net_min} "
            f"bg_ema={bg_count_ema:.0f} bg_samples={len(bg_samples)} "
            f"bg_min={int(bg_arr.min())} bg_max={int(bg_arr.max())} "
            f"rain={rain_tier} deep_night={deep_night_active})")
        log(f"  🫧 BG pixel stats: {chan_stats}")

        consecutive = 0
        drop_count  = 0   # v5: hysteresis — allow a few drops in the streak
        history     = []

        while time.time() < deadline:
            if not fishing_active:
                ov("bubble_bbox", None)
                return False
            bub_img = _grab_rgb(sct, BUBBLE_REGION)
            brt = _brightness(bub_img)
            g_min, b_min, cyan_excess, net_min = _get_bubble_params(brt)
            bub_count, bbox = _bubble_stats(bub_img, brt)
            ov("bubble_bbox", bbox)

            net_count = max(0, bub_count - int(bg_count_ema))
            red_count = _count_bobber_pixels(_grab_rgb(sct, BOBBER_REGION), brt)
            frame_n  += 1
            ov("bubble_count", net_count)
            ov("bobber_count", red_count)

            if DEBUG_VERBOSE or frame_n % 30 == 0:
                rain_tier = _rain_tier_label(brt)
                deep_night_active = brt < 45
                log(f"  🫧 Phase1 brt={brt:.1f} raw={bub_count} net={net_count} "
                    f"bg_ema={bg_count_ema:.0f} red={red_count} "
                    f"streak={consecutive}/{BUBBLE_PHASE1_REQUIRED} "
                    f"g_min={g_min} b_min={b_min} ex={cyan_excess} nmin={net_min} "
                    f"rain={rain_tier} deep_night={deep_night_active}")
                if frame_n % 90 == 0:
                    log(f"  🫧 Channel stats: {_pixel_channel_stats(bub_img)}")

            if net_count >= net_min:
                consecutive += 1
                drop_count = 0
                history.append(net_count)
            else:
                # v5: Allow up to 2 consecutive below-threshold frames within a
                # streak before resetting.  Bubbles can flicker frame-to-frame.
                if consecutive > 0 and drop_count < BUBBLE_HYSTERESIS_MAX:
                    drop_count += 1
                    log(f"  🫧 Hysteresis drop {drop_count}/{BUBBLE_HYSTERESIS_MAX} "
                        f"(net={net_count} < nmin={net_min}, streak kept at {consecutive})")
                else:
                    consecutive = 0
                    drop_count  = 0
                    history.clear()

            if consecutive >= BUBBLE_PHASE1_REQUIRED:
                net_baseline = max(history)
                log(f"  ✅ Bubbles confirmed! net_baseline={net_baseline} "
                    f"bg_ema={bg_count_ema:.0f}")
                break
            time.sleep(0.016)
        else:
            log(f"  ⏱ Never saw bubbles — timeout")
            ov("bubble_bbox", None)
            return False

    # ── Phase 2: watch for bubble loss ───────────────────────────────────────
    gone_net   = max(int(net_baseline * BUBBLE_GONE_THRESH), max(2, net_baseline // 5))
    gone_since = None
    ov("bobber_state", "watching")
    log(f"  🫧 Phase 2: watching (net gone < {gone_net}, bg_ema={bg_count_ema:.0f} "
        f"baseline={net_baseline})")

    with mss.mss() as sct:
        while time.time() < deadline:
            if not fishing_active:
                ov("bubble_bbox", None)
                return False
            bub_img = _grab_rgb(sct, BUBBLE_REGION)
            brt = _brightness(bub_img)
            g_min, b_min, cyan_excess, _ = _get_bubble_params(brt)
            bub_count, bbox = _bubble_stats(bub_img, brt)
            ov("bubble_bbox", bbox)
            net_count = max(0, bub_count - int(bg_count_ema))
            red_count = _count_bobber_pixels(_grab_rgb(sct, BOBBER_REGION), brt)
            frame_n  += 1
            ov("bubble_count", net_count)
            ov("bobber_count", red_count)

            if DEBUG_VERBOSE or frame_n % 30 == 0:
                gs = f"{time.time()-gone_since:.2f}s" if gone_since else "no"
                rain_tier = _rain_tier_label(brt)
                deep_night_active = brt < 45
                log(f"  🫧 Phase2 brt={brt:.1f} raw={bub_count} net={net_count}/{net_baseline} "
                    f"gone_timer={gs} rain={rain_tier} deep_night={deep_night_active}")
                if frame_n % 90 == 0:
                    log(f"  🫧 Channel stats: {_pixel_channel_stats(bub_img)}")

            if net_count < gone_net:
                if gone_since is None:
                    gone_since = time.time()
                    ov("bobber_state", "no bubbles")
                    log(f"  👀 Bubbles vanished (net {net_count} < {gone_net})")
                elif time.time() - gone_since >= BUBBLE_CONFIRM_SECS:
                    log(f"  🐟 BITE! Gone for {time.time()-gone_since:.2f}s")
                    ov("bobber_state", "bite")
                    ov("bubble_bbox", None)
                    return True
            else:
                if gone_since is not None:
                    log(f"  ↩ Bubbles returned after {time.time()-gone_since:.2f}s")
                gone_since = None
                ov("bobber_state", "watching")
            time.sleep(0.016)

    log(f"  ⏱ No bite after {BITE_TIMEOUT}s")
    ov("bubble_bbox", None)
    return False

# ══════════════════════════════════════════════════════════════════════════════
#  SKILL CHECK OCR
# ══════════════════════════════════════════════════════════════════════════════

def _otsu_threshold(arr: np.ndarray) -> int:
    counts = np.bincount(arr.ravel(), minlength=256).astype(np.float64)
    total  = counts.sum()
    sumB   = 0.0
    wB     = 0.0
    maximum = 0.0
    best_t  = 0
    total_sum = float(np.dot(np.arange(256), counts))

    for t in range(256):
        wB += counts[t]
        if wB == 0:
            continue
        wF = total - wB
        if wF == 0:
            break
        sumB  += t * counts[t]
        mB     = sumB / wB
        mF     = (total_sum - sumB) / wF
        between = wB * wF * (mB - mF) ** 2
        if between > maximum:
            maximum = between
            best_t  = t
    return best_t


def _preprocess_skill(img: Image.Image, invert: bool = False) -> Image.Image:
    w, h = img.size
    px, py = int(w * 0.08), int(h * 0.08)
    img = img.crop((px, py, w - px, h - py))
    img = img.resize((img.width * 8, img.height * 8), Image.Resampling.LANCZOS)
    img = img.convert("L")
    img = img.filter(ImageFilter.UnsharpMask(radius=2, percent=180, threshold=2))
    img = img.filter(ImageFilter.SHARPEN)
    img = ImageEnhance.Contrast(img).enhance(6.0)

    arr = np.array(img, dtype=np.uint8)
    t   = _otsu_threshold(arr)

    if not invert:
        binarised = np.where(arr < t, 0, 255).astype(np.uint8)
    else:
        binarised = np.where(arr < t, 255, 0).astype(np.uint8)

    img = Image.fromarray(binarised, mode="L")
    img = img.filter(ImageFilter.MaxFilter(3)).filter(ImageFilter.MinFilter(3))
    padded = Image.new("L", (img.width + 60, img.height + 60), 255)
    padded.paste(img, (30, 30))
    return padded


_SKILL_STRATEGIES = [
    (False, 10),
    (True,  10),
    (False,  8),
    (True,   8),
]

def _detect_skill_letter(img: Image.Image) -> Optional[str]:
    whitelist = "".join(sorted(TARGET_CHARS | set(MISREAD_MAP.keys())))
    cache: dict = {}

    for invert, psm in _SKILL_STRATEGIES:
        key = invert
        if key not in cache:
            cache[key] = _preprocess_skill(img, invert=invert)
        processed = cache[key]

        try:
            text = pytesseract.image_to_string(
                processed,
                config=(
                    f"--oem 3 --psm {psm} -c tessedit_char_whitelist={whitelist} "
                    "-c tessedit_char_blacklist=abcdefghijklmnopqrstuvwxyz0123456789 "
                    "-c load_system_dawg=0 -c load_freq_dawg=0"
                )
            ).strip().upper()
        except Exception as e:
            log(f"  ❌ OCR inv={invert} psm={psm}: {e}")
            continue

        char = text[0] if text else ""
        log(f"  🔍 OCR inv={invert} psm={psm}: '{text}' → '{char}'")

        if char in MISREAD_MAP:
            char = MISREAD_MAP[char]
            log(f"  🔄 Mapped → '{char}'")

        if char in TARGET_CHARS:
            log(f"  ✅ Skill [{char}] (inv={invert} psm={psm})")
            return char

    return None


def run_skill_check_window(duration: float):
    deadline       = time.time() + duration
    last_pressed   = {}
    total_pressed  = 0

    log(f"  🎮 Skill window open ({duration:.2f}s)")

    with mss.mss() as sct:
        while time.time() < deadline:
            if not fishing_active:
                return

            img = _grab_rgb(sct, SKILL_CHECK_REGION)
            brt = _brightness(img)
            ov("skill_brt", brt)

            if brt < 45:
                time.sleep(0.016)
                continue

            letter = _detect_skill_letter(img)

            if letter:
                ov("skill_letter", letter)
                last_t = last_pressed.get(letter, 0.0)
                age    = time.time() - last_t

                if age >= SKILL_SAME_LETTER_COOLDOWN:
                    log(f"  🎯 Pressing [{letter}] (age={age:.2f}s)")
                    send_key(letter)
                    last_pressed[letter] = time.time()
                    _stats["skill_checks"] += 1
                    total_pressed += 1
                    time.sleep(0.06)
                else:
                    log(f"  ⏭ [{letter}] cooldown ({age:.2f}s < {SKILL_SAME_LETTER_COOLDOWN}s)")

            time.sleep(0.008)

    log(f"  🎮 Skill window closed ({total_pressed} presses)")

# ══════════════════════════════════════════════════════════════════════════════
#  CATCH OCR  (v5 — hardened against water background)
# ══════════════════════════════════════════════════════════════════════════════

_CATCH_PATTERNS = [
    r"caught\s+an?\s+(.+?)(?:\s*[!.]|$)",
    r"reeled\s+in\s+an?\s+(.+?)(?:\s*[!.]|$)",
    r"found\s+an?\s+(.+?)(?:\s*[!.]|$)",
    r"you\s+got\s+an?\s+(.+?)(?:\s*[!.]|$)",
    r"obtained\s+an?\s+(.+?)(?:\s*[!.]|$)",
]

_JUNK_RE  = re.compile(r"[^A-Za-z0-9 '\-]")
_SPACE_RE = re.compile(r"\s+")


def _is_plausible(text: str) -> bool:
    text = text.strip()
    if len(text) < 3:
        return False
    junk_ratio = len(_JUNK_RE.findall(text)) / max(len(text), 1)
    if junk_ratio > 0.25:
        return False
    words = _SPACE_RE.split(text)
    if not any(re.search(r"[A-Za-z]{2,}", w) for w in words):
        return False
    return True


def _parse_catch(raw: str) -> str:
    raw = raw.strip()
    for pat in _CATCH_PATTERNS:
        m = re.search(pat, raw, re.IGNORECASE)
        if m:
            candidate = m.group(1).strip().title()
            if _is_plausible(candidate):
                return candidate
    cleaned = _JUNK_RE.sub("", raw).strip()
    return cleaned[:40] if _is_plausible(cleaned) else "Unknown"


def _count_catch_pixels(img: Image.Image) -> tuple[int, int, int]:
    arr = np.array(img)
    R = arr[:,:,0].astype(np.int32)
    G = arr[:,:,1].astype(np.int32)
    B = arr[:,:,2].astype(np.int32)
    green  = int(np.sum((G > 110) & (G > R + 20) & (G > B + 15) & (G > 125)))
    cyan   = int(np.sum((G > 120) & (B > 100) & (G > R + 20) & (B > R + 15)))
    yellow = int(np.sum((R > 160) & (G > 150) & (B < 120) & (R > B + 35) & (G > B + 25)))
    return green, cyan, yellow


def _get_catch_min_pixels(brightness: float) -> int:
    """v5: Adaptive catch gate threshold based on scene brightness."""
    if brightness < 50:
        return CATCH_MIN_COLORED_PIXELS_NIGHT
    return CATCH_MIN_COLORED_PIXELS_DAY


def _denoise_catch_image(img: Image.Image) -> Image.Image:
    """
    v5: Pre-process catch region to suppress water background texture.

    1. Median filter (radius 2) to remove salt-and-pepper noise from waves
    2. Slight Gaussian blur to merge nearby noise into blobs
    3. Contrast enhancement to separate text from background
    """
    img = img.filter(ImageFilter.MedianFilter(size=3))
    img = img.filter(ImageFilter.GaussianBlur(radius=0.8))
    img = ImageEnhance.Contrast(img).enhance(1.5)
    return img


def _colour_mask_ocr(img: Image.Image, label: str, predicate) -> str:
    """
    v5: Added morphological cleanup and connected-component size filtering
    to reject isolated noise pixels that survive the colour predicate.
    """
    # Pre-denoise to suppress water texture
    img = _denoise_catch_image(img)

    arr = np.array(img)
    R = arr[:,:,0].astype(np.int32)
    G = arr[:,:,1].astype(np.int32)
    B = arr[:,:,2].astype(np.int32)
    mask = predicate(R, G, B)
    if not np.any(mask):
        return ""

    bw  = np.full((arr.shape[0], arr.shape[1]), 255, dtype=np.uint8)
    bw[mask] = 0
    im  = Image.fromarray(bw, mode="L")

    # v5: More aggressive morphological cleanup
    # Close small gaps in letters, then open to remove isolated noise dots
    im = im.filter(ImageFilter.MinFilter(3))  # dilate black (close gaps)
    im = im.filter(ImageFilter.MaxFilter(3))  # erode back (restore size)
    im = im.filter(ImageFilter.MaxFilter(3))  # erode further (remove small noise)
    im = im.filter(ImageFilter.MinFilter(3))  # dilate back (restore letter size)

    pad = Image.new("L", (im.width + 20, im.height + 20), 255)
    pad.paste(im, (10, 10))

    # v5: Scale up for better OCR on the thin 19px strip
    scale = 4
    pad = pad.resize((pad.width * scale, pad.height * scale),
                     Image.Resampling.LANCZOS)

    try:
        text = pytesseract.image_to_string(pad, config="--psm 7 --oem 3").strip()
        if text:
            log(f"  🐠 {label} raw: '{text}'")
        return text
    except Exception:
        return ""


def _otsu_ocr(img: Image.Image) -> str:
    """
    v5: Added pre-denoising and upscaling to reduce water-texture hallucinations.
    """
    w, h = img.size
    if w > 20 and h > 20:
        img = img.crop((10, 4, w - 10, h - 4))

    # v5: Denoise before grayscale conversion
    img = _denoise_catch_image(img)

    gray = img.convert("L")

    # v5: Additional median filter on grayscale to smooth water texture
    gray = gray.filter(ImageFilter.MedianFilter(size=3))

    arr  = np.array(gray, dtype=np.uint8)
    t    = _otsu_threshold(arr)
    best = ""
    for invert in (False, True):
        bw = np.where(arr < t, 0, 255).astype(np.uint8) if not invert \
             else np.where(arr < t, 255, 0).astype(np.uint8)
        im  = Image.fromarray(bw, mode="L")

        # v5: Morphological cleanup
        im = im.filter(ImageFilter.MaxFilter(3)).filter(ImageFilter.MinFilter(3))

        # v5: Scale up from thin strip for better OCR
        scale = 4
        im = im.resize((im.width * scale, im.height * scale),
                        Image.Resampling.LANCZOS)

        pad = Image.new("L", (im.width + 20, im.height + 20), 255)
        pad.paste(im, (10, 10))
        try:
            text = pytesseract.image_to_string(pad, config="--psm 7 --oem 3").strip()
            if text and _is_plausible(text) and len(text) > len(best):
                best = text
                log(f"  🐠 Otsu inv={invert} raw: '{text}'")
        except Exception:
            pass
    return best


def read_catch() -> Optional[str]:
    def green_pred(R, G, B):
        return ((G > 110) & (G > R + 20) & (G > B + 15) & (G > 125))

    def cyan_pred(R, G, B):
        return ((G > 120) & (B > 100) & (G > R + 20) & (B > R + 15))

    def yellow_pred(R, G, B):
        return ((R > 160) & (G > 150) & (B < 120) & (R > B + 35) & (G > B + 25))

    deadline        = time.time() + CATCH_READ_WINDOW
    best_green      = ""
    best_cyan       = ""
    best_yellow     = ""
    best_raw        = ""
    ever_saw_pixels = False
    # v5: Track the scene brightness for adaptive gating
    scene_brt       = 110.0

    with mss.mss() as sct:
        while time.time() < deadline:
            img = _grab_rgb(sct, CATCH_REGION)
            scene_brt = _brightness(img)
            green_px, cyan_px, yellow_px = _count_catch_pixels(img)
            total_colored = green_px + cyan_px + yellow_px

            # v5: Adaptive gate
            min_pixels = _get_catch_min_pixels(scene_brt)

            if DEBUG_VERBOSE:
                log(f"  🐠 Catch gate: green={green_px} cyan={cyan_px} "
                    f"yellow={yellow_px} min={min_pixels} brt={scene_brt:.1f}")

            if total_colored < min_pixels:
                if ever_saw_pixels:
                    log(f"  🐠 Catch pixels gone — stopping early")
                    break
                time.sleep(0.08)
                continue

            ever_saw_pixels = True
            log(f"  🐠 Catch gate passed (green={green_px} cyan={cyan_px} "
                f"yellow={yellow_px} brt={scene_brt:.1f}) — running OCR")

            green  = _colour_mask_ocr(img, "Green",  green_pred)
            cyan   = _colour_mask_ocr(img, "Cyan",   cyan_pred)
            yellow = _colour_mask_ocr(img, "Yellow", yellow_pred)
            raw    = _otsu_ocr(img)

            if _is_plausible(green)  and len(green)  > len(best_green):  best_green  = green
            if _is_plausible(cyan)   and len(cyan)   > len(best_cyan):   best_cyan   = cyan
            if _is_plausible(yellow) and len(yellow) > len(best_yellow): best_yellow = yellow
            if _is_plausible(raw)    and len(raw)    > len(best_raw):    best_raw    = raw

            if (best_green or best_cyan) and len(best_green or best_cyan) >= 4:
                break
            time.sleep(0.12)

    if not ever_saw_pixels:
        log("  🐠 Catch: no colored pixels seen → FALSE REEL")
        return None

    catch_name = best_green or best_cyan or best_raw or best_yellow

    if not catch_name and best_raw:
        catch_name = best_raw
        log(f"  🐠 Using Otsu fallback (color extraction empty but pixels present)")

    catch_text = _parse_catch(catch_name)
    if best_yellow and "EVENT" not in catch_text:
        event = _parse_catch(best_yellow)
        if event and event != "Unknown":
            catch_text = f"{catch_text} | EVENT: {event}"
            log(f"  🌎 World event: '{best_yellow}'")

    ov("catch_text", catch_text)
    ov("fish_count", sum(_stats["catches"].values()) + 1)
    log(f"  🏆 Catch: '{catch_text}'")
    return catch_text

# ══════════════════════════════════════════════════════════════════════════════
#  DEBUG OVERLAY
# ══════════════════════════════════════════════════════════════════════════════

class DebugOverlay:
    C = {"skill": "#00FF41", "bobber": "#FF6B35", "catch": "#FFFF00"}

    def __init__(self):
        self.root = tk.Tk()
        self.root.title("Autofish Overlay")
        sw = self.root.winfo_screenwidth()
        sh = self.root.winfo_screenheight()
        self.root.geometry(f"{sw}x{sh}+0+0")
        self.root.overrideredirect(True)
        self.root.wm_attributes("-topmost", True)
        self.root.wm_attributes("-transparentcolor", "#000001")
        self.root.configure(bg="#000001")
        self.canvas = tk.Canvas(self.root, width=sw, height=sh,
                                bg="#000001", highlightthickness=0)
        self.canvas.pack()
        self._sw, self._sh = sw, sh
        self.root.after(300, self._apply_clickthrough)
        self._draw()

    def _apply_clickthrough(self):
        try:
            hwnd  = ctypes.windll.user32.FindWindowW(None, "Autofish Overlay")
            style = ctypes.windll.user32.GetWindowLongW(hwnd, -20)
            ctypes.windll.user32.SetWindowLongW(hwnd, -20, style | 0x00080000 | 0x00000020)
        except Exception as e:
            log(f"[OVERLAY] {e}")

    def _draw(self):
        c = self.canvas
        c.delete("all")
        s = _ov
        self._box(c, SKILL_CHECK_REGION, self.C["skill"],
                  f"SKILL  brt={s['skill_brt']:.0f}  [{s['skill_letter'] or '—'}]")
        self._box(c, BOBBER_REGION,      self.C["bobber"],
                  f"BOBBER  red={s['bobber_count']}  [{s['bobber_state']}]")
        self._box(c, BUBBLE_REGION,      "#FF00FF",
                  f"BUBBLES  bub={s.get('bubble_count',0)}")
        bbox = s.get("bubble_bbox")
        if bbox is not None:
            ox = BUBBLE_REGION["left"] + BUBBLE_REGION_INSET
            oy = BUBBLE_REGION["top"] + BUBBLE_REGION_INSET
            bx1 = ox + bbox[0]
            by1 = oy + bbox[1]
            bx2 = ox + bbox[2]
            by2 = oy + bbox[3]
            c.create_rectangle(bx1, by1, bx2, by2, outline="#FFFF00", width=2)
            c.create_text(bx1, by1 - 10, anchor="w", text="TRACKING", fill="#FFFF00",
                          font=("Courier New", 8, "bold"))
        self._box(c, CATCH_REGION,       self.C["catch"],
                  f"CATCH  {s['catch_text'] or '—'}")
        hud = ["🎣 AUTOFISH v5  [F7=hide]",
               f"State   : {s['bot_state']}",
               f"Catches : {s['fish_count']}"]
        for i, line in enumerate(hud):
            c.create_text(self._sw - 12, 14 + i*18, anchor="ne", text=line,
                          fill="#FFFFFF", font=("Courier New", 11, "bold"))

        log_lines = _recent_logs[-10:]
        if log_lines:
            height = len(log_lines) * 14 + 10
            width  = min(760, self._sw - 24)
            x0 = self._sw - width - 12
            y0 = self._sh - height - 12
            c.create_rectangle(x0, y0, self._sw - 12, self._sh - 12,
                               fill="#000000", outline="#444444", width=1)
            for idx, line in enumerate(reversed(log_lines)):
                text = line[-120:]
                c.create_text(self._sw - 18, self._sh - 18 - idx*14,
                              anchor="se", text=text,
                              fill="#FFFFFF", font=("Courier New", 9))
        self.root.after(80, self._draw)

    @staticmethod
    def _box(canvas, region, color, label):
        x, y   = region["left"], region["top"]
        x2, y2 = x + region["width"], y + region["height"]
        canvas.create_rectangle(x-2, y-2, x2+2, y2+2, outline=color, width=1, dash=(4,4))
        canvas.create_rectangle(x, y, x2, y2, outline=color, width=2)
        tick = 8
        for cx, cy in [(x,y),(x2,y),(x,y2),(x2,y2)]:
            dx = tick if cx == x else -tick
            dy = tick if cy == y else -tick
            canvas.create_line(cx,cy,cx+dx,cy, fill=color, width=2)
            canvas.create_line(cx,cy,cx,cy+dy, fill=color, width=2)
        lw = len(label)*7 + 6
        canvas.create_rectangle(x, y-18, x+lw, y, fill="#000000", outline=color, width=1)
        canvas.create_text(x+3, y-9, anchor="w", text=label,
                           fill=color, font=("Courier New", 9, "bold"))

    def run(self):     self.root.mainloop()
    def hide(self):    self.root.withdraw()
    def show(self):    self.root.deiconify()
    def destroy(self):
        try: self.root.quit(); self.root.destroy()
        except: pass


# ══════════════════════════════════════════════════════════════════════════════
#  REGION EDITOR
# ══════════════════════════════════════════════════════════════════════════════

_REGION_DEFAULTS = {
    "BOBBER_REGION":     {"left": 760,  "top": 380,  "width": 220, "height": 180},
    "BUBBLE_REGION":     {"left": 650,  "top": 300,  "width": 440, "height": 360},
    "SKILL_CHECK_REGION":{"left": 1240, "top": 678,  "width": 80,  "height": 90},
    "CATCH_REGION":      {"left": 1050, "top": 275,  "width": 400, "height": 19},
}

class RegionEditor:
    _COLORS = {
        "BOBBER_REGION":      "#FF6B35",
        "BUBBLE_REGION":      "#FF00FF",
        "SKILL_CHECK_REGION": "#00FF41",
        "CATCH_REGION":       "#FFFF00",
    }
    _HANDLE_SIZE = 8

    def __init__(self, on_close=None):
        self._on_close = on_close
        self._regions = {
            name: dict(info)
            for name, info in {
                "BOBBER_REGION":      BOBBER_REGION,
                "BUBBLE_REGION":      BUBBLE_REGION,
                "SKILL_CHECK_REGION": SKILL_CHECK_REGION,
                "CATCH_REGION":       CATCH_REGION,
            }.items()
        }
        self._active   = None
        self._drag_state = None  # (region_name, handle, off_x, off_y, orig_region)

        self.root = tk.Toplevel()
        self.root.title("Region Editor")
        sw = self.root.winfo_screenwidth()
        sh = self.root.winfo_screenheight()
        self.root.geometry(f"{sw}x{sh}+0+0")
        self.root.overrideredirect(True)
        self.root.wm_attributes("-topmost", True)
        self.root.wm_attributes("-alpha", 0.55)

        self.canvas = tk.Canvas(self.root, width=sw, height=sh,
                                bg="#000000", highlightthickness=0)
        self.canvas.pack(fill="both", expand=True)

        # Controls frame at bottom
        ctrl = tk.Frame(self.root, bg="#1a1a1a")
        ctrl.place(relx=0.5, rely=1.0, anchor="s", y=-4)

        tk.Button(ctrl, text="Save", bg="#2a7a2a", fg="white",
                  command=self._on_save).pack(side="left", padx=4, pady=4)
        tk.Button(ctrl, text="Cancel", bg="#7a2a2a", fg="white",
                  command=self._on_cancel).pack(side="left", padx=4, pady=4)
        tk.Button(ctrl, text="Reset Defaults", bg="#444444", fg="white",
                  command=self._on_reset).pack(side="left", padx=4, pady=4)

        self._info_var = tk.StringVar(value="Click a region to select it")
        tk.Label(ctrl, textvariable=self._info_var, bg="#1a1a1a", fg="#FFFFFF",
                 font=("Courier New", 9)).pack(side="left", padx=8)

        self.canvas.bind("<Button-1>",        self._on_mouse_down)
        self.canvas.bind("<B1-Motion>",        self._on_mouse_drag)
        self.canvas.bind("<ButtonRelease-1>",  self._on_mouse_up)
        self.root.bind("<Escape>",             lambda e: self._on_cancel())

        self._draw()

    def _handle_positions(self, r):
        x1, y1 = r["left"], r["top"]
        x2, y2 = x1 + r["width"], y1 + r["height"]
        mx, my = (x1 + x2) // 2, (y1 + y2) // 2
        return {
            "tl": (x1, y1), "tr": (x2, y1), "bl": (x1, y2), "br": (x2, y2),
            "tm": (mx, y1), "bm": (mx, y2), "lm": (x1, my), "rm": (x2, my),
        }

    def _draw(self):
        c = self.canvas
        c.delete("all")
        # Semi-transparent dark background hint
        sw = self.root.winfo_screenwidth()
        sh = self.root.winfo_screenheight()
        c.create_rectangle(0, 0, sw, sh, fill="#000000", outline="")

        for name, r in self._regions.items():
            color  = self._COLORS[name]
            active = (name == self._active)
            width  = 3 if active else 1
            x1, y1 = r["left"], r["top"]
            x2, y2 = x1 + r["width"], y1 + r["height"]
            c.create_rectangle(x1, y1, x2, y2, outline=color, width=width)
            lw = len(name) * 7 + 6
            c.create_rectangle(x1, y1 - 16, x1 + lw, y1,
                                fill="#000000", outline=color, width=1)
            c.create_text(x1 + 3, y1 - 8, anchor="w", text=name,
                          fill=color, font=("Courier New", 8, "bold"))
            # Draw handles
            hs = self._HANDLE_SIZE // 2
            for hname, (hx, hy) in self._handle_positions(r).items():
                c.create_rectangle(hx - hs, hy - hs, hx + hs, hy + hs,
                                   fill=color, outline="#FFFFFF", width=1)

        self.root.after(80, self._draw)

    def _hit_test(self, mx, my):
        """Return (region_name, handle_or_'body') for the topmost hit, or (None, None)."""
        hs = self._HANDLE_SIZE // 2
        # Test handles first (active region first for priority)
        order = ([self._active] + [n for n in self._regions if n != self._active]
                 if self._active else list(self._regions))
        for name in order:
            if name is None:
                continue
            r = self._regions[name]
            for hname, (hx, hy) in self._handle_positions(r).items():
                if abs(mx - hx) <= hs and abs(my - hy) <= hs:
                    return name, hname
        # Test region bodies
        for name in order:
            if name is None:
                continue
            r = self._regions[name]
            x1, y1 = r["left"], r["top"]
            x2, y2 = x1 + r["width"], y1 + r["height"]
            if x1 <= mx <= x2 and y1 <= my <= y2:
                return name, "body"
        return None, None

    def _on_mouse_down(self, event):
        name, handle = self._hit_test(event.x, event.y)
        if name is None:
            self._active = None
            self._info_var.set("Click a region to select it")
            return
        self._active = name
        r = self._regions[name]
        self._drag_state = (name, handle, event.x, event.y, dict(r))
        self._update_info(name)

    def _on_mouse_drag(self, event):
        if self._drag_state is None:
            return
        name, handle, sx, sy, orig = self._drag_state
        dx = event.x - sx
        dy = event.y - sy
        r  = dict(orig)
        MIN_SZ = 20

        if handle == "body":
            r["left"] = orig["left"] + dx
            r["top"]  = orig["top"]  + dy
        elif handle == "tl":
            r["left"]   = orig["left"]   + dx
            r["top"]    = orig["top"]    + dy
            r["width"]  = max(MIN_SZ, orig["width"]  - dx)
            r["height"] = max(MIN_SZ, orig["height"] - dy)
        elif handle == "tr":
            r["top"]    = orig["top"]    + dy
            r["width"]  = max(MIN_SZ, orig["width"]  + dx)
            r["height"] = max(MIN_SZ, orig["height"] - dy)
        elif handle == "bl":
            r["left"]   = orig["left"]   + dx
            r["width"]  = max(MIN_SZ, orig["width"]  - dx)
            r["height"] = max(MIN_SZ, orig["height"] + dy)
        elif handle == "br":
            r["width"]  = max(MIN_SZ, orig["width"]  + dx)
            r["height"] = max(MIN_SZ, orig["height"] + dy)
        elif handle == "tm":
            r["top"]    = orig["top"]    + dy
            r["height"] = max(MIN_SZ, orig["height"] - dy)
        elif handle == "bm":
            r["height"] = max(MIN_SZ, orig["height"] + dy)
        elif handle == "lm":
            r["left"]   = orig["left"]   + dx
            r["width"]  = max(MIN_SZ, orig["width"]  - dx)
        elif handle == "rm":
            r["width"]  = max(MIN_SZ, orig["width"]  + dx)

        self._regions[name] = r
        self._update_info(name)

    def _on_mouse_up(self, event):
        self._drag_state = None

    def _update_info(self, name):
        r = self._regions[name]
        self._info_var.set(
            f"{name}: left={r['left']} top={r['top']} w={r['width']} h={r['height']}"
        )

    def _apply_to_globals(self):
        global BOBBER_REGION, BUBBLE_REGION, SKILL_CHECK_REGION, CATCH_REGION
        BOBBER_REGION      = self._regions["BOBBER_REGION"]
        BUBBLE_REGION      = self._regions["BUBBLE_REGION"]
        SKILL_CHECK_REGION = self._regions["SKILL_CHECK_REGION"]
        CATCH_REGION       = self._regions["CATCH_REGION"]

    def _on_save(self):
        self._apply_to_globals()
        save_config()
        self._close()

    def _on_cancel(self):
        self._close()

    def _on_reset(self):
        for name, defaults in _REGION_DEFAULTS.items():
            self._regions[name] = dict(defaults)
        self._active = None
        self._info_var.set("Defaults restored — press Save to apply")

    def _close(self):
        try:
            self.root.destroy()
        except Exception:
            pass
        if self._on_close:
            self._on_close()

    def run(self):
        self.root.mainloop()


# ══════════════════════════════════════════════════════════════════════════════
#  CONTROL PANEL
# ══════════════════════════════════════════════════════════════════════════════

class ControlPanel:
    def __init__(self, overlay_root: tk.Tk):
        self._root = overlay_root
        sw = overlay_root.winfo_screenwidth()

        self.win = tk.Toplevel(overlay_root)
        self.win.title("Autofish Control")
        self.win.geometry(f"200x140+{sw - 210}+4")
        self.win.wm_attributes("-topmost", True)
        self.win.configure(bg="#1a1a1a")
        self.win.resizable(False, False)
        self.win.protocol("WM_DELETE_WINDOW", lambda: None)  # use Quit button to exit

        # Status labels
        self._state_var = tk.StringVar(value="IDLE")
        self._count_var = tk.StringVar(value="Catches: 0")

        tk.Label(self.win, textvariable=self._state_var,
                 bg="#1a1a1a", fg="#00FF41",
                 font=("Courier New", 10, "bold")).pack(pady=(6, 0))
        tk.Label(self.win, textvariable=self._count_var,
                 bg="#1a1a1a", fg="#FFFFFF",
                 font=("Courier New", 9)).pack()

        # Buttons
        btn_frame = tk.Frame(self.win, bg="#1a1a1a")
        btn_frame.pack(fill="x", padx=4, pady=4)

        self._toggle_btn = tk.Button(
            btn_frame, text="▶ Start", bg="#2a5a2a", fg="white",
            font=("Courier New", 9), command=self._on_toggle)
        self._toggle_btn.pack(fill="x", pady=1)

        tk.Button(btn_frame, text="✏ Edit Regions", bg="#333355", fg="white",
                  font=("Courier New", 9), command=self._on_edit_regions
                  ).pack(fill="x", pady=1)

        tk.Button(btn_frame, text="✕ Quit", bg="#5a2a2a", fg="white",
                  font=("Courier New", 9), command=self._on_quit
                  ).pack(fill="x", pady=1)

        self._update()

    def _on_toggle(self):
        global fishing_active
        fishing_active = not fishing_active
        if fishing_active:
            if not _stats["start"]:
                _stats["start"] = time.time()
            ov("bot_state", "FISHING")
            log("[BOT] ▶ Fishing STARTED ✅")
        else:
            ov("bot_state", "STOPPED")
            log("[BOT] ⏹ Fishing STOPPED ⛔")
            threading.Thread(target=_save_snaps, daemon=True).start()
            print_summary()

    def _on_edit_regions(self):
        global fishing_active
        was_active = fishing_active
        fishing_active = False

        def restore():
            global fishing_active
            fishing_active = was_active

        editor = RegionEditor(on_close=restore)
        editor.root.wait_window()

    def _on_quit(self):
        global fishing_active, running
        fishing_active = False
        running = False
        log("[BOT] Quitting...")
        print_summary()

    def _update(self):
        self._state_var.set(_ov.get("bot_state", "IDLE"))
        self._count_var.set(f"Catches: {_ov.get('fish_count', 0)}")
        btn_text = "⏹ Stop" if fishing_active else "▶ Start"
        self._toggle_btn.config(text=btn_text)
        self.win.after(300, self._update)


_overlay:     Optional[DebugOverlay] = None
_overlay_vis: bool = True

def _launch_overlay():
    global _overlay
    _overlay = DebugOverlay()
    _control_panel = ControlPanel(_overlay.root)
    _overlay.run()

def toggle_overlay():
    global _overlay_vis
    if _overlay is None: return
    _overlay_vis = not _overlay_vis
    try:
        _overlay.show() if _overlay_vis else _overlay.hide()
    except: pass

# ══════════════════════════════════════════════════════════════════════════════
#  FISHING LOOP
# ══════════════════════════════════════════════════════════════════════════════

def fishing_loop():
    global running
    log("[FISH] Loop started. Press F6 to begin.")

    while running:
        try:
            if not fishing_active:
                time.sleep(0.05)
                continue

            log("[FISH] ── New fishing cycle ──")

            # BAIT
            ov("bot_state", "BAITING")
            send_key(BAIT_KEY)
            time.sleep(BAIT_KEY_DELAY)
            click("apply bait")
            _stats["baits"] += 1
            time.sleep(BAIT_APPLY_DELAY)
            if not fishing_active: continue

            # EQUIP ROD
            ov("bot_state", "EQUIP ROD")
            send_key(ROD_KEY)
            time.sleep(ROD_KEY_DELAY)
            if not fishing_active: continue

            # CAST
            ov("bot_state", "CASTING")
            click("cast")
            _stats["casts"] += 1
            if not fishing_active: continue

            # WATCH BOBBER
            ov("bot_state", "WATCHING")
            ov("bobber_count", 0); ov("bubble_count", 0); ov("bobber_state", "idle")
            bite = watch_bobber()
            if not fishing_active: continue

            if not bite:
                _stats["bite_timeouts"] += 1
                log("[FISH] Timeout — recasting")
                continue

            # REEL
            ov("bot_state", "REELING")
            click("reel in")
            time.sleep(0.35)
            set_cursor_pos(*WATER_CURSOR_POS)
            if not fishing_active: continue

            # SKILL CHECK
            ov("bot_state", "SKILL CHECK")
            ov("skill_letter", "")
            run_skill_check_window(SKILL_CHECK_WINDOW)
            if not fishing_active: continue

            # CATCH
            ov("bot_state", "READING CATCH")
            catch = read_catch()
            if catch is None:
                _stats["false_reels"] += 1
                log("[FISH] ⚠ False reel (no catch notification seen)")
                ov("catch_text", "— false reel —")
            else:
                _record_catch(catch)

            # PAUSE
            ov("bot_state", "WAITING")
            log("[FISH] Cycle done")
            time.sleep(BETWEEN_CAST_DELAY)

        except Exception as e:
            log(f"[FISH] ⚠ Error: {e}")
            time.sleep(1)

    log("[FISH] Loop stopped.")

# ══════════════════════════════════════════════════════════════════════════════
#  SNAPSHOTS
# ══════════════════════════════════════════════════════════════════════════════

def _save_snaps():
    try:
        with mss.mss() as sct:
            for region, name in [
                (SKILL_CHECK_REGION, "snap_skill.png"),
                (BOBBER_REGION,      "snap_bobber.png"),
                (BUBBLE_REGION,      "snap_bubble.png"),
                (CATCH_REGION,       "snap_catch.png"),
            ]:
                _grab_rgb(sct, region).save(os.path.join(BASE_DIR, name))
                log(f"  📸 {name}")
            skill_img = _grab_rgb(sct, SKILL_CHECK_REGION)
            _preprocess_skill(skill_img, invert=False).save(
                os.path.join(BASE_DIR, "snap_skill_processed.png"))
            _preprocess_skill(skill_img, invert=True).save(
                os.path.join(BASE_DIR, "snap_skill_processed_inverted.png"))
            log("  📸 snap_skill_processed*.png")
    except Exception as e:
        log(f"  ⚠ Snap failed: {e}")

# ══════════════════════════════════════════════════════════════════════════════
#  HOTKEYS
# ══════════════════════════════════════════════════════════════════════════════

def on_press(key):
    global fishing_active, running

    if key == Key.f7:
        toggle_overlay()
        return

    if key == HOTKEY_TOGGLE:
        fishing_active = not fishing_active
        if fishing_active:
            if not _stats["start"]:
                _stats["start"] = time.time()
            ov("bot_state", "FISHING")
            log("[BOT] ▶ Fishing STARTED ✅")
        else:
            ov("bot_state", "STOPPED")
            log("[BOT] ⏹ Fishing STOPPED ⛔")
            threading.Thread(target=_save_snaps, daemon=True).start()
            print_summary()

    elif key == HOTKEY_QUIT:
        fishing_active = False
        running        = False
        log("[BOT] Quitting...")
        print_summary()
        return False

# ═══════════════════════════════════��══════════════════════════════════════════
#  REGION FINDER
# ══════════════════════════════════════════════════════════════════════════════

def find_region_helper():
    try:
        import pyautogui
    except ImportError:
        print("pip install pyautogui"); return
    print("\n── Region Finder ─────────────────────────────────────")
    print("Hover over key screen positions. Ctrl+C to exit.\n")
    try:
        while True:
            x, y = pyautogui.position()
            print(f"  x={x:4d}  y={y:4d}", end="\r")
            time.sleep(0.05)
    except KeyboardInterrupt:
        print('\n\nFormat: {"left": x, "top": y, "width": w, "height": h}')

# ══════════════════════════════════════════════════════════════════════════════
#  ENTRY POINT
# ══════════════════════════════════════════════════════════════════════════════

def main():
    global DEBUG_VERBOSE

    parser = argparse.ArgumentParser(description="Autofish Bot v5")
    parser.add_argument("--find-region", action="store_true")
    parser.add_argument("--edit-regions", action="store_true",
                        help="Open the region editor GUI instead of fishing")
    parser.add_argument("--debug", action="store_true",
                        help="Log bobber/bubble pixel counts every frame")
    args = parser.parse_args()

    # Load config first so logged values reflect any overrides
    load_config()

    if args.find_region:
        find_region_helper()
        return

    if args.edit_regions:
        editor = RegionEditor()
        editor.run()
        return

    DEBUG_VERBOSE = args.debug

    _init_tesseract()

    def _prewarm():
        time.sleep(0.5)
        try:
            pytesseract.image_to_string(
                Image.new("L", (40, 40), 255),
                config=f"--psm 10 -c tessedit_char_whitelist={''.join(sorted(TARGET_CHARS))}"
            )
            log("[INIT] Tesseract pre-warmed ✅")
        except: pass
    threading.Thread(target=_prewarm, daemon=True).start()

    init_log()

    print("╔══════════════════════════════════════════════╗")
    print("║   AUTOFISH BOT v5  🎣  (bubble+catch fix)   ║")
    print("╠══════════════════════════════════════════════╣")
    print(f"║  Bait key       : {BAIT_KEY:<25} ║")
    print(f"║  Rod key        : {ROD_KEY:<25} ║")
    print(f"║  Skill chars    : {', '.join(sorted(TARGET_CHARS)):<25} ║")
    print(f"║  Skill window   : {SKILL_CHECK_WINDOW:.1f}s{'':<21} ║")
    print(f"║  Letter cooldown: {SKILL_SAME_LETTER_COOLDOWN*1000:.0f}ms{'':<21} ║")
    print(f"║  Bubble confirm : {BUBBLE_CONFIRM_SECS}s{'':<22} ║")
    print(f"║  Bubble streak  : {BUBBLE_PHASE1_REQUIRED} frames{'':<17} ║")
    print( "╠══════════════════════════════════════════════╣")
    print( "║  F6=Start/Stop  F7=Overlay  F8=Quit         ║")
    print("╚══════════════════════════════════════════════╝\n")
    print("  ⚠  Position cursor over water BEFORE pressing F6.\n")

    threading.Thread(target=_launch_overlay, daemon=True).start()
    threading.Thread(target=fishing_loop,    daemon=True).start()

    with kb.Listener(on_press=on_press) as listener:
        listener.join()

    log("[BOT] Goodbye!")
    if _log_file: _log_file.close()


if __name__ == "__main__":
    main()
