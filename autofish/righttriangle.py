# -*- coding: utf-8 -*-
"""
Autofish Bot — Roblox Western Edition  (v4 — false reel tracking + catch gate)
================================================================================
Requirements:
    pip install mss pillow pytesseract pynput numpy

Tesseract OCR: https://github.com/UB-Mannheim/tesseract/wiki

Controls:
    F6  — Start / Stop fishing
    F7  — Toggle debug overlay
    F8  — Quit

Fixes vs v2:
  • Skill OCR: Otsu binarisation instead of percentile threshold
  • Skill OCR: fast-exit on first hit (psm=10 first, fallbacks only if needed)
  • Skill window: widened to 5s; each frame uses only the cheapest strategy first
  • Same-letter repeat: timer-based cooldown instead of brittle pixel-diff
  • Catch OCR: Otsu + relaxed green/yellow predicates + full-width scan
  • Bubble: baseline update smoothed to avoid false positives from wave spikes
"""

import os, sys, time, threading, argparse, ctypes, shutil, re
from typing import Optional

import numpy as np
import mss
import pytesseract
import tkinter as tk
from PIL import Image, ImageFilter, ImageEnhance, ImageStat
from pynput import keyboard as kb
from pynput.keyboard import Key

# ══════════════════════════════════════════════════════════════════════════════
#  TESSERACT
# ══════════════════════════════════════════════════════════════════════════════

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
CATCH_REGION       = {"left": 1050, "top": 275,  "width": 400, "height": 30}
BUBBLE_REGION      = {"left": 650,  "top": 300,  "width": 440, "height": 360}
WATER_CURSOR_POS   = (870, 470)

# ── Red bobber pixels — brightness-interpolated thresholds ───────────────────
# Each tuple is (brightness, r_min, g_max, b_max).
# Values between anchors are linearly interpolated from the live scene brightness.
#   bright scene : R>180, G<80,  B<60   (vivid red against bright water/sky)
#   dark scene   : R>70,  G<150, B<140  (dim red; background is dark too)
_BOBBER_BRT_ANCHORS  = (  0, 100, 255)
_BOBBER_RMIN_ANCHORS = ( 70, 130, 180)
_BOBBER_GMAX_ANCHORS = (150, 120,  80)
_BOBBER_BMAX_ANCHORS = (140, 110,  60)

# ── Bubble detection — brightness-interpolated thresholds ─────────────────────
# Each tuple is a brightness anchor followed by the corresponding parameter.
# Parameters are linearly interpolated from the live scene brightness so the
# bot adjusts smoothly as the in-game time of day changes.
#   deep night (0–50) : very relaxed — bubbles are barely visible
#   night (65)        : relaxed
#   dusk (65)         : balanced
#   day (110–255)     : strict — avoid false positives in bright, noisy water
_BUBBLE_BRT_ANCHORS  = (  0,  50,  65, 110, 255)
_BUBBLE_GMIN_ANCHORS = ( 15,  20,  75, 135, 135)
_BUBBLE_BMIN_ANCHORS = ( 18,  25,  95, 150, 150)
_BUBBLE_EXCS_ANCHORS = (  3,   5,  30,  75,  75)
_BUBBLE_NMIN_ANCHORS = ( 30,  50, 200, 200, 200)  # net-pixel minimum to confirm bubbles

BUBBLE_GONE_THRESH    = 0.15
BUBBLE_CONFIRM_SECS   = 0.55
BUBBLE_MIN_BASELINE   = 2
BUBBLE_PHASE1_REQUIRED = 12   # consecutive above-net-min frames required to confirm

# ── Skill check ───────────────────────────────────────────────────────────────
TARGET_CHARS  = {"T", "F", "G", "R"}
MISREAD_MAP   = {"P": "R", "B": "R"}          # common OCR mistakes for R

# After pressing a letter, ignore the same letter for this many seconds.
# This prevents double-pressing a sustained prompt without blocking a genuinely
# new prompt that happens to show the same letter.
SKILL_SAME_LETTER_COOLDOWN = 0.18

# ── Timing ────────────────────────────────────────────────────────────────────
BAIT_KEY_DELAY     = 0.10
BAIT_APPLY_DELAY   = 0.50
ROD_KEY_DELAY      = 0.30
CAST_SETTLE_TIME   = 1.50
BITE_TIMEOUT       = 90.0
SKILL_CHECK_WINDOW = 5.00   # widened: each OCR pass ≈ 80ms fast-path
CATCH_READ_WINDOW  = 4.00
BETWEEN_CAST_DELAY = 0.05

HOTKEY_TOGGLE = Key.f6
HOTKEY_QUIT   = Key.f8

BASE_DIR  = r"C:\Users\austi\Downloads\autofish"
LOG_PATH  = BASE_DIR + r"\autofish.log"

DEBUG_VERBOSE = False

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
    log("=== Autofish Bot v3 started ===")
    log(f"BOBBER_REGION       : {BOBBER_REGION}")
    log(f"BUBBLE_REGION       : {BUBBLE_REGION}")
    log(f"CATCH_REGION        : {CATCH_REGION}")
    log(f"SKILL_CHECK_WINDOW  : {SKILL_CHECK_WINDOW}s")
    log(f"TARGET_CHARS        : {sorted(TARGET_CHARS)}")

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
    Bubbles are distinctly cyan (high G+B, lower R) compared to
    the dark grey-green water.  Using (G+B-2R) as a "cyan excess"
    metric separates bubbles from neutral grey pixels where R≈G≈B.
    This is robust across day/night lighting changes.

    Rain rejection: scaled by brightness.
      - Day/dusk (brightness >= 65): require R*2 < G and R*2 < B.
      - Night (65 > brightness >= 50): use relaxed R*3 < G*2 and R*3 < B*2.
      - Deep night (brightness < 50): skip rain rejection (rain invisible and
        bubbles too dim to survive any ratio filter).
    """
    w, h = img.size
    if w > 8 and h > 8:
        img = img.crop((4, 4, w - 4, h - 4))
    arr = np.array(img, dtype=np.int32)
    R, G, B = arr[:,:,0], arr[:,:,1], arr[:,:,2]
    cyan_excess = G + B - 2 * R
    if brightness >= 65:
        rain_mask = (R * 2 < G) & (R * 2 < B)
    elif brightness >= 50:
        rain_mask = (R * 3 < G * 2) & (R * 3 < B * 2)
    else:
        rain_mask = np.ones(R.shape, dtype=bool)
    mask = (G > min_g) & (B > min_b) & (cyan_excess > min_excess) & rain_mask
    return int(np.sum(mask))

# ══════════════════════════════════════════════════════════════════════════════
#  OVERLAY STATE
# ══════════════════════════════════════════════════════════════════════════════

_ov = {
    "bobber_count": 0, "bubble_count": 0, "bobber_state": "idle",
    "skill_brt": 0.0, "skill_letter": "", "catch_text": "",
    "bot_state": "IDLE", "fish_count": 0,
}
_recent_logs = []
def ov(key, val): _ov[key] = val

# ══════════════════════════════════════════════════════════════════════════════
#  BOBBER DETECTION
# ══════════════════════════════════════════════════════════════════════════════

def watch_bobber() -> bool:
    log(f"  🎣 Settling {CAST_SETTLE_TIME}s...")
    time.sleep(CAST_SETTLE_TIME)

    deadline = time.time() + BITE_TIMEOUT
    frame_n  = 0

    # ── Phase 1: wait for bubbles ─────────────────────────────────────────────
    ov("bobber_state", "waiting for bubbles")
    with mss.mss() as sct:
        bg_img = _grab_rgb(sct, BUBBLE_REGION)
        brt = _brightness(bg_img)
        g_min, b_min, cyan_excess, net_min = _get_bubble_params(brt)
        # Measure ambient background count before any bubbles could appear.
        # bg_img is held in memory so bg_count can be recomputed with the
        # current (brightness-interpolated) thresholds on every frame, keeping
        # the net count consistent as lighting changes throughout the session.
        bg_count = _count_bubble_pixels(bg_img, g_min, b_min, cyan_excess, brt)
        log(f"  🫧 Phase 1: waiting for bubbles (brightness={brt:.1f} g_min={g_min} b_min={b_min} excess={cyan_excess} net_min={net_min} bg={bg_count})")

        consecutive = 0
        history     = []   # stores *net* counts

        while time.time() < deadline:
            if not fishing_active:
                return False
            bub_img = _grab_rgb(sct, BUBBLE_REGION)
            brt = _brightness(bub_img)
            g_min, b_min, cyan_excess, net_min = _get_bubble_params(brt)
            bg_count  = _count_bubble_pixels(bg_img, g_min, b_min, cyan_excess, brt)
            bub_count = _count_bubble_pixels(bub_img, g_min, b_min, cyan_excess, brt)
            net_count = max(0, bub_count - bg_count)
            red_count = _count_bobber_pixels(_grab_rgb(sct, BOBBER_REGION), brt)
            frame_n  += 1
            ov("bubble_count", net_count)
            ov("bobber_count", red_count)

            if DEBUG_VERBOSE or frame_n % 30 == 0:
                log(f"  🫧 Phase1 brt={brt:.1f} net={net_count} red={red_count} streak={consecutive}/{BUBBLE_PHASE1_REQUIRED}")

            if net_count >= net_min:
                consecutive += 1
                history.append(net_count)
            else:
                consecutive = 0
                history.clear()

            if consecutive >= BUBBLE_PHASE1_REQUIRED:
                net_baseline = max(history)
                log(f"  ✅ Bubbles confirmed! net_baseline={net_baseline} bg={bg_count}")
                break
            time.sleep(0.016)
        else:
            log(f"  ⏱ Never saw bubbles — timeout")
            return False

    # ── Phase 2: watch for bubble loss ───────────────────────────────────────
    # All thresholds are relative to net_baseline (pixels *above* background)
    # so the persistent background noise floor never triggers a false bite.
    gone_net   = max(int(net_baseline * BUBBLE_GONE_THRESH), max(2, net_baseline // 5))
    gone_since = None
    ov("bobber_state", "watching")
    log(f"  🫧 Phase 2: watching (net gone < {gone_net}, bg={bg_count})")

    with mss.mss() as sct:
        while time.time() < deadline:
            if not fishing_active:
                return False
            bub_img = _grab_rgb(sct, BUBBLE_REGION)
            brt = _brightness(bub_img)
            g_min, b_min, cyan_excess, _ = _get_bubble_params(brt)
            bg_count  = _count_bubble_pixels(bg_img, g_min, b_min, cyan_excess, brt)
            bub_count = _count_bubble_pixels(bub_img, g_min, b_min, cyan_excess, brt)
            net_count = max(0, bub_count - bg_count)
            red_count = _count_bobber_pixels(_grab_rgb(sct, BOBBER_REGION), brt)
            frame_n  += 1
            ov("bubble_count", net_count)
            ov("bobber_count", red_count)

            if DEBUG_VERBOSE or frame_n % 30 == 0:
                gs = f"{time.time()-gone_since:.2f}s" if gone_since else "no"
                log(f"  🫧 net={net_count}/{net_baseline} gone_timer={gs}")

            if net_count < gone_net:
                if gone_since is None:
                    gone_since = time.time()
                    ov("bobber_state", "no bubbles")
                    log(f"  👀 Bubbles vanished (net {net_count} < {gone_net})")
                elif time.time() - gone_since >= BUBBLE_CONFIRM_SECS:
                    log(f"  🐟 BITE! Gone for {time.time()-gone_since:.2f}s")
                    ov("bobber_state", "bite")
                    return True
            else:
                if gone_since is not None:
                    log(f"  ↩ Bubbles returned after {time.time()-gone_since:.2f}s")
                gone_since = None
                ov("bobber_state", "watching")
            time.sleep(0.016)

    log(f"  ⏱ No bite after {BITE_TIMEOUT}s")
    return False

# ══════════════════════════════════════════════════════════════════════════════
#  SKILL CHECK OCR
# ══════════════════════════════════════════════════════════════════════════════

def _otsu_threshold(arr: np.ndarray) -> int:
    """
    Compute Otsu's optimal binarisation threshold on a uint8 grayscale array.

    Otsu's method finds the threshold that minimises intra-class variance
    (equivalently maximises inter-class variance) across the two pixel classes
    (foreground letter vs background).  It adapts automatically to any
    brightness level, which is why it outperforms a fixed midpoint or even
    a percentile-based threshold for game UI text.

    Returns an integer threshold in [0, 255].
    """
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
    """
    Prepare a skill-check crop for Tesseract.

    Uses Otsu's method for binarisation — far more robust than the previous
    percentile midpoint approach, especially when the circle background shifts
    between frames (e.g. different fish animations, day/night).

    invert=False → black letter on white background (Tesseract standard).
    invert=True  → white letter on black (catches the opposite polarity).
    """
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

    # Black letter on white — Tesseract expects dark text on light background
    if not invert:
        binarised = np.where(arr < t, 0, 255).astype(np.uint8)
    else:
        binarised = np.where(arr < t, 255, 0).astype(np.uint8)

    img = Image.fromarray(binarised, mode="L")
    # Light morphological cleanup to close small holes in strokes
    img = img.filter(ImageFilter.MaxFilter(3)).filter(ImageFilter.MinFilter(3))
    padded = Image.new("L", (img.width + 60, img.height + 60), 255)
    padded.paste(img, (30, 30))
    return padded


# ── OCR strategy table ────────────────────────────────────────────────────────
# Ordered from fastest/most reliable to slower fallback.
# We return immediately on the first valid target character.
_SKILL_STRATEGIES = [
    (False, 10),   # normal polarity + single-char mode
    (True,  10),   # inverted + single-char
    (False,  8),   # normal + word mode
    (True,   8),   # inverted + word
]

def _detect_skill_letter(img: Image.Image) -> Optional[str]:
    """
    Run OCR strategies in order and return the first valid character.
    This keeps skill detection as fast as possible.
    """
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
    """
    Watch SKILL_CHECK_REGION for `duration` seconds.

    Same-letter repeat handling (v3):
      After pressing a letter, start a per-letter cooldown timer.
      The same letter is pressed again only if the cooldown has expired.
      This correctly handles:
        • Sustained same-letter prompt (e.g. T still on screen) → ignored
        • New prompt after cooldown → pressed immediately even if same letter
      The old pixel-diff approach was unreliable because the processed image
      of a new "T" prompt looks almost identical to the previous "T" prompt.
    """
    deadline       = time.time() + duration
    last_pressed   = {}    # char → timestamp of last press
    total_pressed  = 0

    log(f"  🎮 Skill window open ({duration:.2f}s)")

    with mss.mss() as sct:
        while time.time() < deadline:
            if not fishing_active:
                return

            img = _grab_rgb(sct, SKILL_CHECK_REGION)
            brt = _brightness(img)
            ov("skill_brt", brt)

            # Fast brightness gate: skip OCR on dark empty frames (~1ms)
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
                    # Brief pause to let the game register the keypress
                    # before the next OCR scan
                    time.sleep(0.06)
                else:
                    log(f"  ⏭ [{letter}] cooldown ({age:.2f}s < {SKILL_SAME_LETTER_COOLDOWN}s)")

            time.sleep(0.008)

    log(f"  🎮 Skill window closed ({total_pressed} presses)")

# ══════════════════════════════════════════════════════════════════════════════
#  CATCH OCR
# ══════════════════════════════════════════════════════════════════════════════
#
#  v4 design:
#
#  GATE FIRST, OCR SECOND.
#  Before calling Tesseract at all, we count how many colored pixels match
#  the notification palette (green or yellow text).  If that count is below
#  CATCH_MIN_COLORED_PIXELS the region contains no notification — we skip
#  OCR entirely and eventually return None (→ false reel).
#
#  Why this fixes the garbage reads:
#  "Seewiege 0 get a SR" / "er ees te Bee BR ae a" came from _otsu_ocr
#  running on a blank game background and hallucinating text from water
#  ripples / UI chrome.  The gate prevents OCR from ever running on empty
#  frames, so those strings can never appear.
#
#  Why read_catch() now returns Optional[str]:
#  None  → no notification pixels seen in the entire window → FALSE REEL
#  str   → notification was visible; str is the best name extracted
#          (may still be "Unknown" if OCR saw pixels but couldn't parse them)

# Minimum number of colored pixels required before OCR is attempted.
# Tune upward if you still get false positives; tune down if real catches
# are being missed (run --debug and watch "catch gate" log lines).
CATCH_MIN_COLORED_PIXELS = 18

_CATCH_PATTERNS = [
    r"caught\s+an?\s+(.+?)(?:\s*[!.]|$)",
    r"reeled\s+in\s+an?\s+(.+?)(?:\s*[!.]|$)",
    r"found\s+an?\s+(.+?)(?:\s*[!.]|$)",
    r"you\s+got\s+an?\s+(.+?)(?:\s*[!.]|$)",
    r"obtained\s+an?\s+(.+?)(?:\s*[!.]|$)",
]

# Characters that are never part of a real fish/item name.
# If >30 % of a result is junk characters, discard it.
_JUNK_RE  = re.compile(r"[^A-Za-z0-9 '\-]")
_SPACE_RE = re.compile(r"\s+")


def _is_plausible(text: str) -> bool:
    """
    Return True if text looks like it could be a real catch name.
    Rejects: too short, too many symbols, suspiciously long word runs.
    """
    text = text.strip()
    if len(text) < 3:
        return False
    junk_ratio = len(_JUNK_RE.findall(text)) / max(len(text), 1)
    if junk_ratio > 0.25:
        return False
    # At least one word must be ≥ 2 real alpha chars
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
    # No pattern matched — return cleaned raw if it looks plausible
    cleaned = _JUNK_RE.sub("", raw).strip()
    return cleaned[:40] if _is_plausible(cleaned) else "Unknown"


def _count_catch_pixels(img: Image.Image) -> tuple[int, int, int]:
    """
    Return (green_px, cyan_px, yellow_px) counts in the catch region.
    Used as a gate: if all are near zero, there is no notification.
    """
    arr = np.array(img)
    R = arr[:,:,0].astype(np.int32)
    G = arr[:,:,1].astype(np.int32)
    B = arr[:,:,2].astype(np.int32)
    green  = int(np.sum((G > 110) & (G > R + 20) & (G > B + 15) & (G > 125)))
    cyan   = int(np.sum((G > 120) & (B > 100) & (G > R + 20) & (B > R + 15)))
    yellow = int(np.sum((R > 160) & (G > 150) & (B < 120) & (R > B + 35) & (G > B + 25)))
    return green, cyan, yellow


def _colour_mask_ocr(img: Image.Image, label: str, predicate) -> str:
    """
    Extract text matching a colour predicate.
    Only called after the gate confirms colored pixels are present.
    """
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
    im  = im.filter(ImageFilter.MaxFilter(3)).filter(ImageFilter.MinFilter(3))
    pad = Image.new("L", (im.width + 20, im.height + 20), 255)
    pad.paste(im, (10, 10))
    try:
        text = pytesseract.image_to_string(pad, config="--psm 6 --oem 3").strip()
        if text:
            log(f"  🐠 {label} raw: '{text}'")
        return text
    except Exception:
        return ""


def _otsu_ocr(img: Image.Image) -> str:
    """
    Otsu-binarise the grayscale crop, try both polarities, return best
    plausible result.  Crops 10px border to remove UI chrome first.
    Only called after the gate confirms colored pixels are present.
    """
    w, h = img.size
    if w > 20 and h > 20:
        img = img.crop((10, 4, w - 10, h - 4))
    gray = img.convert("L")
    arr  = np.array(gray, dtype=np.uint8)
    t    = _otsu_threshold(arr)
    best = ""
    for invert in (False, True):
        bw = np.where(arr < t, 0, 255).astype(np.uint8) if not invert \
             else np.where(arr < t, 255, 0).astype(np.uint8)
        im  = Image.fromarray(bw, mode="L")
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
    """
    Poll CATCH_REGION for up to CATCH_READ_WINDOW seconds.

    Returns:
      None  — no notification pixels seen at all → caller records a false reel.
      str   — best extracted catch name (may be "Unknown" if pixels were seen
              but OCR could not produce a plausible result).
    """
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
    ever_saw_pixels = False   # True once the gate fires at least once

    with mss.mss() as sct:
        while time.time() < deadline:
            img = _grab_rgb(sct, CATCH_REGION)
            green_px, cyan_px, yellow_px = _count_catch_pixels(img)
            total_colored = green_px + cyan_px + yellow_px

            if DEBUG_VERBOSE:
                log(f"  🐠 Catch gate: green={green_px} cyan={cyan_px} yellow={yellow_px}")

            # ── Gate: skip OCR when no notification is visible ────────────────
            if total_colored < CATCH_MIN_COLORED_PIXELS:
                if ever_saw_pixels:
                    log(f"  🐠 Catch pixels gone — stopping early")
                    break
                time.sleep(0.08)
                continue

            ever_saw_pixels = True
            log(f"  🐠 Catch gate passed (green={green_px} cyan={cyan_px} yellow={yellow_px}) — running OCR")

            green  = _colour_mask_ocr(img, "Green",  green_pred)
            cyan   = _colour_mask_ocr(img, "Cyan",   cyan_pred)
            yellow = _colour_mask_ocr(img, "Yellow", yellow_pred)
            raw    = _otsu_ocr(img)

            if _is_plausible(green)  and len(green)  > len(best_green):  best_green  = green
            if _is_plausible(cyan)   and len(cyan)   > len(best_cyan):   best_cyan   = cyan
            if _is_plausible(yellow) and len(yellow) > len(best_yellow): best_yellow = yellow
            if _is_plausible(raw)    and len(raw)    > len(best_raw):    best_raw    = raw

            # Stop as soon as we have a solid green/cyan result
            if (best_green or best_cyan) and len(best_green or best_cyan) >= 4:
                break
            time.sleep(0.12)

    # ── Gate never fired: no notification was visible → false reel ────────────
    if not ever_saw_pixels:
        log("  🐠 Catch: no colored pixels seen → FALSE REEL")
        return None

    # ── Build final catch name ────────────────────────────────────────────────
    catch_name = best_green or best_cyan or best_raw or best_yellow
    
    # If color extraction failed but gate passed, use Otsu fallback
    if not catch_name and raw:
        catch_name = raw
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
    C = {"skill": "#00FF41", "bobber": "#FF6B35", "catch": "#00D4FF"}

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
        self._box(c, CATCH_REGION,       self.C["catch"],
                  f"CATCH  {s['catch_text'] or '—'}")
        hud = ["🎣 AUTOFISH v3  [F7=hide]",
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


_overlay:     Optional[DebugOverlay] = None
_overlay_vis: bool = True

def _launch_overlay():
    global _overlay
    _overlay = DebugOverlay()
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
                # No notification pixels appeared — the reel produced nothing
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

# ══════════════════════════════════════════════════════════════════════════════
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

    parser = argparse.ArgumentParser(description="Autofish Bot v3")
    parser.add_argument("--find-region", action="store_true")
    parser.add_argument("--debug", action="store_true",
                        help="Log bobber/bubble pixel counts every 30 frames")
    args = parser.parse_args()

    if args.find_region:
        find_region_helper()
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
    print("║   AUTOFISH BOT v4  🎣  (gated catch OCR)    ║")
    print("╠══════════════════════════════════════════════╣")
    print(f"║  Bait key       : {BAIT_KEY:<25} ║")
    print(f"║  Rod key        : {ROD_KEY:<25} ║")
    print(f"║  Skill chars    : {', '.join(sorted(TARGET_CHARS)):<25} ║")
    print(f"║  Skill window   : {SKILL_CHECK_WINDOW:.1f}s{'':<21} ║")
    print(f"║  Letter cooldown: {SKILL_SAME_LETTER_COOLDOWN*1000:.0f}ms{'':<21} ║")
    print(f"║  Bubble confirm : {BUBBLE_CONFIRM_SECS}s{'':<22} ║")
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