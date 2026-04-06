"""
Skill Check Bot — Roblox Edition
=================================
Requirements:
    pip install mss pillow pytesseract pynput
 
Tesseract: https://github.com/UB-Mannheim/tesseract/wiki
 
Controls:
    F6 — toggle ON/OFF  (also saves raw + processed snapshots for crop tuning)
    F8 — quit
 
Logs are written to skill_check_boy.log (cleared on each run).
"""
 
import os
import sys
import time
import threading
import argparse
import ctypes
import shutil
from typing import Optional
 
import mss
import pytesseract
from PIL import Image, ImageFilter, ImageEnhance, ImageStat
from pynput import keyboard as kb
from pynput.keyboard import Key
 
# ──────────────────────────────────────────────────────────────────────────────
#  TESSERACT AUTO-DETECTION
# ──────────────────────────────────────────────────────────────────────────────
 
TESSERACT_PATH = None   # Set to r"C:\...\tesseract.exe" to force a specific path
 
_TESSERACT_SEARCH_PATHS = [
    r"C:\Program Files\Tesseract-OCR\tesseract.exe",
    r"C:\Program Files (x86)\Tesseract-OCR\tesseract.exe",
    r"C:\Users\{user}\AppData\Local\Tesseract-OCR\tesseract.exe",
    r"C:\tools\tesseract\tesseract.exe",
]
 
def _find_tesseract() -> Optional[str]:
    if TESSERACT_PATH:
        return TESSERACT_PATH if os.path.isfile(TESSERACT_PATH) else None
    found = shutil.which("tesseract")
    if found:
        return found
    username = os.environ.get("USERNAME", "")
    for path in _TESSERACT_SEARCH_PATHS:
        expanded = path.replace("{user}", username)
        if os.path.isfile(expanded):
            return expanded
    return None
 
def _init_tesseract():
    path = _find_tesseract()
    if path is None:
        print("\n" + "═" * 56)
        print("  ❌  Tesseract not found!")
        print("═" * 56)
        print("  Download and install it from:")
        print("  https://github.com/UB-Mannheim/tesseract/wiki")
        print()
        print("  After installing, either:")
        print("  • Re-run — the script will find it automatically, OR")
        print("  • Set TESSERACT_PATH at the top of this script")
        print("═" * 56 + "\n")
        sys.exit(1)
    pytesseract.pytesseract.tesseract_cmd = path
    print(f"[INIT] Tesseract found: {path}")
 
# ──────────────────────────────────────────────────────────────────────────────
#  CONFIGURATION
# ──────────────────────────────────────────────────────────────────────────────
 
REGION        = {"left": 1240, "top": 678, "width": 80, "height": 90}
TARGET_CHARS  = {"T", "F", "G", "R"}
POLL_INTERVAL = 0.016   # ~60 fps
 
# How long to ignore detections after a keypress. Prevents double-pressing
# while the circle is fading, and resets cleanly for same-letter repeats.
PRESS_COOLDOWN = 0.005
 
# ── Pixel gate ──────────────────────────────────────────────────────────────
# Before running Tesseract, the bot does a fast pixel brightness check.
# The skill-check circle is significantly brighter than the empty background,
# so we measure the mean brightness of the capture region (0–255).
# If it's below ACTIVITY_THRESHOLD, we skip OCR entirely — no Tesseract call,
# no preprocessing, just a bare frame grab and a single stat calculation.
# This makes idle frames take ~1ms instead of ~180ms, so the bot is polling
# at close to true 60fps and reacts the instant the circle appears.
#
# How to tune: run with --debug and watch "gate=XX" in the log.
#   - Empty screen (no circle): gate value should be LOW  (e.g. 20–50)
#   - Circle visible:           gate value should be HIGH (e.g. 80–150)
# Set ACTIVITY_THRESHOLD to a value between those two ranges.
ACTIVITY_THRESHOLD = 60
 
HOTKEY_TOGGLE = Key.f6
HOTKEY_QUIT   = Key.f8
 
LOG_PATH            = r"C:\Users\austi\Downloads\autofish\skill_check_boy.log"
RAW_SNAP_PATH       = r"C:\Users\austi\Downloads\autofish\snap_raw.png"
PROCESSED_SNAP_PATH = r"C:\Users\austi\Downloads\autofish\snap_processed.png"
 
DEBUG_SAVE_FRAMES = False
 
# ──────────────────────────────────────────────────────────────────────────────
#  LOGGING
# ──────────────────────────────────────────────────────────────────────────────
 
_log_file = None
 
def log(msg: str):
    ts   = time.strftime("%H:%M:%S.") + f"{int(time.time() * 1000) % 1000:03d}"
    line = f"[{ts}] {msg}"
    print(line)
    if _log_file:
        _log_file.write(line + "\n")
        _log_file.flush()
 
def init_log():
    global _log_file
    _log_file = open(LOG_PATH, "w", encoding="utf-8")
    log("=== Skill Check Bot started ===")
    log(f"REGION            : {REGION}")
    log(f"TARGET_CHARS      : {sorted(TARGET_CHARS)}")
    log(f"PRESS_COOLDOWN    : {PRESS_COOLDOWN}s")
    log(f"ACTIVITY_THRESHOLD: {ACTIVITY_THRESHOLD}")
 
# ──────────────────────────────────────────────────────────────────────────────
#  STATE
# ──────────────────────────────────────────────────────────────────────────────
 
bot_active = False
running    = True
 
# ──────────────────────────────────────────────────────────────────────────────
#  KEYPRESS — keybd_event with scan codes
# ──────────────────────────────────────────────────────────────────────────────
 
KEYEVENTF_SCANCODE = 0x0008
KEYEVENTF_KEYUP    = 0x0002
 
SCAN_CODES = {
    "A": 0x1E, "B": 0x30, "C": 0x2E, "D": 0x20, "E": 0x12,
    "F": 0x21, "G": 0x22, "H": 0x23, "I": 0x17, "J": 0x24,
    "K": 0x25, "L": 0x26, "M": 0x32, "N": 0x31, "O": 0x18,
    "P": 0x19, "Q": 0x10, "R": 0x13, "S": 0x1F, "T": 0x14,
    "U": 0x16, "V": 0x2F, "W": 0x11, "X": 0x2D, "Y": 0x15,
    "Z": 0x2C,
}
 
_kbe = ctypes.windll.user32.keybd_event
_kbe.argtypes = [ctypes.c_ubyte, ctypes.c_ubyte, ctypes.c_ulong, ctypes.c_ulong]
 
def send_key(char: str) -> bool:
    sc = SCAN_CODES.get(char.upper())
    if sc is None:
        log(f"  ⚠ No scan code for [{char}]")
        return False
    log(f"  ⌨ Sending [{char}] scan=0x{sc:02X}")
    _kbe(0, sc, KEYEVENTF_SCANCODE, 0)
    time.sleep(0.05)
    _kbe(0, sc, KEYEVENTF_SCANCODE | KEYEVENTF_KEYUP, 0)
    log(f"  ⚡ Pressed [{char}]")
    return True
 
# ──────────────────────────────────────────────────────────────────────────────
#  PIXEL GATE — fast activity detection before invoking Tesseract
# ──────────────────────────────────────────────────────────────────────────────
 
def _frame_brightness(img: Image.Image) -> float:
    """
    Return the mean brightness (0–255) of the grayscale image.
    This is very cheap — no resizing, no Tesseract — just a single stat pass.
    Used to skip OCR on dark/empty frames so we poll at true ~60fps when idle.
    """
    return ImageStat.Stat(img.convert("L")).mean[0]
 
# ──────────────────────────────────────────────────────────────────────────────
#  IMAGE PREPROCESSING
# ──────────────────────────────────────────────────────────────────────────────
 
def preprocess_image(img: Image.Image, invert: bool = False) -> Image.Image:
    w, h = img.size
 
    px, py = int(w * 0.05), int(h * 0.05)
    img = img.crop((px, py, w - px, h - py))
 
    img = img.resize((img.width * 8, img.height * 8), Image.Resampling.LANCZOS)
    img = img.convert("L")
    img = img.filter(ImageFilter.SHARPEN)
    img = img.filter(ImageFilter.SHARPEN)
    img = ImageEnhance.Contrast(img).enhance(4.5)
 
    pixels = list(img.getdata())
    lo, hi = min(pixels), max(pixels)
    threshold = (lo + hi) // 2
 
    if not invert:
        img = img.point(lambda p: 0 if p > threshold else 255)
    else:
        img = img.point(lambda p: 255 if p > threshold else 0)
 
    padded = Image.new("L", (img.width + 60, img.height + 60), 255)
    padded.paste(img, (30, 30))
    return padded
 
# ──────────────────────────────────────────────────────────────────────────────
#  OCR — multi-strategy with fallbacks
# ──────────────────────────────────────────────────────────────────────────────
 
_PSM_STRATEGIES = [
    ("normal",   10),
    ("inverted", 10),
    ("normal",    6),
    ("inverted",  6),
]
 
def _run_tesseract(img: Image.Image, psm: int) -> str:
    whitelist = "".join(sorted(TARGET_CHARS))
    config    = f"--psm {psm} -c tessedit_char_whitelist={whitelist}"
    result    = pytesseract.image_to_string(img, config=config)
    return result.strip().upper()
 
def detect_letter(screenshot: Image.Image) -> Optional[str]:
    cache = {}
 
    for polarity, psm in _PSM_STRATEGIES:
        invert = (polarity == "inverted")
 
        if polarity not in cache:
            cache[polarity] = preprocess_image(screenshot, invert=invert)
        img = cache[polarity]
 
        if DEBUG_SAVE_FRAMES:
            img.save(PROCESSED_SNAP_PATH)
 
        try:
            text = _run_tesseract(img, psm)
        except Exception as e:
            log(f"  ❌ Tesseract error (psm={psm} {polarity}): {e}")
            continue
 
        char = text[0] if text else ""
        if char in TARGET_CHARS:
            log(f"  ✅ Detected [{char}] via psm={psm} {polarity}")
            return char
        else:
            log(f"  🔍 psm={psm} {polarity}: '{text}' — no match")
 
    return None
 
# ──────────────────────────────────────────────────────────────────────────────
#  TESSERACT PRE-WARM
# ──────────────────────────────────────────────────────────────────────────────
#  The very first Tesseract call always takes 150–300ms to load the OCR engine
#  into memory, regardless of image content. If that load happens on the first
#  real skill check, you miss it.
#
#  Fix: fire a throwaway 1×1 Tesseract call in a background thread right after
#  startup. By the time you switch to Roblox and a skill check appears, the
#  engine is already warm and subsequent calls take ~30–80ms instead.
 
def _prewarm_tesseract():
    """Run a silent dummy OCR call so the engine is loaded before the first real check."""
    try:
        dummy = Image.new("L", (40, 40), 255)
        whitelist = "".join(sorted(TARGET_CHARS))
        pytesseract.image_to_string(dummy, config=f"--psm 10 -c tessedit_char_whitelist={whitelist}")
        log("[INIT] Tesseract engine pre-warmed ✅")
    except Exception as e:
        log(f"[INIT] Pre-warm failed (non-fatal): {e}")
 
# ──────────────────────────────────────────────────────────────────────────────
#  SNAPSHOT  (saved on F6 toggle-OFF)
# ──────────────────────────────────────────────────────────────────────────────
 
def save_toggle_off_snapshot():
    try:
        with mss.mss() as sct:
            frame = sct.grab(REGION)
            raw   = Image.frombytes("RGB", frame.size, frame.bgra, "raw", "BGRX")
            raw.save(RAW_SNAP_PATH)
            processed = preprocess_image(raw, invert=False)
            processed.save(PROCESSED_SNAP_PATH)
        log(f"  📸 Raw snapshot       → {RAW_SNAP_PATH}")
        log(f"  📸 Processed snapshot → {PROCESSED_SNAP_PATH}")
    except Exception as e:
        log(f"  ⚠ Snapshot failed: {e}")
 
# ──────────────────────────────────────────────────────────────────────────────
#  BOT LOOP
# ──────────────────────────────────────────────────────────────────────────────
 
def bot_loop():
    global running
    log("[BOT] Loop thread started. Waiting for F6...")
 
    press_time  = 0.0
    in_cooldown = False
 
    with mss.mss() as sct:
        while running:
            if not bot_active:
                time.sleep(0.05)
                press_time  = 0.0
                in_cooldown = False
                continue
 
            # ── Post-press cooldown ────────────────────────────────────────
            if in_cooldown:
                elapsed   = time.time() - press_time
                remaining = PRESS_COOLDOWN - elapsed
                if remaining > 0:
                    time.sleep(min(remaining, POLL_INTERVAL))
                    continue
                else:
                    in_cooldown = False
                    log("  🟢 Cooldown done — ready for next letter")
 
            # ── Grab frame ─────────────────────────────────────────────────
            try:
                frame = sct.grab(REGION)
                img   = Image.frombytes("RGB", frame.size, frame.bgra, "raw", "BGRX")
            except Exception as e:
                log(f"  ❌ Screen grab failed: {e}")
                time.sleep(0.1)
                continue
 
            # ── Pixel gate — skip Tesseract on dark/empty frames ───────────
            # This is the key to fast first-detection: we poll at ~60fps with
            # near-zero cost when idle, and only pay the ~80ms OCR cost when
            # the frame actually looks like it has a circle in it.
            brightness = _frame_brightness(img)
            if brightness < ACTIVITY_THRESHOLD:
                if DEBUG_SAVE_FRAMES:
                    log(f"  ⬛ Gate skip (brightness={brightness:.1f})")
                time.sleep(POLL_INTERVAL)
                continue
 
            log(f"  🔆 Gate passed (brightness={brightness:.1f}) — running OCR")
 
            # ── OCR ────────────────────────────────────────────────────────
            try:
                letter = detect_letter(img)
            except Exception as e:
                log(f"  ❌ OCR failed: {e}")
                time.sleep(0.1)
                continue
 
            if letter:
                log(f"  🆕 Letter [{letter}] — pressing")
                send_key(letter)
                press_time  = time.time()
                in_cooldown = True
            else:
                # Circle was visible but OCR couldn't read it yet — retry
                # immediately without sleeping so we catch it next frame
                pass
 
# ──────────────────────────────────────────────────────────────────────────────
#  HOTKEY LISTENER
# ──────────────────────────────────────────────────────────────────────────────
 
def on_press(key):
    global bot_active, running
 
    if key == HOTKEY_TOGGLE:
        bot_active = not bot_active
        status = "ON  ✅" if bot_active else "OFF ⛔"
        log(f"[BOT] Toggled {status}")
        if not bot_active:
            threading.Thread(target=save_toggle_off_snapshot, daemon=True).start()
 
    elif key == HOTKEY_QUIT:
        log("[BOT] Quitting...")
        running = False
        return False
 
# ──────────────────────────────────────────────────────────────────────────────
#  REGION FINDER
# ──────────────────────────────────────────────────────────────────────────────
 
def find_region_helper():
    try:
        import pyautogui
    except ImportError:
        print("Run: pip install pyautogui")
        return
    print("\n── Region Finder ──────────────────────────────────")
    print("Hover over the corners of the letter area. Ctrl+C to exit.\n")
    try:
        while True:
            x, y = pyautogui.position()
            print(f"  x={x:4d}  y={y:4d}", end="\r")
            time.sleep(0.05)
    except KeyboardInterrupt:
        print('\n\nSet REGION = {"left": <x>, "top": <y>, "width": <w>, "height": <h>}')
 
# ──────────────────────────────────────────────────────────────────────────────
#  ENTRY POINT
# ──────────────────────────────────────────────────────────────────────────────
 
def main():
    global DEBUG_SAVE_FRAMES
 
    parser = argparse.ArgumentParser()
    parser.add_argument("--find-region", action="store_true",
                        help="Mouse-position helper to locate your capture region")
    parser.add_argument("--debug", action="store_true",
                        help="Log gate brightness values and save processed frames")
    args = parser.parse_args()
 
    if args.find_region:
        find_region_helper()
        return
 
    if args.debug:
        DEBUG_SAVE_FRAMES = True
        print(f"[DEBUG] Gate values and processed frames enabled")
 
    # Tesseract must be found before threads start
    _init_tesseract()
 
    # Pre-warm in background — engine will be loaded before you switch to Roblox
    print("[INIT] Pre-warming Tesseract engine in background...")
    prewarm_thread = threading.Thread(target=_prewarm_tesseract, daemon=True)
    prewarm_thread.start()
 
    init_log()
 
    print("╔══════════════════════════════════════╗")
    print("║     SKILL CHECK BOT  ⚡  (Roblox)    ║")
    print("╠══════════════════════════════════════╣")
    print(f"║  Target chars : {', '.join(sorted(TARGET_CHARS)):<20} ║")
    print(f"║  Cooldown     : {PRESS_COOLDOWN*1000:.0f}ms after each press{'':>8} ║")
    print(f"║  Activity gate: brightness ≥ {ACTIVITY_THRESHOLD:<3}        ║")
    print( "║  Toggle       : F6  (saves snapshot) ║")
    print( "║  Quit         : F8                   ║")
    print( "║  Log file     : skill_check_boy.log  ║")
    print("╚══════════════════════════════════════╝\n")
 
    thread = threading.Thread(target=bot_loop, daemon=True)
    thread.start()
 
    with kb.Listener(on_press=on_press) as listener:
        listener.join()
 
    thread.join(timeout=1)
    log("[BOT] Stopped.")
    if _log_file:
        _log_file.close()
 
 
if __name__ == "__main__":
    main()
