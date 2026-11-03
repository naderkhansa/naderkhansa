import sys
import os
import re
import math
import subprocess
import tempfile
import shutil
import threading
import traceback
import wave

# ==============================================================================
# STARTUP GUARD — when launched by double-click, show errors instead of closing
# ==============================================================================
CRASH_LOG = os.path.join(os.path.dirname(os.path.abspath(__file__)), "ank_crash_log.txt")


def _show_fatal(title: str, msg: str):
    try:
        with open(CRASH_LOG, "w", encoding="utf-8") as f:
            f.write(msg)
    except OSError:
        pass
    try:
        import tkinter
        import tkinter.messagebox
        root = tkinter.Tk()
        root.withdraw()
        tkinter.messagebox.showerror(title, f"{msg[-1800:]}\n\nDetails saved to:\n{CRASH_LOG}")
        root.destroy()
    except Exception:
        print(f"{title}\n\n{msg}")
        try:
            input("\nPress Enter to close...")
        except Exception:
            pass


_missing = []
for _mod, _pip in (("cv2", "opencv-python"), ("numpy", "numpy"), ("PIL", "pillow"), ("PyQt6.QtWidgets", "PyQt6")):
    try:
        __import__(_mod)
    except Exception as _e:
        _missing.append((_pip, f"{_mod}: {_e}"))
if _missing:
    _show_fatal(
        "ANK Media Studio — missing packages",
        "ANK Media Studio needs these Python packages:\n\n"
        f"    pip install {' '.join(p for p, _ in _missing)}\n\n"
        "Open Command Prompt, run the line above, then double-click the app again.\n\n"
        f"Python used: {sys.executable}\n\nDetails:\n" + "\n".join(d for _, d in _missing)
    )
    sys.exit(1)

import cv2
import numpy as np
from PIL import Image
from PyQt6.QtWidgets import (
    QApplication, QMainWindow, QWidget, QVBoxLayout, QHBoxLayout, QGridLayout,
    QPushButton, QToolButton, QLabel, QFileDialog, QSlider, QTabWidget, QComboBox,
    QMessageBox, QScrollArea, QStatusBar, QCheckBox, QMenu,
    QDoubleSpinBox, QSpinBox, QLineEdit,
    QFormLayout, QProgressDialog, QColorDialog, QButtonGroup, QFrame, QSizePolicy, QListWidget, QListWidgetItem,
    QTableWidget, QTableWidgetItem, QDialog, QDialogButtonBox, QProgressBar,
    QAbstractSpinBox
)
from PyQt6.QtCore import QSettings, Qt, QTimer, QRect, QRectF, QPoint, QPointF, QSize, pyqtSignal, QObject, QElapsedTimer, QBuffer, QByteArray, QIODevice
from PyQt6.QtGui import (
    QImage, QPixmap, QPainter, QColor, QPen, QFont, QBrush, QKeySequence, QShortcut,
    QIcon, QLinearGradient, QPainterPath, QFontMetrics
)

# Optional live audio for the preview monitor (falls back to silent playback)
try:
    from PyQt6.QtMultimedia import QAudioFormat, QAudioSink, QMediaDevices
    HAS_QT_AUDIO = True
except Exception:
    HAS_QT_AUDIO = False

# Optional AI Background Removal (rembg) with OpenCV GrabCut fallback
try:
    from rembg import remove as rembg_remove
    HAS_REMBG = True
except ImportError:
    HAS_REMBG = False

# Locate FFmpeg binary (from system PATH or imageio_ffmpeg installed with moviepy)
FFMPEG_EXE = shutil.which("ffmpeg")
if not FFMPEG_EXE:
    try:
        import imageio_ffmpeg
        FFMPEG_EXE = imageio_ffmpeg.get_ffmpeg_exe()
    except Exception:
        FFMPEG_EXE = None

NO_WINDOW = 0x08000000 if os.name == "nt" else 0

# ==============================================================================
# APPLICATION METADATA & VERSION CONTROL
# ==============================================================================
APP_NAME = "ANK Media Studio"
APP_VERSION = "3.0.0"
APP_AUTHOR = "Nader Alkhansa"

# Expanded 12-Color Palette so every added video has its own unmistakable identity
VIDEO_PALETTE = [
    "#3B82F6",  # V1: Royal Blue
    "#10B981",  # V2: Emerald Green
    "#F59E0B",  # V3: Amber Gold
    "#EF4444",  # V4: Crimson Red
    "#8B5CF6",  # V5: Vivid Purple
    "#EC4899",  # V6: Hot Pink
    "#06B6D4",  # V7: Cyan
    "#F97316",  # V8: Sunset Orange
    "#84CC16",  # V9: Lime Green
    "#14B8A6",  # V10: Teal
    "#6366F1",  # V11: Indigo
    "#D946EF",  # V12: Fuchsia
]

PHOTO_EXTS = {".png", ".jpg", ".jpeg", ".webp", ".bmp", ".tif", ".tiff"}
VIDEO_EXTS = {".mp4", ".mov", ".avi", ".mkv", ".webm", ".m4v"}

# Preview monitors render at most this many pixels on the long edge (exports stay full resolution)
VIDEO_PREVIEW_MAX = 1280
PHOTO_PREVIEW_MAX = 1600


def format_ms(ms: int) -> str:
    """Formats milliseconds into MM:SS.mmm (Seconds & Milliseconds)."""
    ms = max(0, int(ms))
    seconds = (ms // 1000) % 60
    minutes = (ms // 60000)
    millis = ms % 1000
    return f"{minutes:02d}:{seconds:02d}.{millis:03d}"


def run_quiet(cmd, **kw):
    return subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, creationflags=NO_WINDOW, **kw)


# ==============================================================================
# 3D ICON ENGINE — glossy beveled tiles with vector glyphs, drawn with QPainter
# ==============================================================================
ICON_COLORS = {
    "blue": "#3B82F6", "sky": "#0EA5E9", "cyan": "#06B6D4", "teal": "#14B8A6", "green": "#10B981",
    "lime": "#65A30D", "amber": "#F59E0B", "orange": "#F97316", "red": "#EF4444", "rose": "#F43F5E",
    "pink": "#EC4899", "purple": "#8B5CF6", "violet": "#7C3AED", "indigo": "#6366F1", "slate": "#475569",
}


def _glyph(p: QPainter, name: str, s: float):
    """Draws a white vector glyph on a 100x100 grid scaled by s (painter already translated)."""
    def P(x, y):
        return QPointF(x * s, y * s)

    def poly(*pts, fill=True):
        path = QPainterPath(P(*pts[0]))
        for pt in pts[1:]:
            path.lineTo(P(*pt))
        if fill:
            path.closeSubpath()
            p.fillPath(path, p.brush())
        else:
            p.drawPath(path)

    def line(x1, y1, x2, y2):
        p.drawLine(P(x1, y1), P(x2, y2))

    def rect(x, y, w, h, r=0, fill=False):
        rr = QRectF(x * s, y * s, w * s, h * s)
        if fill:
            path = QPainterPath()
            path.addRoundedRect(rr, r * s, r * s)
            p.fillPath(path, p.brush())
        else:
            p.drawRoundedRect(rr, r * s, r * s)

    def circle(cx, cy, r, fill=False):
        rr = QRectF((cx - r) * s, (cy - r) * s, 2 * r * s, 2 * r * s)
        if fill:
            path = QPainterPath()
            path.addEllipse(rr)
            p.fillPath(path, p.brush())
        else:
            p.drawEllipse(rr)

    def arc(cx, cy, r, start, span):
        p.drawArc(QRectF((cx - r) * s, (cy - r) * s, 2 * r * s, 2 * r * s), int(start * 16), int(span * 16))

    def arrow_head(x, y, ang_deg, size=12):
        a = math.radians(ang_deg)
        tip = (x, y)
        l = (x - size * math.cos(a - 0.5), y - size * math.sin(a - 0.5))
        r = (x - size * math.cos(a + 0.5), y - size * math.sin(a + 0.5))
        poly(tip, l, r)

    n = name
    if n == "play":
        poly((34, 22), (34, 78), (80, 50))
    elif n == "pause":
        rect(28, 22, 15, 56, 3, True); rect(57, 22, 15, 56, 3, True)
    elif n == "stop":
        rect(26, 26, 48, 48, 5, True)
    elif n in ("to_start", "to_end"):
        if n == "to_start":
            rect(22, 24, 9, 52, 2, True); poly((78, 24), (78, 76), (36, 50))
        else:
            rect(69, 24, 9, 52, 2, True); poly((22, 24), (22, 76), (64, 50))
    elif n in ("step_back", "step_fwd"):
        if n == "step_back":
            poly((52, 26), (52, 74), (18, 50)); poly((84, 26), (84, 74), (50, 50))
        else:
            poly((48, 26), (48, 74), (82, 50)); poly((16, 26), (16, 74), (50, 50))
    elif n == "split":
        circle(30, 70, 11); circle(70, 70, 11)
        line(37, 61, 68, 18); line(63, 61, 32, 18)
    elif n == "copy":
        rect(20, 30, 40, 48, 6); rect(40, 16, 40, 48, 6, True)
    elif n == "paste":
        rect(24, 22, 52, 60, 6); rect(38, 14, 24, 14, 4, True); line(36, 48, 64, 48); line(36, 62, 58, 62)
    elif n == "trash":
        line(22, 28, 78, 28); rect(42, 18, 16, 10, 2)
        poly((30, 32), (70, 32), (66, 84), (34, 84), fill=False)
        line(44, 42, 44, 74); line(56, 42, 56, 74)
    elif n in ("undo", "redo"):
        if n == "undo":
            arc(54, 56, 24, 90, 220); arrow_head(28, 34, 200, 16)
        else:
            arc(46, 56, 24, -130, 220); arrow_head(72, 34, -20, 16)
    elif n == "crop":
        poly((30, 14), (30, 70), (86, 70), fill=False); poly((14, 30), (70, 30), (70, 86), fill=False)
    elif n == "move":
        line(50, 14, 50, 86); line(14, 50, 86, 50)
        arrow_head(50, 12, -90); arrow_head(50, 88, 90); arrow_head(12, 50, 180); arrow_head(88, 50, 0)
    elif n in ("rotate_cw", "rotate_ccw"):
        if n == "rotate_cw":
            arc(50, 52, 26, 120, -280); arrow_head(64, 26, -40, 16)
        else:
            arc(50, 52, 26, 60, 280); arrow_head(36, 26, 220, 16)
    elif n == "flip_h":
        line(50, 14, 50, 86); poly((42, 24), (42, 76), (14, 76)); poly((58, 24), (58, 76), (86, 76), fill=False)
    elif n == "flip_v":
        line(14, 50, 86, 50); poly((24, 42), (76, 42), (76, 14)); poly((24, 58), (76, 58), (76, 86), fill=False)
    elif n == "reset":
        arc(50, 50, 28, 60, 300); arrow_head(64, 26, -30, 16); circle(50, 50, 6, True)
    elif n in ("zoom_in", "zoom_out"):
        circle(42, 42, 24); line(60, 60, 84, 84); line(30, 42, 54, 42)
        if n == "zoom_in":
            line(42, 30, 42, 54)
    elif n == "speed":
        arc(50, 60, 32, 0, 180); line(50, 60, 70, 34); circle(50, 60, 6, True)
        line(18, 60, 26, 60); line(74, 60, 82, 60); line(50, 28, 50, 36)
    elif n == "mic":
        rect(38, 14, 24, 42, 12, True); arc(50, 46, 22, 180, 180); line(50, 68, 50, 84); line(36, 84, 64, 84)
    elif n == "music":
        circle(30, 72, 12, True); circle(70, 64, 12, True)
        rect(38, 22, 6, 50, 0, True); rect(78, 14, 6, 50, 0, True); poly((38, 22), (84, 14), (84, 28), (38, 36))
    elif n == "noise":
        path = QPainterPath(P(10, 50))
        for i, x in enumerate(range(16, 92, 6)):
            path.lineTo(P(x, 50 + (24 if i % 2 else -24) * (0.4 + 0.6 * abs(math.sin(i)))))
        p.drawPath(path)
    elif n in ("volume", "mute"):
        poly((16, 40), (32, 40), (52, 22), (52, 78), (32, 60), (16, 60))
        if n == "volume":
            arc(52, 50, 16, -50, 100); arc(52, 50, 28, -50, 100)
        else:
            line(62, 38, 84, 62); line(84, 38, 62, 62)
    elif n == "export":
        line(50, 14, 50, 60); arrow_head(50, 64, 90, 18); poly((18, 58), (18, 84), (82, 84), (82, 58), fill=False)
    elif n == "save":
        rect(18, 16, 64, 68, 6); rect(30, 16, 36, 22, 2, True); rect(30, 52, 40, 32, 3)
    elif n == "open":
        poly((14, 30), (40, 30), (46, 38), (86, 38), (86, 80), (14, 80), fill=False); poly((14, 46), (86, 46), (80, 80), (14, 80))
    elif n == "add":
        line(50, 20, 50, 80); line(20, 50, 80, 50)
    elif n == "insert":
        line(50, 14, 50, 50); arrow_head(50, 54, 90, 16); rect(16, 62, 68, 20, 4, True)
    elif n == "magic":
        line(22, 80, 64, 38); rect(60, 30, 10, 10, 2, True)
        for cx, cy, r in ((76, 22, 6), (36, 26, 4), (80, 58, 4)):
            poly((cx, cy - r * 2), (cx + r * 0.6, cy), (cx, cy + r * 2), (cx - r * 0.6, cy))
            poly((cx - r * 2, cy), (cx, cy + r * 0.6), (cx + r * 2, cy), (cx, cy - r * 0.6))
    elif n == "brush":
        line(76, 16, 46, 54); poly((40, 52), (52, 64), (40, 84), (16, 86), (22, 66))
    elif n == "sparkle":
        for cx, cy, r in ((44, 52, 16), (74, 26, 8), (76, 72, 6)):
            poly((cx, cy - r * 2), (cx + r * 0.45, cy - r * 0.45), (cx + r * 2, cy), (cx + r * 0.45, cy + r * 0.45),
                 (cx, cy + r * 2), (cx - r * 0.45, cy + r * 0.45), (cx - r * 2, cy), (cx - r * 0.45, cy - r * 0.45))
    elif n == "person":
        circle(50, 30, 14, True); poly((22, 86), (26, 58), (40, 48), (60, 48), (74, 58), (78, 86))
    elif n == "image":
        rect(14, 20, 72, 60, 6); poly((18, 76), (42, 46), (58, 64), (68, 54), (82, 76)); circle(68, 36, 7, True)
    elif n == "text":
        rect(22, 18, 56, 12, 2, True); rect(44, 18, 12, 64, 2, True); rect(36, 74, 28, 8, 2, True)
    elif n == "palette":
        circle(50, 50, 32); circle(36, 38, 6, True); circle(54, 30, 6, True); circle(68, 44, 6, True); circle(40, 62, 8, True)
    elif n == "filter":
        circle(38, 40, 20); circle(62, 40, 20); circle(50, 62, 20)
    elif n == "fade":
        for i in range(6):
            p.save(); c = QColor(255, 255, 255, 50 + i * 40); p.setBrush(c)
            rect(14 + i * 12, 24, 10, 52, 2, True); p.restore()
    elif n == "marker":
        line(28, 14, 28, 86); poly((28, 16), (76, 30), (28, 46))
    elif n in ("lock", "unlock"):
        rect(22, 46, 56, 40, 6, True)
        if n == "lock":
            arc(50, 46, 18, 0, 180); line(32, 46, 32, 40); line(68, 46, 68, 40)
        else:
            arc(32, 40, 18, 0, 180); line(14, 40, 14, 34)
    elif n == "camera":
        rect(14, 30, 72, 50, 8); rect(36, 20, 28, 12, 3, True); circle(50, 55, 15); circle(50, 55, 6, True)
    elif n == "compare":
        rect(14, 20, 72, 60, 6); rect(14, 20, 36, 60, 6, True); line(50, 12, 50, 88)
    elif n == "skin":
        circle(50, 46, 28); circle(40, 40, 4, True); circle(60, 40, 4, True); arc(50, 50, 14, 200, 140)
    elif n == "hd":
        rect(12, 24, 76, 52, 8)
        p.save(); f = QFont("Arial", max(6, int(30 * s)), QFont.Weight.Black); p.setFont(f)
        p.drawText(QRectF(12 * s, 24 * s, 76 * s, 52 * s), Qt.AlignmentFlag.AlignCenter, "HD"); p.restore()
    elif n == "film":
        rect(16, 14, 68, 72, 6); line(30, 14, 30, 86); line(70, 14, 70, 86)
        for y in (26, 42, 58, 74):
            rect(19, y - 3, 8, 6, 1, True); rect(73, y - 3, 8, 6, 1, True)
    elif n == "eye":
        path = QPainterPath(P(12, 50)); path.quadTo(P(50, 10), P(88, 50)); path.quadTo(P(50, 90), P(12, 50)); p.drawPath(path)
        circle(50, 50, 12, True)
    elif n == "eraser":
        poly((20, 62), (52, 30), (78, 56), (56, 78), (34, 78), fill=False); line(36, 46, 62, 72); line(20, 84, 80, 84)
    elif n == "aspect":
        rect(14, 26, 72, 48, 4); rect(36, 14, 28, 72, 4)
    elif n == "layers":
        poly((50, 16), (86, 34), (50, 52), (14, 34)); poly((20, 50), (50, 66), (80, 50), (86, 54), (50, 72), (14, 54))
    elif n == "auto":
        circle(50, 50, 30); p.save(); f = QFont("Arial", max(6, int(30 * s)), QFont.Weight.Black); p.setFont(f)
        p.drawText(QRectF(20 * s, 20 * s, 60 * s, 60 * s), Qt.AlignmentFlag.AlignCenter, "A"); p.restore()
    elif n == "ab":
        p.save(); f = QFont("Arial", max(6, int(28 * s)), QFont.Weight.Black); p.setFont(f)
        p.drawText(QRectF(8 * s, 18 * s, 84 * s, 64 * s), Qt.AlignmentFlag.AlignCenter, "A·B"); p.restore()
    elif n == "keep":
        rect(14, 30, 72, 40, 6); rect(34, 30, 32, 40, 0, True)
    elif n == "logo":
        poly((34, 20), (34, 80), (82, 50))
        p.save(); p.setBrush(QColor(255, 255, 255, 120)); rect(14, 20, 12, 60, 3, True); p.restore()
    else:
        circle(50, 50, 20, True)


_ICON_CACHE = {}


def make_icon_pixmap(name: str, color: str = "blue", size: int = 64, flat: bool = False) -> QPixmap:
    """Glossy 3D tile: drop shadow, gradient body, bevel rim, glass highlight and a white vector glyph."""
    key = (name, color, size, flat)
    if key in _ICON_CACHE:
        return _ICON_CACHE[key]
    base = QColor(ICON_COLORS.get(color, color))
    pm = QPixmap(size, size)
    pm.fill(Qt.GlobalColor.transparent)
    p = QPainter(pm)
    p.setRenderHint(QPainter.RenderHint.Antialiasing)
    p.setRenderHint(QPainter.RenderHint.TextAntialiasing)
    m = size * 0.06
    body = QRectF(m, m, size - 2 * m, size - 2 * m - size * 0.05)
    rad = size * 0.24

    if not flat:
        # Soft drop shadow (stacked translucent layers)
        for i in range(4, 0, -1):
            sh = body.translated(0, size * 0.035 * i / 2)
            p.setPen(Qt.PenStyle.NoPen)
            p.setBrush(QColor(0, 0, 0, 26))
            p.drawRoundedRect(sh.adjusted(-i * 0.4, 0, i * 0.4, i * 0.6), rad, rad)

        grad = QLinearGradient(body.topLeft(), body.bottomLeft())
        grad.setColorAt(0.0, base.lighter(150))
        grad.setColorAt(0.45, base)
        grad.setColorAt(1.0, base.darker(165))
        p.setBrush(QBrush(grad))
        p.setPen(QPen(base.lighter(175), max(1.0, size * 0.025)))
        p.drawRoundedRect(body, rad, rad)

        # Glass highlight on the upper half
        gloss = QPainterPath()
        gloss.addRoundedRect(body.adjusted(size * 0.05, size * 0.04, -size * 0.05, -body.height() * 0.5), rad * 0.8, rad * 0.8)
        g2 = QLinearGradient(body.topLeft(), QPointF(body.left(), body.center().y()))
        g2.setColorAt(0.0, QColor(255, 255, 255, 120))
        g2.setColorAt(1.0, QColor(255, 255, 255, 8))
        p.fillPath(gloss, QBrush(g2))

    # Glyph with a subtle embossed shadow
    gs = (body.width() * 0.62) / 100.0
    gx = body.left() + (body.width() - 100 * gs) / 2
    gy = body.top() + (body.height() - 100 * gs) / 2
    for dx, dy, col in ((0, size * 0.025, QColor(0, 0, 0, 90)), (0, 0, QColor(255, 255, 255))):
        p.save()
        p.translate(gx + dx, gy + dy)
        pen = QPen(col, max(1.4, 8.5 * gs))
        pen.setCapStyle(Qt.PenCapStyle.RoundCap)
        pen.setJoinStyle(Qt.PenJoinStyle.RoundJoin)
        p.setPen(pen)
        p.setBrush(col)
        _glyph(p, name, gs)
        p.restore()
    p.end()
    _ICON_CACHE[key] = pm
    return pm


def make_icon(name: str, color: str = "blue") -> QIcon:
    icon = QIcon()
    for sz in (24, 32, 48, 64):
        icon.addPixmap(make_icon_pixmap(name, color, sz))
    return icon


def icon_button(text: str, icon: str, color: str = "blue", tip: str = "", kind: str = "", checkable: bool = False) -> QPushButton:
    b = QPushButton(text)
    b.setIcon(make_icon(icon, color))
    b.setIconSize(QSize(22, 22))
    if kind:
        b.setProperty("kind", kind)
    if tip:
        b.setToolTip(tip)
    b.setCheckable(checkable)
    b.setCursor(Qt.CursorShape.PointingHandCursor)
    return b


def tool_button(text: str, icon: str, color: str = "blue", tip: str = "", size: int = 34, checkable: bool = False) -> QToolButton:
    b = QToolButton()
    b.setText(text)
    b.setIcon(make_icon(icon, color))
    b.setIconSize(QSize(size, size))
    b.setToolButtonStyle(Qt.ToolButtonStyle.ToolButtonTextUnderIcon if text else Qt.ToolButtonStyle.ToolButtonIconOnly)
    b.setToolTip(tip or text)
    b.setCheckable(checkable)
    b.setCursor(Qt.CursorShape.PointingHandCursor)
    return b


# ==============================================================================
# AUDIO ENGINE: EXTRACTION, STEM SEPARATION (VOICES, MUSIC, NOISES), TIME-STRETCH
# ==============================================================================
def read_wav_float(path: str):
    with wave.open(path, "rb") as wf:
        sr = wf.getframerate()
        n_ch = wf.getnchannels()
        raw = wf.readframes(wf.getnframes())
    audio = np.frombuffer(raw, dtype=np.int16).astype(np.float32) / 32768.0
    audio = audio.reshape(-1, 2) if n_ch == 2 else np.column_stack([audio, audio])
    return sr, audio


def write_wav_float(path: str, audio: np.ndarray, sr: int):
    pcm16 = (np.clip(audio, -1.0, 1.0) * 32767.0).astype(np.int16)
    with wave.open(path, "wb") as wf:
        wf.setnchannels(2)
        wf.setsampwidth(2)
        wf.setframerate(sr)
        wf.writeframes(pcm16.tobytes())


def probe_media_duration_ms(path: str) -> int:
    """Duration from ffmpeg's header (used when OpenCV cannot count frames, e.g. many MKV/WebM files)."""
    if not FFMPEG_EXE:
        return 0
    try:
        res = run_quiet([FFMPEG_EXE, "-hide_banner", "-i", path], timeout=30)
        m = re.search(r"Duration:\s*(\d+):(\d+):(\d+(?:\.\d+)?)", res.stderr.decode("utf-8", "ignore"))
        if m:
            return int((int(m.group(1)) * 3600 + int(m.group(2)) * 60 + float(m.group(3))) * 1000)
    except Exception:
        pass
    return 0


def atempo_chain(speed: float) -> str:
    parts = []
    s = speed
    while s > 2.0:
        parts.append("atempo=2.0")
        s /= 2.0
    while s < 0.5:
        parts.append("atempo=0.5")
        s /= 0.5
    parts.append(f"atempo={s:.6f}")
    return ",".join(parts)


def time_stretch(audio: np.ndarray, sr: int, speed: float, target_len: int, keep_pitch: bool = True) -> np.ndarray:
    """Changes audio duration by `speed`. With FFmpeg, voices keep their natural pitch (atempo)."""
    if len(audio) == 0:
        return np.zeros((target_len, 2), dtype=np.float32)
    if abs(speed - 1.0) <= 0.01:
        # Normal speed: only pad/trim rounding differences
        if len(audio) >= target_len:
            return audio[:target_len]
        return np.vstack([audio, np.zeros((target_len - len(audio), 2), dtype=np.float32)])
    out = None
    if keep_pitch and abs(speed - 1.0) > 0.01 and FFMPEG_EXE and len(audio) > sr // 10:
        tmp_dir = tempfile.mkdtemp(prefix="ank_ts_")
        try:
            src_wav, dst_wav = os.path.join(tmp_dir, "in.wav"), os.path.join(tmp_dir, "out.wav")
            write_wav_float(src_wav, audio, sr)
            res = run_quiet([FFMPEG_EXE, "-y", "-i", src_wav, "-af", atempo_chain(speed), "-ar", str(sr), "-ac", "2", dst_wav])
            if res.returncode == 0 and os.path.exists(dst_wav):
                _, out = read_wav_float(dst_wav)
        except Exception:
            out = None
        finally:
            shutil.rmtree(tmp_dir, ignore_errors=True)
    if out is None:
        # Linear-interpolated resample (pitch follows speed)
        src_idx = np.linspace(0, len(audio) - 1, target_len)
        out = np.column_stack([np.interp(src_idx, np.arange(len(audio)), audio[:, c]) for c in range(2)]).astype(np.float32)
    if len(out) < target_len:
        out = np.vstack([out, np.zeros((target_len - len(out), 2), dtype=np.float32)])
    return out[:target_len]


class AudioStemProcessor:
    """
    Extracts audio from video files and separates it into 3 controllable stems:
      1. Voices / Speech (Center-channel Mid + 220Hz-3800Hz Vocal Formant Band)
      2. Music / Instruments (Stereo Side + Harmonic Bass/Treble Musical Bed)
      3. Noises / Ambience (Sub-rumble <100Hz + High-frequency hiss >7500Hz)
    v2.0: processed in overlapping windowed blocks (STFT), so long videos use little memory
    and there are no clicks at block edges.
    """
    @staticmethod
    def extract_wav(video_path: str, out_wav: str, sample_rate: int = 44100) -> bool:
        if not FFMPEG_EXE or not os.path.exists(video_path):
            return False
        cmd = [
            FFMPEG_EXE, "-y", "-i", video_path,
            "-vn", "-acodec", "pcm_s16le", "-ar", str(sample_rate), "-ac", "2",
            out_wav
        ]
        try:
            res = run_quiet(cmd)
            return res.returncode == 0 and os.path.exists(out_wav) and os.path.getsize(out_wav) > 44
        except Exception:
            return False

    @staticmethod
    def separate_audio(audio: np.ndarray, sr: int, progress=None):
        n = len(audio)
        win = 8192
        hop = win // 2
        window = np.sqrt(np.hanning(win + 1)[:-1]).astype(np.float32)  # sqrt-Hann analysis+synthesis = perfect overlap-add
        freqs = np.fft.rfftfreq(win, d=1.0 / sr)
        voice_mask = ((freqs >= 220.0) & (freqs <= 3800.0)).astype(np.float32)
        noise_mask = ((freqs < 100.0) | (freqs > 7500.0)).astype(np.float32)
        music_mid_mask = 1.0 - np.clip(voice_mask + noise_mask, 0.0, 1.0)
        music_side_mask = 1.0 - noise_mask

        pad = np.vstack([np.zeros((win, 2), np.float32), audio, np.zeros((win + hop, 2), np.float32)])
        mid = 0.5 * (pad[:, 0] + pad[:, 1])
        side = 0.5 * (pad[:, 0] - pad[:, 1])
        outs = {k: np.zeros(len(pad), np.float32) for k in ("v", "mm", "ms", "nm", "ns")}
        n_frames = (len(pad) - win) // hop + 1
        batch = 64
        for b0 in range(0, n_frames, batch):
            idx = np.arange(b0, min(n_frames, b0 + batch)) * hop
            frames_m = np.stack([mid[i:i + win] for i in idx]) * window
            frames_s = np.stack([side[i:i + win] for i in idx]) * window
            fm = np.fft.rfft(frames_m, axis=1)
            fs = np.fft.rfft(frames_s, axis=1)
            parts = {
                "v": fm * voice_mask, "mm": fm * music_mid_mask, "ms": fs * music_side_mask,
                "nm": fm * noise_mask, "ns": fs * noise_mask,
            }
            for k, spec in parts.items():
                back = np.fft.irfft(spec, n=win, axis=1).astype(np.float32) * window
                for j, i in enumerate(idx):
                    outs[k][i:i + win] += back[j]
            if progress:
                progress(min(1.0, (b0 + batch) / n_frames))

        sl = slice(win, win + n)
        v, mm, ms, nm, ns = (outs[k][sl] for k in ("v", "mm", "ms", "nm", "ns"))
        voices = np.column_stack([v, v])
        music = np.column_stack([mm + ms, mm - ms])
        noise = np.column_stack([nm + ns, nm - ns])
        return voices, music, noise

    @staticmethod
    def envelope(arr: np.ndarray, bins: int = 0, sr: int = 44100) -> np.ndarray:
        if bins <= 0:
            bins = int(min(200000, max(400, (len(arr) if arr is not None else 0) / sr * 40)))
        if arr is None or len(arr) < bins:
            return np.zeros(bins, dtype=np.float32)
        mono = np.abs(arr[:, 0])
        usable = (len(mono) // bins) * bins
        env = mono[:usable].reshape(bins, -1).mean(axis=1).astype(np.float32)
        mx = float(env.max())
        return (env / mx) if mx > 1e-6 else env


# ==============================================================================
# UNIFIED IMAGE / FRAME GEOMETRY & AI UPSIZE ENGINE
# ==============================================================================
class TransformParams:
    """Holds non-destructive Rotate, Flip, Scale, Free-Move Offset, and AI Upsize state."""
    def __init__(self):
        self.rot_90_steps = 0     # 0, 1 (90 CW), 2 (180), 3 (270 CW / 90 CCW)
        self.free_angle = 0.0     # -180.0 to +180.0 degrees
        self.flip_h = False       # Horizontal mirror
        self.flip_v = False       # Vertical flip
        self.scale = 1.0          # 0.10 to 3.00
        self.offset_x = 0         # Free move X (pixels in canvas space)
        self.offset_y = 0         # Free move Y (pixels in canvas space)
        self.ai_upscale = False   # AI Super-Resolution Detail Enhancement
        self.transparent_bg = False
        self.bg_replacement = None

    def clone(self):
        t = TransformParams()
        t.rot_90_steps = self.rot_90_steps
        t.free_angle = self.free_angle
        t.flip_h = self.flip_h
        t.flip_v = self.flip_v
        t.scale = self.scale
        t.offset_x = self.offset_x
        t.offset_y = self.offset_y
        t.ai_upscale = self.ai_upscale
        t.transparent_bg = self.transparent_bg
        t.bg_replacement = self.bg_replacement.copy() if self.bg_replacement is not None else None
        t.bg_path = getattr(self, "bg_path", None)
        return t

    def reset(self):
        self.rot_90_steps = 0
        self.free_angle = 0.0
        self.flip_h = False
        self.flip_v = False
        self.scale = 1.0
        self.offset_x = 0
        self.offset_y = 0
        self.ai_upscale = False

    def is_identity(self) -> bool:
        return (self.rot_90_steps % 4 == 0 and self.free_angle == 0 and not self.flip_h and not self.flip_v
                and abs(self.scale - 1.0) < 1e-6 and self.offset_x == 0 and self.offset_y == 0
                and self.bg_replacement is None)

    def scaled(self, f: float):
        """Copy with pixel offsets scaled, for rendering a downscaled preview."""
        t = self.clone()
        t.offset_x = int(round(self.offset_x * f))
        t.offset_y = int(round(self.offset_y * f))
        return t

    def summary_tag(self) -> str:
        tags = []
        if self.rot_90_steps or self.free_angle != 0:
            total_deg = (self.rot_90_steps * 90 + int(self.free_angle)) % 360
            tags.append(f"ROT:{total_deg}°")
        if self.flip_h:
            tags.append("FLIP-H")
        if self.flip_v:
            tags.append("FLIP-V")
        if abs(self.scale - 1.0) > 0.01:
            tags.append(f"SCALE:{int(self.scale*100)}%")
        if self.offset_x != 0 or self.offset_y != 0:
            tags.append(f"POS:({self.offset_x},{self.offset_y})")
        if self.ai_upscale:
            tags.append("AI-HD")
        if self.transparent_bg:
            tags.append("CUTOUT")
        return (" [" + " ".join(tags) + "]") if tags else ""


def ai_super_res_upscale(img: np.ndarray, factor: int = 2) -> np.ndarray:
    """AI-grade Super-Resolution & Detail Reconstruction Pipeline."""
    if img is None:
        return None
    has_alpha = (img.ndim == 3 and img.shape[2] == 4)
    if has_alpha:
        bgr = img[:, :, :3]
        alpha = img[:, :, 3]
    else:
        bgr = img

    h, w = bgr.shape[:2]
    new_w, new_h = int(w * factor), int(h * factor)

    upscaled = cv2.resize(bgr, (new_w, new_h), interpolation=cv2.INTER_LANCZOS4)
    clean = cv2.bilateralFilter(upscaled, d=5, sigmaColor=35, sigmaSpace=35)
    blur = cv2.GaussianBlur(clean, (0, 0), 1.6)
    sharp = cv2.addWeighted(clean, 1.55, blur, -0.55, 0)

    lab = cv2.cvtColor(sharp, cv2.COLOR_BGR2LAB)
    l, a, b_ch = cv2.split(lab)
    clahe = cv2.createCLAHE(clipLimit=1.6, tileGridSize=(8, 8))
    l_enh = clahe.apply(l)
    enhanced_bgr = cv2.cvtColor(cv2.merge([l_enh, a, b_ch]), cv2.COLOR_LAB2BGR)

    if has_alpha:
        up_alpha = cv2.resize(alpha, (new_w, new_h), interpolation=cv2.INTER_LANCZOS4)
        return cv2.merge([enhanced_bgr[:, :, 0], enhanced_bgr[:, :, 1], enhanced_bgr[:, :, 2], up_alpha])
    return enhanced_bgr


_CHECKER_CACHE = {}


def make_checkerboard(h: int, w: int, tile: int = 20) -> np.ndarray:
    key = (h, w, tile)
    if key not in _CHECKER_CACHE:
        if len(_CHECKER_CACHE) > 8:
            _CHECKER_CACHE.clear()
        y_idx = (np.arange(h) // tile)[:, None]
        x_idx = (np.arange(w) // tile)[None, :]
        pattern = ((x_idx + y_idx) % 2 == 0)
        board = np.where(pattern[..., None], 195, 115).astype(np.uint8)
        _CHECKER_CACHE[key] = np.repeat(board, 3, axis=2)
    return _CHECKER_CACHE[key]


def to_bgra(img: np.ndarray) -> np.ndarray:
    if img.ndim == 2:
        return cv2.cvtColor(img, cv2.COLOR_GRAY2BGRA)
    if img.shape[2] == 3:
        return cv2.cvtColor(img, cv2.COLOR_BGR2BGRA)
    return img


def apply_transform_pipeline(
    img_bgr_or_bgra: np.ndarray,
    params: TransformParams,
    canvas_size: tuple[int, int] = None,
    for_preview_checkerboard: bool = True
) -> tuple[np.ndarray, np.ndarray]:
    if img_bgr_or_bgra is None:
        return None, None

    has_alpha = img_bgr_or_bgra.ndim == 3 and img_bgr_or_bgra.shape[2] == 4
    cur_h0, cur_w0 = img_bgr_or_bgra.shape[:2]
    # Fast path: nothing to move and no transparency — skip the warp entirely
    if params.is_identity() and not has_alpha and (canvas_size is None or tuple(canvas_size) == (cur_w0, cur_h0)):
        return img_bgr_or_bgra, None

    bgra = to_bgra(img_bgr_or_bgra) if not has_alpha else img_bgr_or_bgra

    steps = params.rot_90_steps % 4
    if steps == 1:
        bgra = cv2.rotate(bgra, cv2.ROTATE_90_CLOCKWISE)
    elif steps == 2:
        bgra = cv2.rotate(bgra, cv2.ROTATE_180)
    elif steps == 3:
        bgra = cv2.rotate(bgra, cv2.ROTATE_90_COUNTERCLOCKWISE)

    if params.flip_h and params.flip_v:
        bgra = cv2.flip(bgra, -1)
    elif params.flip_h:
        bgra = cv2.flip(bgra, 1)
    elif params.flip_v:
        bgra = cv2.flip(bgra, 0)

    cur_h, cur_w = bgra.shape[:2]
    target_w, target_h = canvas_size if canvas_size else (cur_w, cur_h)

    center = (cur_w / 2.0, cur_h / 2.0)
    M = cv2.getRotationMatrix2D(center, -params.free_angle, params.scale)
    M[0, 2] += (target_w / 2.0 - center[0]) + params.offset_x
    M[1, 2] += (target_h / 2.0 - center[1]) + params.offset_y

    warped_bgra = cv2.warpAffine(
        bgra, M, (target_w, target_h),
        flags=cv2.INTER_LINEAR,
        borderMode=cv2.BORDER_CONSTANT,
        borderValue=(0, 0, 0, 0)
    )

    alpha = warped_bgra[:, :, 3]
    fg_bgr = warped_bgra[:, :, :3]
    if params.bg_replacement is not None:
        under = cv2.resize(params.bg_replacement, (target_w, target_h), interpolation=cv2.INTER_AREA)
    elif for_preview_checkerboard:
        under = make_checkerboard(target_h, target_w)
    else:
        under = np.zeros_like(fg_bgr)
    if alpha.min() == 255:
        comp_bgr = fg_bgr.copy()
    else:
        a = (alpha.astype(np.float32) / 255.0)[..., None]
        comp_bgr = (fg_bgr.astype(np.float32) * a + under.astype(np.float32) * (1.0 - a)).astype(np.uint8)

    return comp_bgr, warped_bgra


# ==============================================================================
# COLOR GRADING & FILTER ENGINE (shared by Video clips and Photos)
# ==============================================================================
FILTER_PRESETS = [
    ("none", "Original"), ("vivid", "Vivid"), ("cinematic", "Cinematic"), ("warm", "Warm Sun"),
    ("cool", "Cool Blue"), ("vintage", "Vintage"), ("fade", "Matte Fade"), ("bw", "B&W"),
    ("noir", "Noir"), ("sepia", "Sepia"),
]


class ColorParams:
    """Non-destructive color grade: -100..100 sliders, 0..100 sharpen/vignette, plus a filter look."""
    FIELDS = ("brightness", "contrast", "saturation", "warmth", "tint", "highlights", "shadows", "sharpness", "vignette")

    def __init__(self):
        for f in self.FIELDS:
            setattr(self, f, 0)
        self.filter = "none"

    def clone(self):
        c = ColorParams()
        for f in self.FIELDS:
            setattr(c, f, getattr(self, f))
        c.filter = self.filter
        return c

    def is_identity(self) -> bool:
        return self.filter == "none" and all(getattr(self, f) == 0 for f in self.FIELDS)

    def key(self):
        return tuple(getattr(self, f) for f in self.FIELDS) + (self.filter,)

    def summary_tag(self) -> str:
        if self.is_identity():
            return ""
        return " [COLOR" + (f":{self.filter.upper()}" if self.filter != "none" else "") + "]"


_LUT_CACHE = {}
_VIGNETTE_CACHE = {}


def _tone_luts(cp: ColorParams):
    key = cp.key()
    if key in _LUT_CACHE:
        return _LUT_CACHE[key]
    x = np.arange(256, dtype=np.float32) / 255.0
    y = x + cp.brightness / 250.0
    c = 1.0 + cp.contrast / 100.0
    y = (y - 0.5) * c + 0.5
    if cp.shadows:
        y = y + (cp.shadows / 220.0) * (1.0 - y) ** 2 * (y < 0.6)
    if cp.highlights:
        y = y + (cp.highlights / 220.0) * (y ** 2) * (y > 0.4)
    look = cp.filter
    if look == "fade":
        y = 0.08 + y * 0.86
    elif look == "vintage":
        y = 0.05 + y * 0.9
    elif look in ("cinematic", "noir"):
        y = np.clip(y, 0, 1)
        y = y * y * (3 - 2 * y) * 0.6 + y * 0.4  # S-curve
    lut_b = y - cp.warmth / 400.0 + cp.tint / 800.0
    lut_g = y - cp.tint / 400.0
    lut_r = y + cp.warmth / 400.0 + cp.tint / 800.0
    if look == "warm":
        lut_r, lut_b = lut_r + 0.06, lut_b - 0.05
    elif look == "cool":
        lut_r, lut_b = lut_r - 0.05, lut_b + 0.07
    elif look == "cinematic":
        lut_b = lut_b + 0.06 * (1 - x) - 0.03 * x   # teal shadows
        lut_r = lut_r + 0.05 * x - 0.02 * (1 - x)   # orange highlights
    elif look == "vintage":
        lut_r, lut_g, lut_b = lut_r + 0.04, lut_g + 0.02, lut_b - 0.06
    luts = [np.clip(v * 255.0, 0, 255).astype(np.uint8) for v in (lut_b, lut_g, lut_r)]
    if len(_LUT_CACHE) > 64:
        _LUT_CACHE.clear()
    _LUT_CACHE[key] = luts
    return luts


def _vignette_mask(h: int, w: int, strength: int) -> np.ndarray:
    key = (h, w, strength)
    if key not in _VIGNETTE_CACHE:
        if len(_VIGNETTE_CACHE) > 8:
            _VIGNETTE_CACHE.clear()
        yy, xx = np.mgrid[0:h, 0:w].astype(np.float32)
        d = np.sqrt(((xx - w / 2) / (w / 2)) ** 2 + ((yy - h / 2) / (h / 2)) ** 2) / math.sqrt(2)
        _VIGNETTE_CACHE[key] = (1.0 - (strength / 100.0) * np.clip(d, 0, 1) ** 2.2)[..., None].astype(np.float32)
    return _VIGNETTE_CACHE[key]


def apply_color(img: np.ndarray, cp: ColorParams) -> np.ndarray:
    """Applies the grade to a BGR or BGRA image (alpha untouched). Fast: LUTs + vectorised mixes."""
    if img is None or cp is None or cp.is_identity():
        return img
    alpha = img[:, :, 3] if img.shape[2] == 4 else None
    bgr = img[:, :, :3]
    lb, lg, lr = _tone_luts(cp)
    b, g, r = cv2.split(bgr)
    out = cv2.merge([cv2.LUT(b, lb), cv2.LUT(g, lg), cv2.LUT(r, lr)])

    sat = 1.0 + cp.saturation / 100.0
    look = cp.filter
    if look == "vivid":
        sat *= 1.35
    elif look in ("vintage", "fade"):
        sat *= 0.8
    elif look == "cinematic":
        sat *= 0.92
    elif look in ("bw", "noir", "sepia"):
        sat = 0.0
    if abs(sat - 1.0) > 1e-3:
        gray = cv2.cvtColor(cv2.cvtColor(out, cv2.COLOR_BGR2GRAY), cv2.COLOR_GRAY2BGR)
        out = cv2.addWeighted(out, sat, gray, 1.0 - sat, 0)
    if look == "sepia":
        out = cv2.transform(out, np.array([[0.131, 0.534, 0.272], [0.168, 0.686, 0.349], [0.189, 0.769, 0.393]], np.float32))
    elif look == "noir":
        out = cv2.convertScaleAbs(out, alpha=1.25, beta=-30)

    if cp.sharpness > 0:
        blur = cv2.GaussianBlur(out, (0, 0), 1.2)
        k = cp.sharpness / 60.0
        out = cv2.addWeighted(out, 1.0 + k, blur, -k, 0)
    vig = cp.vignette + (35 if look in ("cinematic", "noir", "vintage") else 0)
    if vig > 0:
        h, w = out.shape[:2]
        out = (out.astype(np.float32) * _vignette_mask(h, w, min(100, vig))).astype(np.uint8)
    if alpha is not None:
        out = cv2.merge([out[:, :, 0], out[:, :, 1], out[:, :, 2], alpha])
    return out


def auto_enhance(bgr: np.ndarray) -> np.ndarray:
    """One-click enhance: gray-world white balance + local contrast (CLAHE) + gentle saturation."""
    img = bgr.astype(np.float32)
    means = img.reshape(-1, 3).mean(axis=0) + 1e-6
    img *= (means.mean() / means)[None, None, :] * 0.5 + 0.5
    img = np.clip(img, 0, 255).astype(np.uint8)
    lab = cv2.cvtColor(img, cv2.COLOR_BGR2LAB)
    l, a, b = cv2.split(lab)
    l = cv2.createCLAHE(clipLimit=2.0, tileGridSize=(8, 8)).apply(l)
    out = cv2.cvtColor(cv2.merge([l, a, b]), cv2.COLOR_LAB2BGR)
    gray = cv2.cvtColor(cv2.cvtColor(out, cv2.COLOR_BGR2GRAY), cv2.COLOR_GRAY2BGR)
    return cv2.addWeighted(out, 1.12, gray, -0.12, 0)


# ==============================================================================
# TEXT / TITLE OVERLAY ENGINE (Qt font rendering, outlined text, optional backdrop)
# ==============================================================================
class TextOverlay:
    POSITIONS = ("bottom", "center", "top")

    def __init__(self):
        self.text = ""
        self.size_pct = 7          # text height as % of frame height
        self.color = "#FFFFFF"
        self.position = "bottom"
        self.outline = True
        self.backdrop = False

    def clone(self):
        t = TextOverlay()
        t.__dict__.update(self.__dict__)
        return t

    def active(self) -> bool:
        return bool(self.text.strip())

    def key(self, w, h):
        return (self.text, self.size_pct, self.color, self.position, self.outline, self.backdrop, w, h)


_TEXT_CACHE = {}


def render_text_layer(w: int, h: int, ov: TextOverlay) -> np.ndarray:
    """Returns a BGRA layer (w x h) with the overlay text, cached per settings and size."""
    key = ov.key(w, h)
    if key in _TEXT_CACHE:
        return _TEXT_CACHE[key]
    img = QImage(w, h, QImage.Format.Format_ARGB32)
    img.fill(Qt.GlobalColor.transparent)
    p = QPainter(img)
    p.setRenderHint(QPainter.RenderHint.Antialiasing)
    p.setRenderHint(QPainter.RenderHint.TextAntialiasing)
    px = max(8, int(h * ov.size_pct / 100.0))
    font = QFont("Segoe UI", 10, QFont.Weight.Bold)
    font.setPixelSize(px)
    fm = QFontMetrics(font)
    lines = ov.text.split("\n")
    line_h = fm.height()
    block_h = line_h * len(lines)
    margin = int(h * 0.06)
    if ov.position == "top":
        y0 = margin
    elif ov.position == "center":
        y0 = (h - block_h) // 2
    else:
        y0 = h - margin - block_h
    if ov.backdrop:
        bw = max(fm.horizontalAdvance(ln) for ln in lines) + px
        p.setPen(Qt.PenStyle.NoPen)
        p.setBrush(QColor(0, 0, 0, 150))
        p.drawRoundedRect(QRectF((w - bw) / 2, y0 - px * 0.2, bw, block_h + px * 0.4), px * 0.3, px * 0.3)
    for i, ln in enumerate(lines):
        tw = fm.horizontalAdvance(ln)
        path = QPainterPath()
        path.addText(QPointF((w - tw) / 2, y0 + i * line_h + fm.ascent()), font, ln)
        if ov.outline:
            pen = QPen(QColor(0, 0, 0, 220), max(2.0, px * 0.09))
            pen.setJoinStyle(Qt.PenJoinStyle.RoundJoin)
            p.strokePath(path, pen)
        p.fillPath(path, QColor(ov.color))
    p.end()
    ptr = img.constBits()
    ptr.setsize(img.sizeInBytes())
    arr = np.frombuffer(ptr, np.uint8).reshape(h, img.bytesPerLine() // 4, 4)[:, :w].copy()
    if len(_TEXT_CACHE) > 32:
        _TEXT_CACHE.clear()
    _TEXT_CACHE[key] = arr
    return arr


def composite_bgra_over(bgr: np.ndarray, layer: np.ndarray) -> np.ndarray:
    a = layer[:, :, 3:4].astype(np.float32) / 255.0
    if not a.any():
        return bgr
    return (bgr.astype(np.float32) * (1 - a) + layer[:, :, :3].astype(np.float32) * a).astype(np.uint8)


def fit_into_frame(img: np.ndarray, out_w: int, out_h: int, mode: str = "fit") -> np.ndarray:
    """Places a frame into an output size: 'fit' (black bars), 'blur' (blurred fill like TikTok) or 'fill' (crop)."""
    h, w = img.shape[:2]
    if (w, h) == (out_w, out_h):
        return img
    if mode == "fill":
        s = max(out_w / w, out_h / h)
        nw, nh = max(1, int(round(w * s))), max(1, int(round(h * s)))
        big = cv2.resize(img, (nw, nh), interpolation=cv2.INTER_AREA if s < 1 else cv2.INTER_LINEAR)
        x0, y0 = (nw - out_w) // 2, (nh - out_h) // 2
        return big[y0:y0 + out_h, x0:x0 + out_w]
    s = min(out_w / w, out_h / h)
    nw, nh = max(1, int(round(w * s))), max(1, int(round(h * s)))
    fg = cv2.resize(img, (nw, nh), interpolation=cv2.INTER_AREA if s < 1 else cv2.INTER_LINEAR)
    if mode == "blur":
        # Blur and darken at 1/8 size, then one upscale (the background is soft anyway)
        bg = fit_into_frame(img, max(1, out_w // 8), max(1, out_h // 8), "fill")
        bg = cv2.convertScaleAbs(cv2.GaussianBlur(bg[:, :, :3], (0, 0), 2.5), alpha=0.6)
        canvas = cv2.resize(bg, (out_w, out_h), interpolation=cv2.INTER_LINEAR)
    else:
        canvas = np.zeros((out_h, out_w, 3), np.uint8)
    x0, y0 = (out_w - nw) // 2, (out_h - nh) // 2
    canvas[y0:y0 + nh, x0:x0 + nw] = fg[:, :, :3]
    return canvas


# ==============================================================================
# FAST FRAME READER — decodes forward instead of seeking for every frame
# ==============================================================================
class FrameReader:
    def __init__(self, path: str, fps: float):
        self.cap = cv2.VideoCapture(path)
        self.fps = fps if fps and fps > 0 else 30.0
        self.next_idx = 0
        self.last_idx = -1
        self.last_frame = None

    def frame_at_ms(self, ms: float):
        idx = max(0, int(ms * self.fps / 1000.0 + 1e-6))
        if idx == self.last_idx and self.last_frame is not None:
            return self.last_frame
        if idx < self.next_idx or idx - self.next_idx > int(self.fps * 2):
            self.cap.set(cv2.CAP_PROP_POS_FRAMES, idx)
            self.next_idx = idx
        while self.next_idx < idx:
            if not self.cap.grab():
                break
            self.next_idx += 1
        ok, frame = self.cap.read()
        self.next_idx += 1
        if ok and frame is not None:
            self.last_idx, self.last_frame = idx, frame
            return frame
        return self.last_frame

    def release(self):
        self.cap.release()


# ==============================================================================
# v3 ENGINES: LAYERS, MUSIC, SUBTITLES, TRANSITIONS, MOTION, COMPOSITOR, AI TOOLS
# ==============================================================================
import json
import importlib.util
from collections import OrderedDict

APP_DIR = os.path.dirname(os.path.abspath(__file__))
TRANSITION_TYPES = [("none", "None (hard cut)"), ("crossfade", "Crossfade"), ("black", "Dip to Black"),
                    ("white", "Flash to White"), ("slide", "Slide Left"), ("zoom", "Zoom Blend")]
MOTION_TYPES = [("none", "None"), ("zoom_in", "Slow Zoom In"), ("zoom_out", "Slow Zoom Out"),
                ("pan_right", "Pan Right"), ("pan_left", "Pan Left")]
OUTPUT_PRESETS = [
    # (title, size or None=source, fps or None=source, framing, recommended max seconds)
    ("Custom", None, None, None, None),
    ("TikTok  (9:16 · 1080×1920)", (1080, 1920), 30, "smart", 600),
    ("Instagram Reels  (9:16)", (1080, 1920), 30, "smart", 180),
    ("YouTube Shorts  (9:16)", (1080, 1920), 30, "smart", 180),
    ("YouTube  (16:9 · 1080p)", (1920, 1080), None, "blur", None),
    ("Instagram Post  (4:5)", (1080, 1350), 30, "blur", 60),
    ("Square  (1:1)", (1080, 1080), 30, "blur", None),
]


def has_module(name: str) -> bool:
    try:
        return importlib.util.find_spec(name) is not None
    except Exception:
        return False


def cache_dir() -> str:
    base = os.environ.get("LOCALAPPDATA") or os.path.join(os.path.expanduser("~"), ".cache")
    d = os.path.join(base, "ANK_Media_Studio")
    os.makedirs(d, exist_ok=True)
    return d


def load_image_bgra(path: str):
    try:
        img = cv2.imdecode(np.fromfile(path, dtype=np.uint8), cv2.IMREAD_UNCHANGED)
    except Exception:
        return None
    if img is None:
        return None
    if img.dtype != np.uint8:
        img = cv2.convertScaleAbs(img, alpha=255.0 / max(1.0, float(img.max())))
    return to_bgra(img)


def alpha_blit(dst_bgr: np.ndarray, src_bgra: np.ndarray, cx: float, cy: float, opacity: float = 1.0, dst_alpha=None):
    """Pastes a BGRA image centred at (cx, cy) pixels, clipped to the frame, with opacity."""
    H, W = dst_bgr.shape[:2]
    h, w = src_bgra.shape[:2]
    x0, y0 = int(round(cx - w / 2)), int(round(cy - h / 2))
    sx0, sy0 = max(0, -x0), max(0, -y0)
    dx0, dy0 = max(0, x0), max(0, y0)
    dx1, dy1 = min(W, x0 + w), min(H, y0 + h)
    if dx1 <= dx0 or dy1 <= dy0:
        return dst_bgr
    src = src_bgra[sy0:sy0 + (dy1 - dy0), sx0:sx0 + (dx1 - dx0)]
    a = (src[:, :, 3:4].astype(np.float32) / 255.0) * float(opacity)
    region = dst_bgr[dy0:dy1, dx0:dx1].astype(np.float32)
    dst_bgr[dy0:dy1, dx0:dx1] = (region * (1 - a) + src[:, :, :3].astype(np.float32) * a).astype(np.uint8)
    if dst_alpha is not None:
        reg_a = dst_alpha[dy0:dy1, dx0:dx1].astype(np.float32)
        dst_alpha[dy0:dy1, dx0:dx1] = np.maximum(reg_a, a[:, :, 0] * 255.0).astype(np.uint8)
    return dst_bgr


# --- Overlay layers (logo, watermark, picture-in-picture video) ---
class OverlayItem:
    POSITIONS = {"Top Left": (0.14, 0.12), "Top Right": (0.86, 0.12), "Bottom Left": (0.14, 0.86),
                 "Bottom Right": (0.86, 0.86), "Center": (0.5, 0.5)}

    def __init__(self, path: str = ""):
        self.path = path
        self.kind = "video" if os.path.splitext(path)[1].lower() in VIDEO_EXTS else "image"
        self.start_ms = 0
        self.end_ms = None          # None = until the end
        self.cx, self.cy = 0.86, 0.12
        self.width_pct = 22.0
        self.opacity = 1.0
        self._img = None
        self._scaled = {}

    @property
    def name(self):
        return os.path.basename(self.path)

    def active(self, t_ms: int) -> bool:
        return t_ms >= self.start_ms and (self.end_ms is None or t_ms < self.end_ms)

    def image_bgra(self):
        if self._img is None and self.kind == "image":
            self._img = load_image_bgra(self.path)
        return self._img

    def scaled_for(self, img: np.ndarray, frame_w: int) -> np.ndarray:
        tw = max(4, int(frame_w * self.width_pct / 100.0))
        th = max(4, int(img.shape[0] * tw / img.shape[1]))
        return cv2.resize(img, (tw, th), interpolation=cv2.INTER_AREA if tw < img.shape[1] else cv2.INTER_LINEAR)

    def to_dict(self):
        return {"path": self.path, "start_ms": self.start_ms, "end_ms": self.end_ms, "cx": self.cx, "cy": self.cy,
                "width_pct": self.width_pct, "opacity": self.opacity}

    @staticmethod
    def from_dict(d):
        o = OverlayItem(d["path"])
        for k in ("start_ms", "end_ms", "cx", "cy", "width_pct", "opacity"):
            setattr(o, k, d.get(k, getattr(o, k)))
        return o

    def clone(self):
        c = OverlayItem.from_dict(self.to_dict())
        c._img = self._img
        return c


# --- Background music track with auto-ducking under voices ---
class MusicTrack:
    def __init__(self, path: str = ""):
        self.path = path
        self.start_ms = 0
        self.volume = 0.6
        self.loop = True
        self.duck = 0.3            # music level while someone speaks (1.0 = no ducking)
        self.fade_in_ms = 1000
        self.fade_out_ms = 2000
        self._audio = None         # (sr, float stereo)

    @property
    def name(self):
        return os.path.basename(self.path)

    def audio(self):
        if self._audio is None and self.path:
            tmp = os.path.join(tempfile.gettempdir(), f"ank_music_{os.getpid()}.wav")
            if AudioStemProcessor.extract_wav(self.path, tmp):
                try:
                    self._audio = read_wav_float(tmp)
                finally:
                    try:
                        os.remove(tmp)
                    except OSError:
                        pass
        return self._audio

    def to_dict(self):
        return {k: getattr(self, k) for k in ("path", "start_ms", "volume", "loop", "duck", "fade_in_ms", "fade_out_ms")}

    @staticmethod
    def from_dict(d):
        m = MusicTrack(d.get("path", ""))
        for k, v in d.items():
            if hasattr(m, k) and not k.startswith("_"):
                setattr(m, k, v)
        return m

    def clone(self):
        c = MusicTrack.from_dict(self.to_dict())
        c._audio = self._audio
        return c


# --- Subtitles ---
def format_srt_time(ms: int) -> str:
    ms = max(0, int(ms))
    return f"{ms // 3600000:02d}:{(ms // 60000) % 60:02d}:{(ms // 1000) % 60:02d},{ms % 1000:03d}"


def subtitles_to_srt(cues) -> str:
    return "\n".join(f"{i}\n{format_srt_time(c['start'])} --> {format_srt_time(c['end'])}\n{c['text'].strip()}\n"
                     for i, c in enumerate(cues, 1))


def parse_srt(text: str):
    cues = []
    pat = re.compile(r"((?:\d{1,2}:)?\d{1,2}:\d{2}[,\.]\d{1,3})\s*-->\s*((?:\d{1,2}:)?\d{1,2}:\d{2}[,\.]\d{1,3})")

    def to_ms(t):
        t = t.replace(",", ".")
        parts = t.split(":")
        sec = float(parts[-1])
        mins = int(parts[-2]) if len(parts) >= 2 else 0
        hrs = int(parts[-3]) if len(parts) >= 3 else 0
        return int(round((hrs * 3600 + mins * 60 + sec) * 1000))
    for block in re.split(r"\n\s*\n", text.replace("\r\n", "\n").replace("\r", "\n").strip()):
        lines = [ln for ln in block.split("\n") if ln.strip()]
        for i, ln in enumerate(lines):
            m = pat.search(ln)
            if m:
                body = "\n".join(lines[i + 1:]).strip()
                if body:
                    cues.append({"start": to_ms(m.group(1)), "end": to_ms(m.group(2)), "text": body})
                break
    return sorted(cues, key=lambda c: c["start"])


def subtitle_at(cues, t_ms: int):
    for c in cues:
        if c["start"] <= t_ms < c["end"]:
            return c
    return None


WHISPER_LANGS = [("auto", "Auto-detect"), ("en", "English"), ("ar", "Arabic"), ("zh", "Chinese"), ("ko", "Korean"),
                 ("ja", "Japanese"), ("es", "Spanish"), ("fr", "French"), ("de", "German"), ("tr", "Turkish"),
                 ("hi", "Hindi"), ("ru", "Russian"), ("pt", "Portuguese"), ("it", "Italian"), ("th", "Thai"),
                 ("id", "Indonesian"), ("vi", "Vietnamese"), ("fa", "Persian"), ("ur", "Urdu")]


def whisper_engine_name() -> str:
    if has_module("faster_whisper"):
        return "faster-whisper"
    if has_module("whisper"):
        return "openai-whisper"
    return ""


def transcribe_audio(wav_path: str, model_size="small", language="auto", task="transcribe", progress=None, cancel=None):
    """Speech-to-text with timestamps. Returns [{'start','end','text'}] in ms. Runs fully on this computer."""
    engine = whisper_engine_name()
    lang = None if language == "auto" else language
    cues = []
    if engine == "faster-whisper":
        from faster_whisper import WhisperModel
        try:
            model = WhisperModel(model_size, device="auto", compute_type="auto")
        except Exception:
            model = WhisperModel(model_size, device="cpu", compute_type="int8")
        # Pass decoded samples (16 kHz mono) so faster-whisper never needs its own PyAV decoder,
        # which breaks with some PyAV versions ("unexpected keyword argument 'metadata_errors'")
        sr, audio = read_wav_float(wav_path)
        mono = audio.mean(axis=1).astype(np.float32)
        if sr != 16000:
            mono = np.interp(np.linspace(0, len(mono) - 1, int(len(mono) * 16000 / sr)), np.arange(len(mono)), mono).astype(np.float32)
        segments, info = model.transcribe(mono, language=lang, task=task, vad_filter=True, beam_size=5)
        total = max(1.0, float(getattr(info, "duration", 0) or 1.0))
        for seg in segments:
            if cancel and cancel():
                break
            text = seg.text.strip()
            if text:
                cues.append({"start": int(seg.start * 1000), "end": int(seg.end * 1000), "text": text})
            if progress:
                progress(min(1.0, seg.end / total), len(cues))
    elif engine == "openai-whisper":
        import whisper
        model = whisper.load_model(model_size)
        res = model.transcribe(wav_path, language=lang, task=task)
        for seg in res.get("segments", []):
            text = seg["text"].strip()
            if text:
                cues.append({"start": int(seg["start"] * 1000), "end": int(seg["end"] * 1000), "text": text})
        if progress:
            progress(1.0, len(cues))
    else:
        raise RuntimeError("No speech-to-text engine installed.\n\nInstall one with:\n    pip install faster-whisper")
    return split_long_cues(cues)


def split_long_cues(cues, max_chars=42):
    """Breaks long lines into two-line subtitles that are easy to read on phones."""
    out = []
    for c in cues:
        words = c["text"].split()
        if len(c["text"]) <= max_chars * 2:
            lines, cur = [], ""
            for w in words:
                if len(cur) + len(w) + 1 > max_chars and cur:
                    lines.append(cur)
                    cur = w
                else:
                    cur = f"{cur} {w}".strip()
            lines.append(cur)
            out.append({**c, "text": "\n".join(lines[:2]) + (" " + " ".join(lines[2:]) if len(lines) > 2 else "")})
            continue
        chunks, cur = [], []
        for w in words:
            cur.append(w)
            if len(" ".join(cur)) >= max_chars * 2:
                chunks.append(" ".join(cur))
                cur = []
        if cur:
            chunks.append(" ".join(cur))
        span = (c["end"] - c["start"]) / max(1, len(chunks))
        for i, ch in enumerate(chunks):
            out.extend(split_long_cues([{"start": int(c["start"] + i * span), "end": int(c["start"] + (i + 1) * span), "text": ch}], max_chars))
    return out


def argos_languages():
    if not has_module("argostranslate"):
        return []
    try:
        from argostranslate import translate as at
        return [(l.code, l.name) for l in at.get_installed_languages()]
    except Exception:
        return []


def translate_cues(cues, src: str, dst: str):
    from argostranslate import translate as at
    langs = {l.code: l for l in at.get_installed_languages()}
    if src not in langs or dst not in langs:
        raise RuntimeError(f"Language pack {src} → {dst} is not installed in Argos Translate.")
    tr = langs[src].get_translation(langs[dst])
    return [{**c, "text": tr.translate(c["text"])} for c in cues]


# --- Demucs AI stem separation ---
def demucs_available() -> bool:
    return has_module("demucs")


def demucs_separate(wav_path: str, sr: int, progress=None, cancel=None):
    """Runs Demucs (htdemucs, vocals vs. everything else) in a child process. Returns (vocals, accompaniment)."""
    out_dir = tempfile.mkdtemp(prefix="ank_demucs_")
    cmd = [sys.executable, "-m", "demucs", "--two-stems", "vocals", "-n", "htdemucs", "-o", out_dir, wav_path]
    proc = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, creationflags=NO_WINDOW)
    buf = b""
    try:
        while True:
            ch = proc.stdout.read(64)
            if not ch:
                break
            buf = (buf + ch)[-400:]
            m = re.findall(rb"(\d{1,3})%\|", buf)
            if m and progress:
                progress(min(1.0, int(m[-1]) / 100.0))
            if cancel and cancel():
                proc.kill()
                raise RuntimeError("Cancelled")
        proc.wait()
        if proc.returncode != 0:
            raise RuntimeError("Demucs failed:\n" + buf.decode("utf-8", "ignore")[-600:])
        stem = os.path.splitext(os.path.basename(wav_path))[0]
        base = os.path.join(out_dir, "htdemucs", stem)
        _, vocals = read_wav_float(os.path.join(base, "vocals.wav"))
        _, rest = read_wav_float(os.path.join(base, "no_vocals.wav"))
        return vocals, rest
    finally:
        shutil.rmtree(out_dir, ignore_errors=True)


# --- Real-ESRGAN (optional ncnn executable) ---
def find_realesrgan(custom: str = ""):
    names = ["realesrgan-ncnn-vulkan.exe", "realesrgan-ncnn-vulkan"]
    for cand in ([custom] if custom else []) + [os.path.join(APP_DIR, n) for n in names] + \
            [os.path.join(APP_DIR, "realesrgan", n) for n in names]:
        if cand and os.path.isfile(cand):
            return cand
    for n in names:
        p = shutil.which(n)
        if p:
            return p
    return None


def realesrgan_upscale(exe: str, bgr: np.ndarray, scale: int = 4, anime: bool = False) -> np.ndarray:
    tmp = tempfile.mkdtemp(prefix="ank_esr_")
    try:
        src, dst = os.path.join(tmp, "in.png"), os.path.join(tmp, "out.png")
        cv2.imwrite(src, bgr)
        model = "realesrgan-x4plus-anime" if anime else "realesrgan-x4plus"
        res = run_quiet([exe, "-i", src, "-o", dst, "-s", str(scale), "-n", model], cwd=os.path.dirname(exe))
        out = cv2.imread(dst, cv2.IMREAD_COLOR)
        if res.returncode != 0 or out is None:
            raise RuntimeError(res.stderr.decode("utf-8", "ignore")[-400:] or "Real-ESRGAN failed")
        return out
    finally:
        shutil.rmtree(tmp, ignore_errors=True)


# --- Face tracking for smart vertical reframing ---
_FACE_CASCADE = None


def _face_cascade():
    global _FACE_CASCADE
    if _FACE_CASCADE is None:
        try:
            path = os.path.join(cv2.data.haarcascades, "haarcascade_frontalface_default.xml")
            c = cv2.CascadeClassifier(path)
            _FACE_CASCADE = c if not c.empty() else False
        except Exception:
            _FACE_CASCADE = False
    return _FACE_CASCADE or None


def compute_face_track(path: str, fps: float, duration_ms: int, sample_fps: float = 4.0, cancel=None):
    """Horizontal centre of the main face over time (0..1), smoothed so the camera glides instead of jumping."""
    cascade = _face_cascade()
    times, xs = [], []
    if cascade is None or duration_ms <= 0:
        return np.array([0, max(1, duration_ms)]), np.array([0.5, 0.5])
    reader = FrameReader(path, fps)
    step = 1000.0 / sample_fps
    last = 0.5
    t = 0.0
    while t < duration_ms:
        if cancel and cancel():
            break
        fr = reader.frame_at_ms(t)
        if fr is None:
            break
        h, w = fr.shape[:2]
        s = 320.0 / w
        g = cv2.cvtColor(cv2.resize(fr, (320, max(1, int(h * s)))), cv2.COLOR_BGR2GRAY)
        faces = cascade.detectMultiScale(g, scaleFactor=1.15, minNeighbors=5, minSize=(18, 18))
        if len(faces):
            x, y, fw, fh = max(faces, key=lambda f: f[2] * f[3])
            last = (x + fw / 2) / 320.0
        times.append(t)
        xs.append(last)
        t += step
    reader.release()
    if not xs:
        return np.array([0, max(1, duration_ms)]), np.array([0.5, 0.5])
    xs = np.array(xs, dtype=np.float32)
    k = max(1, int(sample_fps * 1.2))                     # ~1.2 s moving average
    pad = np.pad(xs, (k, k), mode="edge")
    smooth = np.convolve(pad, np.ones(2 * k + 1) / (2 * k + 1), mode="same")[k:-k]
    return np.array(times, dtype=np.float32), smooth


def smart_crop(img: np.ndarray, out_w: int, out_h: int, center_x: float) -> np.ndarray:
    """Crops to the output aspect around a horizontal centre (0..1), then scales to the output size."""
    h, w = img.shape[:2]
    target = out_w / out_h
    if w / h > target:
        cw = int(round(h * target))
        x0 = int(round(center_x * w - cw / 2))
        x0 = max(0, min(w - cw, x0))
        crop = img[:, x0:x0 + cw]
    else:
        ch = int(round(w / target))
        y0 = max(0, (h - ch) // 2)
        crop = img[y0:y0 + ch, :]
    return cv2.resize(crop, (out_w, out_h), interpolation=cv2.INTER_AREA if crop.shape[1] > out_w else cv2.INTER_LINEAR)


# --- Scene & silence detection ---
def detect_scene_cuts(path: str, fps: float, in_ms: int, out_ms: int, sensitivity: float = 0.5, progress=None, cancel=None):
    """Source times (ms) where the picture changes abruptly (hard cuts)."""
    reader = FrameReader(path, fps)
    step = 1000.0 / min(fps, 12.0)
    thr = 0.55 - 0.35 * sensitivity            # higher sensitivity → lower threshold
    prev = None
    cuts = []
    t = float(in_ms)
    span = max(1, out_ms - in_ms)
    last_cut = -1e9
    while t < out_ms:
        if cancel and cancel():
            break
        fr = reader.frame_at_ms(t)
        if fr is None:
            break
        small = cv2.resize(fr, (96, 54))
        hsv = cv2.cvtColor(small, cv2.COLOR_BGR2HSV)
        hist = cv2.calcHist([hsv], [0, 1], None, [16, 8], [0, 180, 0, 256])
        cv2.normalize(hist, hist)
        if prev is not None:
            diff = cv2.compareHist(prev, hist, cv2.HISTCMP_BHATTACHARYYA)
            if diff > thr and t - last_cut > 700:
                cuts.append(int(t))
                last_cut = t
        prev = hist
        if progress:
            progress((t - in_ms) / span)
        t += step
    reader.release()
    return cuts


def detect_silences(audio: np.ndarray, sr: int, threshold_db: float = -40.0, min_len_ms: int = 600, pad_ms: int = 150):
    """Timeline ranges (ms) quieter than threshold_db for at least min_len_ms, shrunk by pad_ms on each side."""
    win = int(sr * 0.02)
    n = len(audio) // win
    if n == 0:
        return []
    frames = audio[:n * win].reshape(n, win, 2)
    rms = np.sqrt((frames ** 2).mean(axis=(1, 2)) + 1e-12)
    db = 20 * np.log10(rms)
    quiet = db < threshold_db
    ranges, start = [], None
    for i, q in enumerate(np.append(quiet, False)):
        if q and start is None:
            start = i
        elif not q and start is not None:
            a, b = start * 20, i * 20
            if b - a >= min_len_ms:
                a2, b2 = a + pad_ms, b - pad_ms
                if b2 - a2 > 50:
                    ranges.append((a2, b2))
            start = None
    return ranges


# --- Encoders (GPU when available) ---
_ENCODERS = None
ENCODER_LABELS = [("auto", "Auto (GPU if available)"), ("libx264", "CPU — x264 (best compatibility)"),
                  ("h264_nvenc", "NVIDIA GPU (NVENC)"), ("h264_qsv", "Intel GPU (QuickSync)"), ("h264_amf", "AMD GPU (AMF)")]


def available_encoders():
    """Encoders that really work on this computer (a tiny test encode for each GPU encoder)."""
    global _ENCODERS
    if _ENCODERS is not None:
        return _ENCODERS
    found = []
    if FFMPEG_EXE:
        try:
            listed = run_quiet([FFMPEG_EXE, "-hide_banner", "-encoders"], timeout=20).stdout.decode("utf-8", "ignore")
        except Exception:
            listed = ""
        for enc in ("h264_nvenc", "h264_qsv", "h264_amf", "libx264"):
            if enc not in listed:
                continue
            if enc == "libx264":
                found.append(enc)
                continue
            try:
                r = run_quiet([FFMPEG_EXE, "-hide_banner", "-f", "lavfi", "-i", "color=c=black:s=256x256:d=0.2",
                               "-c:v", enc, "-f", "null", "-"], timeout=25)
                if r.returncode == 0:
                    found.append(enc)
            except Exception:
                pass
    _ENCODERS = found
    return found


def pick_encoder(choice: str) -> str:
    avail = available_encoders()
    if choice == "auto":
        for enc in ("h264_nvenc", "h264_qsv", "h264_amf", "libx264"):
            if enc in avail:
                return enc
        return "mpeg4"
    return choice if choice in avail else ("libx264" if "libx264" in avail else "mpeg4")


def encoder_args(enc: str, crf: int):
    if enc == "h264_nvenc":
        return ["-c:v", "h264_nvenc", "-preset", "p5", "-rc", "vbr", "-cq", str(crf), "-b:v", "0", "-pix_fmt", "yuv420p"]
    if enc == "h264_qsv":
        return ["-c:v", "h264_qsv", "-global_quality", str(crf), "-pix_fmt", "nv12"]
    if enc == "h264_amf":
        return ["-c:v", "h264_amf", "-rc", "cqp", "-qp_i", str(crf), "-qp_p", str(crf), "-pix_fmt", "yuv420p"]
    if enc == "libx264":
        return ["-c:v", "libx264", "-preset", "faster", "-crf", str(crf), "-pix_fmt", "yuv420p"]
    return ["-c:v", "mpeg4", "-q:v", "3"]


# --- Motion (Ken Burns) and transitions ---
def motion_transform(tf: "TransformParams", motion: dict, progress: float, cw: int, ch: int) -> "TransformParams":
    kind = (motion or {}).get("type", "none")
    if kind == "none":
        return tf
    a = max(0.02, min(0.6, motion.get("amount", 20) / 100.0))
    p = max(0.0, min(1.0, progress))
    p = p * p * (3 - 2 * p)                     # ease in/out
    t = tf.clone()
    if kind == "zoom_in":
        t.scale *= 1 + a * p
    elif kind == "zoom_out":
        t.scale *= 1 + a * (1 - p)
    elif kind in ("pan_right", "pan_left"):
        t.scale *= 1 + a
        d = a * cw / 2
        t.offset_x += int(d * (1 - 2 * p) * (1 if kind == "pan_right" else -1))
    return t


def blend_transition(out_img: np.ndarray, in_img: np.ndarray, w_in: float, kind: str) -> np.ndarray:
    w = max(0.0, min(1.0, w_in))
    if kind == "black" or kind == "white":
        tone = np.zeros_like(out_img) if kind == "black" else np.full_like(out_img, 255)
        return cv2.addWeighted(out_img, 1 - 2 * w, tone, 2 * w, 0) if w < 0.5 else cv2.addWeighted(in_img, 2 * w - 1, tone, 2 - 2 * w, 0)
    if kind == "slide":
        W = out_img.shape[1]
        off = int(round(w * W))
        res = np.empty_like(out_img)
        res[:, :W - off] = out_img[:, off:]
        res[:, W - off:] = in_img[:, :off]
        return res
    if kind == "zoom":
        H, W = out_img.shape[:2]
        z = 1 + 0.35 * w
        zw, zh = int(W / z), int(H / z)
        x0, y0 = (W - zw) // 2, (H - zh) // 2
        zoomed = cv2.resize(out_img[y0:y0 + zh, x0:x0 + zw], (W, H))
        return cv2.addWeighted(zoomed, 1 - w, in_img, w, 0)
    return cv2.addWeighted(out_img, 1 - w, in_img, w, 0)


# --- Clip frame processing (shared by preview, snapshots and export) ---
def process_clip_frame(frame: np.ndarray, seg, canvas_wh, preview_mode=True, scale=1.0, local_ms=None) -> np.ndarray:
    cw, ch = canvas_wh
    crop = seg.crop_rect
    tf = seg.transform
    if local_ms is not None and seg.motion.get("type", "none") != "none":
        tf = motion_transform(tf, seg.motion, local_ms / max(1, seg.duration_ms), cw, ch)
    tw, th = max(1, int(cw * scale)), max(1, int(ch * scale))
    if scale < 0.999 or frame.shape[1] != cw or frame.shape[0] != ch:
        # Works for downscaled previews and for low-resolution proxy files alike
        frame = cv2.resize(frame, (tw, th), interpolation=cv2.INTER_AREA if frame.shape[1] > tw else cv2.INTER_LINEAR)
        if scale < 0.999:
            if crop:
                crop = tuple(int(round(v * scale)) for v in crop)
            tf = tf.scaled(scale)
        cw, ch = tw, th

    if crop:
        x, y, w, h = crop
        fh, fw = frame.shape[:2]
        frame = frame[max(0, y):min(fh, y + h), max(0, x):min(fw, x + w)]
        if frame.size == 0:
            frame = np.zeros((ch, cw, 3), np.uint8)
        frame = fit_into_frame(frame, cw, ch, "fit")

    if tf.transparent_bg:
        if HAS_REMBG:
            rgb = cv2.cvtColor(frame, cv2.COLOR_BGR2RGB)
            frame = cv2.cvtColor(np.array(rembg_remove(Image.fromarray(rgb))), cv2.COLOR_RGBA2BGRA)
        else:
            fh, fw = frame.shape[:2]
            s_gc = min(1.0, 480.0 / max(fh, fw))
            small = cv2.resize(frame, (max(1, int(fw * s_gc)), max(1, int(fh * s_gc))), interpolation=cv2.INTER_AREA)
            sh, sw = small.shape[:2]
            mask = np.zeros((sh, sw), np.uint8)
            bgd, fgd = np.zeros((1, 65), np.float64), np.zeros((1, 65), np.float64)
            cv2.grabCut(small, mask, (int(sw * 0.1), int(sh * 0.1), int(sw * 0.8), int(sh * 0.8)), bgd, fgd, 2, cv2.GC_INIT_WITH_RECT)
            alpha = np.where((mask == 2) | (mask == 0), 0, 255).astype("uint8")
            alpha = cv2.GaussianBlur(cv2.resize(alpha, (fw, fh), interpolation=cv2.INTER_LINEAR), (0, 0), 1.5)
            frame = cv2.merge([frame[:, :, 0], frame[:, :, 1], frame[:, :, 2], alpha])

    if tf.ai_upscale:
        frame = ai_super_res_upscale(frame, factor=2)
        frame = cv2.resize(frame, (cw, ch), interpolation=cv2.INTER_AREA)

    frame = apply_color(frame, seg.color)
    comp_bgr, _ = apply_transform_pipeline(frame, tf, canvas_size=(cw, ch), for_preview_checkerboard=preview_mode)
    if comp_bgr.ndim == 3 and comp_bgr.shape[2] == 4:
        comp_bgr = comp_bgr[:, :, :3]
    if seg.text.active():
        comp_bgr = composite_bgra_over(comp_bgr, render_text_layer(cw, ch, seg.text))
    if local_ms is not None and (seg.fade_in_ms > 0 or seg.fade_out_ms > 0):
        k = 1.0
        if seg.fade_in_ms > 0 and local_ms < seg.fade_in_ms:
            k = min(k, local_ms / seg.fade_in_ms)
        if seg.fade_out_ms > 0 and local_ms > seg.duration_ms - seg.fade_out_ms:
            k = min(k, (seg.duration_ms - local_ms) / seg.fade_out_ms)
        if k < 0.999:
            comp_bgr = cv2.convertScaleAbs(comp_bgr, alpha=max(0.0, k))
    return comp_bgr


# --- The timeline compositor: clips + transitions + reframing + layers + subtitles ---
class RenderContext:
    """Everything needed to draw any moment of the timeline, safe to use from a worker thread (it holds copies)."""
    def __init__(self, segments, overlays, subtitles, sub_style, burn_subs, out_w, out_h, fit_mode,
                 preview=False, use_proxies=False):
        self.segments = segments
        self.overlays = overlays
        self.subtitles = subtitles
        self.sub_style = sub_style
        self.burn_subs = burn_subs
        self.out_w, self.out_h = out_w, out_h
        self.fit_mode = fit_mode
        self.preview = preview
        self.use_proxies = use_proxies
        self.starts = []
        acc = 0
        for s in segments:
            self.starts.append(acc)
            acc += s.duration_ms
        self.total = acc
        self._readers = OrderedDict()
        self._clip_cache = {}

    def reader(self, key, path, fps):
        r = self._readers.get(key)
        if r is None:
            r = FrameReader(path, fps)
            self._readers[key] = r
            if len(self._readers) > 8:
                _, old = self._readers.popitem(last=False)
                old.release()
        else:
            self._readers.move_to_end(key)
        return r

    def release(self):
        for r in self._readers.values():
            r.release()
        self._readers.clear()

    def seg_index_at(self, t):
        for i in range(len(self.segments)):
            if t < self.starts[i] + self.segments[i].duration_ms or i == len(self.segments) - 1:
                return i
        return -1

    def clip_frame(self, i, local_ms):
        """Clip i at its own time, processed and fitted to the output size."""
        seg = self.segments[i]
        src = seg.source
        local_ms = max(0.0, min(seg.duration_ms - 1, local_ms))
        src_ms = min(seg.out_ms - 1, seg.in_ms + local_ms * seg.speed)
        path = src.proxy_path if (self.use_proxies and getattr(src, "proxy_path", None)) else src.filepath
        reader = self.reader((src.source_id, i), path, src.fps)
        frame = reader.frame_at_ms(src_ms)
        if frame is None:
            return np.zeros((self.out_h, self.out_w, 3), np.uint8)
        static = seg.fade_in_ms == 0 and seg.fade_out_ms == 0 and seg.motion.get("type", "none") == "none"
        key = (i, reader.last_idx)
        if static and key in self._clip_cache:
            return self._clip_cache[key]
        cw, ch = src.width or frame.shape[1], src.height or frame.shape[0]
        scale = min(1.0, max(self.out_w, self.out_h) / max(cw, ch)) if self.preview else 1.0
        processed = process_clip_frame(frame, seg, (cw, ch), preview_mode=False, scale=scale, local_ms=local_ms)
        if self.fit_mode == "smart" and getattr(src, "face_track", None) is not None and not seg.crop_rect:
            times, xs = src.face_track
            cx = float(np.interp(src_ms, times, xs))
            out = smart_crop(processed, self.out_w, self.out_h, cx)
        else:
            out = fit_into_frame(processed, self.out_w, self.out_h, "blur" if self.fit_mode == "smart" else self.fit_mode)
        out = np.ascontiguousarray(out)
        if static:
            if len(self._clip_cache) > 6:
                self._clip_cache.clear()
            self._clip_cache[key] = out
        return out

    def frame_at(self, t_ms: float) -> np.ndarray:
        if not self.segments:
            return np.zeros((self.out_h, self.out_w, 3), np.uint8)
        t_ms = max(0.0, min(self.total - 1, t_ms))
        i = self.seg_index_at(t_ms)
        seg = self.segments[i]
        start, end = self.starts[i], self.starts[i] + seg.duration_ms
        img = self.clip_frame(i, t_ms - start)
        # Transition into this clip (from the previous one)
        tr = seg.transition
        if i > 0 and tr.get("type", "none") != "none":
            d = max(80, tr.get("ms", 500))
            if t_ms - start < d / 2:
                prev_i = i - 1
                prev = self.clip_frame(prev_i, t_ms - self.starts[prev_i])
                img = blend_transition(prev, img, 0.5 + (t_ms - start) / d, tr["type"])
        # Transition out of this clip (into the next one)
        if i + 1 < len(self.segments):
            ntr = self.segments[i + 1].transition
            if ntr.get("type", "none") != "none":
                d = max(80, ntr.get("ms", 500))
                if end - t_ms < d / 2:
                    nxt = self.clip_frame(i + 1, 0)
                    img = blend_transition(img, nxt, 0.5 - (end - t_ms) / d, ntr["type"])
        img = img.copy()
        for k, ov in enumerate(self.overlays):
            if not ov.active(t_ms):
                continue
            if ov.kind == "image":
                src_img = ov.image_bgra()
            else:
                src_img = None
                rd = self.reader(("ov", k), ov.path, 30.0)
                fr = rd.frame_at_ms(t_ms - ov.start_ms)
                if fr is not None:
                    src_img = to_bgra(fr)
            if src_img is None:
                continue
            sc = ov.scaled_for(src_img, self.out_w)
            if ov.kind == "video":   # picture-in-picture gets a thin white frame
                cv2.rectangle(sc, (0, 0), (sc.shape[1] - 1, sc.shape[0] - 1), (255, 255, 255, 255), max(2, sc.shape[1] // 120))
            alpha_blit(img, sc, ov.cx * self.out_w, ov.cy * self.out_h, ov.opacity)
        if self.burn_subs and self.subtitles:
            cue = subtitle_at(self.subtitles, int(t_ms))
            if cue:
                st = self.sub_style.clone()
                st.text = cue["text"]
                img = composite_bgra_over(img, render_text_layer(self.out_w, self.out_h, st))
        return img


# --- Audio: clips + music with auto-ducking ---
def build_timeline_audio(segments, music: "MusicTrack" = None, keep_pitch=True, sr=44100):
    chunks = []
    any_audio = False
    for seg in segments:
        src = seg.source
        src.ensure_raw_audio()
        target_len = max(1, int(round((seg.duration_ms / 1000.0) * sr)))
        am = seg.audio_mix
        s0 = int((seg.in_ms / 1000.0) * src.sample_rate)
        s1 = int((seg.out_ms / 1000.0) * src.sample_rate)
        mixed = None
        if am.separated and src.stems_separated and src.voices_data is not None:
            src_len = max(1, s1 - s0)
            mixed = np.zeros((src_len, 2), dtype=np.float32)
            for key, data, vol in (("voices", src.voices_data, am.voices_vol), ("music", src.music_data, am.music_vol),
                                   ("noise", src.noise_data, am.noise_vol)):
                if vol <= 0.0:
                    continue
                part = data[s0:s1] * vol
                t_s = int((am.stem_trim_start.get(key, 0) * seg.speed / 1000.0) * src.sample_rate)
                t_e = int((am.stem_trim_end.get(key, 0) * seg.speed / 1000.0) * src.sample_rate)
                if t_s > 0:
                    part[:min(len(part), t_s)] = 0.0
                if t_e > 0:
                    part[max(0, len(part) - t_e):] = 0.0
                mixed[:len(part)] += part
            any_audio = True
        elif src.raw_audio is not None:
            mixed = src.raw_audio[s0:s1].copy()
            any_audio = True
        if mixed is None or len(mixed) == 0:
            chunks.append(np.zeros((target_len, 2), dtype=np.float32))
            continue
        if src.sample_rate != sr:
            # Bring the clip to the mix's sample rate before any speed change
            n_new = max(1, int(round(len(mixed) * sr / src.sample_rate)))
            pos = np.linspace(0, len(mixed) - 1, n_new)
            mixed = np.column_stack([np.interp(pos, np.arange(len(mixed)), mixed[:, c]) for c in range(2)]).astype(np.float32)
        out = time_stretch(mixed, sr, seg.speed, target_len, keep_pitch=keep_pitch)
        if abs(am.gain - 1.0) > 1e-3:
            out = out * am.gain
        fi = int(max(am.fade_in_ms, seg.fade_in_ms) * sr / 1000)
        fo = int(max(am.fade_out_ms, seg.fade_out_ms) * sr / 1000)
        if fi > 0:
            fi = min(fi, len(out))
            out[:fi] *= np.linspace(0.0, 1.0, fi, dtype=np.float32)[:, None]
        if fo > 0:
            fo = min(fo, len(out))
            out[len(out) - fo:] *= np.linspace(1.0, 0.0, fo, dtype=np.float32)[:, None]
        chunks.append(np.clip(out, -1.0, 1.0))
    if not chunks:
        return None
    clips = np.vstack(chunks).astype(np.float32)
    total = len(clips)
    if music and music.path:
        m = music.audio()
        if m is not None:
            msr, maud = m
            if msr != sr:
                maud = time_stretch(maud, sr, 1.0, int(len(maud) * sr / msr), keep_pitch=False)
            start = int(music.start_ms * sr / 1000)
            need = max(0, total - start)
            if need > 0 and len(maud):
                if music.loop and len(maud) < need:
                    maud = np.tile(maud, (need // len(maud) + 1, 1))
                track = maud[:need] * music.volume
                n = len(track)
                fi, fo = min(n, int(music.fade_in_ms * sr / 1000)), min(n, int(music.fade_out_ms * sr / 1000))
                if fi:
                    track[:fi] *= np.linspace(0, 1, fi, dtype=np.float32)[:, None]
                if fo:
                    track[n - fo:] *= np.linspace(1, 0, fo, dtype=np.float32)[:, None]
                if music.duck < 0.999 and any_audio:
                    # Auto-ducking: lower the music wherever the clips have speech/sound
                    ref = clips[start:start + n]
                    win = int(sr * 0.05)
                    nw = max(1, len(ref) // win)
                    rms = np.sqrt((ref[:nw * win].reshape(nw, win, 2) ** 2).mean(axis=(1, 2)) + 1e-12)
                    active = (20 * np.log10(rms) > -32).astype(np.float32)
                    att, rel = 0.5, 0.12             # fast attack, slower release
                    env = np.zeros_like(active)
                    cur = 0.0
                    for j, a in enumerate(active):
                        cur = cur + (a - cur) * (att if a > cur else rel)
                        env[j] = cur
                    gain = 1.0 - (1.0 - music.duck) * np.repeat(env, win)
                    gain = np.concatenate([gain, np.full(n - len(gain), gain[-1] if len(gain) else 1.0)])[:n]
                    track *= gain[:, None]
                clips[start:start + n] += track
                any_audio = True
    if not any_audio:
        return None
    return sr, np.clip(clips, -1.0, 1.0)


# --- Photo layers ---
class PhotoLayer:
    def __init__(self, kind="image", name="Layer"):
        self.kind = kind
        self.name = name
        self.bgra = None
        self.cx, self.cy = 0.5, 0.5          # centre as a fraction of the canvas
        self.width_frac = 0.35               # width as a fraction of the canvas width
        self.opacity = 1.0
        self.text = TextOverlay() if kind == "text" else None

    def clone(self):
        c = PhotoLayer(self.kind, self.name)
        c.bgra = self.bgra
        c.cx, c.cy, c.width_frac, c.opacity = self.cx, self.cy, self.width_frac, self.opacity
        c.text = self.text.clone() if self.text else None
        return c


def render_text_image(ov: "TextOverlay", px: int = 160, accent: str = None) -> np.ndarray:
    """Tight BGRA image of outlined text (for text layers and thumbnails)."""
    font = QFont("Segoe UI", 10, QFont.Weight.Black)
    font.setPixelSize(px)
    fm = QFontMetrics(font)
    lines = ov.text.split("\n")
    w = max(fm.horizontalAdvance(ln) for ln in lines) + px
    h = fm.height() * len(lines) + px // 2
    img = QImage(w, h, QImage.Format.Format_ARGB32)
    img.fill(Qt.GlobalColor.transparent)
    p = QPainter(img)
    p.setRenderHint(QPainter.RenderHint.Antialiasing)
    if ov.backdrop:
        p.setPen(Qt.PenStyle.NoPen)
        p.setBrush(QColor(0, 0, 0, 160))
        p.drawRoundedRect(QRectF(0, 0, w, h), px * 0.2, px * 0.2)
    for i, ln in enumerate(lines):
        path = QPainterPath()
        path.addText(QPointF((w - fm.horizontalAdvance(ln)) / 2, px / 4 + i * fm.height() + fm.ascent()), font, ln)
        if ov.outline:
            pen = QPen(QColor(accent or "#000000"), max(3.0, px * 0.12))
            pen.setJoinStyle(Qt.PenJoinStyle.RoundJoin)
            p.strokePath(path, pen)
        p.fillPath(path, QColor(ov.color))
    p.end()
    ptr = img.constBits()
    ptr.setsize(img.sizeInBytes())
    return np.frombuffer(ptr, np.uint8).reshape(h, img.bytesPerLine() // 4, 4)[:, :w].copy()


def composite_layers(bgr: np.ndarray, layers, alpha=None) -> np.ndarray:
    H, W = bgr.shape[:2]
    out = bgr.copy()
    for ly in layers:
        if ly.bgra is None:
            continue
        tw = max(4, int(W * ly.width_frac))
        th = max(4, int(ly.bgra.shape[0] * tw / ly.bgra.shape[1]))
        sc = cv2.resize(ly.bgra, (tw, th), interpolation=cv2.INTER_AREA if tw < ly.bgra.shape[1] else cv2.INTER_LINEAR)
        alpha_blit(out, sc, ly.cx * W, ly.cy * H, ly.opacity, alpha)
    return out


# --- yt-dlp ---
def ytdlp_command():
    if has_module("yt_dlp"):
        return [sys.executable, "-m", "yt_dlp"]
    exe = shutil.which("yt-dlp") or shutil.which("yt-dlp.exe")
    if exe:
        return [exe]
    for cand in (os.path.join(APP_DIR, "yt-dlp.exe"), os.path.join(APP_DIR, "..", "downloader", "venv", "Scripts", "yt-dlp.exe")):
        if os.path.isfile(cand):
            return [cand]
    return None



# ==============================================================================
# INTERACTIVE CANVAS (With Drag & Drop + Right-Click Context Menu Support)
# ==============================================================================
class PhotoCanvas(QLabel):
    crop_Completed = pyqtSignal(QRect)
    free_Moved = pyqtSignal(int, int)
    wheel_Scaled = pyqtSignal(float)
    files_Dropped = pyqtSignal(list)
    right_Clicked = pyqtSignal(QPoint)
    move_Started = pyqtSignal()

    def __init__(self, placeholder_text: str = "Drag & Drop Files Here or Use the Open Buttons", placeholder_icon: str = "image"):
        super().__init__()
        self.setAlignment(Qt.AlignmentFlag.AlignCenter)
        self.setMinimumSize(560, 340)
        self.setAcceptDrops(True)
        self.setSizePolicy(QSizePolicy.Policy.Expanding, QSizePolicy.Policy.Expanding)
        self.placeholder_text = placeholder_text
        self.placeholder_icon = placeholder_icon
        self._drag_hover = False
        self._update_border_style()

        self.cv_image = None
        self.brush_mask = None
        self.grabcut_mask = None
        self.display_pixmap = None
        self._scaled_cache = None   # (size, pixmap) so repaints don't rescale
        self.overlay_label = ""

        self.mode = "none"
        self.brush_size = 24
        self.drawing = False
        self.last_pt = QPoint()
        self.move_last_widget_pt = QPoint()
        self.crop_start = QPoint()
        self.crop_end = QPoint()

    def _update_border_style(self):
        if self._drag_hover:
            self.setStyleSheet("background-color: #10213d; border: 2px dashed #38BDF8; border-radius: 10px;")
        else:
            self.setStyleSheet(f"background-color: {THEME['canvas_bg']}; border: 1px solid {THEME['canvas_border']}; border-radius: 10px;")

    def dragEnterEvent(self, event):
        if event.mimeData().hasUrls():
            event.acceptProposedAction()
            self._drag_hover = True
            self._update_border_style()
            self.update()

    def dragLeaveEvent(self, event):
        self._drag_hover = False
        self._update_border_style()
        self.update()

    def dropEvent(self, event):
        self._drag_hover = False
        self._update_border_style()
        paths = [u.toLocalFile() for u in event.mimeData().urls() if os.path.isfile(u.toLocalFile())]
        if paths:
            self.files_Dropped.emit(paths)
        event.acceptProposedAction()

    def clear_image(self):
        self.cv_image = None
        self.display_pixmap = None
        self._scaled_cache = None
        self.update()

    def load_image(self, bgr_img, preserve_masks=False):
        self.cv_image = bgr_img
        h, w = self.cv_image.shape[:2]
        if not preserve_masks or self.brush_mask is None or self.brush_mask.shape[:2] != (h, w):
            self.brush_mask = np.zeros((h, w), dtype=np.uint8)
            self.grabcut_mask = np.full((h, w), cv2.GC_PR_FGD, dtype=np.uint8)
        self.update_display()

    def update_display(self):
        if self.cv_image is None:
            return
        vis = self.cv_image
        if vis.ndim == 3 and vis.shape[2] == 4:
            vis = vis[:, :, :3]
        if self.brush_mask is not None and self.brush_mask.any():
            vis = vis.copy()
            overlay = vis.copy()
            overlay[self.brush_mask == 1] = [0, 0, 255]
            overlay[self.brush_mask == 2] = [0, 255, 0]
            overlay[self.brush_mask == 3] = [255, 0, 0]
            cv2.addWeighted(overlay, 0.45, vis, 0.55, 0, vis)

        rgb = np.ascontiguousarray(cv2.cvtColor(vis, cv2.COLOR_BGR2RGB))
        h, w, ch = rgb.shape
        qimg = QImage(rgb.data, w, h, ch * w, QImage.Format.Format_RGB888)
        self.display_pixmap = QPixmap.fromImage(qimg)
        self._scaled_cache = None
        self.update()

    def _scaled(self):
        size = self.size()
        if self._scaled_cache is None or self._scaled_cache[0] != size:
            self._scaled_cache = (size, self.display_pixmap.scaled(
                size, Qt.AspectRatioMode.KeepAspectRatio, Qt.TransformationMode.SmoothTransformation))
        return self._scaled_cache[1]

    def paintEvent(self, event):
        super().paintEvent(event)
        painter = QPainter(self)
        painter.setRenderHint(QPainter.RenderHint.Antialiasing)
        if self.display_pixmap is None:
            ic = make_icon_pixmap(self.placeholder_icon, "slate", 72)
            painter.setOpacity(0.85)
            painter.drawPixmap((self.width() - 72) // 2, self.height() // 2 - 92, ic)
            painter.setOpacity(1.0)
            painter.setPen(QColor(THEME["canvas_text"]))
            painter.setFont(QFont("Segoe UI", 12, QFont.Weight.Bold))
            painter.drawText(self.rect().adjusted(20, 10, -20, 0), Qt.AlignmentFlag.AlignCenter, self.placeholder_text)
            return

        scaled = self._scaled()
        x_off = (self.width() - scaled.width()) // 2
        y_off = (self.height() - scaled.height()) // 2
        painter.drawPixmap(x_off, y_off, scaled)

        if self.overlay_label:
            painter.setFont(QFont("Segoe UI", 9, QFont.Weight.Bold))
            r = QRect(x_off + 10, y_off + 10, painter.fontMetrics().horizontalAdvance(self.overlay_label) + 16, 22)
            painter.setPen(Qt.PenStyle.NoPen)
            painter.setBrush(QColor(0, 0, 0, 160))
            painter.drawRoundedRect(r, 6, 6)
            painter.setPen(QColor("#FACC15"))
            painter.drawText(r, Qt.AlignmentFlag.AlignCenter, self.overlay_label)

        if self.mode == "crop" and not self.crop_start.isNull() and not self.crop_end.isNull():
            rect = QRect(self.crop_start, self.crop_end).normalized()
            painter.fillRect(QRect(x_off, y_off, scaled.width(), scaled.height()), QColor(0, 0, 0, 90))
            painter.drawPixmap(rect, scaled, rect.translated(-x_off, -y_off))
            pen = QPen(QColor("#00E5FF"), 2, Qt.PenStyle.DashLine)
            painter.setPen(pen)
            painter.setBrush(Qt.BrushStyle.NoBrush)
            painter.drawRect(rect)
            for i in (1, 2):  # rule-of-thirds guides
                painter.setPen(QPen(QColor(255, 255, 255, 80), 1))
                painter.drawLine(rect.left() + rect.width() * i // 3, rect.top(), rect.left() + rect.width() * i // 3, rect.bottom())
                painter.drawLine(rect.left(), rect.top() + rect.height() * i // 3, rect.right(), rect.top() + rect.height() * i // 3)
        elif self.mode == "move":
            pen = QPen(QColor("#FACC15"), 1, Qt.PenStyle.DotLine)
            painter.setPen(pen)
            painter.drawRect(QRect(x_off, y_off, scaled.width(), scaled.height()))
            painter.setPen(QColor("#FACC15"))
            painter.drawText(x_off + 10, y_off + scaled.height() - 12, "FREE MOVE: drag to position  •  mouse wheel to scale")

    def _widget_to_image_coords(self, pos: QPoint):
        if self.display_pixmap is None or self.cv_image is None:
            return None
        scaled = self._scaled()
        x_off = (self.width() - scaled.width()) // 2
        y_off = (self.height() - scaled.height()) // 2
        rel_x = pos.x() - x_off
        rel_y = pos.y() - y_off
        if rel_x < 0 or rel_y < 0 or rel_x >= scaled.width() or rel_y >= scaled.height():
            return None
        img_h, img_w = self.cv_image.shape[:2]
        ix = int(rel_x * img_w / scaled.width())
        iy = int(rel_y * img_h / scaled.height())
        return (ix, iy)

    def _widget_delta_to_image_delta(self, dpos: QPoint) -> tuple[int, int]:
        if self.display_pixmap is None or self.cv_image is None:
            return 0, 0
        scaled = self._scaled()
        if scaled.width() == 0 or scaled.height() == 0:
            return 0, 0
        img_h, img_w = self.cv_image.shape[:2]
        dx = int(dpos.x() * img_w / scaled.width())
        dy = int(dpos.y() * img_h / scaled.height())
        return dx, dy

    def mousePressEvent(self, event):
        if event.button() == Qt.MouseButton.RightButton:
            self.right_Clicked.emit(self.mapToGlobal(event.pos()))
            return
        if self.cv_image is None or event.button() != Qt.MouseButton.LeftButton:
            return
        if self.mode == "crop":
            self.crop_start = event.pos()
            self.crop_end = event.pos()
            self.drawing = True
        elif self.mode == "move":
            self.drawing = True
            self.move_last_widget_pt = event.pos()
            self.move_Started.emit()
        elif self.mode in ("magic_brush", "manual_mark_fg", "manual_mark_bg"):
            self.drawing = True
            pt = self._widget_to_image_coords(event.pos())
            if pt:
                self._paint_mask(pt, pt)
                self.last_pt = pt

    def mouseMoveEvent(self, event):
        if not self.drawing or self.cv_image is None:
            return
        if self.mode == "crop":
            self.crop_end = event.pos()
            self.update()
        elif self.mode == "move":
            dpos = event.pos() - self.move_last_widget_pt
            dx, dy = self._widget_delta_to_image_delta(dpos)
            if dx != 0 or dy != 0:
                self.move_last_widget_pt = event.pos()
                self.free_Moved.emit(dx, dy)
        elif self.mode in ("magic_brush", "manual_mark_fg", "manual_mark_bg"):
            pt = self._widget_to_image_coords(event.pos())
            if pt and self.last_pt:
                self._paint_mask(self.last_pt, pt)
                self.last_pt = pt

    def mouseReleaseEvent(self, event):
        if not self.drawing or event.button() != Qt.MouseButton.LeftButton:
            return
        self.drawing = False
        if self.mode == "crop":
            p1 = self._widget_to_image_coords(self.crop_start)
            p2 = self._widget_to_image_coords(self.crop_end)
            self.crop_start = QPoint()
            self.crop_end = QPoint()
            if p1 and p2:
                x1, y1 = min(p1[0], p2[0]), min(p1[1], p2[1])
                x2, y2 = max(p1[0], p2[0]), max(p1[1], p2[1])
                if (x2 - x1) > 10 and (y2 - y1) > 10:
                    self.crop_Completed.emit(QRect(x1, y1, x2 - x1, y2 - y1))
            self.update()

    def wheelEvent(self, event):
        if self.mode == "move" and self.cv_image is not None:
            delta = event.angleDelta().y()
            factor = 1.08 if delta > 0 else 0.92
            self.wheel_Scaled.emit(factor)
        else:
            super().wheelEvent(event)

    def _paint_mask(self, pt1, pt2):
        val = 1 if self.mode == "magic_brush" else (2 if self.mode == "manual_mark_fg" else 3)
        # brush_size is in full-resolution pixels; shrink it with the preview
        bs = max(2, int(self.brush_size * getattr(self, "brush_scale", 1.0)))
        cv2.line(self.brush_mask, pt1, pt2, val, bs)
        if self.mode == "manual_mark_fg":
            cv2.line(self.grabcut_mask, pt1, pt2, cv2.GC_FGD, bs)
        elif self.mode == "manual_mark_bg":
            cv2.line(self.grabcut_mask, pt1, pt2, cv2.GC_BGD, bs)
        self.update_display()


# ==============================================================================
# VIDEO DATA STRUCTURES & MULTI-STEM AUDIO TIMELINE (WITH LOCKED / STEM TRIMMING)
# ==============================================================================
class VideoSource:
    """Represents a loaded video file with its own unique color, original audio and separated stems."""
    def __init__(self, source_id: int, filepath: str, color: str):
        self.source_id = source_id
        self.filepath = filepath
        self.filename = os.path.basename(filepath)
        self.color = color

        cap = cv2.VideoCapture(filepath)
        fps = cap.get(cv2.CAP_PROP_FPS)
        self.fps = fps if fps and 1 <= fps <= 240 else 30.0
        self.frame_count = int(cap.get(cv2.CAP_PROP_FRAME_COUNT))
        self.width = int(cap.get(cv2.CAP_PROP_FRAME_WIDTH))
        self.height = int(cap.get(cv2.CAP_PROP_FRAME_HEIGHT))
        cap.release()
        self.duration_ms = int((self.frame_count / self.fps) * 1000) if self.frame_count > 0 else 0
        if self.duration_ms <= 0:
            self.duration_ms = probe_media_duration_ms(filepath)

        self.stems_separated = False
        self.sample_rate = 44100
        self.raw_audio = None       # original soundtrack (float32 stereo), loaded on demand
        self.has_audio = None       # None = not checked yet
        self.voices_data = None
        self.music_data = None
        self.noise_data = None
        self.envelopes = None
        self._audio_lock = threading.Lock()
        self.proxy_path = None      # small edit-friendly copy for 4K sources (preview only)
        self.face_track = None      # (times_ms, centre_x) for smart vertical reframing
        self.thumbs = []            # [(source_ms, RGB thumbnail)] for the timeline
        self.stems_engine = ""

    def ensure_raw_audio(self) -> bool:
        """Loads the clip's own soundtrack once (so un-separated clips keep their sound on export)."""
        with self._audio_lock:
            return self._load_raw_audio()

    def _load_raw_audio(self) -> bool:
        if self.has_audio is not None:
            return self.has_audio
        tmp_wav = os.path.join(tempfile.gettempdir(), f"ank_src_{os.getpid()}_{self.source_id}.wav")
        ok = AudioStemProcessor.extract_wav(self.filepath, tmp_wav, self.sample_rate)
        if ok:
            try:
                self.sample_rate, self.raw_audio = read_wav_float(tmp_wav)
                full_env = AudioStemProcessor.envelope(self.raw_audio)
                if self.envelopes is None:
                    self.envelopes = {"full": full_env}
                else:
                    self.envelopes["full"] = full_env
            except Exception:
                ok = False
        try:
            os.remove(tmp_wav)
        except OSError:
            pass
        self.has_audio = bool(ok and self.raw_audio is not None and len(self.raw_audio) > 0)
        return self.has_audio


class AudioMixParams:
    """
    Per-segment volume levels (0.0 to 2.0) AND independent start/end trim offsets (in timeline ms)
    for Voices, Music, and Noises, plus clip gain and audio fades (v2.0).
    """
    def __init__(self, separated=False, voices_vol=1.0, music_vol=1.0, noise_vol=1.0):
        self.separated = separated
        self.voices_vol = float(voices_vol)
        self.music_vol = float(music_vol)
        self.noise_vol = float(noise_vol)
        self.gain = 1.0
        self.fade_in_ms = 0
        self.fade_out_ms = 0
        # Independent start/end trim offsets (in timeline ms) per stem: 'voices', 'music', 'noise'
        self.stem_trim_start = {"voices": 0, "music": 0, "noise": 0}
        self.stem_trim_end = {"voices": 0, "music": 0, "noise": 0}

    def clone(self):
        c = AudioMixParams(self.separated, self.voices_vol, self.music_vol, self.noise_vol)
        c.gain, c.fade_in_ms, c.fade_out_ms = self.gain, self.fade_in_ms, self.fade_out_ms
        c.stem_trim_start = dict(self.stem_trim_start)
        c.stem_trim_end = dict(self.stem_trim_end)
        return c

    def reset_trims(self):
        self.stem_trim_start = {"voices": 0, "music": 0, "noise": 0}
        self.stem_trim_end = {"voices": 0, "music": 0, "noise": 0}

    def key(self):
        return (self.separated, self.voices_vol, self.music_vol, self.noise_vol, self.gain, self.fade_in_ms,
                self.fade_out_ms, tuple(sorted(self.stem_trim_start.items())), tuple(sorted(self.stem_trim_end.items())))

    def badge_str(self) -> str:
        gain = f" VOL:{int(self.gain * 100)}%" if abs(self.gain - 1.0) > 0.01 else ""
        if not self.separated:
            return f" [{gain.strip()}]" if gain else ""
        return f" [V:{int(self.voices_vol*100)}% M:{int(self.music_vol*100)}% N:{int(self.noise_vol*100)}%{gain}]"


class TimelineSegment:
    """
    Represents a non-destructive slice of a VideoSource with spatial transforms,
    variable playback speed, separated audio stem levels + independent stem trims,
    and (v2.0) a color grade, a title overlay and video fades.
    """
    def __init__(
        self,
        source: VideoSource,
        in_ms: int,
        out_ms: int,
        crop_rect=None,
        transform: TransformParams = None,
        speed: float = 1.0,
        audio_mix: AudioMixParams = None,
        color: ColorParams = None,
        text: TextOverlay = None,
        fade_in_ms: int = 0,
        fade_out_ms: int = 0,
        transition: dict = None,
        motion: dict = None,
    ):
        self.source = source
        self.in_ms = max(0, int(in_ms))
        self.out_ms = max(self.in_ms + 50, int(out_ms))
        self.crop_rect = crop_rect
        self.transform = transform.clone() if transform else TransformParams()
        self.speed = max(0.10, min(8.00, float(speed)))
        self.audio_mix = audio_mix.clone() if audio_mix else AudioMixParams(separated=source.stems_separated)
        self.color = color.clone() if color else ColorParams()
        self.text = text.clone() if text else TextOverlay()
        self.fade_in_ms = int(fade_in_ms)
        self.fade_out_ms = int(fade_out_ms)
        self.transition = dict(transition) if transition else {"type": "none", "ms": 500}   # into this clip
        self.motion = dict(motion) if motion else {"type": "none", "amount": 20}
        self._clamp_stem_trims()

    @property
    def source_duration_ms(self) -> int:
        return max(50, self.out_ms - self.in_ms)

    @property
    def duration_ms(self) -> int:
        return max(20, int(round(self.source_duration_ms / self.speed)))

    def _clamp_stem_trims(self):
        dur = self.duration_ms
        for k in ("voices", "music", "noise"):
            s = max(0, min(dur - 20, int(self.audio_mix.stem_trim_start.get(k, 0))))
            e = max(0, min(dur - s - 20, int(self.audio_mix.stem_trim_end.get(k, 0))))
            self.audio_mix.stem_trim_start[k] = s
            self.audio_mix.stem_trim_end[k] = e

    def trim_whole_locked_timeline_ms(self, trim_first_ms: int = 0, trim_last_ms: int = 0):
        """
        Trims the first and/or last `ms` (in timeline time) of the video AND all audio stems together
        so no orphan audio remains when trimming the video.
        """
        if trim_first_ms > 0:
            src_delta = int(round(trim_first_ms * self.speed))
            self.in_ms = min(self.out_ms - 100, self.in_ms + src_delta)
            for k in ("voices", "music", "noise"):
                self.audio_mix.stem_trim_start[k] = max(0, self.audio_mix.stem_trim_start[k] - trim_first_ms)
        if trim_last_ms > 0:
            src_delta = int(round(trim_last_ms * self.speed))
            self.out_ms = max(self.in_ms + 100, self.out_ms - src_delta)
            for k in ("voices", "music", "noise"):
                self.audio_mix.stem_trim_end[k] = max(0, self.audio_mix.stem_trim_end[k] - trim_last_ms)
        self._clamp_stem_trims()

    def trim_single_stem_timeline_ms(self, stem_key: str, trim_first_ms: int = 0, trim_last_ms: int = 0):
        """
        Trims ONLY the specified audio stem ('voices', 'music', or 'noise') from its start or end
        while keeping the video and other stems intact.
        """
        if stem_key not in ("voices", "music", "noise"):
            return
        self.audio_mix.separated = True
        if trim_first_ms != 0:
            self.audio_mix.stem_trim_start[stem_key] = max(0, self.audio_mix.stem_trim_start[stem_key] + trim_first_ms)
        if trim_last_ms != 0:
            self.audio_mix.stem_trim_end[stem_key] = max(0, self.audio_mix.stem_trim_end[stem_key] + trim_last_ms)
        self._clamp_stem_trims()

    def clone(self):
        return TimelineSegment(
            self.source,
            self.in_ms,
            self.out_ms,
            self.crop_rect,
            self.transform,
            self.speed,
            self.audio_mix,
            self.color,
            self.text,
            self.fade_in_ms,
            self.fade_out_ms,
            self.transition,
            self.motion,
        )

    def audio_key(self):
        return (self.source.source_id, self.in_ms, self.out_ms, self.speed, self.audio_mix.key(), self.source.stems_separated)


class TimelineWidget(QWidget):
    """
    Custom Zoomable Timeline with:
      - Drag & Drop file insertion
      - Interactive Left/Right Edge Trimming (Locked Whole-Clip OR Individual Audio Stem!)
      - Full Right-Click Context Menu (`QMenu`) on Video & Audio Stem lanes
    """
    playhead_Moved = pyqtSignal(int)
    marks_Changed = pyqtSignal(object, object)
    videos_Dropped_At_Ms = pyqtSignal(list, int)
    context_Menu_Requested = pyqtSignal(QPoint, int, int, str)  # (global_pos, clicked_ms, seg_idx, lane_type)
    edge_Trim_Started = pyqtSignal()
    edge_Trim_Updated = pyqtSignal()
    edge_Trim_Preview = pyqtSignal(int, str)      # (timeline ms of the edge being dragged, label) — live monitor preview
    edge_Trim_Finished = pyqtSignal()
    mark_Drag_Preview = pyqtSignal(int, str)      # (ms, "A"|"B") while a mark flag is dragged
    mark_Blocked = pyqtSignal(str)                # tried to move a locked mark

    def __init__(self):
        super().__init__()
        self.setMinimumHeight(268)
        self.setAcceptDrops(True)
        self.setMouseTracking(True)
        self.segments: list[TimelineSegment] = []
        self.px_per_sec = 100.0
        self.playhead_ms = 0
        self.mark_a_ms = None
        self.mark_b_ms = None
        self.lock_tracks = True  # Locked by default so trimming video trims all audio stems with it
        self.lock_a = False      # Mark A / Mark B can be locked independently
        self.lock_b = False
        self.overlays = []       # shown on their own lanes (set by the main window)
        self.subtitles = []
        self.music = None
        self._thumb_px = {}      # (source_id, idx) -> QPixmap

        self._dragging_playhead = False
        self._dragging_mark = None   # "A" or "B" while a mark flag is dragged
        # Edge-drag trimming state: (seg_idx, lane_type, 'left'|'right', last_x)
        self._edge_drag_state = None
        self.update_width()

    def dragEnterEvent(self, event):
        if event.mimeData().hasUrls():
            event.acceptProposedAction()

    def dropEvent(self, event):
        paths = [u.toLocalFile() for u in event.mimeData().urls() if os.path.isfile(u.toLocalFile())]
        if paths:
            drop_ms = self.x_to_ms(int(event.position().x()))
            self.videos_Dropped_At_Ms.emit(paths, drop_ms)
        event.acceptProposedAction()

    def total_duration_ms(self) -> int:
        return sum(seg.duration_ms for seg in self.segments)

    def set_zoom(self, px_per_sec: float):
        self.px_per_sec = max(10.0, min(1200.0, px_per_sec))
        self.update_width()
        self.update()

    def update_width(self):
        total_sec = max(10.0, (self.total_duration_ms() / 1000.0) + 5.0)
        w = int(total_sec * self.px_per_sec) + 100
        self.setMinimumWidth(w)

    def ms_to_x(self, ms: int) -> int:
        return int((ms / 1000.0) * self.px_per_sec) + 20

    def x_to_ms(self, x: int) -> int:
        ms = int(((x - 20) / self.px_per_sec) * 1000.0)
        return max(0, min(self.total_duration_ms(), ms))

    def _hit_test(self, pos: QPoint):
        """
        Returns `(seg_idx, lane_type, edge_side)` at `pos`.
        `lane_type` is one of: `'ruler'`, `'video'`, `'voices'`, `'music'`, `'noise'`, or `'empty'`.
        `edge_side` is `'left'`, `'right'`, or `None` (within 8px of segment/stem trim boundary).
        """
        ruler_h = 32
        track_y = ruler_h + 8
        vid_h = 54
        stem_h = 26
        y = pos.y()
        x = pos.x()

        if y <= ruler_h:
            return -1, "ruler", None

        lane = "empty"
        if track_y <= y <= track_y + vid_h:
            lane = "video"
        else:
            for s_idx, s_key in enumerate(("voices", "music", "noise")):
                sy = track_y + vid_h + 4 + s_idx * (stem_h + 3)
                if sy <= y <= sy + stem_h:
                    lane = s_key
                    break

        cur_ms = 0
        for idx, seg in enumerate(self.segments):
            x1 = self.ms_to_x(cur_ms)
            x2 = self.ms_to_x(cur_ms + seg.duration_ms)
            if x1 - 6 <= x <= x2 + 6:
                edge = None
                if lane in ("voices", "music", "noise") and not self.lock_tracks:
                    # Check stem's own active boundaries
                    st_x1 = self.ms_to_x(cur_ms + seg.audio_mix.stem_trim_start[lane])
                    st_x2 = self.ms_to_x(cur_ms + seg.duration_ms - seg.audio_mix.stem_trim_end[lane])
                    if abs(x - st_x1) <= 8:
                        edge = "left"
                    elif abs(x - st_x2) <= 8:
                        edge = "right"
                else:
                    if abs(x - x1) <= 8:
                        edge = "left"
                    elif abs(x - x2) <= 8:
                        edge = "right"
                return idx, lane, edge
            cur_ms += seg.duration_ms

        return -1, lane, None

    @staticmethod
    def _glossy(painter: QPainter, rect: QRect, color: QColor, radius: int, outline: QColor):
        g = QLinearGradient(QPointF(rect.topLeft()), QPointF(rect.bottomLeft()))
        g.setColorAt(0.0, color.lighter(135))
        g.setColorAt(0.5, color)
        g.setColorAt(1.0, color.darker(150))
        painter.setBrush(QBrush(g))
        painter.setPen(QPen(outline, 1))
        painter.drawRoundedRect(rect, radius, radius)
        hi = QRect(rect.left() + 2, rect.top() + 1, max(0, rect.width() - 4), max(1, rect.height() // 3))
        g2 = QLinearGradient(QPointF(hi.topLeft()), QPointF(hi.bottomLeft()))
        g2.setColorAt(0.0, QColor(255, 255, 255, 70))
        g2.setColorAt(1.0, QColor(255, 255, 255, 0))
        painter.setPen(Qt.PenStyle.NoPen)
        painter.setBrush(QBrush(g2))
        painter.drawRoundedRect(hi, radius, radius)

    def paintEvent(self, event):
        painter = QPainter(self)
        painter.setRenderHint(QPainter.RenderHint.Antialiasing)

        bg = QLinearGradient(0, 0, 0, self.height())
        bg.setColorAt(0, QColor(THEME["tl_bg_top"]))
        bg.setColorAt(1, QColor(THEME["tl_bg_bot"]))
        painter.fillRect(self.rect(), QBrush(bg))

        # 1. Draw Time Ruler
        ruler_h = 32
        rg = QLinearGradient(0, 0, 0, ruler_h)
        rg.setColorAt(0, QColor(THEME["tl_ruler_top"]))
        rg.setColorAt(1, QColor(THEME["tl_ruler_bot"]))
        painter.fillRect(0, 0, self.width(), ruler_h, QBrush(rg))
        painter.setPen(QColor(THEME["tl_text"]))
        painter.setFont(QFont("Consolas", 8))

        if self.px_per_sec >= 400:
            major_step_ms, minor_step_ms = 500, 100
        elif self.px_per_sec >= 120:
            major_step_ms, minor_step_ms = 1000, 200
        elif self.px_per_sec >= 40:
            major_step_ms, minor_step_ms = 5000, 1000
        else:
            major_step_ms, minor_step_ms = 10000, 2000

        # Only draw ticks that are actually visible (fast on long timelines)
        vis = event.rect()
        first_ms = max(0, (self.x_to_ms_unclamped(vis.left()) // minor_step_ms) * minor_step_ms)
        last_ms = self.x_to_ms_unclamped(vis.right()) + minor_step_ms
        for ms in range(int(first_ms), int(last_ms), minor_step_ms):
            x = self.ms_to_x(ms)
            if ms % major_step_ms == 0:
                painter.setPen(QColor(THEME["tl_major"]))
                painter.drawLine(x, ruler_h - 12, x, ruler_h)
                painter.drawText(x + 3, ruler_h - 14, format_ms(ms))
            else:
                painter.setPen(QColor(THEME["tl_minor"]))
                painter.drawLine(x, ruler_h - 6, x, ruler_h)

        if not self.segments:
            ic = make_icon_pixmap("film", "slate", 40)
            painter.setOpacity(0.8)
            painter.drawPixmap(30, ruler_h + 60, ic)
            painter.setOpacity(1.0)
            painter.setPen(QColor(THEME["tl_empty"]))
            painter.setFont(QFont("Segoe UI", 11, QFont.Weight.Bold))
            painter.drawText(
                QRect(80, ruler_h, max(200, self.width() - 100), self.height() - ruler_h),
                Qt.AlignmentFlag.AlignVCenter | Qt.AlignmentFlag.AlignLeft,
                "Drag & Drop video files here  •  Right-click any clip for Trim, Split, Copy/Paste & Stem menus"
            )
            return

        # 2. Draw Video Track + 3 Color-Coded Audio Stem Lanes (Voices, Music, Noises)
        track_y = ruler_h + 8
        vid_h = 54
        stem_h = 26
        cur_ms = 0

        for seg in self.segments:
            x1 = self.ms_to_x(cur_ms)
            x2 = self.ms_to_x(cur_ms + seg.duration_ms)
            w = max(4, x2 - x1)
            if x2 < vis.left() - 4 or x1 > vis.right() + 4:
                cur_ms += seg.duration_ms
                continue

            base_color = QColor(seg.source.color)
            vid_rect = QRect(x1, track_y, w, vid_h)
            self._glossy(painter, vid_rect, base_color, 6, base_color.lighter(160))
            thumbs = seg.source.thumbs
            if thumbs:
                painter.save()
                clip_path = QPainterPath()
                clip_path.addRoundedRect(QRectF(vid_rect.adjusted(5, 3, -5, -3)), 4, 4)
                painter.setClipPath(clip_path)
                painter.setOpacity(0.55)
                tw = max(24, int(thumbs[0][1].shape[1] * (vid_h - 6) / thumbs[0][1].shape[0]))
                step_ms = max(1, thumbs[1][0] - thumbs[0][0]) if len(thumbs) > 1 else 1000
                x = max(x1 + 5, vis.left() - tw)
                while x < min(x2 - 5, vis.right() + tw):
                    src_ms = seg.in_ms + (x - x1) / max(1, w) * seg.source_duration_ms
                    k = max(0, min(len(thumbs) - 1, int(src_ms // step_ms)))
                    key = (seg.source.source_id, k)
                    pm = self._thumb_px.get(key)
                    if pm is None:
                        arr = thumbs[k][1]
                        pm = QPixmap.fromImage(QImage(arr.data, arr.shape[1], arr.shape[0], arr.shape[1] * 3,
                                                      QImage.Format.Format_RGB888).copy())
                        self._thumb_px[key] = pm
                    painter.drawPixmap(QRect(x, track_y + 3, tw, vid_h - 6), pm)
                    x += tw
                painter.restore()
                # Keep the label readable over the pictures
                shade = QLinearGradient(QPointF(vid_rect.topLeft()), QPointF(vid_rect.bottomLeft()))
                shade.setColorAt(0.0, QColor(0, 0, 0, 120))
                shade.setColorAt(0.6, QColor(0, 0, 0, 20))
                painter.setPen(Qt.PenStyle.NoPen)
                painter.setBrush(QBrush(shade))
                painter.drawRoundedRect(vid_rect, 6, 6)
            if seg.transition.get("type", "none") != "none" and cur_ms > 0:
                painter.setPen(Qt.PenStyle.NoPen)
                painter.setBrush(QColor(255, 255, 255, 210))
                hw = max(5, int(seg.transition.get("ms", 500) / 2000.0 * self.px_per_sec))
                painter.drawPolygon([QPoint(x1 - hw, track_y + vid_h // 2), QPoint(x1, track_y + 4),
                                     QPoint(x1 + hw, track_y + vid_h // 2), QPoint(x1, track_y + vid_h - 4)])

            # Video fades shown as shaded wedges
            painter.setPen(Qt.PenStyle.NoPen)
            painter.setBrush(QColor(0, 0, 0, 110))
            if seg.fade_in_ms > 0:
                fx = self.ms_to_x(cur_ms + seg.fade_in_ms)
                painter.drawPolygon([QPoint(x1, track_y), QPoint(fx, track_y), QPoint(x1, track_y + vid_h)])
            if seg.fade_out_ms > 0:
                fx = self.ms_to_x(cur_ms + seg.duration_ms - seg.fade_out_ms)
                painter.drawPolygon([QPoint(x2, track_y), QPoint(fx, track_y), QPoint(x2, track_y + vid_h)])

            # Draw left/right trim grab handles on video block
            painter.fillRect(QRect(x1, track_y + 4, 4, vid_h - 8), QColor("#FACC15"))
            painter.fillRect(QRect(x2 - 4, track_y + 4, 4, vid_h - 8), QColor("#FACC15"))

            painter.setPen(QColor("#FFFFFF"))
            painter.setFont(QFont("Segoe UI", 8, QFont.Weight.Bold))
            crop_tag = " [CROP]" if seg.crop_rect else ""
            speed_tag = f" [{seg.speed:.2f}x]" if abs(seg.speed - 1.0) > 0.01 else ""
            lock_icon = "LOCK" if self.lock_tracks else "FREE"
            tf_tag = seg.transform.summary_tag() + seg.color.summary_tag() + (" [TEXT]" if seg.text.active() else "")
            label = (
                f"[{lock_icon}] V{seg.source.source_id}  {seg.source.filename}{speed_tag}{crop_tag}{tf_tag}\n"
                f"In {format_ms(seg.in_ms)}  →  Out {format_ms(seg.out_ms)}   ({format_ms(seg.duration_ms)})"
            )
            painter.drawText(vid_rect.adjusted(9, 4, -7, -3), Qt.AlignmentFlag.AlignLeft | Qt.AlignmentFlag.AlignTop, label)

            # Draw the 3 Audio Stem Lanes under the video segment
            stems_info = [
                ("VOICES", seg.audio_mix.voices_vol, "voices", base_color.darker(125)),
                ("MUSIC",  seg.audio_mix.music_vol,  "music",  base_color.darker(155)),
                ("NOISES", seg.audio_mix.noise_vol,  "noise",  base_color.darker(185)),
            ]
            envs = seg.source.envelopes or {}
            for s_idx, (s_title, s_vol, env_key, s_col) in enumerate(stems_info):
                sy = track_y + vid_h + 4 + s_idx * (stem_h + 3)
                full_s_rect = QRect(x1, sy, w, stem_h)

                # Background slot (shows muted/trimmed area in dark red/gray)
                painter.setBrush(QBrush(QColor(THEME["tl_slot"])))
                painter.setPen(QPen(QColor(THEME["tl_slot_border"]), 1))
                painter.drawRoundedRect(full_s_rect, 3, 3)

                # Active untrimmed portion of this stem
                t_start_ms = seg.audio_mix.stem_trim_start.get(env_key, 0)
                t_end_ms = seg.audio_mix.stem_trim_end.get(env_key, 0)
                act_x1 = self.ms_to_x(cur_ms + t_start_ms)
                act_x2 = self.ms_to_x(cur_ms + max(t_start_ms + 10, seg.duration_ms - t_end_ms))
                act_w = max(2, act_x2 - act_x1)

                act_rect = QRect(act_x1, sy, act_w, stem_h)
                self._glossy(painter, act_rect, s_col, 3, base_color.lighter(130))

                # Waveform: the separated stem, or the original soundtrack on the first lane
                env = None
                if seg.audio_mix.separated and env_key in envs:
                    env = envs[env_key]
                elif s_idx == 0 and "full" in envs:
                    env = envs["full"]
                if env is not None and len(env):
                    eff_vol = s_vol if seg.audio_mix.separated else 1.0
                    painter.setPen(QPen(QColor("#FACC15") if eff_vol > 0.02 else QColor("#52525B"), 1))
                    src_dur = max(1, seg.source.duration_ms)
                    e0 = int(len(env) * seg.in_ms / src_dur)
                    e1 = max(e0 + 1, int(len(env) * seg.out_ms / src_dur))
                    sub = env[e0:min(len(env), e1)]
                    if len(sub):
                        n_bars = max(1, act_w // 3)
                        cy = sy + stem_h // 2
                        for b_i in range(n_bars):
                            val = float(sub[int((b_i / n_bars) * len(sub))]) * min(2.0, eff_vol * seg.audio_mix.gain)
                            bh = int(min(stem_h - 4, val * (stem_h - 4)))
                            bx = act_x1 + int((b_i / n_bars) * act_w)
                            painter.drawLine(bx, cy - bh // 2, bx, cy + bh // 2)

                trim_note = ""
                if t_start_ms > 0 or t_end_ms > 0:
                    trim_note = f" [Trim -{t_start_ms/1000:.1f}s / -{t_end_ms/1000:.1f}s]"
                if not seg.audio_mix.separated:
                    status_txt = ("AUDIO (separate to edit stems)" if s_idx == 0 else "") if seg.source.has_audio is not False else ("NO AUDIO TRACK" if s_idx == 0 else "")
                else:
                    status_txt = f"{s_title}: {int(s_vol * 100)}%{trim_note}"
                painter.setPen(QColor("#FFFFFF") if s_vol > 0.01 else QColor("#EF4444"))
                painter.setFont(QFont("Consolas", 7, QFont.Weight.Bold))
                painter.drawText(act_rect.adjusted(5, 2, -5, -2), Qt.AlignmentFlag.AlignLeft | Qt.AlignmentFlag.AlignVCenter, status_txt)

            cur_ms += seg.duration_ms

        # Extra lanes: background music, layers (logo / PiP) and subtitles
        lane_y = track_y + vid_h + 4 + 3 * (stem_h + 3) + 2
        total = cur_ms
        painter.setFont(QFont("Segoe UI", 7, QFont.Weight.Bold))
        lanes = []
        if self.music is not None:
            start = self.music.start_ms
            aud = self.music._audio      # only use audio that is already loaded (never decode while painting)
            end = total if (self.music.loop or aud is None) else min(total, start + int(len(aud[1]) * 1000 / max(1, aud[0])))
            lanes.append(("MUSIC", [(start, end, self.music.name)], QColor("#ec4899")))
        if self.overlays:
            lanes.append(("LAYERS", [(o.start_ms, o.end_ms if o.end_ms is not None else total, o.name) for o in self.overlays], QColor("#22c55e")))
        if self.subtitles:
            lanes.append(("SUBS", [(c["start"], c["end"], c["text"].replace("\n", " ")) for c in self.subtitles], QColor("#a78bfa")))
        for title, items, col in lanes:
            painter.fillRect(QRect(20, lane_y, max(0, self.ms_to_x(total) - 20), 16), QColor(THEME["tl_lane"]))
            for a, b, label in items:
                ra = QRect(self.ms_to_x(a), lane_y + 1, max(3, self.ms_to_x(b) - self.ms_to_x(a)), 14)
                if ra.right() < vis.left() or ra.left() > vis.right():
                    continue
                self._glossy(painter, ra, col, 3, col.lighter(140))
                painter.setPen(QColor("#ffffff"))
                painter.drawText(ra.adjusted(4, 0, -3, 0), Qt.AlignmentFlag.AlignVCenter | Qt.AlignmentFlag.AlignLeft, f"{title}: {label}")
            lane_y += 19

        # 3. Draw Mark A and Mark B Selection Region
        if self.mark_a_ms is not None and self.mark_b_ms is not None:
            m1, m2 = min(self.mark_a_ms, self.mark_b_ms), max(self.mark_a_ms, self.mark_b_ms)
            x1, x2 = self.ms_to_x(m1), self.ms_to_x(m2)
            painter.fillRect(QRect(x1, ruler_h, x2 - x1, self.height() - ruler_h), QColor(34, 211, 238, 50))

        painter.setFont(QFont("Segoe UI", 8, QFont.Weight.Bold))
        for name, ms, locked, col, text_y in (("A", self.mark_a_ms, self.lock_a, "#22D3EE", self.height() - 18),
                                              ("B", self.mark_b_ms, self.lock_b, "#F43F5E", self.height() - 5)):
            if ms is None:
                continue
            x = self.ms_to_x(ms)
            painter.setPen(QPen(QColor(col), 3 if locked else 2, Qt.PenStyle.SolidLine if locked else Qt.PenStyle.DashLine))
            painter.drawLine(x, 0, x, self.height())
            # Draggable flag in the ruler (shows a padlock when locked)
            flag = QRect(x - 1, 2, 30 if locked else 18, 16)
            self._glossy(painter, flag, QColor(col), 4, QColor(col).lighter(150))
            painter.setPen(QColor("#0b0f17"))
            painter.drawText(QRect(x + 1, 2, 14, 16), Qt.AlignmentFlag.AlignCenter, name)
            if locked:
                painter.drawPixmap(x + 14, 3, make_icon_pixmap("lock", "amber", 14))
            painter.setPen(QColor(col))
            painter.drawText(x + 4, text_y, f"{name}  {format_ms(ms)}{'  LOCKED' if locked else ''}")

        # 4. Draw Playhead
        xp = self.ms_to_x(self.playhead_ms)
        painter.setPen(QPen(QColor("#FACC15"), 2))
        painter.drawLine(xp, 0, xp, self.height())
        painter.setBrush(QColor("#FACC15"))
        painter.setPen(QPen(QColor("#ffffff"), 1))
        painter.drawPolygon([QPoint(xp - 7, 0), QPoint(xp + 7, 0), QPoint(xp + 7, 8), QPoint(xp, 15), QPoint(xp - 7, 8)])

    def x_to_ms_unclamped(self, x: int) -> int:
        return int(((x - 20) / self.px_per_sec) * 1000.0)

    def _mark_at(self, pos: QPoint):
        """'A' or 'B' when the press is on a mark flag in the ruler."""
        if pos.y() > 32:
            return None
        for name, ms in (("B", self.mark_b_ms), ("A", self.mark_a_ms)):
            if ms is not None and -4 <= pos.x() - self.ms_to_x(ms) <= 20:
                return name
        return None

    def _seg_start_ms(self, idx: int) -> int:
        return sum(s.duration_ms for s in self.segments[:idx])

    def _emit_trim_preview(self, seg_idx: int, lane: str, edge: str):
        """Tells the monitor which frame the dragged edge has reached, so you can stop on the exact picture."""
        seg = self.segments[seg_idx]
        start = self._seg_start_ms(seg_idx)
        if self.lock_tracks or lane == "video":
            if edge == "left":
                # +1 ms: the exact boundary belongs to the previous clip
                self.edge_Trim_Preview.emit(start + 1, f"TRIM START  ▸  first frame {format_ms(seg.in_ms)}")
            else:
                self.edge_Trim_Preview.emit(start + seg.duration_ms - 1, f"TRIM END  ▸  last frame {format_ms(seg.out_ms)}")
        else:
            am = seg.audio_mix
            if edge == "left":
                ms = start + am.stem_trim_start[lane]
                self.edge_Trim_Preview.emit(ms + 1, f"{lane.upper()} STARTS  ▸  {format_ms(ms)}")
            else:
                ms = start + seg.duration_ms - am.stem_trim_end[lane] - 1
                self.edge_Trim_Preview.emit(max(start, ms), f"{lane.upper()} ENDS  ▸  {format_ms(ms)}")

    def mousePressEvent(self, event):
        pos = event.pos()
        seg_idx, lane, edge = self._hit_test(pos)

        if event.button() == Qt.MouseButton.RightButton:
            clicked_ms = self.x_to_ms(pos.x())
            self.context_Menu_Requested.emit(self.mapToGlobal(pos), clicked_ms, seg_idx, lane)
            return

        if event.button() == Qt.MouseButton.LeftButton:
            mark = self._mark_at(pos)
            if mark:
                if (mark == "A" and self.lock_a) or (mark == "B" and self.lock_b):
                    self.mark_Blocked.emit(mark)
                else:
                    self._dragging_mark = mark
                    self.setCursor(Qt.CursorShape.SizeHorCursor)
                return
            if seg_idx >= 0 and edge in ("left", "right"):
                # Start interactive edge-trimming
                self.edge_Trim_Started.emit()
                self._edge_drag_state = (seg_idx, lane, edge, pos.x())
                self._emit_trim_preview(seg_idx, lane, edge)
                return

            self._dragging_playhead = True
            self.playhead_ms = self.x_to_ms(pos.x())
            self.playhead_Moved.emit(self.playhead_ms)
            self.update()

    def mouseMoveEvent(self, event):
        pos = event.pos()
        if self._dragging_mark:
            ms = self.x_to_ms(pos.x())
            if self._dragging_mark == "A":
                self.mark_a_ms = ms
            else:
                self.mark_b_ms = ms
            self.update()
            self.mark_Drag_Preview.emit(ms, self._dragging_mark)
            return

        if self._edge_drag_state is not None:
            seg_idx, lane, edge, last_x = self._edge_drag_state
            dx = pos.x() - last_x
            # Hold Shift for fine trimming (the clip edge moves 5x slower than the mouse)
            fine = 0.2 if event.modifiers() & Qt.KeyboardModifier.ShiftModifier else 1.0
            delta_ms = int((dx / self.px_per_sec) * 1000.0 * fine)
            if abs(delta_ms) >= (3 if fine < 1 else 15) and 0 <= seg_idx < len(self.segments):
                seg = self.segments[seg_idx]
                # If locked OR dragging the video bar, trim whole clip + all stems together
                if self.lock_tracks or lane == "video":
                    if edge == "left" and delta_ms != 0:
                        src_delta = int(round(delta_ms * seg.speed))
                        new_in = max(0, min(seg.out_ms - 100, seg.in_ms + src_delta))
                        seg.in_ms = new_in
                        seg._clamp_stem_trims()
                    elif edge == "right" and delta_ms != 0:
                        src_delta = int(round(delta_ms * seg.speed))
                        new_out = max(seg.in_ms + 100, min(seg.source.duration_ms, seg.out_ms + src_delta))
                        seg.out_ms = new_out
                        seg._clamp_stem_trims()
                elif lane in ("voices", "music", "noise"):
                    # Independent stem edge-trimming!
                    if edge == "left":
                        seg.trim_single_stem_timeline_ms(lane, trim_first_ms=delta_ms)
                    elif edge == "right":
                        seg.trim_single_stem_timeline_ms(lane, trim_last_ms=-delta_ms)

                self._edge_drag_state = (seg_idx, lane, edge, pos.x())
                self.update_width()
                self.update()
                self.edge_Trim_Updated.emit()
                self._emit_trim_preview(seg_idx, lane, edge)
            return

        if self._dragging_playhead:
            self.playhead_ms = self.x_to_ms(pos.x())
            self.playhead_Moved.emit(self.playhead_ms)
            self.update()
            return

        # Update hover cursor when near a trimmable left/right clip edge or a mark flag
        seg_idx, lane, edge = self._hit_test(pos)
        mark = self._mark_at(pos)
        if mark:
            locked = self.lock_a if mark == "A" else self.lock_b
            self.setCursor(Qt.CursorShape.ForbiddenCursor if locked else Qt.CursorShape.SizeHorCursor)
            self.setToolTip(f"Mark {mark} is locked — unlock it to move" if locked else f"Drag Mark {mark}")
        elif seg_idx >= 0 and edge in ("left", "right"):
            self.setCursor(Qt.CursorShape.SizeHorCursor)
            self.setToolTip("Drag to trim  •  hold Shift for fine trimming")
        else:
            self.setCursor(Qt.CursorShape.ArrowCursor)
            self.setToolTip("")

    def mouseReleaseEvent(self, event):
        self._dragging_playhead = False
        if self._dragging_mark:
            self._dragging_mark = None
            self.marks_Changed.emit(self.mark_a_ms, self.mark_b_ms)
        if self._edge_drag_state is not None:
            self._edge_drag_state = None
            self.edge_Trim_Finished.emit()

    def wheelEvent(self, event):
        if event.modifiers() & Qt.KeyboardModifier.ShiftModifier:
            super().wheelEvent(event)  # Shift+wheel scrolls the timeline sideways
            return
        delta = event.angleDelta().y()
        factor = 1.25 if delta > 0 else 0.8
        self.set_zoom(self.px_per_sec * factor)


# ==============================================================================
# MAIN WINDOW: ANK MEDIA STUDIO v2.0.0
# ==============================================================================
# ==============================================================================
# THEMES — Dark, Light, or Auto (follows the computer's setting)
# ==============================================================================
THEMES = {
    "dark": {
        "win": "#0b0f17", "text": "#E5E7EB", "text_strong": "#F1F5F9", "muted": "#8b9bb4", "section": "#93c5fd",
        "card_top": "#172033", "card_bot": "#0f1522", "card_border": "#24324d", "card_hi": "#33456a", "card_lo": "#05070d",
        "btn_top": "#3a475e", "btn_mid": "#243045", "btn_bot": "#161e2e", "btn_border": "#3b4a63", "btn_hi": "#5b6b86",
        "btn_h_top": "#4a5a76", "btn_h_mid": "#2e3c56", "btn_h_bot": "#1b2436", "btn_text": "#F1F5F9",
        "btn_p_top": "#111827", "btn_p_bot": "#263248", "dis_text": "#4b5563", "dis_bg": "#121826", "dis_border": "#1f2937",
        "tool_text": "#cbd5e1", "tool_hover": "rgba(255,255,255,0.07)", "tool_hover_border": "#334155",
        "acc_top": "#2b3953", "acc_mid": "#1c2639", "acc_bot": "#121a29", "acc_border": "#2c3b57", "acc_hi": "#43567c", "acc_text": "#dbe4f3",
        "page_top": "#131b2b", "page_bot": "#0c111b", "page_border": "#1f2a3d",
        "pane": "#0d121c", "tab_top": "#2a3650", "tab_bot": "#141b2a", "tab_text": "#aab6cc",
        "groove_top": "#02040a", "groove_bot": "#1f2937", "groove_border": "#0b0f17",
        "field_top": "#05080f", "field_bot": "#111827", "field_border": "#334155", "field_text": "#f8fafc",
        "popup": "#111827", "check_top": "#1e293b", "check_bot": "#0b1220", "check_border": "#475569",
        "scroll_bg": "#0b0f17", "scroll_handle": "#334155", "status_bg": "#0a0e16", "status_text": "#94a3b8",
        "status_border": "#1f2937", "menu_text": "#F4F4F5", "tip_text": "#e5e7eb",
        "clock_bg": "#05080f", "clock_border": "#263248", "clock_text": "#FACC15", "alt_row": "#121a29",
        "badge_bg": "#1f2937", "accent_text": "#FACC15", "info_text": "#22D3EE",
        # custom-painted widgets
        "tl_bg_top": "#0f141f", "tl_bg_bot": "#0a0d14", "tl_ruler_top": "#2a3346", "tl_ruler_bot": "#1a2132",
        "tl_text": "#A1A1AA", "tl_major": "#E4E4E7", "tl_minor": "#52525B", "tl_empty": "#71717A",
        "tl_slot": "#27171A", "tl_slot_border": "#3F3F46", "tl_lane": "#141a26",
        "canvas_bg": "#07090f", "canvas_border": "#263248", "canvas_text": "#8b9bb4",
    },
    "light": {
        "win": "#eef2f7", "text": "#0f172a", "text_strong": "#0f172a", "muted": "#526075", "section": "#1d4ed8",
        "card_top": "#ffffff", "card_bot": "#eef2f8", "card_border": "#cdd6e3", "card_hi": "#ffffff", "card_lo": "#aeb9cb",
        "btn_top": "#ffffff", "btn_mid": "#f1f5f9", "btn_bot": "#dfe6ef", "btn_border": "#c3cddb", "btn_hi": "#ffffff",
        "btn_h_top": "#ffffff", "btn_h_mid": "#e8f0fe", "btn_h_bot": "#d4e2fb", "btn_text": "#0f172a",
        "btn_p_top": "#cfd8e5", "btn_p_bot": "#eef2f7", "dis_text": "#9aa6b8", "dis_bg": "#eef1f5", "dis_border": "#d7dee8",
        "tool_text": "#1e293b", "tool_hover": "rgba(37,99,235,0.08)", "tool_hover_border": "#b8c6db",
        "acc_top": "#ffffff", "acc_mid": "#f2f5fa", "acc_bot": "#e3e9f2", "acc_border": "#c9d3e1", "acc_hi": "#ffffff", "acc_text": "#0f172a",
        "page_top": "#ffffff", "page_bot": "#f5f7fb", "page_border": "#d5dde8",
        "pane": "#f7f9fc", "tab_top": "#ffffff", "tab_bot": "#e4eaf2", "tab_text": "#334155",
        "groove_top": "#c8d1de", "groove_bot": "#e6ebf2", "groove_border": "#b9c4d4",
        "field_top": "#ffffff", "field_bot": "#f6f8fb", "field_border": "#c3cddb", "field_text": "#0f172a",
        "popup": "#ffffff", "check_top": "#ffffff", "check_bot": "#e6ebf2", "check_border": "#94a3b8",
        "scroll_bg": "#eef2f7", "scroll_handle": "#b9c4d4", "status_bg": "#ffffff", "status_text": "#475569",
        "status_border": "#d5dde8", "menu_text": "#0f172a", "tip_text": "#0f172a",
        "clock_bg": "#0f172a", "clock_border": "#334155", "clock_text": "#FACC15", "alt_row": "#f3f6fa",
        "badge_bg": "#dfe6ef", "accent_text": "#b45309", "info_text": "#0e7490",
        "tl_bg_top": "#f4f7fb", "tl_bg_bot": "#e7edf5", "tl_ruler_top": "#ffffff", "tl_ruler_bot": "#dce4ee",
        "tl_text": "#475569", "tl_major": "#0f172a", "tl_minor": "#94a3b8", "tl_empty": "#64748b",
        "tl_slot": "#f1dede", "tl_slot_border": "#cbd5e1", "tl_lane": "#e9eef5",
        "canvas_bg": "#0b0f17", "canvas_border": "#b9c4d4", "canvas_text": "#9fb0c7",
    },
}
THEME = dict(THEMES["dark"])   # active colours (custom-painted widgets read from here)

STYLESHEET_TEMPLATE = """
QMainWindow { background: $win; }
QWidget { color: $text; font-family: 'Segoe UI', 'Inter', sans-serif; font-size: 12px; }
QDialog { background: $win; }
QFrame#Header {
    background: qlineargradient(x1:0, y1:0, x2:1, y2:0, stop:0 #1e3a8a, stop:0.55 #4c1d95, stop:1 #0f172a);
    border: 1px solid #3b4a7a; border-top-color: #6d83c9; border-bottom-color: #05070d; border-radius: 14px;
}
QFrame#Header QLabel { background: transparent; }
QFrame#Header QToolButton { color: #e2e8f0; }
QFrame#Header QToolButton:hover { background: rgba(255,255,255,0.12); border-color: rgba(255,255,255,0.25); }
QFrame#Header QComboBox { background: rgba(0,0,0,0.25); color: white; border: 1px solid rgba(255,255,255,0.3); }
QLabel#AppTitle { color: #ffffff; font-size: 20px; font-weight: 800; }
QLabel#AppSub { color: #c7d2fe; font-size: 11px; }
QLabel#Chip {
    color: white; font-weight: 700; padding: 2px 10px; border-radius: 9px;
    background: qlineargradient(x1:0, y1:0, x2:0, y2:1, stop:0 #34d399, stop:1 #047857); border: 1px solid #6ee7b7;
}
QFrame#Card, QFrame#Transport {
    background: qlineargradient(x1:0, y1:0, x2:0, y2:1, stop:0 $card_top, stop:1 $card_bot);
    border: 1px solid $card_border; border-top-color: $card_hi; border-bottom-color: $card_lo; border-radius: 12px;
}
QPushButton {
    background: qlineargradient(x1:0, y1:0, x2:0, y2:1, stop:0 $btn_top, stop:0.5 $btn_mid, stop:1 $btn_bot);
    border: 1px solid $btn_border; border-top-color: $btn_hi; border-bottom-color: $card_lo;
    border-radius: 8px; padding: 6px 10px; font-weight: 600; color: $btn_text;
}
QPushButton:hover { background: qlineargradient(x1:0, y1:0, x2:0, y2:1, stop:0 $btn_h_top, stop:0.5 $btn_h_mid, stop:1 $btn_h_bot); border-color: #60A5FA; }
QPushButton:pressed { background: qlineargradient(x1:0, y1:0, x2:0, y2:1, stop:0 $btn_p_top, stop:1 $btn_p_bot); padding-top: 7px; padding-bottom: 5px; }
QPushButton:checked { background: qlineargradient(x1:0, y1:0, x2:0, y2:1, stop:0 #60a5fa, stop:0.5 #2563eb, stop:1 #1e40af); border-color: #93c5fd; color: white; }
QPushButton:disabled { color: $dis_text; background: $dis_bg; border-color: $dis_border; }
QPushButton[kind="primary"] { background: qlineargradient(x1:0, y1:0, x2:0, y2:1, stop:0 #60a5fa, stop:0.5 #2563eb, stop:1 #1e3a8a); border-color: #93c5fd; color: white; }
QPushButton[kind="success"] { background: qlineargradient(x1:0, y1:0, x2:0, y2:1, stop:0 #34d399, stop:0.5 #059669, stop:1 #064e3b); border-color: #6ee7b7; color: white; }
QPushButton[kind="danger"]  { background: qlineargradient(x1:0, y1:0, x2:0, y2:1, stop:0 #fb7185, stop:0.5 #e11d48, stop:1 #881337); border-color: #fda4af; color: white; }
QPushButton[kind="warn"]    { background: qlineargradient(x1:0, y1:0, x2:0, y2:1, stop:0 #fbbf24, stop:0.5 #d97706, stop:1 #78350f); border-color: #fcd34d; color: white; }
QPushButton[kind="accent"]  { background: qlineargradient(x1:0, y1:0, x2:0, y2:1, stop:0 #a78bfa, stop:0.5 #7c3aed, stop:1 #4c1d95); border-color: #c4b5fd; color: white; }
QPushButton[kind]:hover { border-color: #ffffff; }
QToolButton { background: transparent; border: 1px solid transparent; border-radius: 9px; padding: 4px; color: $tool_text; font-weight: 600; }
QToolButton:hover { background: $tool_hover; border-color: $tool_hover_border; }
QToolButton:pressed { background: rgba(0,0,0,0.18); }
QToolButton:checked { background: qlineargradient(x1:0, y1:0, x2:0, y2:1, stop:0 rgba(96,165,250,0.45), stop:1 rgba(30,64,175,0.35)); border-color: #60a5fa; }
QPushButton#AccHeader {
    text-align: left; padding: 7px 12px; font-weight: 700; color: $acc_text; border-radius: 9px;
    background: qlineargradient(x1:0, y1:0, x2:0, y2:1, stop:0 $acc_top, stop:0.5 $acc_mid, stop:1 $acc_bot);
    border: 1px solid $acc_border; border-top-color: $acc_hi; border-bottom-color: $card_lo;
}
QPushButton#AccHeader:hover { border-color: #60a5fa; }
QPushButton#AccHeader:checked {
    background: qlineargradient(x1:0, y1:0, x2:0, y2:1, stop:0 #4f8ff7, stop:0.5 #1d4ed8, stop:1 #1e3a8a);
    border-color: #93c5fd; color: white;
}
QWidget#ToolPage {
    background: qlineargradient(x1:0, y1:0, x2:0, y2:1, stop:0 $page_top, stop:1 $page_bot);
    border: 1px solid $page_border; border-radius: 10px;
}
QWidget#ToolPage QLabel { background: transparent; }
QGroupBox { border: 1px solid $card_border; border-radius: 9px; margin-top: 10px; padding: 8px 6px 6px 6px; font-weight: 700; background: $page_bot; }
QGroupBox::title { subcontrol-origin: margin; left: 10px; padding: 0 5px; color: $section; }
QTabWidget::pane { border: 1px solid $page_border; border-radius: 12px; top: -1px; background: $pane; }
QTabBar::tab {
    background: qlineargradient(x1:0, y1:0, x2:0, y2:1, stop:0 $tab_top, stop:1 $tab_bot);
    border: 1px solid $acc_border; border-bottom: none; border-top-left-radius: 10px; border-top-right-radius: 10px;
    padding: 9px 22px; margin-right: 4px; font-weight: 700; color: $tab_text;
}
QTabBar::tab:selected { background: qlineargradient(x1:0, y1:0, x2:0, y2:1, stop:0 #5b9bff, stop:0.5 #2563eb, stop:1 #1d4ed8); color: white; border-color: #93c5fd; }
QTabBar::tab:hover:!selected { border-color: #60a5fa; }
QSlider::groove:horizontal { height: 6px; background: qlineargradient(x1:0, y1:0, x2:0, y2:1, stop:0 $groove_top, stop:1 $groove_bot); border-radius: 3px; border: 1px solid $groove_border; }
QSlider::sub-page:horizontal { background: qlineargradient(x1:0, y1:0, x2:1, y2:0, stop:0 #1d4ed8, stop:1 #38bdf8); border-radius: 3px; }
QSlider::handle:horizontal {
    background: qradialgradient(cx:0.35, cy:0.3, radius:0.9, fx:0.35, fy:0.3, stop:0 #ffffff, stop:0.35 #bfdbfe, stop:1 #1d4ed8);
    width: 16px; height: 16px; margin: -6px 0; border-radius: 8px; border: 1px solid #0b1220;
}
QComboBox, QSpinBox, QDoubleSpinBox, QLineEdit, QPlainTextEdit, QTextEdit {
    background: qlineargradient(x1:0, y1:0, x2:0, y2:1, stop:0 $field_top, stop:1 $field_bot);
    border: 1px solid $field_border; border-radius: 7px; padding: 4px 7px; color: $field_text; selection-background-color: #2563eb; selection-color: white;
}
QComboBox:focus, QSpinBox:focus, QDoubleSpinBox:focus, QLineEdit:focus { border-color: #3b82f6; }
QComboBox QAbstractItemView { background: $popup; color: $field_text; border: 1px solid #3b82f6; selection-background-color: #2563eb; }
QListWidget, QTableWidget {
    background: $field_bot; alternate-background-color: $alt_row; border: 1px solid $field_border; border-radius: 8px;
    color: $field_text; selection-background-color: #2563eb; selection-color: white; gridline-color: $page_border;
}
QHeaderView::section { background: qlineargradient(x1:0, y1:0, x2:0, y2:1, stop:0 $acc_top, stop:1 $acc_bot); color: $acc_text;
    border: none; border-right: 1px solid $page_border; padding: 5px; font-weight: 700; }
QProgressBar { background: $field_bot; border: 1px solid $field_border; border-radius: 7px; text-align: center; color: $text; height: 16px; }
QProgressBar::chunk { border-radius: 6px; background: qlineargradient(x1:0, y1:0, x2:1, y2:0, stop:0 #10b981, stop:1 #34d399); }
QCheckBox { spacing: 7px; }
QCheckBox::indicator { width: 16px; height: 16px; border-radius: 5px; border: 1px solid $check_border;
    background: qlineargradient(x1:0, y1:0, x2:0, y2:1, stop:0 $check_top, stop:1 $check_bot); }
QCheckBox::indicator:checked { border-color: #93c5fd;
    background: qradialgradient(cx:0.35, cy:0.3, radius:1.0, fx:0.35, fy:0.3, stop:0 #bfdbfe, stop:0.45 #3b82f6, stop:1 #1e3a8a); }
QScrollArea { border: none; background: transparent; }
QScrollBar:vertical { background: $scroll_bg; width: 10px; margin: 0; }
QScrollBar::handle:vertical { background: $scroll_handle; border-radius: 5px; min-height: 30px; }
QScrollBar:horizontal { background: $scroll_bg; height: 10px; margin: 0; }
QScrollBar::handle:horizontal { background: $scroll_handle; border-radius: 5px; min-width: 30px; }
QScrollBar::add-line, QScrollBar::sub-line { width: 0; height: 0; }
QStatusBar { background: $status_bg; color: $status_text; border-top: 1px solid $status_border; }
QMenu { background-color: $popup; color: $menu_text; border: 1px solid #3b82f6; padding: 4px; border-radius: 8px; }
QMenu::item { padding: 6px 22px 6px 26px; border-radius: 5px; }
QMenu::item:selected { background-color: #2563EB; color: white; }
QMenu::separator { height: 1px; background: $page_border; margin: 4px 6px; }
QToolTip { background: $popup; color: $tip_text; border: 1px solid #3b82f6; padding: 5px; border-radius: 6px; }
QLabel#Section { color: $section; font-weight: 700; padding-top: 4px; }
QLabel#Muted { color: $muted; }
QLabel#Accent { color: $accent_text; font-weight: bold; }
QLabel#Info { color: $info_text; font-family: Consolas, monospace; }
QLabel#Badge { padding: 5px 10px; border-radius: 7px; background: $badge_bg; }
QCheckBox#Strong { color: $section; font-weight: bold; }
QLabel#Clock { color: $clock_text; font-family: Consolas, monospace; font-size: 17px; font-weight: 800;
    background: $clock_bg; padding: 5px 12px; border-radius: 8px; border: 1px solid $clock_border; }
"""


def system_prefers_dark() -> bool:
    """Reads the computer's light/dark setting (Qt 6.5+, with a Windows registry fallback)."""
    try:
        hints = QApplication.styleHints()
        scheme = hints.colorScheme()
        if scheme == Qt.ColorScheme.Dark:
            return True
        if scheme == Qt.ColorScheme.Light:
            return False
    except Exception:
        pass
    if os.name == "nt":
        try:
            import winreg
            key = winreg.OpenKey(winreg.HKEY_CURRENT_USER, r"Software\Microsoft\Windows\CurrentVersion\Themes\Personalize")
            return winreg.QueryValueEx(key, "AppsUseLightTheme")[0] == 0
        except Exception:
            pass
    return True


def resolve_theme(choice: str) -> str:
    return ("dark" if system_prefers_dark() else "light") if choice == "auto" else choice


def build_stylesheet(name: str) -> str:
    from string import Template
    THEME.clear()
    THEME.update(THEMES[name])
    return Template(STYLESHEET_TEMPLATE).substitute(THEME)


class _UiBridge(QObject):
    """Runs callables on the GUI thread when emitted from worker threads."""
    call = pyqtSignal(object)


class Accordion(QWidget):
    """Inspector sections with 3D header buttons; one section open at a time (QToolBox-compatible API)."""
    currentChanged = pyqtSignal(int)

    def __init__(self):
        super().__init__()
        self._lay = QVBoxLayout(self)
        self._lay.setContentsMargins(0, 0, 0, 0)
        self._lay.setSpacing(5)
        self._lay.addStretch()
        self._headers, self._pages = [], []
        self._current = -1

    def addItem(self, page: QWidget, icon: QIcon, title: str):
        idx = len(self._pages)
        hdr = QPushButton(title)
        hdr.setObjectName("AccHeader")
        hdr.setIcon(icon)
        hdr.setIconSize(QSize(22, 22))
        hdr.setCheckable(True)
        hdr.setCursor(Qt.CursorShape.PointingHandCursor)
        hdr.clicked.connect(lambda _=False, i=idx: self.setCurrentIndex(i))
        page.setVisible(False)
        self._lay.insertWidget(self._lay.count() - 1, hdr)
        self._lay.insertWidget(self._lay.count() - 1, page)
        self._headers.append(hdr)
        self._pages.append(page)
        if self._current < 0:
            self.setCurrentIndex(0)
        return idx

    def count(self) -> int:
        return len(self._pages)

    def currentIndex(self) -> int:
        return self._current

    def setCurrentIndex(self, idx: int):
        if not 0 <= idx < len(self._pages):
            return
        self._current = idx
        for i, (h, pg) in enumerate(zip(self._headers, self._pages)):
            h.setChecked(i == idx)
            pg.setVisible(i == idx)
        self.currentChanged.emit(idx)


class ANKMediaStudio(QMainWindow):
    def __init__(self):
        super().__init__()
        self.setWindowTitle(f"{APP_NAME} v{APP_VERSION} — Created by {APP_AUTHOR}")
        self.setWindowIcon(make_icon("logo", "violet"))
        self.resize(1560, 980)
        self.setAcceptDrops(True)
        self.settings = QSettings("ANK", "MediaStudio")
        self.theme_choice = str(self.settings.value("theme", "auto"))
        self.setStyleSheet(build_stylesheet(resolve_theme(self.theme_choice)))

        self._bridge = _UiBridge()
        self._bridge.call.connect(lambda fn: fn())

        # State for Photo Editor (with Undo + Redo stacks)
        self.photo_base_bgra = None          # full-resolution working image (BGRA)
        self.photo_working_bgra = None
        self.photo_preview_base = None       # downscaled copy used for the live preview
        self.photo_preview_scale = 1.0
        self.photo_transform = TransformParams()
        self.photo_color = ColorParams()
        self.photo_text = TextOverlay()
        self.photo_layers: list[PhotoLayer] = []
        self.photo_path = ""
        self.photo_undo_stack = []
        self.photo_redo_stack = []
        self._photo_compare = False

        # State for Video Editor (with Undo + Redo stacks)
        self.video_sources: list[VideoSource] = []
        self.open_captures: dict[int, FrameReader] = {}
        self.clipboard_segments: list[TimelineSegment] = []
        self.video_undo_stack = []
        self.video_redo_stack = []
        self.video_preview_scale = 1.0
        self._separating = set()

        self.selected_speed = 1.0
        self.is_playing = False
        self.play_timer = QTimer()
        self.play_timer.setInterval(15)
        self.play_timer.timeout.connect(self._on_play_tick)
        self._play_clock = QElapsedTimer()
        self._play_start_ms = 0
        self._audio_sink = None
        self._audio_buffer = None
        self._audio_cache = (None, None, None)   # (key, sr, float audio)

        self.export_settings = {"format": 0, "fit": 0, "fps": 0, "quality": 1, "keep_pitch": True}
        self.overlays: list[OverlayItem] = []
        self.music: MusicTrack = None
        self.subtitles: list[dict] = []
        self.export_jobs = []
        self._export_worker_busy = False
        self.project_path = ""
        self._dirty = False

        self._build_ui()
        self._setup_shortcuts()
        self.timeline.overlays, self.timeline.subtitles, self.timeline.music = self.overlays, self.subtitles, None
        self._detect_encoders_async()
        self._rebuild_recent_menu()
        self._update_title()
        self._autosave_timer = QTimer(self)
        self._autosave_timer.setInterval(60_000)
        self._autosave_timer.timeout.connect(self._autosave)
        self._autosave_timer.start()
        QTimer.singleShot(600, self._offer_recovery)

    # ==========================================================================
    # KEYBOARD SHORTCUTS (paused while typing in a text/number box)
    # ==========================================================================
    def _setup_shortcuts(self):
        self._shortcuts = []

        def sc(keys, fn):
            s = QShortcut(QKeySequence(keys), self)
            s.activated.connect(fn)
            self._shortcuts.append(s)

        video_only = lambda fn: (lambda: fn() if self.tabs.currentIndex() == 0 else None)
        sc(Qt.Key.Key_Space, self._shortcut_space)
        sc("Ctrl+Z", self._shortcut_undo)
        sc("Ctrl+Y", self._shortcut_redo)
        sc("Ctrl+Shift+Z", self._shortcut_redo)
        sc("Ctrl+C", video_only(self._copy_marked_or_active_clip))
        sc("Ctrl+V", video_only(self._insert_copied_at_playhead))
        sc(Qt.Key.Key_Delete, video_only(self._delete_marked_or_active_clip))
        sc(Qt.Key.Key_Backspace, video_only(self._delete_marked_or_active_clip))
        sc("S", video_only(self._split_at_playhead_action))
        sc("[", video_only(self._set_mark_a))
        sc("]", video_only(self._set_mark_b))
        sc("Ctrl+[", video_only(lambda: self._toggle_mark_lock("A")))
        sc("Ctrl+]", video_only(lambda: self._toggle_mark_lock("B")))
        sc(Qt.Key.Key_Left, video_only(lambda: self._seek_relative(-self._frame_ms())))
        sc(Qt.Key.Key_Right, video_only(lambda: self._seek_relative(self._frame_ms())))
        sc("Shift+Left", video_only(lambda: self._seek_relative(-1000)))
        sc("Shift+Right", video_only(lambda: self._seek_relative(1000)))
        sc(Qt.Key.Key_Home, video_only(lambda: self._seek_absolute(0)))
        sc(Qt.Key.Key_End, video_only(lambda: self._seek_absolute(self.timeline.total_duration_ms())))
        sc("Ctrl+O", self._header_open)
        sc("Ctrl+S", self._save_shortcut)
        sc("Ctrl+Shift+S", lambda: self._save_project(save_as=True))
        sc("Ctrl+N", self._new_project)
        sc("Ctrl+Shift+O", lambda: self._open_project())
        sc("Ctrl+E", self._header_export)

        QApplication.instance().focusChanged.connect(self._on_focus_changed)
        try:
            QApplication.styleHints().colorSchemeChanged.connect(self._on_system_scheme_changed)
        except Exception:
            pass

    def _set_theme(self, choice: str):
        self.theme_choice = choice
        self.cmb_theme.blockSignals(True)
        self.cmb_theme.setCurrentIndex({"auto": 0, "dark": 1, "light": 2}.get(choice, 0))
        self.cmb_theme.blockSignals(False)
        self.settings.setValue("theme", choice)
        self._apply_theme()

    def _apply_theme(self):
        name = resolve_theme(self.theme_choice)
        self.setStyleSheet(build_stylesheet(name))
        for canvas in (self.video_Canvas, self.photo_canvas):
            canvas._update_border_style()
            canvas.update()
        self.timeline.update()
        self.status.showMessage(f"Theme: {name.title()}" + (" (following your computer)" if self.theme_choice == "auto" else ""))

    def _on_system_scheme_changed(self, *_):
        if self.theme_choice == "auto":
            self._apply_theme()

    def _on_focus_changed(self, _old, new):
        typing = isinstance(new, (QLineEdit, QAbstractSpinBox)) or (isinstance(new, QComboBox) and new.isEditable())
        for s in self._shortcuts:
            s.setEnabled(not typing)

    def _frame_ms(self) -> int:
        seg = self._get_active_video_segment() if self.timeline.segments else None
        return max(10, int(round(1000.0 / seg.source.fps))) if seg else 40

    def _shortcut_space(self):
        if self.tabs.currentIndex() == 0:
            self._toggle_playback()

    def _shortcut_undo(self):
        if self.tabs.currentIndex() == 1:
            self._undo_photo()
        else:
            self._undo_video()

    def _shortcut_redo(self):
        if self.tabs.currentIndex() == 1:
            self._redo_photo()
        else:
            self._redo_video()

    def _header_open(self):
        if self.tabs.currentIndex() == 1:
            self._open_photo()
        else:
            self.tabs.setCurrentIndex(0)
            self._add_videos(insert_at_playhead=False)

    def _header_export(self):
        if self.tabs.currentIndex() == 1:
            self._save_photo(transparent_png=False)
        else:
            self.tabs.setCurrentIndex(0)
            self._export_timeline_video()

    def _header_copy(self):
        if self.tabs.currentIndex() == 0:
            self._copy_marked_or_active_clip()

    def _header_paste(self):
        if self.tabs.currentIndex() == 0:
            self._insert_copied_at_playhead()

    # Global Drag & Drop routing
    def dragEnterEvent(self, event):
        if event.mimeData().hasUrls():
            event.acceptProposedAction()

    def dropEvent(self, event):
        paths = [u.toLocalFile() for u in event.mimeData().urls() if os.path.isfile(u.toLocalFile())]
        self._route_dropped_files(paths)
        event.acceptProposedAction()

    def _route_dropped_files(self, paths: list[str], insert_at_ms: int = None):
        projects = [p for p in paths if p.lower().endswith(".ank")]
        if projects:
            self._open_project(projects[0])
            return
        photo_files = [p for p in paths if os.path.splitext(p)[1].lower() in PHOTO_EXTS]
        video_files = [p for p in paths if os.path.splitext(p)[1].lower() in VIDEO_EXTS]

        if photo_files and (self.tabs.currentIndex() == 1 or not video_files):
            self.tabs.setCurrentIndex(1)
            self._load_photo_from_path(photo_files[0])
        if video_files:
            self.tabs.setCurrentIndex(0)
            self._load_video_paths(video_files, insert_at_ms=insert_at_ms)
        if not photo_files and not video_files and paths:
            self.status.showMessage("Unsupported file type. Drop videos (MP4, MOV, MKV, WEBM…) or photos (JPG, PNG, WEBP…).")

    # ==========================================================================
    # UI HELPERS
    # ==========================================================================
    @staticmethod
    def _row(*widgets, stretch_last=False):
        lay = QHBoxLayout()
        lay.setSpacing(6)
        for i, w in enumerate(widgets):
            if isinstance(w, int):
                lay.addSpacing(w)
            elif w is None:
                lay.addStretch()
            else:
                lay.addWidget(w, 1 if (stretch_last and i == len(widgets) - 1) else 0)
        return lay

    @staticmethod
    def _section(text):
        lbl = QLabel(text)
        lbl.setObjectName("Section")
        return lbl

    @staticmethod
    def _muted(text):
        lbl = QLabel(text)
        lbl.setObjectName("Muted")
        lbl.setWordWrap(True)
        return lbl

    def _toolbox_page(self, toolbox: "Accordion", title: str, icon: str, color: str):
        page = QWidget()
        page.setObjectName("ToolPage")
        lay = QVBoxLayout(page)
        lay.setContentsMargins(8, 8, 8, 10)
        lay.setSpacing(6)
        # "&" would be read as a keyboard mnemonic by Qt, so it is doubled
        toolbox.addItem(page, make_icon(icon, color), f"  {title.replace('&', '&&')}")
        return lay

    def _labeled_slider(self, lay, title, lo, hi, val, on_change, suffix=""):
        lbl = QLabel(f"{title}: {val}{suffix}")
        lbl.setMinimumWidth(150)
        sl = QSlider(Qt.Orientation.Horizontal)
        sl.setRange(lo, hi)
        sl.setValue(val)
        sl._title, sl._suffix, sl._label = title, suffix, lbl

        def changed(v):
            lbl.setText(f"{title}: {v}{suffix}")
            on_change(v)
        sl.valueChanged.connect(changed)
        lay.addLayout(self._row(lbl, sl, stretch_last=True))
        return sl

    @staticmethod
    def _set_slider_silently(sl: QSlider, v: int):
        sl.blockSignals(True)
        sl.setValue(int(v))
        sl.blockSignals(False)
        if hasattr(sl, "_label"):
            sl._label.setText(f"{sl._title}: {int(v)}{sl._suffix}")

    def _build_ui(self):
        main_widget = QWidget()
        main_layout = QVBoxLayout(main_widget)
        main_layout.setContentsMargins(10, 8, 10, 4)
        main_layout.setSpacing(8)

        # 3D Header: logo, title, version chip and the main toolbar
        header = QFrame()
        header.setObjectName("Header")
        hl = QHBoxLayout(header)
        hl.setContentsMargins(12, 6, 12, 6)
        logo = QLabel()
        logo.setPixmap(make_icon_pixmap("logo", "violet", 52))
        title_box = QVBoxLayout()
        title_box.setSpacing(0)
        title_lbl = QLabel(APP_NAME)
        title_lbl.setObjectName("AppTitle")
        sub_lbl = QLabel(f"Created by {APP_AUTHOR}  •  Video • AI Subtitles • Audio Stems • Photo • Download")
        sub_lbl.setObjectName("AppSub")
        title_box.addWidget(title_lbl)
        title_box.addWidget(sub_lbl)
        chip = QLabel(f"v{APP_VERSION}")
        chip.setObjectName("Chip")
        hl.addWidget(logo)
        hl.addLayout(title_box)
        hl.addSpacing(8)
        hl.addWidget(chip, 0, Qt.AlignmentFlag.AlignTop)
        hl.addStretch()
        theme_lbl = QLabel("Theme")
        theme_lbl.setStyleSheet("color: #c7d2fe; font-weight: 700;")
        self.cmb_theme = QComboBox()
        self.cmb_theme.addItems(["Auto (follow computer)", "Dark", "Light"])
        self.cmb_theme.setCurrentIndex({"auto": 0, "dark": 1, "light": 2}.get(self.theme_choice, 0))
        self.cmb_theme.setToolTip("Auto follows your computer's dark / light setting")
        self.cmb_theme.currentIndexChanged.connect(lambda i: self._set_theme(("auto", "dark", "light")[i]))
        hl.addWidget(theme_lbl)
        hl.addWidget(self.cmb_theme)
        hl.addSpacing(10)
        proj_btn = tool_button("Project", "save", "violet", "New, open and save projects (.ank) — autosaved every minute", size=30)
        proj_btn.setPopupMode(QToolButton.ToolButtonPopupMode.InstantPopup)
        pm = QMenu(proj_btn)
        pm.addAction(make_icon("add", "green"), "New Project\tCtrl+N", self._new_project)
        pm.addAction(make_icon("open", "amber"), "Open Project…\tCtrl+Shift+O", lambda: self._open_project())
        pm.addAction(make_icon("save", "blue"), "Save Project\tCtrl+S", self._save_project)
        pm.addAction(make_icon("save", "violet"), "Save Project As…\tCtrl+Shift+S", lambda: self._save_project(save_as=True))
        pm.addSeparator()
        self.menu_recent = pm.addMenu(make_icon("film", "slate"), "Recent Projects")
        proj_btn.setMenu(pm)
        hl.addWidget(proj_btn)
        for text, icon, color, tip, fn in (
            ("Open", "open", "amber", "Open video(s) or a photo (Ctrl+O)", self._header_open),
            ("Undo", "undo", "slate", "Undo (Ctrl+Z)", self._shortcut_undo),
            ("Redo", "redo", "slate", "Redo (Ctrl+Y)", self._shortcut_redo),
            ("Copy", "copy", "sky", "Copy [A-B] or active clip (Ctrl+C)", self._header_copy),
            ("Paste", "paste", "sky", "Paste at playhead (Ctrl+V)", self._header_paste),
            ("Export", "export", "green", "Export video / Save photo (Ctrl+E / Ctrl+S)", self._header_export),
        ):
            b = tool_button(text, icon, color, tip, size=30)
            b.clicked.connect(fn)
            hl.addWidget(b)
        main_layout.addWidget(header)

        # Workspace Tabs
        self.tabs = QTabWidget()
        self.tabs.setIconSize(QSize(22, 22))
        self.tabs.addTab(self._build_video_tab(), make_icon("film", "blue"), "Video && Audio Stem Studio")
        self.tabs.addTab(self._build_photo_tab(), make_icon("image", "pink"), "Photo, Retouch && AI Studio")
        self.tabs.addTab(self._build_download_tab(), make_icon("export", "green"), "Download")
        self.tabs.currentChanged.connect(lambda _: self.is_playing and self._toggle_playback())
        main_layout.addWidget(self.tabs, 1)

        self.setCentralWidget(main_widget)
        self.status = QStatusBar()
        self.setStatusBar(self.status)
        audio_note = "" if HAS_QT_AUDIO else "  •  (Preview audio unavailable: QtMultimedia missing)"
        self.status.showMessage(
            f"Ready — {APP_NAME} v{APP_VERSION} by {APP_AUTHOR}. Right-click the monitor or timeline for quick menus.{audio_note}"
        )

    # ==========================================================================
    # TAB 1: MULTI-CLIP VIDEO & AUDIO STEM STUDIO
    # ==========================================================================
    def _build_video_tab(self):
        tab = QWidget()
        layout = QVBoxLayout(tab)
        layout.setContentsMargins(8, 8, 8, 8)
        top_split = QHBoxLayout()
        top_split.setSpacing(10)

        # Left: Video Monitor + transport + clip info
        monitor_box = QVBoxLayout()
        monitor_box.setSpacing(6)
        self.video_Canvas = PhotoCanvas("Drag & drop video files here  •  Right-click for the quick menu", "film")
        self.video_Canvas.crop_Completed.connect(self._apply_video_crop_to_active_segment)
        self.video_Canvas.free_Moved.connect(self._on_video_free_moved)
        self.video_Canvas.move_Started.connect(self._push_video_undo)
        self.video_Canvas.wheel_Scaled.connect(self._on_video_wheel_scaled)
        self.video_Canvas.files_Dropped.connect(lambda paths: self._route_dropped_files(paths, insert_at_ms=None))
        self.video_Canvas.right_Clicked.connect(self._on_video_monitor_right_clicked)
        monitor_box.addWidget(self.video_Canvas, stretch=1)

        transport = QFrame()
        transport.setObjectName("Transport")
        tl = QHBoxLayout(transport)
        tl.setContentsMargins(10, 4, 10, 4)
        for icon, tip, fn in (
            ("to_start", "Go to start (Home)", lambda: self._seek_absolute(0)),
            ("step_back", "Back 1 frame (←)  •  Shift+← = 1 s", lambda: self._seek_relative(-self._frame_ms())),
        ):
            b = tool_button("", icon, "slate", tip, size=30)
            b.clicked.connect(fn)
            tl.addWidget(b)
        self.btn_play = tool_button("", "play", "green", "Play / Pause (Space)", size=42)
        self.btn_play.clicked.connect(self._toggle_playback)
        tl.addWidget(self.btn_play)
        for icon, tip, fn in (
            ("step_fwd", "Forward 1 frame (→)  •  Shift+→ = 1 s", lambda: self._seek_relative(self._frame_ms())),
            ("to_end", "Go to end (End)", lambda: self._seek_absolute(self.timeline.total_duration_ms())),
        ):
            b = tool_button("", icon, "slate", tip, size=30)
            b.clicked.connect(fn)
            tl.addWidget(b)
        tl.addSpacing(10)
        self.lbl_time_counter = QLabel("00:00.000 / 00:00.000")
        self.lbl_time_counter.setObjectName("Clock")
        tl.addWidget(self.lbl_time_counter)
        tl.addSpacing(6)
        self.chk_preview_audio = QCheckBox("Sound")
        self.chk_preview_audio.setChecked(HAS_QT_AUDIO)
        self.chk_preview_audio.setEnabled(HAS_QT_AUDIO)
        self.chk_preview_audio.setToolTip("Play the timeline's audio mix while previewing")
        tl.addWidget(self.chk_preview_audio)
        self.chk_loop = QCheckBox("Loop A-B")
        self.chk_loop.setToolTip("Loop playback between Mark A and Mark B")
        tl.addWidget(self.chk_loop)
        self.chk_output_view = QCheckBox("Final output")
        self.chk_output_view.setToolTip("Preview exactly what will be exported: framing, transitions, layers and subtitles")
        self.chk_output_view.toggled.connect(self._on_output_view_toggled)
        tl.addWidget(self.chk_output_view)
        tl.addStretch()
        for icon, tip, fn in (
            ("camera", "Save the current frame as PNG", self._snapshot_frame),
            ("image", "Send the current frame to the Photo Studio", self._frame_to_photo_studio),
        ):
            b = tool_button("", icon, "pink", tip, size=28)
            b.clicked.connect(fn)
            tl.addWidget(b)
        monitor_box.addWidget(transport)

        info_bar = QHBoxLayout()
        self.lbl_active_clip_badge = QLabel("Active Clip: None")
        self.lbl_active_clip_badge.setFont(QFont("Segoe UI", 10, QFont.Weight.Bold))
        self.lbl_active_clip_badge.setObjectName("Badge")
        info_bar.addWidget(self.lbl_active_clip_badge, 1)
        monitor_box.addLayout(info_bar)

        # Color-coded bar showing all loaded video sources
        self.sources_legend_layout = QHBoxLayout()
        lbl_leg = QLabel("Loaded videos:")
        lbl_leg.setObjectName("Muted")
        self.sources_legend_layout.addWidget(lbl_leg)
        self.sources_legend_layout.addStretch()
        monitor_box.addLayout(self.sources_legend_layout)
        top_split.addLayout(monitor_box, stretch=3)

        # Right: Inspector (accordion of tool sections)
        inspector = Accordion()
        inspector.setMinimumWidth(470)
        self.video_inspector = inspector

        # --- 1. Media & Edit ---
        lay = self._toolbox_page(inspector, "Media & Edit", "film", "blue")
        btn_add_end = icon_button("Append Video(s)", "add", "green", "Add videos at the end of the timeline", "primary")
        btn_add_end.clicked.connect(lambda: self._add_videos(insert_at_playhead=False))
        btn_insert_between = icon_button("Insert at Playhead", "insert", "teal", "Insert videos where the playhead is")
        btn_insert_between.clicked.connect(lambda: self._add_videos(insert_at_playhead=True))
        lay.addLayout(self._row(btn_add_end, btn_insert_between))
        btn_split_here = icon_button("Split (S)", "split", "orange", "Split the clip at the playhead")
        btn_split_here.clicked.connect(self._split_at_playhead_action)
        btn_cp = icon_button("Copy", "copy", "sky", "Copy [A-B] or the active clip (Ctrl+C)")
        btn_cp.clicked.connect(self._copy_marked_or_active_clip)
        btn_pst = icon_button("Paste", "paste", "sky", "Paste at the playhead (Ctrl+V)")
        btn_pst.clicked.connect(self._insert_copied_at_playhead)
        btn_del = icon_button("Delete", "trash", "red", "Delete [A-B] or the active clip (Del)")
        btn_del.clicked.connect(self._delete_marked_or_active_clip)
        lay.addLayout(self._row(btn_split_here, btn_cp, btn_pst, btn_del))

        lay.addWidget(self._section("Selection  (Mark A → Mark B)"))
        self.lbl_marks_info = QLabel("Mark A: --:--.---   |   Mark B: --:--.---")
        self.lbl_marks_info.setObjectName("Info")
        lay.addWidget(self.lbl_marks_info)
        btn_set_a = icon_button("Mark A ([)", "marker", "cyan")
        btn_set_a.clicked.connect(self._set_mark_a)
        btn_set_b = icon_button("Mark B (])", "marker", "rose")
        btn_set_b.clicked.connect(self._set_mark_b)
        btn_auto_mark = icon_button("Mark Clip", "ab", "indigo", "Mark the whole active clip")
        btn_auto_mark.clicked.connect(self._auto_mark_scene)
        btn_clear_marks = icon_button("Clear", "reset", "slate")
        btn_clear_marks.clicked.connect(self._clear_marks)
        lay.addLayout(self._row(btn_set_a, btn_set_b, btn_auto_mark, btn_clear_marks))
        self.btn_lock_a = icon_button("Lock A", "unlock", "cyan", "Lock Mark A so it can't move (Ctrl+[). Play starts from a locked A.", checkable=True)
        self.btn_lock_a.clicked.connect(lambda checked: self._toggle_mark_lock("A", checked))
        self.btn_lock_b = icon_button("Lock B", "unlock", "rose", "Lock Mark B so it can't move (Ctrl+]). Play stops at a locked B.", checkable=True)
        self.btn_lock_b.clicked.connect(lambda checked: self._toggle_mark_lock("B", checked))
        lay.addLayout(self._row(self.btn_lock_a, self.btn_lock_b))
        lay.addWidget(self._muted("Drag the A / B flags on the timeline ruler to move a mark — the monitor shows the exact frame live."))
        btn_del_mark = icon_button("Delete [A-B]", "trash", "red")
        btn_del_mark.clicked.connect(self._delete_marked_region)
        btn_trim_mark = icon_button("Keep Only [A-B]", "keep", "amber")
        btn_trim_mark.clicked.connect(self._trim_to_marked_region)
        btn_replace_mark = icon_button("Replace [A-B]", "paste", "violet", "Replace [A-B] with the copied selection")
        btn_replace_mark.clicked.connect(self._replace_marked_with_copied)
        lay.addLayout(self._row(btn_del_mark, btn_trim_mark, btn_replace_mark))
        lay.addStretch()

        # --- 2. Trim ---
        lay = self._toolbox_page(inspector, "Trim Start / End (Locked or Single Stem)", "split", "orange")
        self.chk_lock_tracks = QCheckBox("Lock video and all audio stems together when trimming")
        self.chk_lock_tracks.setChecked(True)
        self.chk_lock_tracks.setObjectName("Strong")
        self.chk_lock_tracks.toggled.connect(self._on_lock_tracks_toggled)
        lay.addWidget(self.chk_lock_tracks)
        self.cmb_trim_target = QComboBox()
        self.cmb_trim_target.addItems([
            "Whole Clip (Video + Voices + Music + Noises)",
            "Voices / Speech Stem Only (Keep Video)",
            "Music / Instruments Stem Only (Keep Video)",
            "Noises / Ambience Stem Only (Keep Video)",
        ])
        self.cmb_trim_target.currentIndexChanged.connect(self._on_trim_target_combo_changed)
        self.spn_trim_sec = QDoubleSpinBox()
        self.spn_trim_sec.setRange(0.1, 120.0)
        self.spn_trim_sec.setSingleStep(0.5)
        self.spn_trim_sec.setValue(2.0)
        self.spn_trim_sec.setSuffix(" s")
        lay.addLayout(self._row(QLabel("Target:"), self.cmb_trim_target, stretch_last=True))
        lay.addLayout(self._row(QLabel("Amount:"), self.spn_trim_sec, None))
        btn_trim_first = icon_button("Cut First N s", "to_start", "amber", kind="warn")
        btn_trim_first.clicked.connect(lambda: self._exec_quick_trim(from_start=True))
        btn_trim_last = icon_button("Cut Last N s", "to_end", "amber", kind="warn")
        btn_trim_last.clicked.connect(lambda: self._exec_quick_trim(from_start=False))
        lay.addLayout(self._row(btn_trim_first, btn_trim_last))
        btn_trim_start_ph = icon_button("Trim Start → Playhead", "split", "orange")
        btn_trim_start_ph.clicked.connect(lambda: self._trim_at_timestamp(self.timeline.playhead_ms, from_start=True))
        btn_trim_end_ph = icon_button("Trim Playhead → End", "split", "orange")
        btn_trim_end_ph.clicked.connect(lambda: self._trim_at_timestamp(self.timeline.playhead_ms, from_start=False))
        lay.addLayout(self._row(btn_trim_start_ph, btn_trim_end_ph))
        lay.addWidget(self._muted("Tip: drag the yellow edges of a clip on the timeline to trim. Unlock to drag a single stem's edges."))
        lay.addStretch()

        # --- 3. Audio Mixer ---
        lay = self._toolbox_page(inspector, "Audio Mixer & Stem Separator", "mic", "sky")
        self.btn_sep_audio = icon_button("Separate Audio into Voices, Music & Noises", "mic", "sky", kind="primary")
        self.btn_sep_audio.clicked.connect(self._separate_audio_for_active_clip)
        self.cmb_sep_engine = QComboBox()
        self.cmb_sep_engine.addItem("Fast — frequency filter (instant)", "fast")
        self.cmb_sep_engine.addItem("AI — Demucs (clean vocals, slower)" if demucs_available() else
                                    "AI — Demucs (not installed: pip install demucs)", "demucs")
        if demucs_available():
            self.cmb_sep_engine.setCurrentIndex(1)
        else:
            self.cmb_sep_engine.model().item(1).setEnabled(False)
        lay.addWidget(self.btn_sep_audio)
        lay.addLayout(self._row(QLabel("Engine:"), self.cmb_sep_engine, stretch_last=True))
        self.lbl_sep_progress = self._muted("Stems: not separated yet for the active clip.")
        lay.addWidget(self.lbl_sep_progress)

        self.lbl_vox = QLabel("Voices / Speech: 100%")
        self.sl_vox = QSlider(Qt.Orientation.Horizontal)
        self.sl_vox.setRange(0, 200)
        self.sl_vox.setValue(100)
        self.sl_vox.valueChanged.connect(self._on_audio_stem_sliders_changed)
        btn_mute_vox = icon_button("", "mute", "slate", "Mute / restore voices")
        btn_mute_vox.clicked.connect(lambda: self.sl_vox.setValue(0 if self.sl_vox.value() > 0 else 100))
        lay.addLayout(self._row(QLabel(), self.lbl_vox, None))
        lay.addLayout(self._row(self.sl_vox, btn_mute_vox))
        self.lbl_vox.setMinimumWidth(180)

        self.lbl_mus = QLabel("Music / Instruments: 100%")
        self.sl_mus = QSlider(Qt.Orientation.Horizontal)
        self.sl_mus.setRange(0, 200)
        self.sl_mus.setValue(100)
        self.sl_mus.valueChanged.connect(self._on_audio_stem_sliders_changed)
        btn_mute_mus = icon_button("", "mute", "slate", "Mute / restore music")
        btn_mute_mus.clicked.connect(lambda: self.sl_mus.setValue(0 if self.sl_mus.value() > 0 else 100))
        lay.addLayout(self._row(QLabel(), self.lbl_mus, None))
        lay.addLayout(self._row(self.sl_mus, btn_mute_mus))

        self.lbl_nse = QLabel("Noises / Ambience: 100%")
        self.sl_nse = QSlider(Qt.Orientation.Horizontal)
        self.sl_nse.setRange(0, 200)
        self.sl_nse.setValue(100)
        self.sl_nse.valueChanged.connect(self._on_audio_stem_sliders_changed)
        btn_kill_nse = icon_button("", "mute", "red", "Remove background noise")
        btn_kill_nse.clicked.connect(lambda: self.sl_nse.setValue(0))
        lay.addLayout(self._row(QLabel(), self.lbl_nse, None))
        lay.addLayout(self._row(self.sl_nse, btn_kill_nse))

        lay.addWidget(self._section("Clip volume & audio fades"))
        self.sl_gain = self._labeled_slider(lay, "Clip Volume", 0, 200, 100, self._on_clip_gain_changed, "%")
        self.spn_afade_in = QDoubleSpinBox()
        self.spn_afade_in.setRange(0, 10)
        self.spn_afade_in.setSingleStep(0.25)
        self.spn_afade_in.setSuffix(" s")
        self.spn_afade_out = QDoubleSpinBox()
        self.spn_afade_out.setRange(0, 10)
        self.spn_afade_out.setSingleStep(0.25)
        self.spn_afade_out.setSuffix(" s")
        btn_afade = icon_button("Apply Fades", "fade", "indigo")
        btn_afade.clicked.connect(self._apply_audio_fades)
        lay.addLayout(self._row(QLabel("Fade in"), self.spn_afade_in, QLabel("out"), self.spn_afade_out, btn_afade))
        btn_apply_stems_mark = icon_button("Apply Mix to [Mark A - B]", "ab", "violet", kind="accent")
        btn_apply_stems_mark.clicked.connect(self._apply_audio_mix_to_marked_region)
        lay.addWidget(btn_apply_stems_mark)
        lay.addStretch()

        # --- 4. Transform & AI ---
        lay = self._toolbox_page(inspector, "Transform, Crop & AI", "move", "teal")
        btn_v_cw = icon_button("90° CW", "rotate_cw", "teal")
        btn_v_cw.clicked.connect(lambda: self._mod_video_transform(rot_step=1))
        btn_v_ccw = icon_button("90° CCW", "rotate_ccw", "teal")
        btn_v_ccw.clicked.connect(lambda: self._mod_video_transform(rot_step=-1))
        btn_v_180 = icon_button("180°", "rotate_cw", "cyan")
        btn_v_180.clicked.connect(lambda: self._mod_video_transform(rot_step=2))
        lay.addLayout(self._row(btn_v_cw, btn_v_ccw, btn_v_180))
        btn_v_fliph = icon_button("Flip H", "flip_h", "indigo")
        btn_v_fliph.clicked.connect(lambda: self._mod_video_transform(flip_h=True))
        btn_v_flipv = icon_button("Flip V", "flip_v", "indigo")
        btn_v_flipv.clicked.connect(lambda: self._mod_video_transform(flip_v=True))
        btn_v_reset = icon_button("Reset Clip", "reset", "slate", "Reset transform, crop, speed and audio mix")
        btn_v_reset.clicked.connect(self._reset_video_transform)
        lay.addLayout(self._row(btn_v_fliph, btn_v_flipv, btn_v_reset))
        self.lbl_v_angle = QLabel("Free Angle: 0°")
        self.lbl_v_angle.setMinimumWidth(110)
        self.sl_v_angle = QSlider(Qt.Orientation.Horizontal)
        self.sl_v_angle.setRange(-180, 180)
        self.sl_v_angle.setValue(0)
        self.sl_v_angle.sliderPressed.connect(self._push_video_undo)
        self.sl_v_angle.valueChanged.connect(self._on_video_angle_slider)
        lay.addLayout(self._row(self.lbl_v_angle, self.sl_v_angle, stretch_last=True))
        self.lbl_v_scale = QLabel("Scale: 100%")
        self.lbl_v_scale.setMinimumWidth(110)
        self.sl_v_scale = QSlider(Qt.Orientation.Horizontal)
        self.sl_v_scale.setRange(10, 300)
        self.sl_v_scale.setValue(100)
        self.sl_v_scale.sliderPressed.connect(self._push_video_undo)
        self.sl_v_scale.valueChanged.connect(self._on_video_scale_slider)
        lay.addLayout(self._row(self.lbl_v_scale, self.sl_v_scale, stretch_last=True))
        self.btn_crop_vid = icon_button("Crop Frame", "crop", "orange", "Drag a rectangle on the monitor", checkable=True)
        self.btn_crop_vid.clicked.connect(self._toggle_video_spatial_crop)
        btn_uncrop = icon_button("Remove Crop", "reset", "slate")
        btn_uncrop.clicked.connect(self._remove_video_crop)
        self.btn_move_vid = icon_button("Free Move", "move", "amber", "Drag the picture; wheel to scale", checkable=True)
        self.btn_move_vid.clicked.connect(self._toggle_video_free_move)
        lay.addLayout(self._row(self.btn_crop_vid, btn_uncrop, self.btn_move_vid))
        lay.addWidget(self._section("AI tools"))
        self.btn_v_ai_upscale = icon_button("AI Upsize / HD", "hd", "violet", checkable=True)
        self.btn_v_ai_upscale.clicked.connect(self._toggle_video_ai_upscale)
        self.btn_v_cutout = icon_button("AI Cutout Subject", "person", "pink", checkable=True)
        self.btn_v_cutout.clicked.connect(self._toggle_video_cutout)
        lay.addLayout(self._row(self.btn_v_ai_upscale, self.btn_v_cutout))
        btn_v_bg_img = icon_button("Background Image…", "image", "green")
        btn_v_bg_img.clicked.connect(self._set_video_custom_bg)
        btn_v_bg_clear = icon_button("Clear BG", "reset", "slate")
        btn_v_bg_clear.clicked.connect(self._clear_video_custom_bg)
        lay.addLayout(self._row(btn_v_bg_img, btn_v_bg_clear))
        lay.addStretch()

        # --- 5. Color & Filters ---
        lay = self._toolbox_page(inspector, "Color Grading & Filters", "palette", "pink")
        self.cmb_v_filter = QComboBox()
        for key, title in FILTER_PRESETS:
            self.cmb_v_filter.addItem(title, key)
        self.cmb_v_filter.currentIndexChanged.connect(self._on_video_color_changed)
        lay.addLayout(self._row(QLabel("Look:"), self.cmb_v_filter, stretch_last=True))
        self.v_color_sliders = {}
        for field, title, lo, hi in (
            ("brightness", "Brightness", -100, 100), ("contrast", "Contrast", -100, 100),
            ("saturation", "Saturation", -100, 100), ("warmth", "Warmth", -100, 100), ("tint", "Tint", -100, 100),
            ("highlights", "Highlights", -100, 100), ("shadows", "Shadows", -100, 100),
            ("sharpness", "Sharpen", 0, 100), ("vignette", "Vignette", 0, 100),
        ):
            sl = self._labeled_slider(lay, title, lo, hi, 0, lambda _v: self._on_video_color_changed())
            sl.sliderPressed.connect(self._push_video_undo)
            self.v_color_sliders[field] = sl
        btn_c_reset = icon_button("Reset Color", "reset", "slate")
        btn_c_reset.clicked.connect(self._reset_video_color)
        btn_c_all = icon_button("Apply to All Clips", "layers", "violet", kind="accent")
        btn_c_all.clicked.connect(self._apply_color_to_all_clips)
        lay.addLayout(self._row(btn_c_reset, btn_c_all))
        lay.addStretch()

        # --- 6. Titles & Fades ---
        lay = self._toolbox_page(inspector, "Titles, Text & Video Fades", "text", "amber")
        self.txt_v_title = QLineEdit()
        self.txt_v_title.setPlaceholderText("Title or caption for the active clip  (use | for a new line)")
        lay.addWidget(self.txt_v_title)
        self.spn_v_text_size = QSpinBox()
        self.spn_v_text_size.setRange(2, 30)
        self.spn_v_text_size.setValue(7)
        self.spn_v_text_size.setSuffix(" % height")
        self.cmb_v_text_pos = QComboBox()
        self.cmb_v_text_pos.addItems(["Bottom", "Center", "Top"])
        self.btn_v_text_color = QPushButton("Color")
        self.btn_v_text_color.clicked.connect(lambda: self._pick_text_color(self.btn_v_text_color))
        self._set_color_button(self.btn_v_text_color, "#FFFFFF")
        lay.addLayout(self._row(QLabel("Size"), self.spn_v_text_size, QLabel("Position"), self.cmb_v_text_pos, self.btn_v_text_color))
        self.chk_v_text_outline = QCheckBox("Outline")
        self.chk_v_text_outline.setChecked(True)
        self.chk_v_text_backdrop = QCheckBox("Dark backdrop")
        btn_text_apply = icon_button("Apply Title", "text", "amber", kind="warn")
        btn_text_apply.clicked.connect(self._apply_video_title)
        btn_text_clear = icon_button("Remove", "trash", "red")
        btn_text_clear.clicked.connect(self._clear_video_title)
        lay.addLayout(self._row(self.chk_v_text_outline, self.chk_v_text_backdrop, None))
        lay.addLayout(self._row(btn_text_apply, btn_text_clear))
        lay.addWidget(self._section("Fade from / to black"))
        self.spn_vfade_in = QDoubleSpinBox()
        self.spn_vfade_in.setRange(0, 10)
        self.spn_vfade_in.setSingleStep(0.25)
        self.spn_vfade_in.setSuffix(" s")
        self.spn_vfade_out = QDoubleSpinBox()
        self.spn_vfade_out.setRange(0, 10)
        self.spn_vfade_out.setSingleStep(0.25)
        self.spn_vfade_out.setSuffix(" s")
        btn_vfade = icon_button("Apply", "fade", "indigo")
        btn_vfade.clicked.connect(self._apply_video_fades)
        lay.addLayout(self._row(QLabel("In"), self.spn_vfade_in, QLabel("Out"), self.spn_vfade_out, btn_vfade))
        lay.addWidget(self._muted("Video fades also fade the clip's sound so cuts feel smooth."))
        lay.addStretch()

        # --- 7. Speed ---
        lay = self._toolbox_page(inspector, "Speed — Slow-Mo & Fast-Forward", "speed", "violet")
        self.lbl_speed_val = QLabel("Target Speed: 1.00x (Normal)")
        self.lbl_speed_val.setObjectName("Accent")
        self.sl_speed = QSlider(Qt.Orientation.Horizontal)
        self.sl_speed.setRange(10, 800)
        self.sl_speed.setValue(100)
        self.sl_speed.valueChanged.connect(self._on_speed_slider_changed)
        lay.addWidget(self.lbl_speed_val)
        lay.addWidget(self.sl_speed)
        grid = QGridLayout()
        for i, (spd, title) in enumerate([(0.10, "0.1x"), (0.25, "0.25x"), (0.50, "0.5x"), (0.75, "0.75x"), (1.0, "1x"),
                                          (1.25, "1.25x"), (1.50, "1.5x"), (2.0, "2x"), (4.0, "4x"), (8.0, "8x")]):
            b = QPushButton(title)
            b.clicked.connect(lambda _, s=spd: self._set_speed_preset(s))
            grid.addWidget(b, i // 5, i % 5)
        lay.addLayout(grid)
        btn_apply_sp_mark = icon_button("Apply to [Mark A - B]", "ab", "violet", kind="accent")
        btn_apply_sp_mark.clicked.connect(self._apply_speed_to_marked_region)
        btn_apply_sp_clip = icon_button("Apply to Active Clip", "speed", "violet")
        btn_apply_sp_clip.clicked.connect(self._apply_speed_to_active_clip)
        lay.addLayout(self._row(btn_apply_sp_mark, btn_apply_sp_clip))
        lay.addWidget(self._muted("Exports keep voices at their natural pitch when the speed changes (needs FFmpeg)."))
        lay.addStretch()

        # --- 8. Transitions & Motion ---
        lay = self._toolbox_page(inspector, "Transitions & Motion (Ken Burns)", "layers", "cyan")
        lay.addWidget(self._section("Transition into the active clip"))
        self.cmb_transition = QComboBox()
        for key, title in TRANSITION_TYPES:
            self.cmb_transition.addItem(title, key)
        self.spn_transition = QDoubleSpinBox()
        self.spn_transition.setRange(0.1, 3.0)
        self.spn_transition.setSingleStep(0.1)
        self.spn_transition.setValue(0.6)
        self.spn_transition.setSuffix(" s")
        lay.addLayout(self._row(self.cmb_transition, self.spn_transition, stretch_last=False))
        btn_tr = icon_button("Apply to This Cut", "layers", "cyan", kind="primary")
        btn_tr.clicked.connect(lambda: self._apply_transition(all_cuts=False))
        btn_tr_all = icon_button("Apply to All Cuts", "layers", "violet", kind="accent")
        btn_tr_all.clicked.connect(lambda: self._apply_transition(all_cuts=True))
        lay.addLayout(self._row(btn_tr, btn_tr_all))
        lay.addWidget(self._section("Motion over the active clip"))
        self.cmb_motion = QComboBox()
        for key, title in MOTION_TYPES:
            self.cmb_motion.addItem(title, key)
        self.spn_motion = QSpinBox()
        self.spn_motion.setRange(5, 60)
        self.spn_motion.setValue(20)
        self.spn_motion.setSuffix(" % strength")
        btn_mo = icon_button("Apply Motion", "zoom_in", "teal")
        btn_mo.clicked.connect(self._apply_motion)
        lay.addLayout(self._row(self.cmb_motion, self.spn_motion, btn_mo))
        lay.addWidget(self._muted("Slow zooms and pans bring still shots and photos to life. Transitions show in "
                                  "'Final output' view and in exports."))
        lay.addStretch()

        # --- 9. Layers & Music ---
        lay = self._toolbox_page(inspector, "Layers (Logo, PiP) & Background Music", "image", "green")
        btn_ov_img = icon_button("Add Logo / Image", "image", "green", kind="primary")
        btn_ov_img.clicked.connect(lambda: self._add_overlay("image"))
        btn_ov_vid = icon_button("Add Picture-in-Picture", "film", "blue")
        btn_ov_vid.clicked.connect(lambda: self._add_overlay("video"))
        lay.addLayout(self._row(btn_ov_img, btn_ov_vid))
        self.lst_overlays = QListWidget()
        self.lst_overlays.setMaximumHeight(92)
        self.lst_overlays.currentRowChanged.connect(self._on_overlay_selected)
        lay.addWidget(self.lst_overlays)
        self.cmb_ov_pos = QComboBox()
        self.cmb_ov_pos.addItems(list(OverlayItem.POSITIONS.keys()))
        self.cmb_ov_pos.setCurrentText("Top Right")
        self.cmb_ov_pos.currentIndexChanged.connect(self._on_overlay_changed)
        lay.addLayout(self._row(QLabel("Position"), self.cmb_ov_pos, stretch_last=True))
        self.sl_ov_size = self._labeled_slider(lay, "Size", 5, 80, 22, lambda _v: self._on_overlay_changed(), "% width")
        self.sl_ov_opacity = self._labeled_slider(lay, "Opacity", 10, 100, 100, lambda _v: self._on_overlay_changed(), "%")
        btn_ov_marks = icon_button("Show Only in [A-B]", "ab", "indigo")
        btn_ov_marks.clicked.connect(lambda: self._set_overlay_range(use_marks=True))
        btn_ov_all = icon_button("Whole Video", "film", "slate")
        btn_ov_all.clicked.connect(lambda: self._set_overlay_range(use_marks=False))
        btn_ov_del = icon_button("Remove", "trash", "red")
        btn_ov_del.clicked.connect(self._remove_overlay)
        lay.addLayout(self._row(btn_ov_marks, btn_ov_all, btn_ov_del))

        lay.addWidget(self._section("Background music"))
        self.lbl_music = self._muted("No music track.")
        lay.addWidget(self.lbl_music)
        btn_music = icon_button("Choose Music…", "music", "pink", kind="primary")
        btn_music.clicked.connect(self._set_music)
        btn_music_ph = icon_button("Start at Playhead", "insert", "teal")
        btn_music_ph.clicked.connect(self._music_to_playhead)
        btn_music_del = icon_button("Remove", "trash", "red")
        btn_music_del.clicked.connect(self._remove_music)
        lay.addLayout(self._row(btn_music, btn_music_ph, btn_music_del))
        self.sl_music_vol = self._labeled_slider(lay, "Music Volume", 0, 150, 60, lambda _v: self._on_music_changed(), "%")
        self.sl_music_duck = self._labeled_slider(lay, "Under Voices", 5, 100, 30, lambda _v: self._on_music_changed(), "%")
        self.chk_music_loop = QCheckBox("Loop to fill the video")
        self.chk_music_loop.setChecked(True)
        self.chk_music_loop.toggled.connect(lambda _c: self._on_music_changed())
        lay.addWidget(self.chk_music_loop)
        lay.addWidget(self._muted("'Under Voices' is auto-ducking: the music drops to this level whenever someone speaks."))
        lay.addStretch()

        # --- 10. Subtitles (AI) ---
        lay = self._toolbox_page(inspector, "Subtitles — AI Auto-Captions (Whisper)", "text", "violet")
        eng = whisper_engine_name()
        self.lbl_sub_engine = self._muted(
            f"Speech engine: {eng} (runs on this computer, free)." if eng else
            "Speech engine not installed. Run:  pip install faster-whisper   then restart the app.")
        lay.addWidget(self.lbl_sub_engine)
        form = QFormLayout()
        self.cmb_sub_model = QComboBox()
        self.cmb_sub_model.addItems(["tiny  (fastest)", "base", "small  (recommended)", "medium", "large-v3  (best, slow)"])
        self.cmb_sub_model.setCurrentIndex(2)
        self.cmb_sub_lang = QComboBox()
        for code, name in WHISPER_LANGS:
            self.cmb_sub_lang.addItem(name, code)
        self.cmb_sub_task = QComboBox()
        self.cmb_sub_task.addItems(["Captions in the spoken language", "Translate speech to English"])
        form.addRow("Model", self.cmb_sub_model)
        form.addRow("Spoken language", self.cmb_sub_lang)
        form.addRow("Result", self.cmb_sub_task)
        lay.addLayout(form)
        self.btn_gen_subs = icon_button("Generate Subtitles", "sparkle", "violet", kind="accent")
        self.btn_gen_subs.setEnabled(bool(eng))
        self.btn_gen_subs.clicked.connect(self._generate_subtitles)
        lay.addWidget(self.btn_gen_subs)
        self.lbl_sub_status = self._muted("No subtitles yet.")
        lay.addWidget(self.lbl_sub_status)
        btn_sub_edit = icon_button("Edit…", "text", "amber")
        btn_sub_edit.clicked.connect(self._edit_subtitles)
        btn_sub_imp = icon_button("Import .SRT", "open", "amber")
        btn_sub_imp.clicked.connect(self._import_srt)
        btn_sub_exp = icon_button("Save .SRT", "save", "blue")
        btn_sub_exp.clicked.connect(self._export_srt)
        btn_sub_clr = icon_button("", "trash", "red", "Remove all subtitles")
        btn_sub_clr.clicked.connect(self._clear_subtitles)
        lay.addLayout(self._row(btn_sub_edit, btn_sub_imp, btn_sub_exp, btn_sub_clr))
        btn_sub_tr = icon_button("Translate Subtitles To…", "sparkle", "teal")
        btn_sub_tr.clicked.connect(self._translate_subtitles)
        lay.addWidget(btn_sub_tr)
        lay.addWidget(self._section("Caption style"))
        self.spn_sub_size = QSpinBox()
        self.spn_sub_size.setRange(2, 15)
        self.spn_sub_size.setValue(5)
        self.spn_sub_size.setSuffix(" % height")
        self.cmb_sub_pos = QComboBox()
        self.cmb_sub_pos.addItems(["Bottom", "Center", "Top"])
        self.btn_sub_color = QPushButton("Color")
        self.btn_sub_color.clicked.connect(lambda: (self._pick_text_color(self.btn_sub_color), self._on_sub_style_changed()))
        self._set_color_button(self.btn_sub_color, "#FFFFFF")
        lay.addLayout(self._row(self.spn_sub_size, self.cmb_sub_pos, self.btn_sub_color))
        self.chk_sub_backdrop = QCheckBox("Dark box behind text")
        self.chk_sub_backdrop.setChecked(True)
        self.chk_sub_burn = QCheckBox("Burn into exported video")
        self.chk_sub_burn.setChecked(True)
        lay.addLayout(self._row(self.chk_sub_backdrop, self.chk_sub_burn, None))
        for w_ in (self.spn_sub_size,):
            w_.valueChanged.connect(lambda _v: self._on_sub_style_changed())
        self.cmb_sub_pos.currentIndexChanged.connect(lambda _i: self._on_sub_style_changed())
        self.chk_sub_backdrop.toggled.connect(lambda _c: self._on_sub_style_changed())
        self.chk_sub_burn.toggled.connect(lambda _c: self._on_sub_style_changed())
        lay.addStretch()

        # --- 11. Smart Tools ---
        lay = self._toolbox_page(inspector, "Smart Tools — Scenes, Silence, Face Reframe", "magic", "orange")
        self.sl_scene_sens = self._labeled_slider(lay, "Scene Sensitivity", 10, 100, 55, lambda _v: None, "%")
        btn_scenes = icon_button("Split Active Clip at Scene Cuts", "split", "orange", kind="warn")
        btn_scenes.clicked.connect(lambda: self._detect_scenes(all_clips=False))
        btn_scenes_all = icon_button("All Clips", "layers", "orange")
        btn_scenes_all.clicked.connect(lambda: self._detect_scenes(all_clips=True))
        lay.addLayout(self._row(btn_scenes, btn_scenes_all))
        lay.addWidget(self._section("Remove silent gaps"))
        self.spn_sil_db = QSpinBox()
        self.spn_sil_db.setRange(-70, -15)
        self.spn_sil_db.setValue(-40)
        self.spn_sil_db.setSuffix(" dB")
        self.spn_sil_min = QDoubleSpinBox()
        self.spn_sil_min.setRange(0.2, 10.0)
        self.spn_sil_min.setSingleStep(0.1)
        self.spn_sil_min.setValue(0.7)
        self.spn_sil_min.setSuffix(" s min")
        lay.addLayout(self._row(QLabel("Quieter than"), self.spn_sil_db, QLabel("for"), self.spn_sil_min))
        btn_sil = icon_button("Remove Silences", "mute", "red", kind="danger")
        btn_sil.clicked.connect(self._remove_silences)
        lay.addWidget(btn_sil)
        lay.addWidget(self._section("Vertical reframing"))
        btn_faces = icon_button("Analyze Faces for Smart 9:16 Reframe", "person", "pink")
        btn_faces.clicked.connect(self._analyze_faces)
        lay.addWidget(btn_faces)
        self.lbl_smart_status = self._muted("Smart reframe keeps the speaker's face centred when you export 9:16 / 1:1.")
        lay.addWidget(self.lbl_smart_status)
        lay.addStretch()

        # --- 12. Export ---
        lay = self._toolbox_page(inspector, "Export — Platforms, GPU & Queue", "export", "green")
        form = QFormLayout()
        self.cmb_exp_platform = QComboBox()
        self.cmb_exp_platform.addItems([p[0] for p in OUTPUT_PRESETS])
        self.cmb_exp_platform.currentIndexChanged.connect(self._on_platform_preset)
        self.cmb_exp_format = QComboBox()
        self.cmb_exp_format.addItems(["Source size (first clip)", "1080p  16:9  (1920×1080)", "720p  16:9  (1280×720)",
                                      "Vertical 9:16  (1080×1920)", "Square 1:1  (1080×1080)",
                                      "Portrait 4:5  (1080×1350)", "4K  16:9  (3840×2160)"])
        self.cmb_exp_fit = QComboBox()
        self.cmb_exp_fit.addItems(["Fit + blurred background", "Fit + black bars", "Fill (crop edges)",
                                   "Smart reframe (follow faces)"])
        self.cmb_exp_fps = QComboBox()
        self.cmb_exp_fps.addItems(["Source FPS", "24", "25", "30", "50", "60"])
        self.cmb_exp_quality = QComboBox()
        self.cmb_exp_quality.addItems(["Maximum (CRF 16)", "High (CRF 19)", "Balanced (CRF 23)", "Small file (CRF 28)"])
        self.cmb_exp_quality.setCurrentIndex(1)
        self.cmb_exp_encoder = QComboBox()
        for key, title in ENCODER_LABELS:
            self.cmb_exp_encoder.addItem(title, key)
        form.addRow("Platform", self.cmb_exp_platform)
        form.addRow("Size", self.cmb_exp_format)
        form.addRow("Framing", self.cmb_exp_fit)
        form.addRow("Frame rate", self.cmb_exp_fps)
        form.addRow("Quality", self.cmb_exp_quality)
        form.addRow("Encoder", self.cmb_exp_encoder)
        lay.addLayout(form)
        self.lbl_exp_warning = QLabel("")
        self.lbl_exp_warning.setObjectName("Accent")
        self.lbl_exp_warning.setWordWrap(True)
        lay.addWidget(self.lbl_exp_warning)
        self.chk_exp_pitch = QCheckBox("Keep natural voice pitch on speed changes")
        self.chk_exp_pitch.setChecked(True)
        lay.addWidget(self.chk_exp_pitch)
        btn_export_vid = icon_button("Export Video  (runs in the background)", "export", "green", kind="success")
        btn_export_vid.setMinimumHeight(40)
        btn_export_vid.clicked.connect(self._export_timeline_video)
        lay.addWidget(btn_export_vid)
        lay.addWidget(self._section("Export queue — keep editing while it renders"))
        self.lst_exports = QListWidget()
        self.lst_exports.setMaximumHeight(110)
        lay.addWidget(self.lst_exports)
        btn_exp_cancel = icon_button("Cancel Selected", "stop", "red")
        btn_exp_cancel.clicked.connect(self._cancel_selected_export)
        btn_exp_open = icon_button("Open Folder", "open", "amber")
        btn_exp_open.clicked.connect(self._open_export_folder)
        lay.addLayout(self._row(btn_exp_cancel, btn_exp_open))
        self.lbl_encoders = self._muted("Checking which GPU encoders this computer supports…")
        lay.addWidget(self.lbl_encoders)
        lay.addStretch()

        right_wrap = QScrollArea()
        right_wrap.setWidgetResizable(True)
        right_wrap.setMinimumWidth(490)
        right_wrap.setWidget(inspector)
        top_split.addWidget(right_wrap, stretch=1)
        layout.addLayout(top_split, stretch=3)

        # Bottom Section: Scrollable & Zoomable Multi-Stem Timeline
        tl_bar = QHBoxLayout()
        tl_title = QLabel("Timeline")
        tl_title.setObjectName("Section")
        tl_bar.addWidget(tl_title)
        tl_bar.addWidget(self._muted("Wheel = zoom  •  Shift+Wheel = scroll  •  Drag edges = trim  •  Right-click = menu"))
        tl_bar.addStretch()
        for icon, tip, fn in (
            ("zoom_out", "Zoom out", lambda: self.timeline.set_zoom(self.timeline.px_per_sec * 0.75)),
            ("zoom_in", "Zoom in", lambda: self.timeline.set_zoom(self.timeline.px_per_sec * 1.35)),
            ("aspect", "Fit whole timeline", self._zoom_to_fit),
        ):
            b = tool_button("", icon, "slate", tip, size=24)
            b.clicked.connect(fn)
            tl_bar.addWidget(b)
        layout.addLayout(tl_bar)

        self.timeline = TimelineWidget()
        self.timeline.playhead_Moved.connect(self._on_timeline_scrub)
        self.timeline.marks_Changed.connect(self._update_marks_label)
        self.timeline.videos_Dropped_At_Ms.connect(
            lambda paths, ms: self._route_dropped_files(paths, insert_at_ms=ms)
        )
        self.timeline.context_Menu_Requested.connect(self._show_timeline_context_menu)
        self.timeline.edge_Trim_Started.connect(self._push_video_undo)
        self.timeline.edge_Trim_Preview.connect(self._on_live_preview)
        self.timeline.edge_Trim_Finished.connect(self._end_live_preview)
        self.timeline.mark_Drag_Preview.connect(lambda ms, name: (self._on_live_preview(ms, f"MARK {name}  ▸  {format_ms(ms)}"),
                                                                 self._update_marks_label(self.timeline.mark_a_ms, self.timeline.mark_b_ms)))
        self.timeline.marks_Changed.connect(lambda a, b: self._end_live_preview())
        self.timeline.mark_Blocked.connect(lambda name: self.status.showMessage(f"Mark {name} is locked — unlock it (Lock {name} button or Ctrl+{'[' if name == 'A' else ']'}) to move it."))

        self.timeline_scroll = QScrollArea()
        self.timeline_scroll.setWidgetResizable(True)
        self.timeline_scroll.setFixedHeight(286)
        self.timeline_scroll.setWidget(self.timeline)
        layout.addWidget(self.timeline_scroll)

        return tab

    # ==========================================================================
    # TAB 2: AI PHOTO, TRANSFORM & SKIN RETOUCH STUDIO
    # ==========================================================================
    def _build_photo_tab(self):
        tab = QWidget()
        layout = QHBoxLayout(tab)
        layout.setContentsMargins(8, 8, 8, 8)
        layout.setSpacing(10)

        # Left tool rail
        rail = QFrame()
        rail.setObjectName("Card")
        rl = QVBoxLayout(rail)
        rl.setContentsMargins(6, 8, 6, 8)
        rl.setSpacing(4)
        self.photo_tool_group = QButtonGroup(self)
        self.photo_tool_group.setExclusive(True)
        self.photo_tool_buttons = {}
        for mode, icon, color, tip in (
            ("none", "eye", "slate", "View (no tool)"),
            ("move", "move", "amber", "Free Move: drag the subject, wheel to scale"),
            ("crop", "crop", "orange", "Crop: drag a rectangle"),
            ("magic_brush", "brush", "red", "Magic Brush: paint over objects to erase"),
            ("manual_mark_fg", "marker", "green", "Mark KEEP (for background cut)"),
            ("manual_mark_bg", "eraser", "blue", "Mark REMOVE (for background cut)"),
        ):
            b = tool_button("", icon, color, tip, size=34, checkable=True)
            b.clicked.connect(lambda _, m=mode: self._set_photo_mode(m))
            self.photo_tool_group.addButton(b)
            self.photo_tool_buttons[mode] = b
            rl.addWidget(b)
        self.photo_tool_buttons["none"].setChecked(True)
        line = QFrame()
        line.setFrameShape(QFrame.Shape.HLine)
        line.setStyleSheet("color: #263248;")
        rl.addWidget(line)
        for icon, color, tip, fn in (
            ("rotate_ccw", "teal", "Rotate 90° CCW", lambda: self._mod_photo_transform(rot_step=-1)),
            ("rotate_cw", "teal", "Rotate 90° CW", lambda: self._mod_photo_transform(rot_step=1)),
            ("flip_h", "indigo", "Flip horizontal", lambda: self._mod_photo_transform(flip_h=True)),
            ("flip_v", "indigo", "Flip vertical", lambda: self._mod_photo_transform(flip_v=True)),
            ("auto", "violet", "Auto Enhance", self._photo_auto_enhance),
        ):
            b = tool_button("", icon, color, tip, size=34)
            b.clicked.connect(fn)
            rl.addWidget(b)
        self.btn_p_compare = tool_button("", "compare", "sky", "Hold to compare with the original", size=34)
        self.btn_p_compare.pressed.connect(lambda: self._set_photo_compare(True))
        self.btn_p_compare.released.connect(lambda: self._set_photo_compare(False))
        rl.addWidget(self.btn_p_compare)
        rl.addStretch()
        layout.addWidget(rail)

        center = QVBoxLayout()
        self.photo_canvas = PhotoCanvas("Drag & drop a photo here (PNG, JPG, WEBP, BMP, TIFF) or click Open", "image")
        self.photo_canvas.crop_Completed.connect(self._exec_photo_crop)
        self.photo_canvas.free_Moved.connect(self._on_photo_free_moved)
        self.photo_canvas.move_Started.connect(self._push_photo_undo)
        self.photo_canvas.wheel_Scaled.connect(self._on_photo_wheel_scaled)
        self.photo_canvas.files_Dropped.connect(self._route_dropped_files)
        center.addWidget(self.photo_canvas, 1)
        self.lbl_photo_info = self._muted("No photo loaded.")
        center.addWidget(self.lbl_photo_info)
        layout.addLayout(center, stretch=3)

        inspector = Accordion()
        inspector.setMinimumWidth(420)

        # --- File ---
        lay = self._toolbox_page(inspector, "File & Export", "open", "amber")
        btn_open_img = icon_button("Open Photo", "open", "amber", kind="primary")
        btn_open_img.clicked.connect(self._open_photo)
        btn_undo_img = icon_button("Undo", "undo", "slate")
        btn_undo_img.clicked.connect(self._undo_photo)
        btn_redo_img = icon_button("Redo", "redo", "slate")
        btn_redo_img.clicked.connect(self._redo_photo)
        lay.addLayout(self._row(btn_open_img, btn_undo_img, btn_redo_img))
        form = QFormLayout()
        self.cmb_p_format = QComboBox()
        self.cmb_p_format.addItems(["JPEG", "PNG", "WEBP"])
        self.spn_p_quality = QSpinBox()
        self.spn_p_quality.setRange(40, 100)
        self.spn_p_quality.setValue(92)
        self.spn_p_quality.setSuffix(" %")
        self.spn_p_long_edge = QSpinBox()
        self.spn_p_long_edge.setRange(0, 12000)
        self.spn_p_long_edge.setSingleStep(100)
        self.spn_p_long_edge.setSpecialValueText("Original size")
        self.spn_p_long_edge.setSuffix(" px long edge")
        form.addRow("Format", self.cmb_p_format)
        form.addRow("Quality", self.spn_p_quality)
        form.addRow("Resize", self.spn_p_long_edge)
        lay.addLayout(form)
        btn_save_img = icon_button("Save Photo", "save", "blue", kind="primary")
        btn_save_img.clicked.connect(lambda: self._save_photo(transparent_png=False))
        btn_save_alpha = icon_button("Save Transparent PNG", "layers", "teal", kind="success")
        btn_save_alpha.clicked.connect(lambda: self._save_photo(transparent_png=True))
        lay.addLayout(self._row(btn_save_img, btn_save_alpha))
        lay.addStretch()

        # --- Adjust ---
        lay = self._toolbox_page(inspector, "Adjust Light & Color", "palette", "pink")
        btn_auto = icon_button("Auto Enhance", "auto", "violet", "White balance + local contrast", kind="accent")
        btn_auto.clicked.connect(self._photo_auto_enhance)
        btn_adj_reset = icon_button("Reset Adjustments", "reset", "slate")
        btn_adj_reset.clicked.connect(self._reset_photo_color)
        lay.addLayout(self._row(btn_auto, btn_adj_reset))
        self.p_color_sliders = {}
        for field, title, lo, hi in (
            ("brightness", "Brightness", -100, 100), ("contrast", "Contrast", -100, 100),
            ("saturation", "Saturation", -100, 100), ("warmth", "Warmth", -100, 100), ("tint", "Tint", -100, 100),
            ("highlights", "Highlights", -100, 100), ("shadows", "Shadows", -100, 100),
            ("sharpness", "Sharpen", 0, 100), ("vignette", "Vignette", 0, 100),
        ):
            sl = self._labeled_slider(lay, title, lo, hi, 0, lambda v, f=field: self._on_photo_color_slider(f, v))
            sl.sliderPressed.connect(self._push_photo_undo)
            self.p_color_sliders[field] = sl
        lay.addStretch()

        # --- Filters ---
        lay = self._toolbox_page(inspector, "Filters & Looks", "filter", "violet")
        self.photo_filter_grid = QGridLayout()
        self.photo_filter_buttons = {}
        for i, (key, title) in enumerate(FILTER_PRESETS):
            b = QToolButton()
            b.setText(title.replace("&", "&&"))
            b.setCheckable(True)
            b.setToolButtonStyle(Qt.ToolButtonStyle.ToolButtonTextUnderIcon)
            b.setIconSize(QSize(96, 72))
            b.setIcon(make_icon("filter", "violet"))
            b.clicked.connect(lambda _, k=key: self._set_photo_filter(k))
            self.photo_filter_grid.addWidget(b, i // 3, i % 3)
            self.photo_filter_buttons[key] = b
        self.photo_filter_buttons["none"].setChecked(True)
        lay.addLayout(self.photo_filter_grid)
        lay.addWidget(self._muted("Previews update with your photo. Filters combine with the Adjust sliders."))
        lay.addStretch()

        # --- Transform ---
        lay = self._toolbox_page(inspector, "Transform, Crop & Resize", "crop", "orange")
        btn_p_cw = icon_button("90° CW", "rotate_cw", "teal")
        btn_p_cw.clicked.connect(lambda: self._mod_photo_transform(rot_step=1))
        btn_p_ccw = icon_button("90° CCW", "rotate_ccw", "teal")
        btn_p_ccw.clicked.connect(lambda: self._mod_photo_transform(rot_step=-1))
        btn_p_180 = icon_button("180°", "rotate_cw", "cyan")
        btn_p_180.clicked.connect(lambda: self._mod_photo_transform(rot_step=2))
        lay.addLayout(self._row(btn_p_cw, btn_p_ccw, btn_p_180))
        btn_p_fliph = icon_button("Flip H", "flip_h", "indigo")
        btn_p_fliph.clicked.connect(lambda: self._mod_photo_transform(flip_h=True))
        btn_p_flipv = icon_button("Flip V", "flip_v", "indigo")
        btn_p_flipv.clicked.connect(lambda: self._mod_photo_transform(flip_v=True))
        btn_p_reset = icon_button("Reset", "reset", "slate")
        btn_p_reset.clicked.connect(self._reset_photo_transform)
        lay.addLayout(self._row(btn_p_fliph, btn_p_flipv, btn_p_reset))
        self.lbl_p_angle = QLabel("Free Angle: 0°")
        self.lbl_p_angle.setMinimumWidth(110)
        self.sl_p_angle = QSlider(Qt.Orientation.Horizontal)
        self.sl_p_angle.setRange(-180, 180)
        self.sl_p_angle.setValue(0)
        self.sl_p_angle.sliderPressed.connect(self._push_photo_undo)
        self.sl_p_angle.valueChanged.connect(self._on_photo_angle_slider)
        lay.addLayout(self._row(self.lbl_p_angle, self.sl_p_angle, stretch_last=True))
        self.lbl_p_scale = QLabel("Scale: 100%")
        self.lbl_p_scale.setMinimumWidth(110)
        self.sl_p_scale = QSlider(Qt.Orientation.Horizontal)
        self.sl_p_scale.setRange(10, 300)
        self.sl_p_scale.setValue(100)
        self.sl_p_scale.sliderPressed.connect(self._push_photo_undo)
        self.sl_p_scale.valueChanged.connect(self._on_photo_scale_slider)
        lay.addLayout(self._row(self.lbl_p_scale, self.sl_p_scale, stretch_last=True))
        self.btn_p_free_move = icon_button("Free Move (drag subject)", "move", "amber", checkable=True)
        self.btn_p_free_move.clicked.connect(self._toggle_photo_free_move)
        btn_crop_mode = icon_button("Crop Tool", "crop", "orange")
        btn_crop_mode.clicked.connect(lambda: self._set_photo_mode("crop"))
        lay.addLayout(self._row(self.btn_p_free_move, btn_crop_mode))
        lay.addWidget(self._section("Quick crop to aspect ratio (centered)"))
        aspect_row = QHBoxLayout()
        for title, ratio in (("1:1", 1.0), ("4:5", 4 / 5), ("9:16", 9 / 16), ("16:9", 16 / 9), ("4:3", 4 / 3)):
            b = QPushButton(title)
            b.clicked.connect(lambda _, r=ratio: self._photo_crop_aspect(r))
            aspect_row.addWidget(b)
        lay.addLayout(aspect_row)
        btn_p_upscale = icon_button("AI Upsize 2x (Super-Res)", "hd", "violet", kind="accent")
        btn_p_upscale.clicked.connect(self._apply_photo_ai_upscale)
        lay.addWidget(btn_p_upscale)
        lay.addStretch()

        # --- Retouch ---
        lay = self._toolbox_page(inspector, "Retouch & Object Removal", "magic", "red")
        btn_magic_mode = icon_button("Paint Magic Brush", "brush", "red", "Paint over unwanted objects")
        btn_magic_mode.clicked.connect(lambda: self._set_photo_mode("magic_brush"))
        btn_apply_magic = icon_button("Erase Painted Area", "magic", "violet", kind="accent")
        btn_apply_magic.clicked.connect(self._apply_magic_brush)
        lay.addLayout(self._row(btn_magic_mode, btn_apply_magic))
        self.sl_brush = self._labeled_slider(lay, "Brush Size", 5, 160, 24, lambda v: setattr(self.photo_canvas, "brush_size", v), " px")
        btn_clear_paint = icon_button("Clear Painted Marks", "reset", "slate")
        btn_clear_paint.clicked.connect(self._clear_photo_marks)
        lay.addWidget(btn_clear_paint)
        lay.addWidget(self._section("Portrait"))
        btn_sharpen_skin = icon_button("Smart Skin Smooth & Sharpen", "skin", "pink")
        btn_sharpen_skin.clicked.connect(self._apply_skin_sharpen)
        lay.addWidget(btn_sharpen_skin)
        btn_denoise = icon_button("Reduce Noise / Grain", "sparkle", "sky")
        btn_denoise.clicked.connect(self._apply_photo_denoise)
        lay.addWidget(btn_denoise)
        lay.addStretch()

        # --- Background ---
        lay = self._toolbox_page(inspector, "Background Remove & Replace", "person", "teal")
        btn_auto_bg = icon_button("Auto Remove Background (AI)", "person", "teal", kind="success")
        btn_auto_bg.clicked.connect(self._auto_remove_bg)
        lay.addWidget(btn_auto_bg)
        lay.addWidget(self._muted("Uses rembg when installed (best), otherwise OpenCV GrabCut."))
        btn_mark_fg = icon_button("Mark Keep", "marker", "green")
        btn_mark_fg.clicked.connect(lambda: self._set_photo_mode("manual_mark_fg"))
        btn_mark_bg = icon_button("Mark Remove", "eraser", "blue")
        btn_mark_bg.clicked.connect(lambda: self._set_photo_mode("manual_mark_bg"))
        lay.addLayout(self._row(btn_mark_fg, btn_mark_bg))
        btn_exec_man_bg = icon_button("Cut Background from Marks", "crop", "orange")
        btn_exec_man_bg.clicked.connect(self._manual_remove_bg)
        lay.addWidget(btn_exec_man_bg)
        btn_replace_bg_img = icon_button("Replace with Image…", "image", "green")
        btn_replace_bg_img.clicked.connect(self._replace_bg_with_image)
        btn_replace_bg_col = icon_button("Solid Color…", "palette", "pink")
        btn_replace_bg_col.clicked.connect(self._replace_bg_with_color)
        btn_bg_clear = icon_button("Transparent", "layers", "slate")
        btn_bg_clear.clicked.connect(self._clear_photo_bg_replacement)
        lay.addLayout(self._row(btn_replace_bg_img, btn_replace_bg_col, btn_bg_clear))
        lay.addStretch()

        # --- Text ---
        lay = self._toolbox_page(inspector, "Text & Watermark", "text", "amber")
        self.txt_p_text = QLineEdit()
        self.txt_p_text.setPlaceholderText("Caption or watermark  (use | for a new line)")
        lay.addWidget(self.txt_p_text)
        self.spn_p_text_size = QSpinBox()
        self.spn_p_text_size.setRange(2, 30)
        self.spn_p_text_size.setValue(6)
        self.spn_p_text_size.setSuffix(" % height")
        self.cmb_p_text_pos = QComboBox()
        self.cmb_p_text_pos.addItems(["Bottom", "Center", "Top"])
        self.btn_p_text_color = QPushButton("Color")
        self.btn_p_text_color.clicked.connect(lambda: self._pick_text_color(self.btn_p_text_color))
        self._set_color_button(self.btn_p_text_color, "#FFFFFF")
        lay.addLayout(self._row(QLabel("Size"), self.spn_p_text_size, QLabel("Position"), self.cmb_p_text_pos, self.btn_p_text_color))
        self.chk_p_text_outline = QCheckBox("Outline")
        self.chk_p_text_outline.setChecked(True)
        self.chk_p_text_backdrop = QCheckBox("Dark backdrop")
        lay.addLayout(self._row(self.chk_p_text_outline, self.chk_p_text_backdrop, None))
        btn_p_text_apply = icon_button("Apply Text", "text", "amber", kind="warn")
        btn_p_text_apply.clicked.connect(self._apply_photo_text)
        btn_p_text_clear = icon_button("Remove Text", "trash", "red")
        btn_p_text_clear.clicked.connect(self._clear_photo_text)
        lay.addLayout(self._row(btn_p_text_apply, btn_p_text_clear))
        lay.addStretch()

        # --- Layers ---
        lay = self._toolbox_page(inspector, "Layers — Images, Cut-outs & Text", "layers", "indigo")
        b_l_img = icon_button("Add Image", "image", "green")
        b_l_img.clicked.connect(lambda: self._add_photo_layer("image"))
        b_l_cut = icon_button("Add Cut-out", "person", "teal", "Add a picture with its background removed automatically")
        b_l_cut.clicked.connect(lambda: self._add_photo_layer("cutout"))
        b_l_txt = icon_button("Add Text", "text", "amber")
        b_l_txt.clicked.connect(lambda: self._add_photo_layer("text"))
        lay.addLayout(self._row(b_l_img, b_l_cut, b_l_txt))
        self.txt_layer_text = QLineEdit()
        self.txt_layer_text.setPlaceholderText("Text for a new text layer (use | for a new line)")
        self.btn_layer_color = QPushButton("Color")
        self.btn_layer_color.clicked.connect(lambda: self._pick_text_color(self.btn_layer_color))
        self._set_color_button(self.btn_layer_color, "#FFFFFF")
        lay.addLayout(self._row(self.txt_layer_text, self.btn_layer_color, stretch_last=False))
        self.lst_layers = QListWidget()
        self.lst_layers.setMaximumHeight(120)
        self.lst_layers.currentRowChanged.connect(self._on_photo_layer_selected)
        lay.addWidget(self.lst_layers)
        b_up = icon_button("Up", "to_end", "slate", "Bring forward")
        b_up.clicked.connect(lambda: self._move_photo_layer(1))
        b_dn = icon_button("Down", "to_start", "slate", "Send backward")
        b_dn.clicked.connect(lambda: self._move_photo_layer(-1))
        b_sel_none = icon_button("Deselect", "eye", "slate", "Move/scale the photo instead of a layer")
        b_sel_none.clicked.connect(lambda: self.lst_layers.setCurrentRow(-1))
        b_l_del = icon_button("Delete", "trash", "red")
        b_l_del.clicked.connect(self._delete_photo_layer)
        lay.addLayout(self._row(b_up, b_dn, b_sel_none, b_l_del))
        self.sl_layer_size = self._labeled_slider(lay, "Layer Size", 2, 100, 35, lambda _v: self._on_photo_layer_changed(), "%")
        self.sl_layer_opacity = self._labeled_slider(lay, "Layer Opacity", 5, 100, 100, lambda _v: self._on_photo_layer_changed(), "%")
        for sl in (self.sl_layer_size, self.sl_layer_opacity):
            sl.sliderPressed.connect(self._push_photo_undo)
        lay.addWidget(self._muted("Select a layer, then use the Free Move tool to drag it (mouse wheel resizes it)."))
        lay.addStretch()

        # --- Batch & Thumbnails ---
        lay = self._toolbox_page(inspector, "Batch Edit & Thumbnail Maker", "sparkle", "amber")
        b_thumb = icon_button("Create YouTube / TikTok Thumbnail…", "image", "red", kind="danger")
        b_thumb.clicked.connect(self._thumbnail_maker)
        lay.addWidget(b_thumb)
        lay.addWidget(self._muted("Big outlined title, your subject cut out, blurred background — ready to tweak with layers."))
        lay.addWidget(self._section("Batch process many photos"))
        self.chk_batch_color = QCheckBox("Apply current Adjust + Filter")
        self.chk_batch_color.setChecked(True)
        self.chk_batch_text = QCheckBox("Add current text / watermark")
        self.chk_batch_layers = QCheckBox("Add current layers (e.g. logo)")
        self.chk_batch_auto = QCheckBox("Auto Enhance each photo")
        for c in (self.chk_batch_color, self.chk_batch_text, self.chk_batch_layers, self.chk_batch_auto):
            lay.addWidget(c)
        lay.addWidget(self._muted("Format, quality and resize come from the File & Export section."))
        b_batch = icon_button("Choose Photos & Run Batch…", "layers", "violet", kind="accent")
        b_batch.clicked.connect(self._batch_photos)
        lay.addWidget(b_batch)
        lay.addWidget(self._section("AI upscaling engine"))
        self.lbl_esrgan = self._muted("")
        lay.addWidget(self.lbl_esrgan)
        b_esr = icon_button("Locate Real-ESRGAN…", "open", "amber")
        b_esr.clicked.connect(self._locate_realesrgan)
        lay.addWidget(b_esr)
        self._update_esrgan_label()
        lay.addStretch()

        side_scroll = QScrollArea()
        side_scroll.setWidgetResizable(True)
        side_scroll.setMinimumWidth(440)
        side_scroll.setWidget(inspector)
        layout.addWidget(side_scroll, stretch=1)
        return tab

    # --- Shared small UI helpers ---
    @staticmethod
    def _set_color_button(btn: QPushButton, hex_color: str):
        btn._color = hex_color
        q = QColor(hex_color)
        fg = "#000000" if q.lightness() > 140 else "#ffffff"
        btn.setStyleSheet(f"background: {hex_color}; color: {fg}; border: 1px solid #94a3b8; border-radius: 7px; padding: 5px 10px;")

    def _pick_text_color(self, btn: QPushButton):
        c = QColorDialog.getColor(QColor(getattr(btn, "_color", "#FFFFFF")), self, "Text Color")
        if c.isValid():
            self._set_color_button(btn, c.name())


    # ==========================================================================
    # PHOTO STUDIO LOGIC (WITH UNDO + REDO)
    # ==========================================================================
    def _photo_snapshot(self):
        return (self.photo_base_bgra.copy(), self.photo_transform.clone(), self.photo_color.clone(), self.photo_text.clone(),
                [ly.clone() for ly in self.photo_layers])

    def _restore_photo_snapshot(self, snap):
        base, tf, col, txt, layers = snap
        self.photo_layers = layers
        self._refresh_layer_list()
        base_changed = self.photo_base_bgra is None or base.shape != self.photo_base_bgra.shape or not np.array_equal(base, self.photo_base_bgra)
        self.photo_base_bgra, self.photo_transform, self.photo_color, self.photo_text = base, tf, col, txt
        if base_changed:
            self._rebuild_photo_preview()
        self._sync_photo_ui_sliders()
        self._refresh_photo_canvas()

    def _push_photo_undo(self):
        if self.photo_base_bgra is not None:
            self.photo_undo_stack.append(self._photo_snapshot())
            if len(self.photo_undo_stack) > 25:
                self.photo_undo_stack.pop(0)
            self.photo_redo_stack.clear()

    def _undo_photo(self):
        if not self.photo_undo_stack:
            self.status.showMessage("Nothing to undo in Photo Studio.")
            return
        if self.photo_base_bgra is not None:
            self.photo_redo_stack.append(self._photo_snapshot())
        self._restore_photo_snapshot(self.photo_undo_stack.pop())
        self.status.showMessage("Undid last photo operation (Ctrl+Z).")

    def _redo_photo(self):
        if not self.photo_redo_stack:
            self.status.showMessage("Nothing to redo in Photo Studio.")
            return
        if self.photo_base_bgra is not None:
            self.photo_undo_stack.append(self._photo_snapshot())
        self._restore_photo_snapshot(self.photo_redo_stack.pop())
        self.status.showMessage("Redid photo operation (Ctrl+Y).")

    def _sync_photo_ui_sliders(self):
        self.sl_p_angle.blockSignals(True)
        self.sl_p_scale.blockSignals(True)
        self.sl_p_angle.setValue(int(self.photo_transform.free_angle))
        self.lbl_p_angle.setText(f"Free Angle: {int(self.photo_transform.free_angle)}°")
        self.sl_p_scale.setValue(int(self.photo_transform.scale * 100))
        self.lbl_p_scale.setText(f"Scale: {int(self.photo_transform.scale * 100)}%")
        self.sl_p_angle.blockSignals(False)
        self.sl_p_scale.blockSignals(False)
        for f, sl in self.p_color_sliders.items():
            self._set_slider_silently(sl, getattr(self.photo_color, f))
        for k, b in self.photo_filter_buttons.items():
            b.setChecked(k == self.photo_color.filter)

    def _rebuild_photo_preview(self):
        h, w = self.photo_base_bgra.shape[:2]
        s = min(1.0, PHOTO_PREVIEW_MAX / max(h, w))
        self.photo_preview_scale = s
        self.photo_preview_base = self.photo_base_bgra if s >= 1.0 else cv2.resize(
            self.photo_base_bgra, (max(1, int(w * s)), max(1, int(h * s))), interpolation=cv2.INTER_AREA)
        self._update_filter_thumbnails()

    def _update_filter_thumbnails(self):
        if self.photo_preview_base is None:
            return
        thumb = fit_into_frame(self.photo_preview_base[:, :, :3], 96, 72, "fill")
        for key, b in self.photo_filter_buttons.items():
            cp = ColorParams()
            cp.filter = key
            t = np.ascontiguousarray(cv2.cvtColor(apply_color(thumb, cp), cv2.COLOR_BGR2RGB))
            b.setIcon(QIcon(QPixmap.fromImage(QImage(t.data, 96, 72, 96 * 3, QImage.Format.Format_RGB888).copy())))

    def _refresh_photo_canvas(self, preserve_masks=False):
        if self.photo_base_bgra is None:
            return
        if self.photo_preview_base is None:
            self._rebuild_photo_preview()
        s = self.photo_preview_scale
        base = self.photo_preview_base
        if not self._photo_compare:
            base = apply_color(base, self.photo_color)
        comp, _ = apply_transform_pipeline(base, self.photo_transform.scaled(s), canvas_size=None, for_preview_checkerboard=True)
        if self.photo_text.active() and not self._photo_compare:
            ch, cw = comp.shape[:2]
            comp = composite_bgra_over(comp, render_text_layer(cw, ch, self.photo_text))
        if self.photo_layers and not self._photo_compare:
            comp = composite_layers(comp, self.photo_layers)
        self.photo_canvas.brush_scale = s
        self.photo_canvas.overlay_label = "ORIGINAL" if self._photo_compare else ""
        self.photo_canvas.load_image(comp, preserve_masks=preserve_masks)
        h, w = self.photo_base_bgra.shape[:2]
        name = os.path.basename(self.photo_path) if self.photo_path else "photo"
        self.lbl_photo_info.setText(
            f"{name}  •  {w}×{h} px  •  preview {int(s * 100)}%{self.photo_transform.summary_tag()}{self.photo_color.summary_tag()}"
        )

    def _photo_render_full(self):
        """Full-resolution render for saving: color grade → geometry → text. Returns (BGR, BGRA)."""
        colored = apply_color(self.photo_base_bgra, self.photo_color)
        comp, warped = apply_transform_pipeline(colored, self.photo_transform, canvas_size=None, for_preview_checkerboard=False)
        if warped is None:
            warped = to_bgra(comp)
        if self.photo_text.active():
            h, w = comp.shape[:2]
            layer = render_text_layer(w, h, self.photo_text)
            comp = composite_bgra_over(comp, layer)
            rgb = composite_bgra_over(warped[:, :, :3], layer)
            warped = cv2.merge([rgb[:, :, 0], rgb[:, :, 1], rgb[:, :, 2], np.maximum(warped[:, :, 3], layer[:, :, 3])])
        if self.photo_layers:
            comp = composite_layers(comp, self.photo_layers)
            alpha = warped[:, :, 3].copy()
            rgb = composite_layers(np.ascontiguousarray(warped[:, :, :3]), self.photo_layers, alpha)
            warped = cv2.merge([rgb[:, :, 0], rgb[:, :, 1], rgb[:, :, 2], alpha])
        return comp, warped

    def _bake_photo_transform_into_base(self):
        """Applies the current geometry to the full-resolution base (used before crops, erases and cutouts)."""
        if self.photo_base_bgra is None or self.photo_transform.is_identity():
            return
        _, warped = apply_transform_pipeline(self.photo_base_bgra, self.photo_transform, None, for_preview_checkerboard=False)
        if warped is not None:
            self.photo_base_bgra = warped
        bg_keep = self.photo_transform.bg_replacement
        transparent = self.photo_transform.transparent_bg
        self.photo_transform.reset()
        self.photo_transform.bg_replacement = bg_keep
        self.photo_transform.transparent_bg = transparent
        self._rebuild_photo_preview()
        self._sync_photo_ui_sliders()

    def _open_photo(self):
        path, _ = QFileDialog.getOpenFileName(self, "Open Photo", "", "Images (*.png *.jpg *.jpeg *.webp *.bmp *.tif *.tiff)")
        if path:
            self._load_photo_from_path(path)

    def _load_photo_from_path(self, path: str):
        try:
            raw = cv2.imdecode(np.fromfile(path, dtype=np.uint8), cv2.IMREAD_UNCHANGED)
        except Exception:
            raw = None
        if raw is None:
            QMessageBox.warning(self, "Open Photo", f"Could not read this image:\n{path}")
            return
        if raw.dtype != np.uint8:
            raw = cv2.convertScaleAbs(raw, alpha=255.0 / max(1.0, float(raw.max())))
        raw = to_bgra(raw)
        self.photo_undo_stack.clear()
        self.photo_redo_stack.clear()
        self.photo_base_bgra = raw
        self.photo_layers = []
        self._refresh_layer_list()
        self.photo_path = path
        self.photo_transform = TransformParams()
        self.photo_color = ColorParams()
        self.photo_text = TextOverlay()
        self._rebuild_photo_preview()
        self._sync_photo_ui_sliders()
        self._refresh_photo_canvas()
        self.status.showMessage(f"Loaded photo: {os.path.basename(path)} ({raw.shape[1]}x{raw.shape[0]})")

    def _save_photo(self, transparent_png=False):
        if self.photo_base_bgra is None:
            self.status.showMessage("Open a photo first.")
            return
        fmt = "PNG" if transparent_png else self.cmb_p_format.currentText()
        ext = {"JPEG": ".jpg", "PNG": ".png", "WEBP": ".webp"}[fmt]
        stem = os.path.splitext(os.path.basename(self.photo_path))[0] if self.photo_path else "ank"
        default_name = f"{stem}_{'transparent' if transparent_png else 'edited'}{ext}"
        flt = {"JPEG": "JPEG (*.jpg *.jpeg)", "PNG": "PNG (*.png)", "WEBP": "WebP (*.webp)"}[fmt]
        path, _ = QFileDialog.getSaveFileName(self, "Save Photo", default_name, flt)
        if not path:
            return
        if os.path.splitext(path)[1].lower() not in (ext, ".jpeg" if ext == ".jpg" else ext):
            path += ext
        QApplication.setOverrideCursor(Qt.CursorShape.WaitCursor)
        try:
            comp, warped = self._photo_render_full()
            out = warped if (transparent_png or (fmt in ("PNG", "WEBP") and self.photo_transform.transparent_bg
                                                  and self.photo_transform.bg_replacement is None)) else comp
            long_edge = self.spn_p_long_edge.value()
            if long_edge > 0:
                h, w = out.shape[:2]
                s = long_edge / max(h, w)
                out = cv2.resize(out, (max(1, int(w * s)), max(1, int(h * s))),
                                 interpolation=cv2.INTER_AREA if s < 1 else cv2.INTER_LANCZOS4)
            q = self.spn_p_quality.value()
            params = {".jpg": [cv2.IMWRITE_JPEG_QUALITY, q], ".webp": [cv2.IMWRITE_WEBP_QUALITY, q],
                      ".png": [cv2.IMWRITE_PNG_COMPRESSION, 3]}[ext]
            if ext == ".jpg" and out.shape[2] == 4:
                out = out[:, :, :3]
            ok, buf = cv2.imencode(ext, out, params)
            if not ok:
                raise RuntimeError("Encoder failed")
            buf.tofile(path)
            self.status.showMessage(f"Saved photo to {path}  ({out.shape[1]}×{out.shape[0]})")
        except Exception as e:
            QMessageBox.critical(self, "Save Photo", f"Could not save the photo:\n{e}")
        finally:
            QApplication.restoreOverrideCursor()

    def _set_photo_mode(self, mode: str):
        self.btn_p_free_move.setChecked(mode == "move")
        if mode in self.photo_tool_buttons:
            self.photo_tool_buttons[mode].setChecked(True)
        self.photo_canvas.mode = mode
        self.photo_canvas.setCursor(Qt.CursorShape.CrossCursor if mode in ("crop", "magic_brush", "manual_mark_fg", "manual_mark_bg")
                                    else (Qt.CursorShape.OpenHandCursor if mode == "move" else Qt.CursorShape.ArrowCursor))
        self.photo_canvas.update()
        names = {"none": "View", "move": "Free Move", "crop": "Crop", "magic_brush": "Magic Brush",
                 "manual_mark_fg": "Mark Keep", "manual_mark_bg": "Mark Remove"}
        self.status.showMessage(f"Photo tool: {names.get(mode, mode)}")

    def _toggle_photo_free_move(self, checked: bool):
        self._set_photo_mode("move" if checked else "none")
        if checked:
            self.status.showMessage("Free Move: drag the subject anywhere on the canvas; scroll the mouse wheel to scale.")

    def _mod_photo_transform(self, rot_step=0, flip_h=False, flip_v=False):
        if self.photo_base_bgra is None:
            return
        self._push_photo_undo()
        if rot_step:
            self.photo_transform.rot_90_steps = (self.photo_transform.rot_90_steps + rot_step) % 4
        if flip_h:
            self.photo_transform.flip_h = not self.photo_transform.flip_h
        if flip_v:
            self.photo_transform.flip_v = not self.photo_transform.flip_v
        self._refresh_photo_canvas()

    def _reset_photo_transform(self):
        if self.photo_base_bgra is None:
            return
        self._push_photo_undo()
        self.photo_transform.reset()
        self._sync_photo_ui_sliders()
        self._refresh_photo_canvas()

    def _on_photo_angle_slider(self, val: int):
        if self.photo_base_bgra is None:
            return
        self.photo_transform.free_angle = float(val)
        self.lbl_p_angle.setText(f"Free Angle: {val}°")
        self._refresh_photo_canvas()

    def _on_photo_scale_slider(self, val: int):
        if self.photo_base_bgra is None:
            return
        self.photo_transform.scale = val / 100.0
        self.lbl_p_scale.setText(f"Scale: {val}%")
        self._refresh_photo_canvas()

    def _on_photo_free_moved(self, dx: int, dy: int):
        if self.photo_base_bgra is None:
            return
        ly = self._selected_photo_layer()
        if ly is not None and self.photo_canvas.cv_image is not None:
            ch, cw = self.photo_canvas.cv_image.shape[:2]
            ly.cx = max(-0.2, min(1.2, ly.cx + dx / cw))
            ly.cy = max(-0.2, min(1.2, ly.cy + dy / ch))
            self._refresh_photo_canvas()
            return
        s = self.photo_preview_scale
        self.photo_transform.offset_x += int(round(dx / s))
        self.photo_transform.offset_y += int(round(dy / s))
        self._refresh_photo_canvas()

    def _on_photo_wheel_scaled(self, factor: float):
        if self.photo_base_bgra is None:
            return
        ly = self._selected_photo_layer()
        if ly is not None:
            ly.width_frac = max(0.02, min(1.5, ly.width_frac * factor))
            self._set_slider_silently(self.sl_layer_size, int(min(100, ly.width_frac * 100)))
            self._refresh_photo_canvas()
            return
        self.photo_transform.scale = max(0.10, min(3.00, self.photo_transform.scale * factor))
        self._sync_photo_ui_sliders()
        self._refresh_photo_canvas()

    def _with_busy(self, message: str, fn):
        self.status.showMessage(message)
        QApplication.setOverrideCursor(Qt.CursorShape.WaitCursor)
        QApplication.processEvents()
        try:
            return fn()
        finally:
            QApplication.restoreOverrideCursor()



    def _exec_photo_crop(self, rect: QRect):
        if self.photo_base_bgra is None:
            return
        self._push_photo_undo()
        self._bake_photo_transform_into_base()
        s = self.photo_preview_scale
        bh, bw = self.photo_base_bgra.shape[:2]
        x = max(0, int(rect.x() / s))
        y = max(0, int(rect.y() / s))
        w = min(bw - x, int(rect.width() / s))
        h = min(bh - y, int(rect.height() / s))
        if w < 4 or h < 4:
            return
        self.photo_base_bgra = self.photo_base_bgra[y:y + h, x:x + w].copy()
        self._set_photo_mode("none")
        self._rebuild_photo_preview()
        self._refresh_photo_canvas()
        self.status.showMessage(f"Cropped to {w}×{h}.")

    def _photo_crop_aspect(self, ratio: float):
        if self.photo_base_bgra is None:
            return
        self._push_photo_undo()
        self._bake_photo_transform_into_base()
        h, w = self.photo_base_bgra.shape[:2]
        if w / h > ratio:
            nw, nh = int(h * ratio), h
        else:
            nw, nh = w, int(w / ratio)
        x0, y0 = (w - nw) // 2, (h - nh) // 2
        self.photo_base_bgra = self.photo_base_bgra[y0:y0 + nh, x0:x0 + nw].copy()
        self._rebuild_photo_preview()
        self._refresh_photo_canvas()
        self.status.showMessage(f"Cropped to {nw}×{nh} (centered).")

    def _canvas_mask_full(self, mask_preview: np.ndarray) -> np.ndarray:
        """Scales a mask painted on the preview up to the full-resolution base."""
        bh, bw = self.photo_base_bgra.shape[:2]
        if mask_preview.shape[:2] == (bh, bw):
            return mask_preview
        return cv2.resize(mask_preview, (bw, bh), interpolation=cv2.INTER_NEAREST)

    def _clear_photo_marks(self):
        if self.photo_canvas.cv_image is not None:
            self.photo_canvas.load_image(self.photo_canvas.cv_image, preserve_masks=False)

    def _apply_magic_brush(self):
        if self.photo_base_bgra is None:
            return
        mask_prev = (self.photo_canvas.brush_mask == 1).astype(np.uint8) * 255
        if not np.any(mask_prev):
            QMessageBox.information(self, "Magic Brush", "Paint over an unwanted object first using 'Paint Magic Brush'.")
            return
        self._push_photo_undo()
        self._bake_photo_transform_into_base()

        def work():
            mask = self._canvas_mask_full(mask_prev)
            ys, xs = np.nonzero(mask)
            pad = 40
            y0, y1 = max(0, ys.min() - pad), min(mask.shape[0], ys.max() + pad + 1)
            x0, x1 = max(0, xs.min() - pad), min(mask.shape[1], xs.max() + pad + 1)
            bgr = np.ascontiguousarray(self.photo_base_bgra[y0:y1, x0:x1, :3])
            # Only the painted area is inpainted (much faster on big photos)
            fixed = cv2.inpaint(bgr, mask[y0:y1, x0:x1], 7, cv2.INPAINT_TELEA)
            out = self.photo_base_bgra.copy()
            out[y0:y1, x0:x1, :3] = fixed
            return out
        self.photo_base_bgra = self._with_busy("Erasing painted area…", work)
        self._rebuild_photo_preview()
        self._refresh_photo_canvas()
        self.status.showMessage("Magic Brush erase complete.")

    def _apply_skin_sharpen(self):
        if self.photo_base_bgra is None:
            return
        self._push_photo_undo()

        def work():
            bgr = self.photo_base_bgra[:, :, :3]
            alpha = self.photo_base_bgra[:, :, 3]
            smooth = cv2.bilateralFilter(bgr, d=9, sigmaColor=55, sigmaSpace=55)
            gaussian = cv2.GaussianBlur(smooth, (0, 0), 2.0)
            sharpened = cv2.addWeighted(smooth, 1.45, gaussian, -0.45, 0)
            return cv2.merge([sharpened[:, :, 0], sharpened[:, :, 1], sharpened[:, :, 2], alpha])
        self.photo_base_bgra = self._with_busy("Smoothing skin and sharpening details…", work)
        self._rebuild_photo_preview()
        self._refresh_photo_canvas()
        self.status.showMessage("Skin smooth & sharpen applied.")

    def _apply_photo_denoise(self):
        if self.photo_base_bgra is None:
            return
        self._push_photo_undo()

        def work():
            bgr = np.ascontiguousarray(self.photo_base_bgra[:, :, :3])
            den = cv2.fastNlMeansDenoisingColored(bgr, None, 5, 5, 7, 21)
            return cv2.merge([den[:, :, 0], den[:, :, 1], den[:, :, 2], self.photo_base_bgra[:, :, 3]])
        self.photo_base_bgra = self._with_busy("Reducing noise (this can take a moment on large photos)…", work)
        self._rebuild_photo_preview()
        self._refresh_photo_canvas()
        self.status.showMessage("Noise reduction applied.")

    def _photo_auto_enhance(self):
        if self.photo_base_bgra is None:
            return
        self._push_photo_undo()
        enhanced = self._with_busy("Auto-enhancing…", lambda: auto_enhance(np.ascontiguousarray(self.photo_base_bgra[:, :, :3])))
        self.photo_base_bgra = cv2.merge([enhanced[:, :, 0], enhanced[:, :, 1], enhanced[:, :, 2], self.photo_base_bgra[:, :, 3]])
        self._rebuild_photo_preview()
        self._refresh_photo_canvas()
        self.status.showMessage("Auto Enhance applied (white balance + local contrast). Ctrl+Z to undo.")

    def _set_photo_compare(self, on: bool):
        if self.photo_base_bgra is None:
            return
        self._photo_compare = on
        self._refresh_photo_canvas(preserve_masks=True)

    def _on_photo_color_slider(self, field: str, value: int):
        setattr(self.photo_color, field, int(value))
        if self.photo_base_bgra is not None:
            self._refresh_photo_canvas(preserve_masks=True)

    def _set_photo_filter(self, key: str):
        if self.photo_base_bgra is None:
            self.photo_filter_buttons[key].setChecked(key == "none")
            return
        self._push_photo_undo()
        self.photo_color.filter = key
        for k, b in self.photo_filter_buttons.items():
            b.setChecked(k == key)
        self._refresh_photo_canvas(preserve_masks=True)

    def _reset_photo_color(self):
        if self.photo_base_bgra is None:
            return
        self._push_photo_undo()
        self.photo_color = ColorParams()
        self._sync_photo_ui_sliders()
        self._refresh_photo_canvas()

    def _grabcut_alpha(self, bgr_small: np.ndarray, mask_small: np.ndarray, init_rect=None) -> np.ndarray:
        bgd_model = np.zeros((1, 65), np.float64)
        fgd_model = np.zeros((1, 65), np.float64)
        if init_rect is not None:
            cv2.grabCut(bgr_small, mask_small, init_rect, bgd_model, fgd_model, 5, cv2.GC_INIT_WITH_RECT)
        else:
            cv2.grabCut(bgr_small, mask_small, None, bgd_model, fgd_model, 5, cv2.GC_INIT_WITH_MASK)
        return np.where((mask_small == cv2.GC_BGD) | (mask_small == cv2.GC_PR_BGD), 0, 255).astype(np.uint8)

    def _alpha_to_full(self, alpha_small: np.ndarray) -> np.ndarray:
        bh, bw = self.photo_base_bgra.shape[:2]
        a = cv2.resize(alpha_small, (bw, bh), interpolation=cv2.INTER_LINEAR)
        return cv2.GaussianBlur(a, (0, 0), max(0.8, bw / 1500.0))  # soft, natural edge

    def _auto_remove_bg(self):
        if self.photo_base_bgra is None:
            return
        self._push_photo_undo()
        self._bake_photo_transform_into_base()

        def work():
            img_bgr = np.ascontiguousarray(self.photo_base_bgra[:, :, :3])
            if HAS_REMBG:
                rgb = cv2.cvtColor(img_bgr, cv2.COLOR_BGR2RGB)
                rgba = np.array(rembg_remove(Image.fromarray(rgb)))
                return cv2.cvtColor(rgba, cv2.COLOR_RGBA2BGRA)
            # GrabCut on a reduced copy (seconds instead of minutes), mask scaled back up
            h, w = img_bgr.shape[:2]
            s = min(1.0, 640.0 / max(h, w))
            small = cv2.resize(img_bgr, (max(1, int(w * s)), max(1, int(h * s))), interpolation=cv2.INTER_AREA)
            sh, sw = small.shape[:2]
            mask = np.zeros((sh, sw), np.uint8)
            alpha = self._alpha_to_full(self._grabcut_alpha(small, mask, (int(sw * 0.06), int(sh * 0.06), int(sw * 0.88), int(sh * 0.88))))
            return cv2.merge([img_bgr[:, :, 0], img_bgr[:, :, 1], img_bgr[:, :, 2], alpha])
        self.photo_base_bgra = self._with_busy("Removing background…", work)
        self.photo_transform.transparent_bg = True
        self._rebuild_photo_preview()
        self._refresh_photo_canvas()
        self._toggle_photo_free_move(True)

    def _manual_remove_bg(self):
        if self.photo_base_bgra is None or self.photo_canvas.grabcut_mask is None:
            return
        if not np.any(self.photo_canvas.brush_mask >= 2):
            QMessageBox.information(self, "Background Cut", "Paint some Keep (green) and Remove (blue) marks first.")
            return
        self._push_photo_undo()
        self._bake_photo_transform_into_base()
        gc_mask = self.photo_canvas.grabcut_mask.copy()

        def work():
            # GrabCut runs at preview resolution (the marks were painted there)
            small = np.ascontiguousarray(self.photo_preview_base[:, :, :3])
            if gc_mask.shape[:2] != small.shape[:2]:
                m = cv2.resize(gc_mask, (small.shape[1], small.shape[0]), interpolation=cv2.INTER_NEAREST)
            else:
                m = gc_mask
            alpha = self._alpha_to_full(self._grabcut_alpha(small, m))
            bgr = self.photo_base_bgra[:, :, :3]
            return cv2.merge([bgr[:, :, 0], bgr[:, :, 1], bgr[:, :, 2], alpha])
        self.photo_base_bgra = self._with_busy("Cutting background from your marks…", work)
        self.photo_transform.transparent_bg = True
        self._rebuild_photo_preview()
        self._refresh_photo_canvas()
        self._toggle_photo_free_move(True)

    def _replace_bg_with_image(self):
        if self.photo_base_bgra is None:
            return
        path, _ = QFileDialog.getOpenFileName(self, "Select New Background Image", "", "Images (*.png *.jpg *.jpeg *.webp *.bmp)")
        if not path:
            return
        bg_img = cv2.imdecode(np.fromfile(path, dtype=np.uint8), cv2.IMREAD_COLOR)
        if bg_img is None:
            return
        self._push_photo_undo()
        self.photo_transform.bg_replacement = bg_img
        self._refresh_photo_canvas()
        self._toggle_photo_free_move(True)

    def _replace_bg_with_color(self):
        if self.photo_base_bgra is None:
            return
        c = QColorDialog.getColor(QColor("#ffffff"), self, "Background Color")
        if not c.isValid():
            return
        self._push_photo_undo()
        self.photo_transform.bg_replacement = np.full((8, 8, 3), (c.blue(), c.green(), c.red()), np.uint8)
        self._refresh_photo_canvas()

    def _clear_photo_bg_replacement(self):
        if self.photo_base_bgra is None:
            return
        self._push_photo_undo()
        self.photo_transform.bg_replacement = None
        self._refresh_photo_canvas()

    def _read_text_overlay(self, txt: QLineEdit, size: QSpinBox, pos: QComboBox, color_btn, outline, backdrop) -> TextOverlay:
        ov = TextOverlay()
        ov.text = txt.text().replace("|", "\n")
        ov.size_pct = size.value()
        ov.position = TextOverlay.POSITIONS[pos.currentIndex()]
        ov.color = getattr(color_btn, "_color", "#FFFFFF")
        ov.outline = outline.isChecked()
        ov.backdrop = backdrop.isChecked()
        return ov

    def _apply_photo_text(self):
        if self.photo_base_bgra is None:
            return
        self._push_photo_undo()
        self.photo_text = self._read_text_overlay(self.txt_p_text, self.spn_p_text_size, self.cmb_p_text_pos,
                                                  self.btn_p_text_color, self.chk_p_text_outline, self.chk_p_text_backdrop)
        self._refresh_photo_canvas()

    def _clear_photo_text(self):
        if self.photo_base_bgra is None:
            return
        self._push_photo_undo()
        self.photo_text = TextOverlay()
        self._refresh_photo_canvas()


    # ==========================================================================
    # v3: PHOTO LAYERS, REAL-ESRGAN, BATCH, THUMBNAIL MAKER
    # ==========================================================================
    def _refresh_layer_list(self):
        self.lst_layers.blockSignals(True)
        cur = self.lst_layers.currentRow()
        self.lst_layers.clear()
        for ly in reversed(self.photo_layers):      # top layer first, like design apps
            self.lst_layers.addItem(f"{'T' if ly.kind == 'text' else '▣'}  {ly.name}")
        self.lst_layers.setCurrentRow(min(cur, len(self.photo_layers) - 1))
        self.lst_layers.blockSignals(False)

    def _selected_photo_layer(self):
        row = self.lst_layers.currentRow()
        if row < 0 or row >= len(self.photo_layers):
            return None
        return self.photo_layers[len(self.photo_layers) - 1 - row]

    def _add_photo_layer(self, kind: str):
        if self.photo_base_bgra is None:
            self.status.showMessage("Open a photo first, then add layers on top.")
            return
        ly = None
        if kind in ("image", "cutout"):
            path, _ = QFileDialog.getOpenFileName(self, "Add Layer Image", "", "Images (*.png *.jpg *.jpeg *.webp *.bmp)")
            if not path:
                return
            img = load_image_bgra(path)
            if img is None:
                QMessageBox.warning(self, "Layer", "Could not read that image.")
                return
            if kind == "cutout":
                img = self._with_busy("Cutting out the subject…", lambda: self._cutout_bgra(img))
            ly = PhotoLayer("image", os.path.basename(path))
            ly.bgra = img
            ly.width_frac = 0.4
        else:
            text = self.txt_layer_text.text().strip() or "Your Title"
            ly = PhotoLayer("text", text.replace("|", " "))
            ly.text.text = text.replace("|", "\n")
            ly.text.color = getattr(self.btn_layer_color, "_color", "#FFFFFF")
            ly.text.outline = True
            ly.bgra = render_text_image(ly.text, 160)
            ly.width_frac = 0.6
            ly.cy = 0.82
        self._push_photo_undo()
        self.photo_layers.append(ly)
        self._refresh_layer_list()
        self.lst_layers.setCurrentRow(0)
        self._refresh_photo_canvas()
        self._set_photo_mode("move")

    def _cutout_bgra(self, img: np.ndarray) -> np.ndarray:
        bgr = np.ascontiguousarray(img[:, :, :3])
        if HAS_REMBG:
            rgba = np.array(rembg_remove(Image.fromarray(cv2.cvtColor(bgr, cv2.COLOR_BGR2RGB))))
            return cv2.cvtColor(rgba, cv2.COLOR_RGBA2BGRA)
        h, w = bgr.shape[:2]
        s = min(1.0, 640.0 / max(h, w))
        small = cv2.resize(bgr, (max(1, int(w * s)), max(1, int(h * s))), interpolation=cv2.INTER_AREA)
        sh, sw = small.shape[:2]
        mask = np.zeros((sh, sw), np.uint8)
        alpha = self._grabcut_alpha(small, mask, (int(sw * 0.06), int(sh * 0.06), int(sw * 0.88), int(sh * 0.88)))
        alpha = cv2.GaussianBlur(cv2.resize(alpha, (w, h), interpolation=cv2.INTER_LINEAR), (0, 0), max(0.8, w / 1500.0))
        return cv2.merge([bgr[:, :, 0], bgr[:, :, 1], bgr[:, :, 2], alpha])

    def _on_photo_layer_selected(self, _row):
        ly = self._selected_photo_layer()
        if ly:
            self._set_slider_silently(self.sl_layer_size, int(ly.width_frac * 100))
            self._set_slider_silently(self.sl_layer_opacity, int(ly.opacity * 100))
            self.status.showMessage(f"Layer '{ly.name}' selected — Free Move drags it, the wheel resizes it.")

    def _on_photo_layer_changed(self):
        ly = self._selected_photo_layer()
        if ly:
            ly.width_frac = self.sl_layer_size.value() / 100.0
            ly.opacity = self.sl_layer_opacity.value() / 100.0
            self._refresh_photo_canvas(preserve_masks=True)

    def _move_photo_layer(self, direction: int):
        ly = self._selected_photo_layer()
        if not ly:
            return
        i = self.photo_layers.index(ly)
        j = max(0, min(len(self.photo_layers) - 1, i + direction))
        if i != j:
            self._push_photo_undo()
            self.photo_layers[i], self.photo_layers[j] = self.photo_layers[j], self.photo_layers[i]
            self._refresh_layer_list()
            self.lst_layers.setCurrentRow(len(self.photo_layers) - 1 - j)
            self._refresh_photo_canvas()

    def _delete_photo_layer(self):
        ly = self._selected_photo_layer()
        if ly:
            self._push_photo_undo()
            self.photo_layers.remove(ly)
            self._refresh_layer_list()
            self._refresh_photo_canvas()

    # --- Real-ESRGAN ---
    def _update_esrgan_label(self):
        exe = find_realesrgan(str(self.settings.value("realesrgan", "") or ""))
        self.lbl_esrgan.setText(f"Real-ESRGAN ready: {os.path.basename(exe)} — AI Upsize uses it." if exe else
                                "Real-ESRGAN not found — AI Upsize uses the built-in sharpener. For true AI detail, download "
                                "'realesrgan-ncnn-vulkan' (free, GitHub: xinntao/Real-ESRGAN) and point to it here.")

    def _locate_realesrgan(self):
        p, _ = QFileDialog.getOpenFileName(self, "Locate realesrgan-ncnn-vulkan", "", "Programs (*.exe);;All files (*)")
        if p:
            self.settings.setValue("realesrgan", p)
            self._update_esrgan_label()

    def _apply_photo_ai_upscale(self):
        if self.photo_base_bgra is None:
            return
        self._push_photo_undo()
        exe = find_realesrgan(str(self.settings.value("realesrgan", "") or ""))

        def work():
            base = self.photo_base_bgra
            if exe:
                try:
                    up = realesrgan_upscale(exe, np.ascontiguousarray(base[:, :, :3]), 4)
                    h, w = base.shape[:2]
                    up = cv2.resize(up, (w * 2, h * 2), interpolation=cv2.INTER_AREA)
                    alpha = cv2.resize(base[:, :, 3], (w * 2, h * 2), interpolation=cv2.INTER_LANCZOS4)
                    return cv2.merge([up[:, :, 0], up[:, :, 1], up[:, :, 2], alpha]), "Real-ESRGAN"
                except Exception as e:
                    self.status.showMessage(f"Real-ESRGAN failed ({e}); using the built-in upscaler.")
            return ai_super_res_upscale(base, factor=2), "built-in"
        self.photo_base_bgra, engine = self._with_busy("AI upscaling 2x…", work)
        self._rebuild_photo_preview()
        self._refresh_photo_canvas()
        h, w = self.photo_base_bgra.shape[:2]
        self.status.showMessage(f"Upscaled 2x with {engine}. New resolution: {w}×{h}")

    # --- Batch ---
    def _batch_photos(self):
        files, _ = QFileDialog.getOpenFileNames(self, "Choose Photos to Process", "", "Images (*.png *.jpg *.jpeg *.webp *.bmp *.tif *.tiff)")
        if not files:
            return
        out_dir = QFileDialog.getExistingDirectory(self, "Save Processed Photos To", os.path.dirname(files[0]))
        if not out_dir:
            return
        fmt = self.cmb_p_format.currentText()
        ext = {"JPEG": ".jpg", "PNG": ".png", "WEBP": ".webp"}[fmt]
        q = self.spn_p_quality.value()
        long_edge = self.spn_p_long_edge.value()
        color = self.photo_color.clone() if self.chk_batch_color.isChecked() else None
        text = self.photo_text.clone() if self.chk_batch_text.isChecked() and self.photo_text.active() else None
        layers = [ly.clone() for ly in self.photo_layers] if self.chk_batch_layers.isChecked() else []
        auto = self.chk_batch_auto.isChecked()
        prog = QProgressDialog("Processing photos…", "Cancel", 0, len(files), self)
        prog.setWindowTitle("Batch")
        prog.setWindowModality(Qt.WindowModality.WindowModal)
        prog.setMinimumDuration(0)
        state = {"done": 0, "failed": [], "cancel": False}

        def work():
            for path in files:
                if state["cancel"]:
                    break
                try:
                    img = load_image_bgra(path)
                    if img is None:
                        raise RuntimeError("unreadable")
                    bgr = np.ascontiguousarray(img[:, :, :3])
                    if auto:
                        bgr = auto_enhance(bgr)
                    if color:
                        bgr = apply_color(bgr, color)
                    if long_edge > 0:
                        h, w = bgr.shape[:2]
                        s = long_edge / max(h, w)
                        bgr = cv2.resize(bgr, (max(1, int(w * s)), max(1, int(h * s))), interpolation=cv2.INTER_AREA if s < 1 else cv2.INTER_LANCZOS4)
                    h, w = bgr.shape[:2]
                    if text:
                        bgr = composite_bgra_over(bgr, render_text_layer(w, h, text))
                    if layers:
                        bgr = composite_layers(bgr, layers)
                    params = {".jpg": [cv2.IMWRITE_JPEG_QUALITY, q], ".webp": [cv2.IMWRITE_WEBP_QUALITY, q], ".png": [cv2.IMWRITE_PNG_COMPRESSION, 3]}[ext]
                    ok, buf = cv2.imencode(ext, bgr, params)
                    if not ok:
                        raise RuntimeError("encode failed")
                    buf.tofile(os.path.join(out_dir, os.path.splitext(os.path.basename(path))[0] + "_ank" + ext))
                except Exception as e:
                    state["failed"].append(f"{os.path.basename(path)}: {e}")
                state["done"] += 1
                self._bridge.call.emit(lambda: prog.setValue(state["done"]))

            def finish():
                prog.close()
                ok_n = state["done"] - len(state["failed"])
                msg = f"Batch finished: {ok_n} photo(s) saved to {out_dir}"
                if state["failed"]:
                    msg += "\n\nSkipped:\n" + "\n".join(state["failed"][:10])
                QMessageBox.information(self, "Batch", msg)
                self.status.showMessage(msg.split("\n")[0])
            self._bridge.call.emit(finish)
        prog.canceled.connect(lambda: state.__setitem__("cancel", True))
        threading.Thread(target=work, daemon=True).start()

    # --- Thumbnail / cover maker ---
    def _thumbnail_maker(self):
        if self.photo_base_bgra is None:
            QMessageBox.information(self, "Thumbnail Maker", "Open the photo (or send a video frame) you want on the thumbnail first.")
            return
        dlg = QDialog(self)
        dlg.setWindowTitle("Thumbnail Maker")
        form = QFormLayout(dlg)
        t1, t2 = QLineEdit("YOU WON'T BELIEVE"), QLineEdit("WHAT HAPPENED")
        size_cb = QComboBox()
        size_cb.addItems(["YouTube 16:9 (1280×720)", "TikTok / Reels cover 9:16 (1080×1920)", "Square 1:1 (1080×1080)"])
        accent_btn = QPushButton("Accent")
        self._set_color_button(accent_btn, "#FACC15")
        accent_btn.clicked.connect(lambda: self._pick_text_color(accent_btn))
        cut_chk = QCheckBox("Cut out the subject and place it beside the text")
        cut_chk.setChecked(True)
        form.addRow("Title line 1", t1)
        form.addRow("Title line 2", t2)
        form.addRow("Size", size_cb)
        form.addRow("Highlight colour", accent_btn)
        form.addRow(cut_chk)
        bb = QDialogButtonBox(QDialogButtonBox.StandardButton.Ok | QDialogButtonBox.StandardButton.Cancel)
        bb.accepted.connect(dlg.accept)
        bb.rejected.connect(dlg.reject)
        form.addRow(bb)
        if dlg.exec() != QDialog.DialogCode.Accepted:
            return
        W, H = [(1280, 720), (1080, 1920), (1080, 1080)][size_cb.currentIndex()]
        accent = getattr(accent_btn, "_color", "#FACC15")
        src = np.ascontiguousarray(apply_color(self.photo_base_bgra, self.photo_color)[:, :, :3])

        def build():
            bg = fit_into_frame(src, W, H, "fill")
            bg = cv2.convertScaleAbs(cv2.GaussianBlur(bg, (0, 0), max(6, W / 90)), alpha=0.55)
            cp = ColorParams()
            cp.saturation, cp.contrast, cp.vignette = 25, 15, 45
            bg = apply_color(bg, cp)
            layers = []
            if cut_chk.isChecked():
                cut = self._cutout_bgra(to_bgra(src))
                ys, xs = np.nonzero(cut[:, :, 3] > 40)
                if len(xs):
                    cut = cut[ys.min():ys.max() + 1, xs.min():xs.max() + 1]
                ly = PhotoLayer("image", "Subject")
                ly.bgra = cut
                landscape = W > H
                ly.width_frac = 0.42 if landscape else 0.85
                ly.cx, ly.cy = (0.74, 0.55) if landscape else (0.5, 0.66)
                layers.append(ly)
            for k, line in enumerate((t1.text().strip(), t2.text().strip())):
                if not line:
                    continue
                ly = PhotoLayer("text", line)
                ly.text.text = line
                ly.text.color = "#FFFFFF" if k == 0 else accent
                ly.text.outline = True
                ly.bgra = render_text_image(ly.text, 170, "#000000")
                landscape = W > H
                ly.width_frac = 0.52 if landscape else 0.9
                ly.cx = 0.3 if landscape else 0.5
                ly.cy = (0.36 + 0.24 * k) if landscape else (0.14 + 0.11 * k)
                layers.append(ly)
            return bg, layers
        bg, layers = self._with_busy("Building the thumbnail…", build)
        self._push_photo_undo()
        self.photo_base_bgra = to_bgra(bg)
        self.photo_transform = TransformParams()
        self.photo_color = ColorParams()
        self.photo_text = TextOverlay()
        self.photo_layers = layers
        self.photo_path = "thumbnail.jpg"
        self._rebuild_photo_preview()
        self._sync_photo_ui_sliders()
        self._refresh_layer_list()
        self._refresh_photo_canvas()
        self.status.showMessage(f"Thumbnail ready ({W}×{H}). Select a layer to move or resize it, then Save Photo.")


    # ==========================================================================
    # VIDEO STUDIO: UNDO/REDO, RIGHT-CLICK CONTEXT MENU, & LOCKED/STEM TRIMMING
    # ==========================================================================
    def _video_snapshot(self):
        return (
            [s.clone() for s in self.timeline.segments],
            self.timeline.mark_a_ms,
            self.timeline.mark_b_ms,
            self.timeline.playhead_ms,
        )

    def _push_video_undo(self):
        self._mark_dirty()
        self.video_undo_stack.append(self._video_snapshot())
        if len(self.video_undo_stack) > 40:
            self.video_undo_stack.pop(0)
        self.video_redo_stack.clear()

    def _restore_video_snapshot(self, snap):
        segs, ma, mb, ph = snap
        self.timeline.segments = segs
        self._assign_marks(ma, mb)
        self.timeline.playhead_ms = min(ph, self.timeline.total_duration_ms())
        self.timeline.update_width()
        self.timeline.update()
        self._sync_video_transform_ui(self._get_active_video_segment())
        self._render_frame_at_ms(self.timeline.playhead_ms)

    def _undo_video(self):
        if not self.video_undo_stack:
            self.status.showMessage("Nothing to undo on Video Timeline.")
            return
        self.video_redo_stack.append(self._video_snapshot())
        self._restore_video_snapshot(self.video_undo_stack.pop())
        self.status.showMessage("Undid last video timeline edit (Ctrl+Z).")

    def _redo_video(self):
        if not self.video_redo_stack:
            self.status.showMessage("Nothing to redo on Video Timeline.")
            return
        self.video_undo_stack.append(self._video_snapshot())
        self._restore_video_snapshot(self.video_redo_stack.pop())
        self.status.showMessage("Redid video timeline edit (Ctrl+Y).")

    # --- LOCKED vs INDEPENDENT STEM TRIMMING LOGIC ---
    def _on_lock_tracks_toggled(self, checked: bool):
        self.timeline.lock_tracks = checked
        if checked:
            self.cmb_trim_target.setCurrentIndex(0)
            self.status.showMessage("Locked: trimming start/end cuts Video + Voices + Music + Noises together.")
        else:
            self.status.showMessage("Unlocked: you can now trim individual audio stems without cutting the video.")
        self.timeline.update()

    def _on_trim_target_combo_changed(self, idx: int):
        # If user selects an individual stem in the combo box, automatically unlock stem trimming
        self.chk_lock_tracks.blockSignals(True)
        self.chk_lock_tracks.setChecked(idx == 0)
        self.timeline.lock_tracks = (idx == 0)
        self.chk_lock_tracks.blockSignals(False)
        self.timeline.update()

    def _exec_quick_trim(self, from_start: bool, target_override: str = None, sec_override: float = None):
        seg = self._get_active_video_segment()
        if not seg:
            QMessageBox.information(self, "No Active Clip", "Place the playhead over a clip on the timeline first.")
            return

        trim_ms = int(round((sec_override if sec_override is not None else self.spn_trim_sec.value()) * 1000.0))
        idx = self.cmb_trim_target.currentIndex()
        target = target_override or (
            "all" if idx == 0 else ("voices" if idx == 1 else ("music" if idx == 2 else "noise"))
        )

        self._push_video_undo()
        if target == "all":
            if from_start:
                seg.trim_whole_locked_timeline_ms(trim_first_ms=trim_ms, trim_last_ms=0)
                msg = f"Trimmed first {trim_ms/1000:.2f}s from video + all audio stems together."
            else:
                seg.trim_whole_locked_timeline_ms(trim_first_ms=0, trim_last_ms=trim_ms)
                msg = f"Trimmed last {trim_ms/1000:.2f}s from video + all audio stems together."
        else:
            if from_start:
                seg.trim_single_stem_timeline_ms(target, trim_first_ms=trim_ms, trim_last_ms=0)
                msg = f"Trimmed first {trim_ms/1000:.2f}s from the '{target.upper()}' stem only (video unchanged)."
            else:
                seg.trim_single_stem_timeline_ms(target, trim_first_ms=0, trim_last_ms=trim_ms)
                msg = f"Trimmed last {trim_ms/1000:.2f}s from the '{target.upper()}' stem only (video unchanged)."

        self.timeline.update_width()
        self.timeline.update()
        self._render_frame_at_ms(min(self.timeline.playhead_ms, self.timeline.total_duration_ms()))
        self.status.showMessage(msg)

    def _trim_at_timestamp(self, global_ms: int, from_start: bool, target_override: str = None, seg_idx_override: int = None):
        """Trims either the whole clip (locked) or a single stem from its start up to `global_ms` or from `global_ms` to its end."""
        acc = 0
        target_seg = None
        seg_start_ms = 0
        for i, seg in enumerate(self.timeline.segments):
            if (seg_idx_override is not None and seg_idx_override >= 0 and i == seg_idx_override) or (
                (seg_idx_override is None or seg_idx_override < 0) and acc <= global_ms <= acc + seg.duration_ms
            ):
                target_seg = seg
                seg_start_ms = acc
                break
            acc += seg.duration_ms

        if not target_seg:
            return

        local_ms = max(0, min(target_seg.duration_ms, global_ms - seg_start_ms))
        idx = self.cmb_trim_target.currentIndex()
        target = target_override or (
            "all" if (self.timeline.lock_tracks or idx == 0) else ("voices" if idx == 1 else ("music" if idx == 2 else "noise"))
        )

        self._push_video_undo()
        if target == "all":
            if from_start:
                target_seg.trim_whole_locked_timeline_ms(trim_first_ms=local_ms, trim_last_ms=0)
                self.timeline.playhead_ms = seg_start_ms
            else:
                cut_end = target_seg.duration_ms - local_ms
                target_seg.trim_whole_locked_timeline_ms(trim_first_ms=0, trim_last_ms=cut_end)
                self.timeline.playhead_ms = min(global_ms, self.timeline.total_duration_ms())
        else:
            target_seg.audio_mix.separated = True
            if from_start:
                target_seg.audio_mix.stem_trim_start[target] = local_ms
            else:
                target_seg.audio_mix.stem_trim_end[target] = max(0, target_seg.duration_ms - local_ms)
            target_seg._clamp_stem_trims()

        self.timeline.update_width()
        self.timeline.update()
        self._render_frame_at_ms(self.timeline.playhead_ms)
        self.status.showMessage(f"Trimmed {'start' if from_start else 'end'} ({target.upper()}) at {format_ms(global_ms)}.")

    # --- RIGHT-CLICK CONTEXT MENU ON TIMELINE & VIDEO MONITOR ---
    def _on_video_monitor_right_clicked(self, global_pos: QPoint):
        seg, _ = self._get_segment_at_ms(self.timeline.playhead_ms)
        seg_idx = self.timeline.segments.index(seg) if seg in self.timeline.segments else -1
        self._show_timeline_context_menu(global_pos, self.timeline.playhead_ms, seg_idx, "video")

    def _show_timeline_context_menu(self, global_pos: QPoint, clicked_ms: int, seg_idx: int, lane: str):
        menu = QMenu(self)

        # Move playhead to clicked position for convenience
        self.timeline.playhead_ms = clicked_ms
        self._render_frame_at_ms(clicked_ms)
        self.timeline.update()

        def act(icon, color, text, fn, enabled=True, parent=menu):
            a = parent.addAction(make_icon(icon, color), text)
            a.triggered.connect(fn)
            a.setEnabled(enabled)
            return a

        act("marker", "cyan", f"Set Mark A here ({format_ms(clicked_ms)})   [", self._set_mark_a)
        act("marker", "rose", f"Set Mark B here ({format_ms(clicked_ms)})   ]", self._set_mark_b)
        act("reset", "slate", "Clear Mark A & Mark B", self._clear_marks)
        act("unlock" if self.timeline.lock_a else "lock", "cyan", "Unlock Mark A" if self.timeline.lock_a else "Lock Mark A   (Ctrl+[)",
            lambda: self._toggle_mark_lock("A"))
        act("unlock" if self.timeline.lock_b else "lock", "rose", "Unlock Mark B" if self.timeline.lock_b else "Lock Mark B   (Ctrl+])",
            lambda: self._toggle_mark_lock("B"))
        menu.addSeparator()
        act("split", "orange", "Split clip here (S)", self._split_at_playhead_action)
        act("copy", "sky", "Copy [Mark A-B] or active clip (Ctrl+C)", self._copy_marked_or_active_clip)
        act("paste", "sky", "Paste copied clip here (Ctrl+V)", self._insert_copied_at_playhead, bool(self.clipboard_segments))
        act("paste", "violet", "Replace [Mark A-B] with copied clip", self._replace_marked_with_copied,
            bool(self.clipboard_segments) and self.timeline.mark_a_ms is not None and self.timeline.mark_b_ms is not None)
        act("trash", "red", "Delete [Mark A-B] or active clip (Del)", self._delete_marked_or_active_clip)
        menu.addSeparator()

        # Submenu: Trim Whole Clip (Video + All Audio Stems Locked Together)
        sub_locked = menu.addMenu(make_icon("lock", "amber"), "Trim whole clip (video + all stems locked)")
        sub_locked.addAction("Trim first part up to here", lambda: self._trim_at_timestamp(clicked_ms, True, "all", seg_idx))
        sub_locked.addAction("Trim last part from here to end", lambda: self._trim_at_timestamp(clicked_ms, False, "all", seg_idx))
        sub_locked.addSeparator()
        sub_locked.addAction("Remove first 1.0 s", lambda: self._exec_quick_trim(True, "all", 1.0))
        sub_locked.addAction("Remove first 2.0 s", lambda: self._exec_quick_trim(True, "all", 2.0))
        sub_locked.addAction("Remove last 1.0 s", lambda: self._exec_quick_trim(False, "all", 1.0))
        sub_locked.addAction("Remove last 2.0 s", lambda: self._exec_quick_trim(False, "all", 2.0))

        # Submenu: Trim ONLY a Specific Audio Stem (Keep Video Intact!)
        stem_names = [
            ("voices", "Voices / Speech only", "mic"),
            ("music", "Music / Instruments only", "music"),
            ("noise", "Noises / Ambience only", "noise"),
        ]
        # Put the lane user right-clicked on at the top!
        if lane in ("voices", "music", "noise"):
            stem_names.sort(key=lambda item: 0 if item[0] == lane else 1)

        for st_key, st_label, st_icon in stem_names:
            sub_st = menu.addMenu(make_icon(st_icon, "sky"), f"Trim {st_label} (keep video)")
            sub_st.addAction(f"Cut first part of {st_key} up to here", lambda k=st_key: self._trim_at_timestamp(clicked_ms, True, k, seg_idx))
            sub_st.addAction(f"Cut last part of {st_key} from here", lambda k=st_key: self._trim_at_timestamp(clicked_ms, False, k, seg_idx))
            sub_st.addSeparator()
            sub_st.addAction(f"Remove first 2.0 s of {st_key} only", lambda k=st_key: self._exec_quick_trim(True, k, 2.0))
            sub_st.addAction(f"Remove last 2.0 s of {st_key} only", lambda k=st_key: self._exec_quick_trim(False, k, 2.0))
            sub_st.addAction(f"Mute {st_key} completely", lambda k=st_key: self._mute_single_stem(seg_idx, k))
            sub_st.addAction(f"Restore full length of {st_key}", lambda k=st_key: self._restore_single_stem_trim(seg_idx, k))

        menu.addSeparator()
        lock_text = "Lock video & audio stems together" if not self.timeline.lock_tracks else "Unlock stems for independent edge-drag trim"
        act("lock" if not self.timeline.lock_tracks else "unlock", "amber", lock_text,
            lambda: self.chk_lock_tracks.setChecked(not self.chk_lock_tracks.isChecked()))
        act("mic", "sky", "Separate audio into Voices, Music & Noises", self._separate_audio_for_active_clip)
        act("fade", "indigo", "Fade in + out 1 s (video & sound)", lambda: self._quick_fades(1.0))
        act("camera", "pink", "Save this frame as PNG…", self._snapshot_frame)
        act("image", "pink", "Send this frame to Photo Studio", self._frame_to_photo_studio)
        menu.addSeparator()
        act("undo", "slate", "Undo (Ctrl+Z)", self._undo_video)
        act("redo", "slate", "Redo (Ctrl+Y)", self._redo_video)

        menu.exec(global_pos)

    def _mute_single_stem(self, seg_idx: int, stem_key: str):
        if 0 <= seg_idx < len(self.timeline.segments):
            self._push_video_undo()
            seg = self.timeline.segments[seg_idx]
            seg.audio_mix.separated = True
            if stem_key == "voices":
                seg.audio_mix.voices_vol = 0.0
            elif stem_key == "music":
                seg.audio_mix.music_vol = 0.0
            elif stem_key == "noise":
                seg.audio_mix.noise_vol = 0.0
            self._sync_video_transform_ui(seg)
            self.timeline.update()

    def _restore_single_stem_trim(self, seg_idx: int, stem_key: str):
        if 0 <= seg_idx < len(self.timeline.segments):
            self._push_video_undo()
            seg = self.timeline.segments[seg_idx]
            seg.audio_mix.stem_trim_start[stem_key] = 0
            seg.audio_mix.stem_trim_end[stem_key] = 0
            self.timeline.update()
            self.status.showMessage(f"Restored full duration for {stem_key.title()} stem.")

    def _clear_marks(self):
        self._assign_marks(None, None)
        if self.timeline.lock_a or self.timeline.lock_b:
            self.status.showMessage("Cleared the unlocked mark(s). Locked marks stay until you unlock them.")

    def _split_at_playhead_action(self):
        if not self.timeline.segments:
            return
        self._push_video_undo()
        left, right = self._split_segments_at_ms(self.timeline.segments, self.timeline.playhead_ms)
        self.timeline.segments = left + right
        self.timeline.update()
        self.status.showMessage(f"Split clip at playhead ({format_ms(self.timeline.playhead_ms)}).")

    def _copy_marked_or_active_clip(self):
        if self.timeline.mark_a_ms is not None and self.timeline.mark_b_ms is not None and self.timeline.mark_a_ms != self.timeline.mark_b_ms:
            m1, m2 = min(self.timeline.mark_a_ms, self.timeline.mark_b_ms), max(self.timeline.mark_a_ms, self.timeline.mark_b_ms)
            self.clipboard_segments = self._extract_range_segments(m1, m2)
            self.status.showMessage(f"Copied [Mark A - Mark B] ({format_ms(m2 - m1)}) to clipboard (Ctrl+V to paste).")
        else:
            seg = self._get_active_video_segment()
            if seg:
                self.clipboard_segments = [seg.clone()]
                self.status.showMessage(f"Copied active clip [V{seg.source.source_id}] ({format_ms(seg.duration_ms)}) to clipboard (Ctrl+V to paste).")

    def _delete_marked_or_active_clip(self):
        if self.timeline.mark_a_ms is not None and self.timeline.mark_b_ms is not None and self.timeline.mark_a_ms != self.timeline.mark_b_ms:
            self._delete_marked_region()
        else:
            seg = self._get_active_video_segment()
            if seg and seg in self.timeline.segments:
                self._push_video_undo()
                self.timeline.segments.remove(seg)
                self.timeline.playhead_ms = min(self.timeline.playhead_ms, self.timeline.total_duration_ms())
                self.timeline.update_width()
                self.timeline.update()
                if not self.timeline.segments:
                    self.video_Canvas.clear_image()
                self._render_frame_at_ms(self.timeline.playhead_ms)
                self.status.showMessage(f"Deleted active clip [V{seg.source.source_id}].")

    # --- VIDEO LOADING & AUDIO SEPARATION ---
    def _add_videos(self, insert_at_playhead=False):
        paths, _ = QFileDialog.getOpenFileNames(
            self, "Select Video File(s)", "", "Videos (*.mp4 *.mov *.avi *.mkv *.webm *.m4v)"
        )
        if paths:
            insert_ms = self.timeline.playhead_ms if insert_at_playhead else None
            self._load_video_paths(paths, insert_at_ms=insert_ms)

    def _load_video_paths(self, paths: list[str], insert_at_ms: int = None):
        new_segments = []
        failed = []
        for p in paths:
            src_id = len(self.video_sources) + 1
            color = VIDEO_PALETTE[(src_id - 1) % len(VIDEO_PALETTE)]
            src = VideoSource(src_id, p, color)
            if src.duration_ms <= 0 or src.width <= 0:
                failed.append(os.path.basename(p))
                continue
            self.video_sources.append(src)
            self.open_captures[src.source_id] = FrameReader(p, src.fps)
            new_segments.append(TimelineSegment(src, 0, src.duration_ms))

            badge = QLabel(f" V{src.source_id}  {src.filename} ")
            badge.setStyleSheet(
                f"background: qlineargradient(x1:0, y1:0, x2:0, y2:1, stop:0 {QColor(src.color).lighter(130).name()}, "
                f"stop:1 {QColor(src.color).darker(140).name()}); color: white; font-weight: bold; padding: 3px 9px; "
                f"border-radius: 7px; border: 1px solid {QColor(src.color).lighter(160).name()};"
            )
            self.sources_legend_layout.insertWidget(self.sources_legend_layout.count() - 1, badge)
            self._load_source_audio_async(src)
            self._make_thumbs_async(src)
            self._make_proxy_async(src)

        if failed:
            QMessageBox.warning(self, "Some files could not be opened",
                                "These videos could not be read (unsupported codec or damaged file):\n\n" + "\n".join(failed))
        if not new_segments:
            return

        self._push_video_undo()
        if insert_at_ms is None or not self.timeline.segments:
            self.timeline.segments.extend(new_segments)
        else:
            before, after = self._split_segments_at_ms(self.timeline.segments, insert_at_ms)
            self.timeline.segments = before + new_segments + after

        self.timeline.update_width()
        self.timeline.update()
        self._render_frame_at_ms(self.timeline.playhead_ms)
        self.status.showMessage(f"Loaded {len(new_segments)} video(s). Reading their soundtracks in the background…")

    def _load_source_audio_async(self, src: VideoSource):
        def work():
            src.ensure_raw_audio()
            self._bridge.call.emit(self.timeline.update)
        threading.Thread(target=work, daemon=True).start()

    def _separate_audio_for_active_clip(self):
        seg = self._get_active_video_segment()
        if not seg:
            QMessageBox.information(self, "No Active Video", "Add or drag-and-drop a video onto the timeline first.")
            return

        src = seg.source
        if src.stems_separated:
            for s in self.timeline.segments:
                if s.source.source_id == src.source_id:
                    s.audio_mix.separated = True
            self._sync_video_transform_ui(seg)
            self.timeline.update()
            self.status.showMessage(f"[V{src.source_id}] is already separated into Voices, Music and Noises.")
            return
        if src.source_id in self._separating:
            self.status.showMessage("Separation already running for this video…")
            return

        self._separating.add(src.source_id)
        engine = self.cmb_sep_engine.currentData()
        self.btn_sep_audio.setEnabled(False)
        self.lbl_sep_progress.setText(f"Separating V{src.source_id}: reading soundtrack…")
        last_pct = [-1]

        def report(frac):
            pct = int(frac * 100)
            if pct - last_pct[0] >= 4:
                last_pct[0] = pct
                self._bridge.call.emit(lambda p=pct: self.lbl_sep_progress.setText(f"Separating V{src.source_id}: {p}%"))

        def work():
            msg, ok = "", False
            try:
                if not src.ensure_raw_audio():
                    msg = f"[V{src.source_id}] has no audio track to separate."
                else:
                    if engine == "demucs":
                        tmp = os.path.join(tempfile.gettempdir(), f"ank_dm_{os.getpid()}_{src.source_id}.wav")
                        write_wav_float(tmp, src.raw_audio, src.sample_rate)
                        try:
                            vocals, rest = demucs_separate(tmp, src.sample_rate, progress=report)
                        finally:
                            try:
                                os.remove(tmp)
                            except OSError:
                                pass
                        n = min(len(vocals), len(rest), len(src.raw_audio))
                        # Demucs gives clean vocals; the accompaniment is split into music and noise bands
                        v_band, m_band, nse = AudioStemProcessor.separate_audio(rest[:n], src.sample_rate)
                        vox, mus = vocals[:n], v_band + m_band
                    else:
                        vox, mus, nse = AudioStemProcessor.separate_audio(src.raw_audio, src.sample_rate, progress=report)
                    src.voices_data, src.music_data, src.noise_data = vox, mus, nse
                    src.stems_engine = engine
                    envs = dict(src.envelopes or {})
                    envs.update({"voices": AudioStemProcessor.envelope(vox), "music": AudioStemProcessor.envelope(mus),
                                 "noise": AudioStemProcessor.envelope(nse)})
                    src.envelopes = envs
                    src.stems_separated = True
                    ok = True
                    msg = f"Separated [V{src.source_id}] into Voices, Music and Noises ({'AI Demucs' if engine == 'demucs' else 'fast filter'})."
            except Exception as e:
                msg = f"Audio separation failed: {e}"

            def done():
                self._separating.discard(src.source_id)
                self.btn_sep_audio.setEnabled(True)
                if ok:
                    for s in self.timeline.segments:
                        if s.source.source_id == src.source_id:
                            s.audio_mix.separated = True
                self.lbl_sep_progress.setText(msg)
                self._sync_video_transform_ui(self._get_active_video_segment())
                self.timeline.update()
                self.status.showMessage(msg)
            self._bridge.call.emit(done)
        threading.Thread(target=work, daemon=True).start()

    def _on_audio_stem_sliders_changed(self):
        vox_v = self.sl_vox.value() / 100.0
        mus_v = self.sl_mus.value() / 100.0
        nse_v = self.sl_nse.value() / 100.0

        self.lbl_vox.setText(f"Voices / Speech: {int(vox_v * 100)}%")
        self.lbl_mus.setText(f"Music / Instruments: {int(mus_v * 100)}%")
        self.lbl_nse.setText(f"Noises / Ambience: {int(nse_v * 100)}%")

        seg = self._get_active_video_segment()
        if seg:
            if not seg.source.stems_separated:
                self.status.showMessage("Tip: click 'Separate Audio' first — the stem sliders apply once the clip is separated.")
            seg.audio_mix.separated = seg.source.stems_separated or seg.audio_mix.separated
            seg.audio_mix.voices_vol = vox_v
            seg.audio_mix.music_vol = mus_v
            seg.audio_mix.noise_vol = nse_v
            self.timeline.update()

    def _on_clip_gain_changed(self, v: int):
        seg = self._get_active_video_segment()
        if seg:
            seg.audio_mix.gain = v / 100.0
            self.timeline.update()

    def _apply_audio_fades(self):
        seg = self._get_active_video_segment()
        if not seg:
            return
        self._push_video_undo()
        seg.audio_mix.fade_in_ms = int(self.spn_afade_in.value() * 1000)
        seg.audio_mix.fade_out_ms = int(self.spn_afade_out.value() * 1000)
        self.status.showMessage(f"Audio fades set: in {self.spn_afade_in.value():.2f}s, out {self.spn_afade_out.value():.2f}s.")

    def _apply_audio_mix_to_marked_region(self):
        marks = self._get_valid_marks()
        if not marks:
            return
        self._push_video_undo()
        m1, m2 = marks
        left, rest = self._split_segments_at_ms(self.timeline.segments, m1)
        marked_segs, right = self._split_segments_at_ms(rest, m2 - m1)

        vox_v = self.sl_vox.value() / 100.0
        mus_v = self.sl_mus.value() / 100.0
        nse_v = self.sl_nse.value() / 100.0

        for s in marked_segs:
            s.audio_mix.separated = True
            s.audio_mix.voices_vol = vox_v
            s.audio_mix.music_vol = mus_v
            s.audio_mix.noise_vol = nse_v
            s.audio_mix.gain = self.sl_gain.value() / 100.0

        self.timeline.segments = left + marked_segs + right
        self.timeline.update()

    def _split_segments_at_ms(self, seg_list: list[TimelineSegment], split_ms: int):
        left, right = [], []
        acc = 0
        for seg in seg_list:
            seg_len = seg.duration_ms
            if acc + seg_len <= split_ms:
                left.append(seg.clone())
            elif acc >= split_ms:
                right.append(seg.clone())
            else:
                timeline_offset_ms = split_ms - acc
                source_offset_ms = int(round(timeline_offset_ms * seg.speed))
                mid_source_ms = min(seg.out_ms - 1, max(seg.in_ms + 1, seg.in_ms + source_offset_ms))

                left_seg = TimelineSegment(seg.source, seg.in_ms, mid_source_ms, seg.crop_rect, seg.transform, seg.speed,
                                           seg.audio_mix, seg.color, seg.text, seg.fade_in_ms, 0, seg.transition, seg.motion)
                right_seg = TimelineSegment(seg.source, mid_source_ms, seg.out_ms, seg.crop_rect, seg.transform, seg.speed,
                                            seg.audio_mix, seg.color, seg.text, 0, seg.fade_out_ms, None, seg.motion)
                left_seg.audio_mix.fade_out_ms = 0
                right_seg.audio_mix.fade_in_ms = 0

                # Preserve any independent stem trims across the split
                for k in ("voices", "music", "noise"):
                    st_s = seg.audio_mix.stem_trim_start[k]
                    st_e = seg.audio_mix.stem_trim_end[k]
                    left_seg.audio_mix.stem_trim_start[k] = min(left_seg.duration_ms, st_s)
                    left_seg.audio_mix.stem_trim_end[k] = max(0, st_e - right_seg.duration_ms)
                    right_seg.audio_mix.stem_trim_start[k] = max(0, st_s - left_seg.duration_ms)
                    right_seg.audio_mix.stem_trim_end[k] = min(right_seg.duration_ms, st_e)
                left_seg._clamp_stem_trims()
                right_seg._clamp_stem_trims()

                left.append(left_seg)
                right.append(right_seg)
            acc += seg_len
        return left, right

    def _extract_range_segments(self, start_ms: int, end_ms: int) -> list[TimelineSegment]:
        _, after_start = self._split_segments_at_ms(self.timeline.segments, start_ms)
        middle, _ = self._split_segments_at_ms(after_start, end_ms - start_ms)
        return middle

    def _get_active_video_segment(self) -> TimelineSegment:
        seg, _ = self._get_segment_at_ms(self.timeline.playhead_ms)
        return seg

    def _segment_start_ms(self, target: TimelineSegment) -> int:
        acc = 0
        for seg in self.timeline.segments:
            if seg is target:
                return acc
            acc += seg.duration_ms
        return 0

    # --- SPEED CONTROL METHODS ---
    def _on_speed_slider_changed(self, val: int):
        self.selected_speed = val / 100.0
        tag = "Slow-Mo" if self.selected_speed < 1.0 else ("Fast-Forward" if self.selected_speed > 1.0 else "Normal")
        self.lbl_speed_val.setText(f"Target Speed: {self.selected_speed:.2f}x ({tag})")

    def _set_speed_preset(self, speed_val: float):
        self.selected_speed = speed_val
        self.sl_speed.blockSignals(True)
        self.sl_speed.setValue(int(round(speed_val * 100)))
        self.sl_speed.blockSignals(False)
        tag = "Slow-Mo" if speed_val < 1.0 else ("Fast-Forward" if speed_val > 1.0 else "Normal")
        self.lbl_speed_val.setText(f"Target Speed: {speed_val:.2f}x ({tag})")

    def _apply_speed_to_marked_region(self):
        marks = self._get_valid_marks()
        if not marks:
            return
        self._push_video_undo()
        m1, m2 = marks
        left, rest = self._split_segments_at_ms(self.timeline.segments, m1)
        marked_segs, right = self._split_segments_at_ms(rest, m2 - m1)

        if not marked_segs:
            return

        for s in marked_segs:
            s.speed = self.selected_speed
            s._clamp_stem_trims()

        new_marked_duration = sum(s.duration_ms for s in marked_segs)
        self.timeline.segments = left + marked_segs + right
        self._assign_marks(m1, m1 + new_marked_duration)
        self.timeline.playhead_ms = m1
        self.timeline.update_width()
        self.timeline.update()
        self._render_frame_at_ms(m1)

    def _apply_speed_to_active_clip(self):
        seg = self._get_active_video_segment()
        if not seg:
            return
        self._push_video_undo()
        seg.speed = self.selected_speed
        seg._clamp_stem_trims()
        self.timeline.update_width()
        self.timeline.update()
        self._render_frame_at_ms(self.timeline.playhead_ms)

    # --- SPATIAL, COLOR, TITLE & AI METHODS ---
    def _sync_video_transform_ui(self, seg: TimelineSegment):
        if not seg:
            return
        tf = seg.transform
        am = seg.audio_mix
        sliders = [self.sl_v_angle, self.sl_v_scale, self.sl_speed, self.sl_vox, self.sl_mus, self.sl_nse, self.cmb_v_filter]
        for sl in sliders:
            sl.blockSignals(True)

        self.sl_v_angle.setValue(int(tf.free_angle))
        self.lbl_v_angle.setText(f"Free Angle: {int(tf.free_angle)}°")
        self.sl_v_scale.setValue(int(tf.scale * 100))
        self.lbl_v_scale.setText(f"Scale: {int(tf.scale * 100)}%")
        self.btn_v_ai_upscale.setChecked(tf.ai_upscale)
        self.btn_v_cutout.setChecked(tf.transparent_bg)

        self.selected_speed = seg.speed
        self.sl_speed.setValue(int(round(seg.speed * 100)))
        tag = "Slow-Mo" if seg.speed < 1.0 else ("Fast-Forward" if seg.speed > 1.0 else "Normal")
        self.lbl_speed_val.setText(f"Target Speed: {seg.speed:.2f}x ({tag})")

        self.sl_vox.setValue(int(round(am.voices_vol * 100)))
        self.sl_mus.setValue(int(round(am.music_vol * 100)))
        self.sl_nse.setValue(int(round(am.noise_vol * 100)))
        self.lbl_vox.setText(f"Voices / Speech: {int(am.voices_vol * 100)}%")
        self.lbl_mus.setText(f"Music / Instruments: {int(am.music_vol * 100)}%")
        self.lbl_nse.setText(f"Noises / Ambience: {int(am.noise_vol * 100)}%")
        self._set_slider_silently(self.sl_gain, int(round(am.gain * 100)))

        idx = self.cmb_v_filter.findData(seg.color.filter)
        self.cmb_v_filter.setCurrentIndex(max(0, idx))
        for f, sl in self.v_color_sliders.items():
            self._set_slider_silently(sl, getattr(seg.color, f))

        for sl in sliders:
            sl.blockSignals(False)

        if seg.source.source_id in self._separating:
            pass
        elif seg.source.stems_separated:
            self.lbl_sep_progress.setText(f"Stems ready for V{seg.source.source_id}. Sliders control this clip.")
        elif seg.source.has_audio is False:
            self.lbl_sep_progress.setText(f"V{seg.source.source_id} has no audio track.")
        else:
            self.lbl_sep_progress.setText(f"V{seg.source.source_id}: not separated yet (clip volume and fades still work).")

    def _mod_video_transform(self, rot_step=0, flip_h=False, flip_v=False):
        seg = self._get_active_video_segment()
        if not seg:
            return
        self._push_video_undo()
        if rot_step:
            seg.transform.rot_90_steps = (seg.transform.rot_90_steps + rot_step) % 4
        if flip_h:
            seg.transform.flip_h = not seg.transform.flip_h
        if flip_v:
            seg.transform.flip_v = not seg.transform.flip_v
        self.timeline.update()
        self._render_frame_at_ms(self.timeline.playhead_ms)

    def _reset_video_transform(self):
        seg = self._get_active_video_segment()
        if not seg:
            return
        self._push_video_undo()
        seg.transform.reset()
        seg.transform.transparent_bg = False
        seg.transform.bg_replacement = None
        seg.crop_rect = None
        seg.speed = 1.0
        seg.audio_mix = AudioMixParams(separated=seg.source.stems_separated)
        self._sync_video_transform_ui(seg)
        self.timeline.update_width()
        self.timeline.update()
        self._render_frame_at_ms(self.timeline.playhead_ms)

    def _on_video_angle_slider(self, val: int):
        seg = self._get_active_video_segment()
        if not seg:
            return
        seg.transform.free_angle = float(val)
        self.lbl_v_angle.setText(f"Free Angle: {val}°")
        self.timeline.update()
        self._render_frame_at_ms(self.timeline.playhead_ms)

    def _on_video_scale_slider(self, val: int):
        seg = self._get_active_video_segment()
        if not seg:
            return
        seg.transform.scale = val / 100.0
        self.lbl_v_scale.setText(f"Scale: {val}%")
        self.timeline.update()
        self._render_frame_at_ms(self.timeline.playhead_ms)

    def _toggle_video_free_move(self, checked: bool):
        if checked and self.chk_output_view.isChecked():
            self.chk_output_view.setChecked(False)
        if checked:
            self.btn_crop_vid.setChecked(False)
            self.video_Canvas.mode = "move"
        else:
            self.video_Canvas.mode = "none"
        self.video_Canvas.update()

    def _on_video_free_moved(self, dx: int, dy: int):
        seg = self._get_active_video_segment()
        if not seg:
            return
        s = self.video_preview_scale or 1.0
        seg.transform.offset_x += int(round(dx / s))
        seg.transform.offset_y += int(round(dy / s))
        self.timeline.update()
        self._render_frame_at_ms(self.timeline.playhead_ms)

    def _on_video_wheel_scaled(self, factor: float):
        seg = self._get_active_video_segment()
        if not seg:
            return
        seg.transform.scale = max(0.10, min(3.00, seg.transform.scale * factor))
        self._sync_video_transform_ui(seg)
        self.timeline.update()
        self._render_frame_at_ms(self.timeline.playhead_ms)

    def _toggle_video_ai_upscale(self, checked: bool):
        seg = self._get_active_video_segment()
        if not seg:
            return
        self._push_video_undo()
        seg.transform.ai_upscale = checked
        self.timeline.update()
        self._render_frame_at_ms(self.timeline.playhead_ms)

    def _toggle_video_cutout(self, checked: bool):
        seg = self._get_active_video_segment()
        if not seg:
            return
        self._push_video_undo()
        seg.transform.transparent_bg = checked
        self.timeline.update()
        self._render_frame_at_ms(self.timeline.playhead_ms)
        if checked:
            self.btn_move_vid.setChecked(True)
            self._toggle_video_free_move(True)

    def _set_video_custom_bg(self):
        seg = self._get_active_video_segment()
        if not seg:
            return
        path, _ = QFileDialog.getOpenFileName(self, "Select Custom Background for Video Clip", "", "Images (*.png *.jpg *.jpeg *.webp *.bmp)")
        if not path:
            return
        bg_img = cv2.imdecode(np.fromfile(path, dtype=np.uint8), cv2.IMREAD_COLOR)
        if bg_img is not None:
            self._push_video_undo()
            seg.transform.bg_replacement = bg_img
            seg.transform.bg_path = path
            self._render_frame_at_ms(self.timeline.playhead_ms)

    def _clear_video_custom_bg(self):
        seg = self._get_active_video_segment()
        if seg and seg.transform.bg_replacement is not None:
            self._push_video_undo()
            seg.transform.bg_replacement = None
            self._render_frame_at_ms(self.timeline.playhead_ms)

    def _on_video_color_changed(self, *_):
        seg = self._get_active_video_segment()
        if not seg:
            return
        if self.sender() is self.cmb_v_filter:
            self._push_video_undo()
        seg.color.filter = self.cmb_v_filter.currentData() or "none"
        for f, sl in self.v_color_sliders.items():
            setattr(seg.color, f, sl.value())
        self.timeline.update()
        self._render_frame_at_ms(self.timeline.playhead_ms)

    def _reset_video_color(self):
        seg = self._get_active_video_segment()
        if not seg:
            return
        self._push_video_undo()
        seg.color = ColorParams()
        self._sync_video_transform_ui(seg)
        self.timeline.update()
        self._render_frame_at_ms(self.timeline.playhead_ms)

    def _apply_color_to_all_clips(self):
        seg = self._get_active_video_segment()
        if not seg:
            return
        self._push_video_undo()
        for s in self.timeline.segments:
            s.color = seg.color.clone()
        self.timeline.update()
        self.status.showMessage("Applied this clip's color grade to every clip.")

    def _apply_video_title(self):
        seg = self._get_active_video_segment()
        if not seg:
            return
        self._push_video_undo()
        seg.text = self._read_text_overlay(self.txt_v_title, self.spn_v_text_size, self.cmb_v_text_pos,
                                           self.btn_v_text_color, self.chk_v_text_outline, self.chk_v_text_backdrop)
        self.timeline.update()
        self._render_frame_at_ms(self.timeline.playhead_ms)

    def _clear_video_title(self):
        seg = self._get_active_video_segment()
        if seg:
            self._push_video_undo()
            seg.text = TextOverlay()
            self.timeline.update()
            self._render_frame_at_ms(self.timeline.playhead_ms)

    def _apply_video_fades(self):
        seg = self._get_active_video_segment()
        if not seg:
            return
        self._push_video_undo()
        half = seg.duration_ms // 2
        seg.fade_in_ms = min(half, int(self.spn_vfade_in.value() * 1000))
        seg.fade_out_ms = min(half, int(self.spn_vfade_out.value() * 1000))
        self.timeline.update()
        self._render_frame_at_ms(self.timeline.playhead_ms)

    def _quick_fades(self, sec: float):
        self.spn_vfade_in.setValue(sec)
        self.spn_vfade_out.setValue(sec)
        self._apply_video_fades()

    def _set_mark_a(self):
        if self.timeline.lock_a:
            self.status.showMessage("Mark A is locked — unlock it first (Lock A button or Ctrl+[).")
            return
        self.timeline.mark_a_ms = self.timeline.playhead_ms
        b = self.timeline.mark_b_ms
        if b is not None and b < self.timeline.mark_a_ms and not self.timeline.lock_b:
            self.timeline.mark_a_ms, self.timeline.mark_b_ms = b, self.timeline.mark_a_ms
        self._update_marks_label(self.timeline.mark_a_ms, self.timeline.mark_b_ms)
        self.timeline.update()

    def _set_mark_b(self):
        if self.timeline.lock_b:
            self.status.showMessage("Mark B is locked — unlock it first (Lock B button or Ctrl+]).")
            return
        self.timeline.mark_b_ms = self.timeline.playhead_ms
        a = self.timeline.mark_a_ms
        if a is not None and self.timeline.mark_b_ms < a and not self.timeline.lock_a:
            self.timeline.mark_a_ms, self.timeline.mark_b_ms = self.timeline.mark_b_ms, a
        self._update_marks_label(self.timeline.mark_a_ms, self.timeline.mark_b_ms)
        self.timeline.update()

    def _assign_marks(self, a, b):
        """Sets the marks after an edit, leaving any locked mark exactly where it is."""
        total = self.timeline.total_duration_ms()
        if self.timeline.lock_a and self.timeline.mark_a_ms is not None:
            a = min(self.timeline.mark_a_ms, total)
        if self.timeline.lock_b and self.timeline.mark_b_ms is not None:
            b = min(self.timeline.mark_b_ms, total)
        self.timeline.mark_a_ms, self.timeline.mark_b_ms = a, b
        self._update_marks_label(a, b)
        self.timeline.update()

    def _toggle_mark_lock(self, name: str, checked: bool = None):
        tl = self.timeline
        locked = (not (tl.lock_a if name == "A" else tl.lock_b)) if checked is None else bool(checked)
        if locked and (tl.mark_a_ms if name == "A" else tl.mark_b_ms) is None:
            # Locking a mark that isn't set yet places it at the playhead first
            if name == "A":
                tl.mark_a_ms = tl.playhead_ms
            else:
                tl.mark_b_ms = tl.playhead_ms
        if name == "A":
            tl.lock_a = locked
        else:
            tl.lock_b = locked
        btn = self.btn_lock_a if name == "A" else self.btn_lock_b
        btn.setChecked(locked)
        btn.setText(f"{'Unlock' if locked else 'Lock'} {name}")
        btn.setIcon(make_icon("lock" if locked else "unlock", "amber" if locked else ("cyan" if name == "A" else "rose")))
        self._update_marks_label(tl.mark_a_ms, tl.mark_b_ms)
        tl.update()
        if name == "A":
            self.status.showMessage("Mark A locked — Play now starts from Mark A." if locked else "Mark A unlocked — Play starts from the playhead again.")
        else:
            self.status.showMessage("Mark B locked — Play now stops at Mark B." if locked else "Mark B unlocked — Play runs to the end again.")

    def _update_marks_label(self, a, b):
        str_a = (format_ms(a) if a is not None else "--:--.---") + ("  [LOCKED]" if self.timeline.lock_a else "")
        str_b = (format_ms(b) if b is not None else "--:--.---") + ("  [LOCKED]" if self.timeline.lock_b else "")
        self.lbl_marks_info.setText(f"Mark A: {str_a}   |   Mark B: {str_b}")

    def _on_live_preview(self, ms: int, label: str):
        """While trimming or dragging a mark, the monitor shows the exact frame reached."""
        self.video_Canvas.overlay_label = label
        self._render_frame_at_ms(max(0, int(ms)))
        self.lbl_time_counter.setText(f"{format_ms(ms)} / {format_ms(self.timeline.total_duration_ms())}")

    def _end_live_preview(self):
        self.video_Canvas.overlay_label = ""
        self._render_frame_at_ms(min(self.timeline.playhead_ms, self.timeline.total_duration_ms()))

    def _auto_mark_scene(self):
        if not self.timeline.segments:
            return
        acc = 0
        for seg in self.timeline.segments:
            if acc <= self.timeline.playhead_ms <= acc + seg.duration_ms:
                self._assign_marks(acc, acc + seg.duration_ms)
                return
            acc += seg.duration_ms

    def _get_valid_marks(self, quiet: bool = False):
        a, b = self.timeline.mark_a_ms, self.timeline.mark_b_ms
        if a is None or b is None or a == b:
            if not quiet:
                QMessageBox.warning(self, "Mark A & B Required", "Please set both Mark A and Mark B on the timeline first.")
            return None
        return min(a, b), max(a, b)

    def _delete_marked_region(self):
        marks = self._get_valid_marks()
        if not marks:
            return
        self._push_video_undo()
        m1, m2 = marks
        left, rest = self._split_segments_at_ms(self.timeline.segments, m1)
        _, right = self._split_segments_at_ms(rest, m2 - m1)
        self.timeline.segments = left + right
        self._assign_marks(None, None)
        self.timeline.playhead_ms = min(m1, self.timeline.total_duration_ms())
        self.timeline.update_width()
        self.timeline.update()
        self._render_frame_at_ms(self.timeline.playhead_ms)

    def _trim_to_marked_region(self):
        marks = self._get_valid_marks()
        if not marks:
            return
        self._push_video_undo()
        m1, m2 = marks
        self.timeline.segments = self._extract_range_segments(m1, m2)
        self._assign_marks(0, self.timeline.total_duration_ms())
        self.timeline.playhead_ms = 0
        self.timeline.update_width()
        self.timeline.update()
        self._render_frame_at_ms(0)

    def _insert_copied_at_playhead(self):
        if not self.clipboard_segments:
            QMessageBox.information(self, "Clipboard Empty", "Copy a [Mark A - B] region or clip first (Ctrl+C).")
            return
        self._push_video_undo()
        cloned = [s.clone() for s in self.clipboard_segments]
        left, right = self._split_segments_at_ms(self.timeline.segments, self.timeline.playhead_ms)
        self.timeline.segments = left + cloned + right
        self.timeline.update_width()
        self.timeline.update()
        self._render_frame_at_ms(self.timeline.playhead_ms)
        self.status.showMessage("Pasted copied clip(s) at playhead (Ctrl+V).")

    def _replace_marked_with_copied(self):
        if not self.clipboard_segments:
            QMessageBox.information(self, "Clipboard Empty", "First copy a selection or clip (Ctrl+C).")
            return
        marks = self._get_valid_marks()
        if not marks:
            return
        self._push_video_undo()
        m1, m2 = marks
        cloned = [s.clone() for s in self.clipboard_segments]
        left, rest = self._split_segments_at_ms(self.timeline.segments, m1)
        _, right = self._split_segments_at_ms(rest, m2 - m1)
        self.timeline.segments = left + cloned + right
        self.timeline.update_width()
        self.timeline.update()
        self._render_frame_at_ms(m1)

    def _toggle_video_spatial_crop(self, checked: bool):
        if checked and self.chk_output_view.isChecked():
            self.chk_output_view.setChecked(False)
        if checked:
            self.btn_move_vid.setChecked(False)
            self.video_Canvas.mode = "crop"
            self.status.showMessage("Crop: drag a rectangle on the monitor. The crop fills the frame.")
        else:
            self.video_Canvas.mode = "none"

    def _apply_video_crop_to_active_segment(self, rect: QRect):
        seg = self._get_active_video_segment()
        if not seg:
            return
        s = self.video_preview_scale or 1.0
        W, H = seg.source.width, seg.source.height
        x1, y1 = rect.x() / s, rect.y() / s
        x2, y2 = (rect.x() + rect.width()) / s, (rect.y() + rect.height()) / s
        if seg.crop_rect:
            # Map from the current (already cropped & fitted) picture back to the original frame
            cx, cy, cw, ch = seg.crop_rect
            f = min(W / cw, H / ch)
            ox, oy = (W - cw * f) / 2, (H - ch * f) / 2
            x1, x2 = cx + (x1 - ox) / f, cx + (x2 - ox) / f
            y1, y2 = cy + (y1 - oy) / f, cy + (y2 - oy) / f
        x1, x2 = max(0, min(W, x1)), max(0, min(W, x2))
        y1, y2 = max(0, min(H, y1)), max(0, min(H, y2))
        if x2 - x1 < 8 or y2 - y1 < 8:
            return
        self._push_video_undo()
        seg.crop_rect = (int(x1), int(y1), int(x2 - x1), int(y2 - y1))
        self.btn_crop_vid.setChecked(False)
        self.video_Canvas.mode = "none"
        self.timeline.update()
        self._render_frame_at_ms(self.timeline.playhead_ms)

    def _remove_video_crop(self):
        seg = self._get_active_video_segment()
        if seg and seg.crop_rect:
            self._push_video_undo()
            seg.crop_rect = None
            self.timeline.update()
            self._render_frame_at_ms(self.timeline.playhead_ms)

    def _get_segment_at_ms(self, global_ms: int):
        acc = 0
        for seg in self.timeline.segments:
            if acc <= global_ms <= acc + seg.duration_ms:
                elapsed_timeline_ms = global_ms - acc
                local_source_ms = seg.in_ms + int(round(elapsed_timeline_ms * seg.speed))
                local_source_ms = min(seg.out_ms, max(seg.in_ms, local_source_ms))
                return seg, local_source_ms
            acc += seg.duration_ms
        return None, 0

    def _on_timeline_scrub(self, ms: int):
        seg = self._get_active_video_segment()
        if seg:
            self._sync_video_transform_ui(seg)
        if self.is_playing:
            self._play_start_ms = ms
            self._start_preview_audio()
            self._play_clock.restart()       # start timing only once the sound is ready
        self._render_frame_at_ms(ms)

    def _seek_relative(self, delta_ms: int):
        self._seek_absolute(self.timeline.playhead_ms + delta_ms)

    def _seek_absolute(self, ms: int):
        target = max(0, min(self.timeline.total_duration_ms(), int(ms)))
        self.timeline.playhead_ms = target
        self.timeline.update()
        self._keep_playhead_visible()
        self._on_timeline_scrub(target)

    def _keep_playhead_visible(self):
        x = self.timeline.ms_to_x(self.timeline.playhead_ms)
        self.timeline_scroll.ensureVisible(x, 10, 80, 0)

    def _zoom_to_fit(self):
        total_s = max(1.0, self.timeline.total_duration_ms() / 1000.0)
        avail = max(200, self.timeline_scroll.viewport().width() - 140)
        self.timeline.set_zoom(avail / total_s)

    # --- PLAYBACK (real-time clock + optional sound) ---
    def _toggle_playback(self):
        if not self.timeline.segments:
            return
        self.is_playing = not self.is_playing
        if self.is_playing:
            tl = self.timeline
            if tl.lock_a and tl.mark_a_ms is not None:
                tl.playhead_ms = tl.mark_a_ms           # a locked A is always the start point
            elif tl.playhead_ms >= tl.total_duration_ms() - 20 or (
                    tl.lock_b and tl.mark_b_ms is not None and abs(tl.playhead_ms - tl.mark_b_ms) <= 40):
                tl.playhead_ms = 0                      # at the end (or stopped at a locked B): start over
            self._play_start_ms = tl.playhead_ms
            self._start_preview_audio()      # may take a moment the first time (builds the mix)
            self._play_clock.start()
            self.play_timer.start()
            self.btn_play.setIcon(make_icon("pause", "amber"))
        else:
            self.play_timer.stop()
            self._stop_preview_audio()
            self.btn_play.setIcon(make_icon("play", "green"))

    def _on_play_tick(self):
        nxt = self._play_start_ms + self._play_clock.elapsed()
        if self.chk_loop.isChecked():
            marks = self._get_valid_marks(quiet=True)
            if marks and nxt >= marks[1]:
                self._play_start_ms = marks[0]
                nxt = marks[0]
                self._start_preview_audio(nxt)
                self._play_clock.restart()
        total = self.timeline.total_duration_ms()
        tl = self.timeline
        stop_at = total
        if tl.lock_b and tl.mark_b_ms is not None and tl.mark_b_ms > self._play_start_ms:
            stop_at = min(total, tl.mark_b_ms)          # a locked B is the end point
        if nxt >= stop_at:
            nxt = stop_at
            self.timeline.playhead_ms = nxt
            self._toggle_playback()
        self.timeline.playhead_ms = nxt
        self.timeline.update()
        self._keep_playhead_visible()
        self._render_frame_at_ms(nxt)

    def _preview_audio_data(self):
        key = tuple(s.audio_key() for s in self.timeline.segments) + tuple((s.source_id, s.has_audio) for s in self.video_sources)
        if self._audio_cache[0] == key:
            return self._audio_cache[1], self._audio_cache[2]
        built = self._build_timeline_audio(keep_pitch=False)
        if built is None:
            self._audio_cache = (key, None, None)
            return None, None
        self._audio_cache = (key, built[0], built[1])
        return built

    def _start_preview_audio(self, from_ms: int = None):
        self._stop_preview_audio()
        if not (HAS_QT_AUDIO and self.chk_preview_audio.isChecked() and self.is_playing):
            return
        try:
            sr, audio = self._preview_audio_data()
            if audio is None:
                return
            start = int((self.timeline.playhead_ms if from_ms is None else from_ms) * sr / 1000)
            if start >= len(audio):
                return
            dev = QMediaDevices.defaultAudioOutput()
            if dev.isNull():
                return
            fmt = QAudioFormat()
            fmt.setSampleRate(sr)
            fmt.setChannelCount(2)
            fmt.setSampleFormat(QAudioFormat.SampleFormat.Int16)
            pcm = (np.clip(audio[start:], -1.0, 1.0) * 32767.0).astype(np.int16).tobytes()
            self._audio_buffer = QBuffer(self)
            self._audio_buffer.setData(QByteArray(pcm))
            self._audio_buffer.open(QIODevice.OpenModeFlag.ReadOnly)
            self._audio_sink = QAudioSink(dev, fmt, self)
            self._audio_sink.start(self._audio_buffer)
        except Exception as e:
            self.status.showMessage(f"Preview audio unavailable: {e}")

    def _stop_preview_audio(self):
        if self._audio_sink is not None:
            try:
                self._audio_sink.stop()
            except Exception:
                pass
            self._audio_sink = None
        if self._audio_buffer is not None:
            self._audio_buffer.close()
            self._audio_buffer = None

    # --- FRAME PIPELINE (shared by preview, snapshots and export) ---
    def _process_video_frame(self, frame: np.ndarray, seg: TimelineSegment, canvas_wh: tuple[int, int],
                             preview_mode: bool = True, scale: float = 1.0, local_ms: float = None) -> np.ndarray:
        return process_clip_frame(frame, seg, canvas_wh, preview_mode, scale, local_ms)

    def _render_frame_at_ms(self, global_ms: int):
        total = self.timeline.total_duration_ms()
        self._update_export_warning()
        self.lbl_time_counter.setText(f"{format_ms(global_ms)} / {format_ms(total)}")

        seg, source_ms = self._get_segment_at_ms(global_ms)
        if not seg:
            self.lbl_active_clip_badge.setText("Active Clip: None")
            self.lbl_active_clip_badge.setStyleSheet("")
            return

        speed_badge = f" [{seg.speed:.2f}x]" if abs(seg.speed - 1.0) > 0.01 else ""
        audio_badge = seg.audio_mix.badge_str()
        self.lbl_active_clip_badge.setText(
            f"Editing V{seg.source.source_id}  {seg.source.filename}{speed_badge}{audio_badge}{seg.transform.summary_tag()}{seg.color.summary_tag()}"
        )
        c = QColor(seg.source.color)
        self.lbl_active_clip_badge.setStyleSheet(
            f"padding: 5px 10px; border-radius: 7px; color: white; font-weight: bold; border: 1px solid {c.lighter(160).name()};"
            f"background: qlineargradient(x1:0, y1:0, x2:0, y2:1, stop:0 {c.lighter(125).name()}, stop:1 {c.darker(150).name()});"
        )

        if self.chk_output_view.isChecked():
            # Exactly what the export will look like (framing, transitions, layers, subtitles)
            ctx = self._preview_context()
            self.video_preview_scale = 1.0
            self.video_Canvas.load_image(ctx.frame_at(global_ms))
            return

        reader = self.open_captures.get(seg.source.source_id)
        if not reader:
            return
        frame = reader.frame_at_ms(source_ms)
        if frame is not None:
            cw, ch = (seg.source.width or frame.shape[1], seg.source.height or frame.shape[0])
            s = min(1.0, VIDEO_PREVIEW_MAX / max(cw, ch))
            self.video_preview_scale = s
            local_ms = global_ms - self._segment_start_ms(seg)
            processed = self._process_video_frame(frame, seg, (cw, ch), preview_mode=True, scale=s, local_ms=local_ms)
            self.video_Canvas.load_image(processed)

    def _current_frame_full(self):
        seg, source_ms = self._get_segment_at_ms(self.timeline.playhead_ms)
        if not seg:
            return None, None
        reader = self.open_captures.get(seg.source.source_id)
        frame = reader.frame_at_ms(source_ms) if reader else None
        if frame is None:
            return None, None
        local_ms = self.timeline.playhead_ms - self._segment_start_ms(seg)
        out = self._process_video_frame(frame, seg, (seg.source.width, seg.source.height), preview_mode=False, local_ms=local_ms)
        return out, seg

    def _snapshot_frame(self):
        img, seg = self._current_frame_full()
        if img is None:
            self.status.showMessage("No frame to save — add a video first.")
            return
        stem = os.path.splitext(seg.source.filename)[0]
        path, _ = QFileDialog.getSaveFileName(self, "Save Frame", f"{stem}_{self.timeline.playhead_ms}ms.png", "PNG (*.png);;JPEG (*.jpg)")
        if path:
            ext = os.path.splitext(path)[1].lower() or ".png"
            ok, buf = cv2.imencode(ext if ext in (".png", ".jpg", ".jpeg") else ".png", img)
            if ok:
                buf.tofile(path)
                self.status.showMessage(f"Saved frame to {path}")

    def _frame_to_photo_studio(self):
        img, seg = self._current_frame_full()
        if img is None:
            self.status.showMessage("No frame to send — add a video first.")
            return
        self.photo_undo_stack.clear()
        self.photo_redo_stack.clear()
        self.photo_base_bgra = to_bgra(img)
        self.photo_layers = []
        self._refresh_layer_list()
        self.photo_path = f"{os.path.splitext(seg.source.filename)[0]}_frame.png"
        self.photo_transform = TransformParams()
        self.photo_color = ColorParams()
        self.photo_text = TextOverlay()
        self._rebuild_photo_preview()
        self._sync_photo_ui_sliders()
        self.tabs.setCurrentIndex(1)
        self._refresh_photo_canvas()
        self.status.showMessage("Frame sent to the Photo Studio.")

    # ==========================================================================
    # AUDIO MIX & EXPORT
    # ==========================================================================
    def _build_timeline_audio(self, keep_pitch: bool = True):
        return build_timeline_audio(self.timeline.segments, self.music, keep_pitch=keep_pitch)

    def _build_mixed_timeline_wav(self, out_wav_path: str, keep_pitch: bool = True) -> bool:
        built = self._build_timeline_audio(keep_pitch=keep_pitch)
        if built is None:
            return False
        write_wav_float(out_wav_path, built[1], built[0])
        return True


    # ==========================================================================
    # v3: FINAL-OUTPUT PREVIEW
    # ==========================================================================
    def _export_target(self):
        """(width, height, fps, fit_mode) from the Export settings."""
        first = self.timeline.segments[0].source if self.timeline.segments else None
        presets = [None, (1920, 1080), (1280, 720), (1080, 1920), (1080, 1080), (1080, 1350), (3840, 2160)]
        size = presets[self.cmb_exp_format.currentIndex()] or ((first.width, first.height) if first else (1280, 720))
        out_w, out_h = max(2, size[0] // 2 * 2), max(2, size[1] // 2 * 2)
        fps_txt = self.cmb_exp_fps.currentText()
        fps = (round(first.fps, 3) if first else 30.0) if fps_txt.startswith("Source") else float(fps_txt)
        fit = ("blur", "fit", "fill", "smart")[self.cmb_exp_fit.currentIndex()]
        return out_w, out_h, max(10.0, min(120.0, fps)), fit

    def _sub_style_overlay(self) -> TextOverlay:
        st = TextOverlay()
        st.size_pct = self.spn_sub_size.value()
        st.position = TextOverlay.POSITIONS[self.cmb_sub_pos.currentIndex()]
        st.color = getattr(self.btn_sub_color, "_color", "#FFFFFF")
        st.outline = True
        st.backdrop = self.chk_sub_backdrop.isChecked()
        return st

    def _preview_context(self):
        out_w, out_h, _fps, fit = self._export_target()
        s = min(1.0, 960.0 / max(out_w, out_h))
        pw, ph = max(2, int(out_w * s) // 2 * 2), max(2, int(out_h * s) // 2 * 2)
        ctx = getattr(self, "_pv_ctx", None)
        if ctx is None or (ctx.out_w, ctx.out_h, ctx.fit_mode) != (pw, ph, fit):
            if ctx is not None:
                ctx.release()
            ctx = RenderContext([], [], [], None, False, pw, ph, fit, preview=True, use_proxies=True)
            self._pv_ctx = ctx
        ctx.segments = self.timeline.segments
        ctx.overlays = self.overlays
        ctx.subtitles = self.subtitles
        ctx.sub_style = self._sub_style_overlay()
        ctx.burn_subs = True
        ctx.starts, acc = [], 0
        for sgm in ctx.segments:
            ctx.starts.append(acc)
            acc += sgm.duration_ms
        ctx.total = acc
        ctx._clip_cache.clear()
        return ctx

    def _on_output_view_toggled(self, on: bool):
        if on:
            self.btn_crop_vid.setChecked(False)
            self.btn_move_vid.setChecked(False)
            self.video_Canvas.mode = "none"
        self._render_frame_at_ms(self.timeline.playhead_ms)

    # ==========================================================================
    # v3: TRANSITIONS & MOTION
    # ==========================================================================
    def _apply_transition(self, all_cuts: bool):
        if not self.timeline.segments:
            return
        self._push_video_undo()
        tr = {"type": self.cmb_transition.currentData(), "ms": int(self.spn_transition.value() * 1000)}
        if all_cuts:
            for s in self.timeline.segments[1:]:
                s.transition = dict(tr)
            self.status.showMessage(f"{self.cmb_transition.currentText()} applied to all {len(self.timeline.segments) - 1} cuts.")
        else:
            seg = self._get_active_video_segment()
            if seg is None or seg is self.timeline.segments[0]:
                self.status.showMessage("Put the playhead on a clip that follows another clip — transitions go between clips.")
                return
            seg.transition = dict(tr)
            self.status.showMessage(f"{self.cmb_transition.currentText()} into this clip.")
        self.timeline.update()
        self.chk_output_view.setChecked(True)
        self._render_frame_at_ms(self.timeline.playhead_ms)

    def _apply_motion(self):
        seg = self._get_active_video_segment()
        if not seg:
            return
        self._push_video_undo()
        seg.motion = {"type": self.cmb_motion.currentData(), "amount": self.spn_motion.value()}
        self.timeline.update()
        self._render_frame_at_ms(self.timeline.playhead_ms)
        self.status.showMessage(f"Motion: {self.cmb_motion.currentText()} on this clip.")

    # ==========================================================================
    # v3: LAYERS (LOGO / PIP) & MUSIC
    # ==========================================================================
    def _refresh_overlay_list(self):
        self.lst_overlays.blockSignals(True)
        cur = self.lst_overlays.currentRow()
        self.lst_overlays.clear()
        for ov in self.overlays:
            rng = "whole video" if ov.end_ms is None and ov.start_ms == 0 else f"{format_ms(ov.start_ms)} → {format_ms(ov.end_ms or self.timeline.total_duration_ms())}"
            self.lst_overlays.addItem(f"{'PiP' if ov.kind == 'video' else 'Logo'}  •  {ov.name}  •  {rng}")
        self.lst_overlays.setCurrentRow(min(cur, len(self.overlays) - 1) if self.overlays else -1)
        self.lst_overlays.blockSignals(False)
        self.timeline.update()

    def _add_overlay(self, kind: str):
        flt = "Images (*.png *.jpg *.jpeg *.webp *.bmp)" if kind == "image" else "Videos (*.mp4 *.mov *.mkv *.webm *.avi *.m4v)"
        path, _ = QFileDialog.getOpenFileName(self, "Add Logo / Image" if kind == "image" else "Add Picture-in-Picture Video", "", flt)
        if not path:
            return
        ov = OverlayItem(path)
        if ov.kind == "image" and ov.image_bgra() is None:
            QMessageBox.warning(self, "Layer", "Could not read that image.")
            return
        if ov.kind == "video":
            ov.cx, ov.cy, ov.width_pct = 0.78, 0.78, 34.0
        self._push_video_undo()
        self.overlays.append(ov)
        self._refresh_overlay_list()
        self.lst_overlays.setCurrentRow(len(self.overlays) - 1)
        self.chk_output_view.setChecked(True)
        self._render_frame_at_ms(self.timeline.playhead_ms)

    def _current_overlay(self):
        i = self.lst_overlays.currentRow()
        return self.overlays[i] if 0 <= i < len(self.overlays) else None

    def _on_overlay_selected(self, _row):
        ov = self._current_overlay()
        if not ov:
            return
        for w_ in (self.cmb_ov_pos, self.sl_ov_size, self.sl_ov_opacity):
            w_.blockSignals(True)
        pos = min(OverlayItem.POSITIONS.items(), key=lambda kv: abs(kv[1][0] - ov.cx) + abs(kv[1][1] - ov.cy))[0]
        self.cmb_ov_pos.setCurrentText(pos)
        self._set_slider_silently(self.sl_ov_size, int(ov.width_pct))
        self._set_slider_silently(self.sl_ov_opacity, int(ov.opacity * 100))
        for w_ in (self.cmb_ov_pos, self.sl_ov_size, self.sl_ov_opacity):
            w_.blockSignals(False)

    def _on_overlay_changed(self, *_):
        ov = self._current_overlay()
        if not ov:
            return
        ov.cx, ov.cy = OverlayItem.POSITIONS[self.cmb_ov_pos.currentText()]
        ov.width_pct = float(self.sl_ov_size.value())
        ov.opacity = self.sl_ov_opacity.value() / 100.0
        self._mark_dirty()
        if self.chk_output_view.isChecked():
            self._render_frame_at_ms(self.timeline.playhead_ms)

    def _set_overlay_range(self, use_marks: bool):
        ov = self._current_overlay()
        if not ov:
            return
        if use_marks:
            marks = self._get_valid_marks()
            if not marks:
                return
            self._push_video_undo()
            ov.start_ms, ov.end_ms = marks
        else:
            self._push_video_undo()
            ov.start_ms, ov.end_ms = 0, None
        self._refresh_overlay_list()

    def _remove_overlay(self):
        i = self.lst_overlays.currentRow()
        if 0 <= i < len(self.overlays):
            self._push_video_undo()
            self.overlays.pop(i)
            self._refresh_overlay_list()
            self._render_frame_at_ms(self.timeline.playhead_ms)

    def _set_music(self):
        path, _ = QFileDialog.getOpenFileName(self, "Choose Background Music", "",
                                              "Audio (*.mp3 *.wav *.m4a *.aac *.ogg *.flac *.opus);;Videos (*.mp4 *.mkv *.webm *.mov)")
        if not path:
            return
        mt = MusicTrack(path)
        if mt.audio() is None:
            QMessageBox.warning(self, "Music", "Could not read audio from that file (FFmpeg is needed).")
            return
        self._push_video_undo()
        self.music = mt
        self._on_music_changed()
        self._sync_music_ui()

    def _music_to_playhead(self):
        if self.music:
            self.music.start_ms = self.timeline.playhead_ms
            self._sync_music_ui()
            self._mark_dirty()

    def _remove_music(self):
        if self.music:
            self._push_video_undo()
            self.music = None
            self._sync_music_ui()

    def _on_music_changed(self):
        if not self.music:
            return
        self.music.volume = self.sl_music_vol.value() / 100.0
        self.music.duck = self.sl_music_duck.value() / 100.0
        self.music.loop = self.chk_music_loop.isChecked()
        self._mark_dirty()
        self.timeline.update()

    def _sync_music_ui(self):
        self.timeline.music = self.music
        if self.music:
            self.lbl_music.setText(f"{self.music.name}  •  starts {format_ms(self.music.start_ms)}")
            self._set_slider_silently(self.sl_music_vol, int(self.music.volume * 100))
            self._set_slider_silently(self.sl_music_duck, int(self.music.duck * 100))
            self.chk_music_loop.blockSignals(True)
            self.chk_music_loop.setChecked(self.music.loop)
            self.chk_music_loop.blockSignals(False)
        else:
            self.lbl_music.setText("No music track.")
        self.timeline.update()

    # ==========================================================================
    # v3: SUBTITLES (WHISPER) — GENERATE, EDIT, IMPORT/EXPORT, TRANSLATE
    # ==========================================================================
    def _on_subtitles_changed(self):
        self.timeline.subtitles = self.subtitles
        n = len(self.subtitles)
        self.lbl_sub_status.setText(f"{n} subtitle line{'s' if n != 1 else ''}." if n else "No subtitles yet.")
        self.timeline.update()
        self._mark_dirty()
        self._render_frame_at_ms(self.timeline.playhead_ms)

    def _on_sub_style_changed(self):
        self._mark_dirty()
        if self.chk_output_view.isChecked():
            self._render_frame_at_ms(self.timeline.playhead_ms)

    def _generate_subtitles(self):
        if not self.timeline.segments:
            QMessageBox.information(self, "Subtitles", "Add a video first.")
            return
        if getattr(self, "_sub_job", False):
            return
        model = self.cmb_sub_model.currentText().split()[0]
        lang = self.cmb_sub_lang.currentData()
        task = "translate" if self.cmb_sub_task.currentIndex() == 1 else "transcribe"
        segs = [s.clone() for s in self.timeline.segments]
        self._sub_job = True
        self.btn_gen_subs.setEnabled(False)
        self.lbl_sub_status.setText(f"Preparing audio… (first use downloads the '{model}' model once)")

        def work():
            tmp = os.path.join(tempfile.gettempdir(), f"ank_subs_{os.getpid()}.wav")
            try:
                built = build_timeline_audio(segs, None, keep_pitch=True, sr=16000)
                if built is None:
                    raise RuntimeError("The timeline has no sound to transcribe.")
                write_wav_float(tmp, built[1], built[0])
                self._bridge.call.emit(lambda: self.lbl_sub_status.setText("Listening… (speech-to-text)"))

                def prog(frac, n):
                    self._bridge.call.emit(lambda f=frac, k=n: self.lbl_sub_status.setText(f"Listening… {int(f * 100)}%  •  {k} lines"))
                cues = transcribe_audio(tmp, model, lang, task, progress=prog)

                def done():
                    self._push_video_undo()
                    self.subtitles = cues
                    self._on_subtitles_changed()
                    self.chk_output_view.setChecked(True)
                    self.status.showMessage(f"Generated {len(cues)} subtitle lines. Edit them with 'Edit…'.")
                self._bridge.call.emit(done)
            except Exception as e:
                msg = str(e)
                self._bridge.call.emit(lambda: (self.lbl_sub_status.setText("Subtitle generation failed."),
                                                QMessageBox.warning(self, "Subtitles", msg)))
            finally:
                try:
                    os.remove(tmp)
                except OSError:
                    pass
                self._bridge.call.emit(lambda: (setattr(self, "_sub_job", False), self.btn_gen_subs.setEnabled(bool(whisper_engine_name()))))
        threading.Thread(target=work, daemon=True).start()

    def _edit_subtitles(self):
        dlg = QDialog(self)
        dlg.setWindowTitle("Edit Subtitles")
        dlg.resize(760, 520)
        v = QVBoxLayout(dlg)
        table = QTableWidget(len(self.subtitles), 3)
        table.setHorizontalHeaderLabels(["Start", "End", "Text"])
        table.horizontalHeader().setStretchLastSection(True)
        table.setAlternatingRowColors(True)
        table.setColumnWidth(0, 110)
        table.setColumnWidth(1, 110)
        for r, c in enumerate(self.subtitles):
            for col, val in enumerate((format_ms(c["start"]), format_ms(c["end"]), c["text"].replace("\n", " | "))):
                table.setItem(r, col, QTableWidgetItem(val))
        v.addWidget(table)

        def add_row():
            r = table.rowCount()
            t = self.timeline.playhead_ms
            table.insertRow(r)
            for col, val in enumerate((format_ms(t), format_ms(t + 2000), "New line")):
                table.setItem(r, col, QTableWidgetItem(val))
        def del_rows():
            for r in sorted({i.row() for i in table.selectedIndexes()}, reverse=True):
                table.removeRow(r)
        shift = QSpinBox()
        shift.setRange(-60000, 60000)
        shift.setSingleStep(100)
        shift.setSuffix(" ms")
        def do_shift():
            for r in range(table.rowCount()):
                for col in (0, 1):
                    ms = self._parse_clock(table.item(r, col).text()) + shift.value()
                    table.item(r, col).setText(format_ms(max(0, ms)))
        b_add = icon_button("Add at Playhead", "add", "green")
        b_add.clicked.connect(add_row)
        b_del = icon_button("Delete Selected", "trash", "red")
        b_del.clicked.connect(del_rows)
        b_shift = icon_button("Shift All", "speed", "indigo")
        b_shift.clicked.connect(do_shift)
        v.addLayout(self._row(b_add, b_del, None, QLabel("Shift by"), shift, b_shift))
        bb = QDialogButtonBox(QDialogButtonBox.StandardButton.Ok | QDialogButtonBox.StandardButton.Cancel)
        bb.accepted.connect(dlg.accept)
        bb.rejected.connect(dlg.reject)
        v.addWidget(bb)
        if dlg.exec() != QDialog.DialogCode.Accepted:
            return
        cues = []
        for r in range(table.rowCount()):
            try:
                a = self._parse_clock(table.item(r, 0).text())
                b = self._parse_clock(table.item(r, 1).text())
                txt = table.item(r, 2).text().replace(" | ", "\n").strip()
                if txt and b > a:
                    cues.append({"start": a, "end": b, "text": txt})
            except Exception:
                continue
        self._push_video_undo()
        self.subtitles = sorted(cues, key=lambda c: c["start"])
        self._on_subtitles_changed()

    @staticmethod
    def _parse_clock(text: str) -> int:
        parts = text.strip().replace(",", ".").split(":")
        sec = float(parts[-1])
        mins = int(parts[-2]) if len(parts) > 1 else 0
        hrs = int(parts[-3]) if len(parts) > 2 else 0
        return int(round((hrs * 3600 + mins * 60 + sec) * 1000))

    def _import_srt(self):
        path, _ = QFileDialog.getOpenFileName(self, "Import Subtitles", "", "Subtitles (*.srt *.vtt)")
        if not path:
            return
        with open(path, encoding="utf-8", errors="ignore") as f:
            cues = parse_srt(re.sub(r"^WEBVTT[^\n]*\n", "", f.read()))
        if not cues:
            QMessageBox.warning(self, "Import", "No subtitle lines found in that file.")
            return
        self._push_video_undo()
        self.subtitles = cues
        self._on_subtitles_changed()

    def _export_srt(self):
        if not self.subtitles:
            self.status.showMessage("No subtitles to save.")
            return
        path, _ = QFileDialog.getSaveFileName(self, "Save Subtitles", "subtitles.srt", "SubRip (*.srt)")
        if path:
            with open(path, "w", encoding="utf-8") as f:
                f.write(subtitles_to_srt(self.subtitles))
            self.status.showMessage(f"Saved {len(self.subtitles)} lines to {path}")

    def _clear_subtitles(self):
        if self.subtitles:
            self._push_video_undo()
            self.subtitles = []
            self._on_subtitles_changed()

    def _translate_subtitles(self):
        if not self.subtitles:
            self.status.showMessage("Generate or import subtitles first.")
            return
        langs = argos_languages()
        if not langs:
            QMessageBox.information(
                self, "Translate Subtitles",
                "Offline translation uses Argos Translate (free):\n\n    pip install argostranslate\n\n"
                "then install the language packs you need (for example English → Arabic) with:\n"
                "    argospm install translate-en_ar\n\n"
                "Tip: to get English subtitles, choose 'Translate speech to English' and generate again.")
            return
        names = [f"{n} ({c})" for c, n in langs]
        dlg = QDialog(self)
        dlg.setWindowTitle("Translate Subtitles")
        form = QFormLayout(dlg)
        src_cb, dst_cb = QComboBox(), QComboBox()
        src_cb.addItems(names)
        dst_cb.addItems(names)
        form.addRow("From", src_cb)
        form.addRow("To", dst_cb)
        bb = QDialogButtonBox(QDialogButtonBox.StandardButton.Ok | QDialogButtonBox.StandardButton.Cancel)
        bb.accepted.connect(dlg.accept)
        bb.rejected.connect(dlg.reject)
        form.addRow(bb)
        if dlg.exec() != QDialog.DialogCode.Accepted:
            return
        try:
            out = self._with_busy("Translating subtitles…", lambda: translate_cues(
                self.subtitles, langs[src_cb.currentIndex()][0], langs[dst_cb.currentIndex()][0]))
        except Exception as e:
            QMessageBox.warning(self, "Translate Subtitles", str(e))
            return
        self._push_video_undo()
        self.subtitles = out
        self._on_subtitles_changed()

    # ==========================================================================
    # v3: SMART TOOLS — SCENES, SILENCES, FACES
    # ==========================================================================
    def _detect_scenes(self, all_clips: bool):
        segs = list(self.timeline.segments) if all_clips else [self._get_active_video_segment()]
        segs = [s for s in segs if s]
        if not segs:
            return
        sens = self.sl_scene_sens.value() / 100.0
        jobs = [(s, s.source.filepath, s.source.fps, s.in_ms, s.out_ms) for s in segs]
        self.lbl_smart_status.setText("Looking for scene cuts…")

        def work():
            found = []
            for k, (seg, path, fps, a, b) in enumerate(jobs):
                cuts = detect_scene_cuts(path, fps, a, b, sens, progress=lambda f, k=k: self._bridge.call.emit(
                    lambda: self.lbl_smart_status.setText(f"Looking for scene cuts… {int((k + f) / len(jobs) * 100)}%")))
                found.append((seg, cuts))

            def apply():
                positions = []
                for seg, cuts in found:
                    if seg not in self.timeline.segments:
                        continue
                    start = self._segment_start_ms(seg)
                    positions += [start + int((c - seg.in_ms) / seg.speed) for c in cuts if seg.in_ms + 300 < c < seg.out_ms - 300]
                if not positions:
                    self.lbl_smart_status.setText("No scene cuts found. Try a higher sensitivity.")
                    return
                self._push_video_undo()
                for pos in sorted(positions, reverse=True):
                    left, right = self._split_segments_at_ms(self.timeline.segments, pos)
                    self.timeline.segments = left + right
                self.timeline.update_width()
                self.timeline.update()
                self.lbl_smart_status.setText(f"Split at {len(positions)} scene cut(s).")
                self.status.showMessage(f"Scene detection: {len(positions)} cut(s) — each scene is now its own clip.")
            self._bridge.call.emit(apply)
        threading.Thread(target=work, daemon=True).start()

    def _remove_silences(self):
        if not self.timeline.segments:
            return
        built = self._with_busy("Measuring sound levels…", lambda: build_timeline_audio(self.timeline.segments, None, keep_pitch=False))
        if built is None:
            QMessageBox.information(self, "Remove Silences", "The timeline has no sound.")
            return
        ranges = detect_silences(built[1], built[0], self.spn_sil_db.value(), int(self.spn_sil_min.value() * 1000))
        if not ranges:
            self.lbl_smart_status.setText("No silent gaps found with these settings.")
            return
        self._push_video_undo()
        removed = 0
        for a, b in sorted(ranges, reverse=True):
            left, rest = self._split_segments_at_ms(self.timeline.segments, a)
            _, right = self._split_segments_at_ms(rest, b - a)
            self.timeline.segments = left + right
            removed += b - a
        self.timeline.playhead_ms = min(self.timeline.playhead_ms, self.timeline.total_duration_ms())
        self.timeline.update_width()
        self.timeline.update()
        self._render_frame_at_ms(self.timeline.playhead_ms)
        msg = f"Removed {len(ranges)} silent gap(s), {removed / 1000:.1f} s in total. Ctrl+Z to undo."
        self.lbl_smart_status.setText(msg)
        self.status.showMessage(msg)

    def _analyze_faces(self, then=None):
        sources = {s.source.source_id: s.source for s in self.timeline.segments}
        todo = [src for src in sources.values() if src.face_track is None]
        if not todo:
            self.lbl_smart_status.setText("Faces already analysed — choose 'Smart reframe' framing when exporting.")
            if then:
                then()
            return
        self.lbl_smart_status.setText("Analysing faces…")

        def work():
            for k, src in enumerate(todo):
                self._bridge.call.emit(lambda k=k, n=src.filename: self.lbl_smart_status.setText(f"Analysing faces in {n} ({k + 1}/{len(todo)})…"))
                src.face_track = compute_face_track(src.filepath, src.fps, src.duration_ms)

            def done():
                self.lbl_smart_status.setText("Faces analysed. Smart reframe will follow the speaker.")
                self.cmb_exp_fit.setCurrentIndex(3)
                if then:
                    then()
                self._render_frame_at_ms(self.timeline.playhead_ms)
            self._bridge.call.emit(done)
        threading.Thread(target=work, daemon=True).start()

    # ==========================================================================
    # v3: PROXIES & TIMELINE THUMBNAILS (background)
    # ==========================================================================
    def _make_proxy_async(self, src: VideoSource):
        if not FFMPEG_EXE or max(src.width, src.height) <= 1920:
            return
        out = os.path.join(cache_dir(), f"proxy_{abs(hash((src.filepath, os.path.getsize(src.filepath))))}.mp4")

        def work():
            if not os.path.exists(out):
                tmp = out + ".part.mp4"
                res = run_quiet([FFMPEG_EXE, "-y", "-i", src.filepath, "-vf", "scale=-2:540", "-c:v", "libx264",
                                 "-preset", "ultrafast", "-crf", "28", "-g", "12", "-an", tmp])
                if res.returncode != 0:
                    return
                os.replace(tmp, out)

            def done():
                src.proxy_path = out
                old = self.open_captures.get(src.source_id)
                self.open_captures[src.source_id] = FrameReader(out, src.fps)
                if old:
                    old.release()
                self.status.showMessage(f"Fast preview ready for {src.filename} (4K edit proxy). Exports still use the original.")
            self._bridge.call.emit(done)
        threading.Thread(target=work, daemon=True).start()

    def _make_thumbs_async(self, src: VideoSource):
        def work():
            reader = FrameReader(src.filepath, src.fps)
            step = max(500, src.duration_ms // 240)
            thumbs = []
            t = 0
            while t < src.duration_ms:
                fr = reader.frame_at_ms(t)
                if fr is None:
                    break
                h, w = fr.shape[:2]
                th = 46
                tw = max(1, int(w * th / h))
                thumbs.append((t, np.ascontiguousarray(cv2.cvtColor(cv2.resize(fr, (tw, th), interpolation=cv2.INTER_AREA), cv2.COLOR_BGR2RGB))))
                t += step
            reader.release()
            src.thumbs = thumbs
            self._bridge.call.emit(self.timeline.update)
        threading.Thread(target=work, daemon=True).start()

    # ==========================================================================
    # v3: EXPORT QUEUE (BACKGROUND, GPU ENCODING, PLATFORM PRESETS)
    # ==========================================================================
    def _on_platform_preset(self, idx: int):
        title, size, fps, fit, limit = OUTPUT_PRESETS[idx]
        if size:
            sizes = [None, (1920, 1080), (1280, 720), (1080, 1920), (1080, 1080), (1080, 1350), (3840, 2160)]
            if size in sizes:
                self.cmb_exp_format.setCurrentIndex(sizes.index(size))
            self.cmb_exp_fps.setCurrentText(str(fps) if fps else "Source FPS")
            self.cmb_exp_fit.setCurrentIndex({"blur": 0, "fit": 1, "fill": 2, "smart": 3}[fit])
        self._update_export_warning()

    def _update_export_warning(self):
        idx = self.cmb_exp_platform.currentIndex()
        limit = OUTPUT_PRESETS[idx][4] if 0 <= idx < len(OUTPUT_PRESETS) else None
        total = self.timeline.total_duration_ms() / 1000.0
        if limit and total > limit:
            self.lbl_exp_warning.setText(f"Heads up: your video is {total / 60:.1f} min. {OUTPUT_PRESETS[idx][0].split('(')[0].strip()} "
                                         f"usually allows up to {limit // 60 if limit >= 60 else limit} {'min' if limit >= 60 else 's'}.")
        else:
            self.lbl_exp_warning.setText("")

    def _detect_encoders_async(self):
        def work():
            encs = available_encoders()

            def done():
                gpu = [e for e in encs if e != "libx264"]
                names = {"h264_nvenc": "NVIDIA", "h264_qsv": "Intel QuickSync", "h264_amf": "AMD"}
                self.lbl_encoders.setText(("GPU encoding available: " + ", ".join(names[e] for e in gpu) + " — Auto will use it.")
                                          if gpu else ("No GPU encoder found — using CPU (x264)." if encs else "FFmpeg not found — install it for H.264 export."))
                model = self.cmb_exp_encoder.model()
                for i in range(self.cmb_exp_encoder.count()):
                    key = self.cmb_exp_encoder.itemData(i)
                    item = model.item(i)
                    item.setEnabled(key == "auto" or key in encs)
            self._bridge.call.emit(done)
        threading.Thread(target=work, daemon=True).start()

    def _export_timeline_video(self):
        if not self.timeline.segments:
            QMessageBox.warning(self, "Empty Timeline", "Add or drag-and-drop at least one video first.")
            return
        out_path, _ = QFileDialog.getSaveFileName(self, "Export Edited Video", "ank_output.mp4", "MP4 Video (*.mp4)")
        if not out_path:
            return
        if not out_path.lower().endswith(".mp4"):
            out_path += ".mp4"
        out_w, out_h, fps, fit = self._export_target()
        job = {
            "id": len(self.export_jobs) + 1, "out": out_path, "w": out_w, "h": out_h, "fps": fps, "fit": fit,
            "crf": (16, 19, 23, 28)[self.cmb_exp_quality.currentIndex()],
            "encoder": self.cmb_exp_encoder.currentData(), "keep_pitch": self.chk_exp_pitch.isChecked(),
            "segments": [s.clone() for s in self.timeline.segments], "overlays": [o.clone() for o in self.overlays],
            "subtitles": [dict(c) for c in self.subtitles], "sub_style": self._sub_style_overlay(),
            "burn": self.chk_sub_burn.isChecked(), "music": self.music.clone() if self.music else None,
            "status": "Queued", "progress": 0.0, "cancel": False, "error": "", "encoder_used": "",
        }
        self.export_jobs.append(job)
        self.video_inspector.setCurrentIndex(self.video_inspector.count() - 1)
        self._refresh_export_list()
        self.status.showMessage(f"Export #{job['id']} queued — it renders in the background, keep editing.")
        if not self._export_worker_busy:
            self._export_worker_busy = True
            threading.Thread(target=self._export_worker, daemon=True).start()

    def _refresh_export_list(self):
        sel = self.lst_exports.currentRow()
        self.lst_exports.clear()
        for j in self.export_jobs:
            pct = f" {int(j['progress'] * 100)}%" if j["status"].startswith("Rendering") else ""
            enc = f"  [{j['encoder_used']}]" if j["encoder_used"] else ""
            self.lst_exports.addItem(f"#{j['id']}  {os.path.basename(j['out'])}  —  {j['status']}{pct}{enc}")
        if 0 <= sel < self.lst_exports.count():
            self.lst_exports.setCurrentRow(sel)

    def _cancel_selected_export(self):
        i = self.lst_exports.currentRow()
        if not 0 <= i < len(self.export_jobs):
            return
        job = self.export_jobs[i]
        if job["status"] in ("Done", "Failed", "Cancelled"):
            return
        job["cancel"] = True
        if job["status"] == "Queued":
            job["status"] = "Cancelled"
        self._refresh_export_list()

    def _open_export_folder(self):
        done = [j for j in self.export_jobs if j["status"] == "Done"]
        folder = os.path.dirname(done[-1]["out"]) if done else os.path.expanduser("~")
        if os.name == "nt":
            os.startfile(folder)
        else:
            subprocess.Popen(["xdg-open" if sys.platform != "darwin" else "open", folder])

    def _export_worker(self):
        try:
            while True:
                job = next((j for j in self.export_jobs if j["status"] == "Queued"), None)
                if job is None:
                    break
                try:
                    self._run_export_job(job)
                except Exception as e:
                    job["status"] = "Failed"
                    job["error"] = str(e)
                    err = str(e)
                    self._bridge.call.emit(lambda j=job, m=err: QMessageBox.critical(self, f"Export #{j['id']} failed", m))
                self._bridge.call.emit(self._refresh_export_list)
        finally:
            self._export_worker_busy = False
            # A job queued at the very last moment still gets rendered
            if any(j["status"] == "Queued" for j in self.export_jobs):
                self._export_worker_busy = True
                threading.Thread(target=self._export_worker, daemon=True).start()

    def _run_export_job(self, job):
        def ui():
            self._bridge.call.emit(self._refresh_export_list)
        segs = job["segments"]
        if job["fit"] == "smart":
            job["status"] = "Analysing faces"
            ui()
            for src in {s.source.source_id: s.source for s in segs}.values():
                if src.face_track is None:
                    src.face_track = compute_face_track(src.filepath, src.fps, src.duration_ms, cancel=lambda: job["cancel"])
        job["status"] = "Mixing audio"
        ui()
        tmp_dir = tempfile.mkdtemp(prefix="ank_export_")
        wav = os.path.join(tmp_dir, "mix.wav")
        built = build_timeline_audio(segs, job["music"], keep_pitch=job["keep_pitch"])
        if built is not None:
            write_wav_float(wav, built[1], built[0])
        ctx = RenderContext(segs, job["overlays"], job["subtitles"], job["sub_style"], job["burn"],
                            job["w"], job["h"], job["fit"], preview=False)
        fps = job["fps"]
        total_frames = max(1, int(round(ctx.total * fps / 1000.0)))
        enc = pick_encoder(job["encoder"]) if FFMPEG_EXE else ""
        attempts = [enc] + (["libx264"] if enc not in ("libx264", "mpeg4", "") else [])
        try:
            for attempt, enc in enumerate(attempts):
                job["encoder_used"] = {"h264_nvenc": "NVIDIA GPU", "h264_qsv": "Intel GPU", "h264_amf": "AMD GPU",
                                       "libx264": "CPU x264", "mpeg4": "MPEG-4", "": "OpenCV"}.get(enc, enc)
                job["status"] = "Rendering"
                job["progress"] = 0.0
                ui()
                ok = self._encode_frames(job, ctx, enc, wav if built is not None else None, total_frames, tmp_dir)
                if ok or job["cancel"]:
                    break
            if job["cancel"]:
                job["status"] = "Cancelled"
                try:
                    os.remove(job["out"])
                except OSError:
                    pass
                return
            if not ok:
                raise RuntimeError(job.get("error") or "Encoding failed.")
            job["status"] = "Done"
            job["progress"] = 1.0
            size_mb = os.path.getsize(job["out"]) / (1024 * 1024)
            self._bridge.call.emit(lambda: self.status.showMessage(
                f"Export #{job['id']} finished: {job['out']}  ({job['w']}×{job['h']}, {size_mb:.1f} MB, {job['encoder_used']})"))
        finally:
            ctx.release()
            shutil.rmtree(tmp_dir, ignore_errors=True)

    def _encode_frames(self, job, ctx, enc, wav, total_frames, tmp_dir) -> bool:
        w, h, fps = job["w"], job["h"], job["fps"]
        proc = writer = None
        log_path = os.path.join(tmp_dir, f"ffmpeg_{enc or 'cv'}.log")
        if enc:
            cmd = [FFMPEG_EXE, "-y", "-f", "rawvideo", "-pix_fmt", "bgr24", "-s", f"{w}x{h}", "-r", f"{fps}", "-i", "-"]
            if wav:
                cmd += ["-i", wav, "-map", "0:v:0", "-map", "1:a:0", "-c:a", "aac", "-b:a", "192k", "-shortest"]
            cmd += encoder_args(enc, job["crf"]) + ["-movflags", "+faststart", job["out"]]
            log_f = open(log_path, "wb")
            proc = subprocess.Popen(cmd, stdin=subprocess.PIPE, stdout=subprocess.DEVNULL, stderr=log_f, creationflags=NO_WINDOW)
        else:
            writer = cv2.VideoWriter(job["out"], cv2.VideoWriter_fourcc(*"mp4v"), fps, (w, h))
        try:
            for k in range(total_frames):
                if job["cancel"]:
                    break
                img = ctx.frame_at(k * 1000.0 / fps)
                if img.shape[1] != w or img.shape[0] != h:
                    img = cv2.resize(img, (w, h))
                if proc:
                    proc.stdin.write(np.ascontiguousarray(img).tobytes())
                else:
                    writer.write(img)
                if k % 10 == 0:
                    job["progress"] = k / total_frames
                    if k % 30 == 0:
                        self._bridge.call.emit(self._refresh_export_list)
            if proc:
                proc.stdin.close()
                if job["cancel"]:
                    proc.kill()
                proc.wait()
                if proc.returncode != 0 and not job["cancel"]:
                    log_f.close()
                    with open(log_path, "rb") as f:
                        job["error"] = f"FFmpeg ({enc}) failed:\n" + f.read()[-1200:].decode("utf-8", "ignore")
                    return False
            return True
        except (BrokenPipeError, OSError) as e:
            if proc:
                proc.kill()
                proc.wait()
            job["error"] = f"Encoder {enc} stopped: {e}"
            return False
        finally:
            if writer:
                writer.release()
            if proc:
                try:
                    log_f.close()
                except Exception:
                    pass


    # ==========================================================================
    # v3: PROJECTS (.ank) — SAVE / OPEN / RECENT, AUTOSAVE & CRASH RECOVERY
    # ==========================================================================
    @staticmethod
    def _autosave_path() -> str:
        return os.path.join(cache_dir(), "autosave.ank")

    def _update_title(self):
        name = os.path.basename(self.project_path) if self.project_path else "Untitled project"
        self.setWindowTitle(f"{'• ' if self._dirty else ''}{name} — {APP_NAME} v{APP_VERSION} — Created by {APP_AUTHOR}")

    def _mark_dirty(self):
        self._dirty = True
        self._update_title()

    def _project_dict(self) -> dict:
        def tf_dict(tf):
            return {"rot": tf.rot_90_steps, "angle": tf.free_angle, "flip_h": tf.flip_h, "flip_v": tf.flip_v,
                    "scale": tf.scale, "ox": tf.offset_x, "oy": tf.offset_y, "ai": tf.ai_upscale,
                    "cutout": tf.transparent_bg, "bg_path": getattr(tf, "bg_path", None)}
        sources = {}
        segs = []
        for s in self.timeline.segments:
            sources[s.source.source_id] = s.source
            am = s.audio_mix
            segs.append({
                "source": s.source.source_id, "in": s.in_ms, "out": s.out_ms, "crop": list(s.crop_rect) if s.crop_rect else None,
                "transform": tf_dict(s.transform), "speed": s.speed,
                "audio": {"separated": am.separated, "voices": am.voices_vol, "music": am.music_vol, "noise": am.noise_vol,
                          "gain": am.gain, "fade_in": am.fade_in_ms, "fade_out": am.fade_out_ms,
                          "trim_start": am.stem_trim_start, "trim_end": am.stem_trim_end},
                "color": {**{f: getattr(s.color, f) for f in ColorParams.FIELDS}, "filter": s.color.filter},
                "text": dict(s.text.__dict__), "fade_in": s.fade_in_ms, "fade_out": s.fade_out_ms,
                "transition": s.transition, "motion": s.motion,
            })
        return {
            "app": APP_NAME, "app_version": APP_VERSION, "project_version": 3,
            "sources": [{"id": src.source_id, "path": src.filepath, "color": src.color,
                         "stems": src.stems_engine if src.stems_separated else ""} for src in sources.values()],
            "segments": segs,
            "overlays": [o.to_dict() for o in self.overlays],
            "music": self.music.to_dict() if self.music else None,
            "subtitles": self.subtitles,
            "sub_style": {"size": self.spn_sub_size.value(), "pos": self.cmb_sub_pos.currentIndex(),
                          "color": getattr(self.btn_sub_color, "_color", "#FFFFFF"), "backdrop": self.chk_sub_backdrop.isChecked(),
                          "burn": self.chk_sub_burn.isChecked()},
            "marks": {"a": self.timeline.mark_a_ms, "b": self.timeline.mark_b_ms, "lock_a": self.timeline.lock_a, "lock_b": self.timeline.lock_b},
            "playhead": self.timeline.playhead_ms,
            "export": {"platform": self.cmb_exp_platform.currentIndex(), "format": self.cmb_exp_format.currentIndex(),
                       "fit": self.cmb_exp_fit.currentIndex(), "fps": self.cmb_exp_fps.currentIndex(),
                       "quality": self.cmb_exp_quality.currentIndex(), "encoder": self.cmb_exp_encoder.currentIndex()},
        }

    def _write_project(self, path: str, data: dict = None):
        data = data or self._project_dict()
        tmp = path + ".tmp"
        with open(tmp, "w", encoding="utf-8") as f:
            json.dump(data, f, indent=1)
        os.replace(tmp, path)   # never leaves a half-written project behind

    def _clear_legend(self):
        lay = self.sources_legend_layout
        for i in reversed(range(1, lay.count() - 1)):
            item = lay.takeAt(i)
            if item.widget():
                item.widget().deleteLater()

    def _reset_video_project(self):
        if self.is_playing:
            self._toggle_playback()
        for r in self.open_captures.values():
            r.release()
        self.open_captures.clear()
        self.video_sources = []
        self.timeline.segments = []
        self.timeline.mark_a_ms = self.timeline.mark_b_ms = None
        self.timeline.lock_a = self.timeline.lock_b = False
        for name in ("A", "B"):
            btn = self.btn_lock_a if name == "A" else self.btn_lock_b
            btn.setChecked(False)
            btn.setText(f"Lock {name}")
            btn.setIcon(make_icon("unlock", "cyan" if name == "A" else "rose"))
        self.timeline.playhead_ms = 0
        self.overlays.clear()
        self.music = None
        self.subtitles = []
        self.video_undo_stack.clear()
        self.video_redo_stack.clear()
        self.clipboard_segments = []
        self._clear_legend()
        self._refresh_overlay_list()
        self._sync_music_ui()
        self.timeline.subtitles = self.subtitles
        self._on_subtitles_changed()
        self._update_marks_label(None, None)
        self.timeline.update_width()
        self.timeline.update()
        self.video_Canvas.clear_image()
        self.lbl_time_counter.setText("00:00.000 / 00:00.000")

    def _confirm_discard(self) -> bool:
        """True when it's OK to replace the current project (saving first if the user wants)."""
        if not self._dirty or not self.timeline.segments:
            return True
        ans = QMessageBox.question(self, APP_NAME, "Save changes to the current project first?",
                                   QMessageBox.StandardButton.Save | QMessageBox.StandardButton.Discard | QMessageBox.StandardButton.Cancel)
        if ans == QMessageBox.StandardButton.Save:
            return self._save_project()
        return ans == QMessageBox.StandardButton.Discard

    def _new_project(self):
        if not self._confirm_discard():
            return
        self._reset_video_project()
        self.project_path = ""
        self._dirty = False
        self._update_title()
        self.status.showMessage("New project.")

    def _save_project(self, save_as: bool = False) -> bool:
        if not self.timeline.segments:
            self.status.showMessage("Nothing to save yet — add a video first.")
            return False
        path = self.project_path
        if save_as or not path:
            path, _ = QFileDialog.getSaveFileName(self, "Save Project", path or "my_edit.ank", "ANK Project (*.ank)")
            if not path:
                return False
            if not path.lower().endswith(".ank"):
                path += ".ank"
        try:
            self._write_project(path)
        except Exception as e:
            QMessageBox.critical(self, "Save Project", f"Could not save the project:\n{e}")
            return False
        self.project_path = path
        self._dirty = False
        self._add_recent(path)
        self._update_title()
        self.status.showMessage(f"Project saved: {path}")
        return True

    def _open_project(self, path: str = None):
        if not self._confirm_discard():
            return
        if not path:
            path, _ = QFileDialog.getOpenFileName(self, "Open Project", "", "ANK Project (*.ank)")
            if not path:
                return
        try:
            with open(path, encoding="utf-8") as f:
                data = json.load(f)
        except Exception as e:
            QMessageBox.critical(self, "Open Project", f"Could not open the project:\n{e}")
            return
        self._load_project_dict(data, os.path.dirname(path))
        self.project_path = path if not path.endswith("autosave.ank") else ""
        self._dirty = False
        if self.project_path:
            self._add_recent(path)
        self._update_title()

    def _load_project_dict(self, data: dict, base_dir: str = ""):
        self.tabs.setCurrentIndex(0)
        self._reset_video_project()
        id_map, missing = {}, []
        for sd in data.get("sources", []):
            p = sd["path"]
            if not os.path.exists(p):
                alt = os.path.join(base_dir, os.path.basename(p))
                p = alt if os.path.exists(alt) else p
            if not os.path.exists(p):
                missing.append(sd["path"])
                continue
            src = VideoSource(len(self.video_sources) + 1, p, sd.get("color") or VIDEO_PALETTE[len(self.video_sources) % len(VIDEO_PALETTE)])
            if src.duration_ms <= 0:
                missing.append(sd["path"])
                continue
            self.video_sources.append(src)
            self.open_captures[src.source_id] = FrameReader(p, src.fps)
            id_map[sd["id"]] = (src, sd.get("stems", ""))
            badge = QLabel(f" V{src.source_id}  {src.filename} ")
            c = QColor(src.color)
            badge.setStyleSheet(f"background: qlineargradient(x1:0, y1:0, x2:0, y2:1, stop:0 {c.lighter(130).name()}, "
                                f"stop:1 {c.darker(140).name()}); color: white; font-weight: bold; padding: 3px 9px; "
                                f"border-radius: 7px; border: 1px solid {c.lighter(160).name()};")
            self.sources_legend_layout.insertWidget(self.sources_legend_layout.count() - 1, badge)
            self._load_source_audio_async(src)
            self._make_thumbs_async(src)
            self._make_proxy_async(src)
        segs = []
        for sd in data.get("segments", []):
            if sd["source"] not in id_map:
                continue
            src = id_map[sd["source"]][0]
            seg = TimelineSegment(src, sd["in"], min(sd["out"], src.duration_ms), tuple(sd["crop"]) if sd.get("crop") else None,
                                  speed=sd.get("speed", 1.0), fade_in_ms=sd.get("fade_in", 0), fade_out_ms=sd.get("fade_out", 0),
                                  transition=sd.get("transition"), motion=sd.get("motion"))
            t = sd.get("transform", {})
            tf = seg.transform
            tf.rot_90_steps, tf.free_angle = t.get("rot", 0), t.get("angle", 0.0)
            tf.flip_h, tf.flip_v, tf.scale = t.get("flip_h", False), t.get("flip_v", False), t.get("scale", 1.0)
            tf.offset_x, tf.offset_y = t.get("ox", 0), t.get("oy", 0)
            tf.ai_upscale, tf.transparent_bg = t.get("ai", False), t.get("cutout", False)
            if t.get("bg_path") and os.path.exists(t["bg_path"]):
                tf.bg_replacement = cv2.imdecode(np.fromfile(t["bg_path"], dtype=np.uint8), cv2.IMREAD_COLOR)
                tf.bg_path = t["bg_path"]
            a = sd.get("audio", {})
            am = seg.audio_mix
            am.separated = a.get("separated", False)
            am.voices_vol, am.music_vol, am.noise_vol = a.get("voices", 1.0), a.get("music", 1.0), a.get("noise", 1.0)
            am.gain, am.fade_in_ms, am.fade_out_ms = a.get("gain", 1.0), a.get("fade_in", 0), a.get("fade_out", 0)
            am.stem_trim_start.update(a.get("trim_start", {}))
            am.stem_trim_end.update(a.get("trim_end", {}))
            for f in ColorParams.FIELDS:
                setattr(seg.color, f, sd.get("color", {}).get(f, 0))
            seg.color.filter = sd.get("color", {}).get("filter", "none")
            seg.text.__dict__.update(sd.get("text", {}))
            seg._clamp_stem_trims()
            segs.append(seg)
        self.timeline.segments = segs
        self.overlays.extend(OverlayItem.from_dict(o) for o in data.get("overlays", []) if os.path.exists(o.get("path", "")))
        md = data.get("music")
        self.music = MusicTrack.from_dict(md) if md and os.path.exists(md.get("path", "")) else None
        self.subtitles = list(data.get("subtitles", []))
        st = data.get("sub_style", {})
        self.spn_sub_size.setValue(st.get("size", 5))
        self.cmb_sub_pos.setCurrentIndex(st.get("pos", 0))
        self._set_color_button(self.btn_sub_color, st.get("color", "#FFFFFF"))
        self.chk_sub_backdrop.setChecked(st.get("backdrop", True))
        self.chk_sub_burn.setChecked(st.get("burn", True))
        ex = data.get("export", {})
        for cb, key in ((self.cmb_exp_platform, "platform"), (self.cmb_exp_format, "format"), (self.cmb_exp_fit, "fit"),
                        (self.cmb_exp_fps, "fps"), (self.cmb_exp_quality, "quality"), (self.cmb_exp_encoder, "encoder")):
            if key in ex and 0 <= ex[key] < cb.count():
                cb.blockSignals(True)
                cb.setCurrentIndex(ex[key])
                cb.blockSignals(False)
        mk = data.get("marks", {})
        self.timeline.mark_a_ms, self.timeline.mark_b_ms = mk.get("a"), mk.get("b")
        for name, locked in (("A", mk.get("lock_a")), ("B", mk.get("lock_b"))):
            if locked:
                self._toggle_mark_lock(name, True)
        self._refresh_overlay_list()
        self._sync_music_ui()
        self._on_subtitles_changed()
        self.timeline.playhead_ms = min(data.get("playhead", 0), self.timeline.total_duration_ms())
        self._update_marks_label(self.timeline.mark_a_ms, self.timeline.mark_b_ms)
        self.timeline.update_width()
        self.timeline.update()
        self._render_frame_at_ms(self.timeline.playhead_ms)
        # Separated stems are recomputed in the background with the same engine as before
        for src, engine in id_map.values():
            if engine and any(s.source is src and s.audio_mix.separated for s in segs):
                self._resume_separation(src, engine)
        if missing:
            QMessageBox.warning(self, "Missing media", "These files could not be found and were left out:\n\n" + "\n".join(missing))
        self.status.showMessage(f"Opened project with {len(segs)} clip(s).")

    def _resume_separation(self, src, engine):
        idx = self.cmb_sep_engine.findData(engine)
        if idx >= 0 and self.cmb_sep_engine.model().item(idx).isEnabled():
            self.cmb_sep_engine.setCurrentIndex(idx)
        playhead = self.timeline.playhead_ms
        seg = next((s for s in self.timeline.segments if s.source is src), None)
        if seg:
            self.timeline.playhead_ms = self._segment_start_ms(seg) + 1
            self._separate_audio_for_active_clip()
            self.timeline.playhead_ms = playhead

    def _add_recent(self, path: str):
        rec = [p for p in (self.settings.value("recent", []) or []) if p != path]
        rec.insert(0, path)
        self.settings.setValue("recent", rec[:8])
        self._rebuild_recent_menu()

    def _rebuild_recent_menu(self):
        if not hasattr(self, "menu_recent"):
            return
        self.menu_recent.clear()
        rec = [p for p in (self.settings.value("recent", []) or []) if isinstance(p, str)]
        for p in rec:
            act = self.menu_recent.addAction(os.path.basename(p))
            act.setToolTip(p)
            act.triggered.connect(lambda _=False, pp=p: self._open_project(pp))
        if not rec:
            a = self.menu_recent.addAction("(no recent projects)")
            a.setEnabled(False)

    def _autosave(self):
        if not self._dirty or not self.timeline.segments:
            return
        try:
            data = self._project_dict()
            data["autosave_of"] = self.project_path
            self._write_project(self._autosave_path(), data)
        except Exception:
            pass

    def _offer_recovery(self):
        path = self._autosave_path()
        crashed = str(self.settings.value("clean_exit", "true")).lower() != "true"
        self.settings.setValue("clean_exit", "false")
        if crashed and os.path.exists(path):
            ans = QMessageBox.question(self, "Recover your work?",
                                       "ANK Media Studio did not close normally last time.\n\nRestore the automatically saved edit?",
                                       QMessageBox.StandardButton.Yes | QMessageBox.StandardButton.No)
            if ans == QMessageBox.StandardButton.Yes:
                with open(path, encoding="utf-8") as f:
                    data = json.load(f)
                self._load_project_dict(data, os.path.dirname(data.get("autosave_of") or path))
                self.project_path = data.get("autosave_of") or ""
                self._mark_dirty()
                self.status.showMessage("Recovered your last session from the autosave.")

    def _save_shortcut(self):
        if self.tabs.currentIndex() == 0:
            self._save_project()
        elif self.tabs.currentIndex() == 1:
            self._save_photo(transparent_png=False)


    # ==========================================================================
    # v3: TAB 3 — DOWNLOAD (yt-dlp) + NADER DOWNLOADER INTEGRATION
    # ==========================================================================
    def _build_download_tab(self):
        tab = QWidget()
        layout = QHBoxLayout(tab)
        layout.setContentsMargins(10, 10, 10, 10)
        layout.setSpacing(12)

        left = QFrame()
        left.setObjectName("Card")
        lv = QVBoxLayout(left)
        lv.setContentsMargins(16, 14, 16, 14)
        title = QLabel("Download a video, then edit it here")
        title.setObjectName("Section")
        title.setStyleSheet("font-size: 15px;")
        lv.addWidget(title)
        self.txt_dl_url = QLineEdit()
        self.txt_dl_url.setPlaceholderText("Paste a video link (YouTube, TikTok, Instagram, Dailymotion, …)")
        btn_paste = icon_button("Paste", "paste", "sky")
        btn_paste.clicked.connect(lambda: self.txt_dl_url.setText(QApplication.clipboard().text().strip()))
        lv.addLayout(self._row(self.txt_dl_url, btn_paste))
        self.cmb_dl_quality = QComboBox()
        self.cmb_dl_quality.addItems(["Best quality (MP4)", "1080p (MP4)", "720p (MP4)", "Audio only (MP3)"])
        self.chk_dl_open = QCheckBox("Open in the Video Studio when finished")
        self.chk_dl_open.setChecked(True)
        lv.addLayout(self._row(QLabel("Quality"), self.cmb_dl_quality, self.chk_dl_open, None))
        self.btn_dl_start = icon_button("Download", "export", "green", kind="success")
        self.btn_dl_start.setMinimumHeight(38)
        self.btn_dl_start.clicked.connect(self._start_download)
        self.btn_dl_stop = icon_button("Stop", "stop", "red")
        self.btn_dl_stop.setEnabled(False)
        self.btn_dl_stop.clicked.connect(self._stop_download)
        lv.addLayout(self._row(self.btn_dl_start, self.btn_dl_stop))
        self.dl_progress = QProgressBar()
        self.dl_progress.setRange(0, 100)
        self.dl_progress.setValue(0)
        lv.addWidget(self.dl_progress)
        self.lbl_dl_status = self._muted("Ready." if ytdlp_command() else "yt-dlp not found. Install it with:  pip install yt-dlp")
        lv.addWidget(self.lbl_dl_status)

        lv.addWidget(self._section("Save downloads to"))
        self.txt_dl_dir = QLineEdit(str(self.settings.value("download_dir", os.path.join(os.path.expanduser("~"), "Videos", "ANK Downloads"))))
        btn_dir = icon_button("", "open", "amber", "Choose folder")
        btn_dir.clicked.connect(lambda: self._choose_dir(self.txt_dl_dir, "download_dir"))
        lv.addLayout(self._row(self.txt_dl_dir, btn_dir, stretch_last=False))

        lv.addWidget(self._section("Nader Downloader (Narto, Shortmax, TikTok bulk…)"))
        self.txt_nd_path = QLineEdit(self._find_nader_downloader())
        self.txt_nd_path.setPlaceholderText("Path to Downloader.py")
        btn_nd_browse = icon_button("", "open", "amber", "Find Downloader.py")
        btn_nd_browse.clicked.connect(self._browse_nader_downloader)
        lv.addLayout(self._row(self.txt_nd_path, btn_nd_browse))
        btn_nd_launch = icon_button("Launch Nader Downloader", "film", "violet", kind="accent")
        btn_nd_launch.clicked.connect(self._launch_nader_downloader)
        lv.addWidget(btn_nd_launch)
        lv.addWidget(self._muted("Its finished videos appear in the list on the right, ready to open in the editor."))
        lv.addStretch()
        layout.addWidget(left, 2)

        right = QFrame()
        right.setObjectName("Card")
        rv = QVBoxLayout(right)
        rv.setContentsMargins(14, 14, 14, 14)
        hdr = QLabel("Recent downloads")
        hdr.setObjectName("Section")
        hdr.setStyleSheet("font-size: 15px;")
        rv.addWidget(hdr)
        self.lst_downloads = QListWidget()
        self.lst_downloads.setIconSize(QSize(96, 54))
        self.lst_downloads.itemDoubleClicked.connect(lambda _it: self._open_download_in_editor())
        rv.addWidget(self.lst_downloads, 1)
        b_open = icon_button("Open in Video Studio", "film", "blue", kind="primary")
        b_open.clicked.connect(self._open_download_in_editor)
        b_folder = icon_button("Show in Folder", "open", "amber")
        b_folder.clicked.connect(self._show_download_folder)
        b_refresh = icon_button("Refresh", "reset", "slate")
        b_refresh.clicked.connect(self._refresh_downloads)
        rv.addLayout(self._row(b_open, b_folder, b_refresh))
        layout.addWidget(right, 3)
        self._dl_proc = None
        QTimer.singleShot(300, self._refresh_downloads)
        return tab

    def _choose_dir(self, line: QLineEdit, key: str):
        d = QFileDialog.getExistingDirectory(self, "Choose Folder", line.text())
        if d:
            line.setText(d)
            self.settings.setValue(key, d)
            self._refresh_downloads()

    def _find_nader_downloader(self) -> str:
        saved = str(self.settings.value("nader_downloader", "") or "")
        for cand in (saved, os.path.join(APP_DIR, "Downloader.py"), os.path.join(APP_DIR, "..", "downloader", "Downloader.py"),
                     os.path.join(os.path.expanduser("~"), "Desktop", "Downloader.py")):
            if cand and os.path.isfile(cand):
                return os.path.abspath(cand)
        return ""

    def _browse_nader_downloader(self):
        p, _ = QFileDialog.getOpenFileName(self, "Find Downloader.py", "", "Python (*.py *.pyw)")
        if p:
            self.txt_nd_path.setText(p)
            self.settings.setValue("nader_downloader", p)
            self._refresh_downloads()

    def _launch_nader_downloader(self):
        p = self.txt_nd_path.text().strip()
        if not os.path.isfile(p):
            QMessageBox.information(self, "Nader Downloader", "Choose where Downloader.py is first.")
            return
        self.settings.setValue("nader_downloader", p)
        py = sys.executable
        if os.name == "nt" and py.lower().endswith("python.exe") and os.path.exists(py[:-10] + "pythonw.exe"):
            py = py[:-10] + "pythonw.exe"
        subprocess.Popen([py, p], cwd=os.path.dirname(p))
        self.status.showMessage("Nader Downloader opened in its own window.")

    def _download_folders(self):
        dirs = [self.txt_dl_dir.text().strip()]
        nd = self.txt_nd_path.text().strip()
        if nd:
            dirs.append(os.path.join(os.path.dirname(nd), "Finished_Videos"))
        return [d for d in dirs if d and os.path.isdir(d)]

    def _refresh_downloads(self):
        files = []
        for d in self._download_folders():
            for root, _dirs, names in os.walk(d):
                for n in names:
                    if os.path.splitext(n)[1].lower() in VIDEO_EXTS | {".mp3", ".m4a"} and not n.endswith(".part"):
                        fp = os.path.join(root, n)
                        try:
                            files.append((os.path.getmtime(fp), fp))
                        except OSError:
                            pass
        files.sort(reverse=True)
        self.lst_downloads.clear()
        for mtime, fp in files[:60]:
            size_mb = os.path.getsize(fp) / (1024 * 1024)
            item = QListWidgetItem(f"{os.path.basename(fp)}\n{size_mb:.1f} MB  •  {os.path.dirname(fp)}")
            item.setData(Qt.ItemDataRole.UserRole, fp)
            item.setIcon(make_icon("music" if fp.lower().endswith((".mp3", ".m4a")) else "film", "blue"))
            self.lst_downloads.addItem(item)
        if not files:
            self.lst_downloads.addItem("No downloads yet.")

    def _selected_download(self):
        it = self.lst_downloads.currentItem()
        return it.data(Qt.ItemDataRole.UserRole) if it else None

    def _open_download_in_editor(self):
        fp = self._selected_download()
        if not fp:
            return
        if fp.lower().endswith((".mp3", ".m4a")):
            self.tabs.setCurrentIndex(0)
            self.music = MusicTrack(fp)
            self.music.audio()
            self._sync_music_ui()
            self.status.showMessage(f"Added {os.path.basename(fp)} as background music.")
            return
        self.tabs.setCurrentIndex(0)
        self._load_video_paths([fp])

    def _show_download_folder(self):
        fp = self._selected_download()
        folder = os.path.dirname(fp) if fp else self.txt_dl_dir.text()
        if os.name == "nt":
            if fp:
                subprocess.Popen(["explorer", "/select,", os.path.normpath(fp)])
            else:
                os.startfile(folder)
        else:
            subprocess.Popen(["xdg-open" if sys.platform != "darwin" else "open", folder])

    def _start_download(self):
        url = self.txt_dl_url.text().strip()
        cmd0 = ytdlp_command()
        if not url:
            self.lbl_dl_status.setText("Paste a link first.")
            return
        if not cmd0:
            QMessageBox.information(self, "Download", "yt-dlp is not installed.\n\nInstall it with:\n    pip install yt-dlp")
            return
        out_dir = self.txt_dl_dir.text().strip()
        os.makedirs(out_dir, exist_ok=True)
        self.settings.setValue("download_dir", out_dir)
        q = self.cmb_dl_quality.currentIndex()
        fmt = {0: ["-f", "bv*+ba/b", "--merge-output-format", "mp4"],
               1: ["-f", "bv*[height<=1080]+ba/b[height<=1080]", "--merge-output-format", "mp4"],
               2: ["-f", "bv*[height<=720]+ba/b[height<=720]", "--merge-output-format", "mp4"],
               3: ["-x", "--audio-format", "mp3"]}[q]
        cmd = cmd0 + fmt + ["--newline", "--no-playlist", "-o", os.path.join(out_dir, "%(title).80s.%(ext)s"),
                            "--print", "after_move:filepath"]
        if FFMPEG_EXE:
            cmd += ["--ffmpeg-location", FFMPEG_EXE]
        cmd.append(url)
        self.btn_dl_start.setEnabled(False)
        self.btn_dl_stop.setEnabled(True)
        self.dl_progress.setValue(0)
        self.lbl_dl_status.setText("Starting…")

        def work():
            final_path, tail = "", []
            try:
                self._dl_proc = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True,
                                                 encoding="utf-8", errors="ignore", bufsize=1, creationflags=NO_WINDOW)
                for line in self._dl_proc.stdout:
                    line = line.strip()
                    if not line:
                        continue
                    tail = (tail + [line])[-12:]
                    m = re.search(r"(\d+(?:\.\d+)?)%", line)
                    if "[download]" in line and m:
                        pct = float(m.group(1))
                        self._bridge.call.emit(lambda p=pct, l=line: (self.dl_progress.setValue(int(p)),
                                                                      self.lbl_dl_status.setText(l.replace("[download]", "").strip()[:110])))
                    elif os.path.isabs(line) and os.path.exists(line):
                        final_path = line
                    elif "[Merger]" in line or "[ExtractAudio]" in line:
                        self._bridge.call.emit(lambda: self.lbl_dl_status.setText("Merging video and audio…"))
                rc = self._dl_proc.wait()
            except Exception as e:
                rc, tail = -1, [str(e)]

            def done():
                self._dl_proc = None
                self.btn_dl_start.setEnabled(True)
                self.btn_dl_stop.setEnabled(False)
                if rc == 0 and final_path:
                    self.dl_progress.setValue(100)
                    self.lbl_dl_status.setText(f"Saved: {os.path.basename(final_path)}")
                    self._refresh_downloads()
                    if self.chk_dl_open.isChecked():
                        if final_path.lower().endswith(".mp3"):
                            self.music = MusicTrack(final_path)
                            self.music.audio()
                            self._sync_music_ui()
                            self.tabs.setCurrentIndex(0)
                        else:
                            self.tabs.setCurrentIndex(0)
                            self._load_video_paths([final_path])
                elif rc != 0:
                    err = next((t for t in reversed(tail) if "ERROR" in t), tail[-1] if tail else "Download failed.")
                    self.lbl_dl_status.setText(err[:160])
            self._bridge.call.emit(done)
        threading.Thread(target=work, daemon=True).start()

    def _stop_download(self):
        if self._dl_proc and self._dl_proc.poll() is None:
            self._dl_proc.kill()
            self.lbl_dl_status.setText("Stopped.")






    def closeEvent(self, event):
        if not self._confirm_discard():
            event.ignore()
            return
        busy = [j for j in self.export_jobs if j["status"] not in ("Done", "Failed", "Cancelled")]
        if busy and QMessageBox.question(self, APP_NAME, f"{len(busy)} export(s) still running. Quit anyway?",
                                         QMessageBox.StandardButton.Yes | QMessageBox.StandardButton.No) != QMessageBox.StandardButton.Yes:
            event.ignore()
            return
        for j in busy:
            j["cancel"] = True
        self.play_timer.stop()
        self._stop_preview_audio()
        for r in self.open_captures.values():
            r.release()
        self.settings.setValue("clean_exit", "true")
        try:
            os.remove(self._autosave_path())
        except OSError:
            pass
        super().closeEvent(event)


def _install_error_handler():
    """PyQt6 closes the app on any error inside a button handler; show and log it instead."""
    def log(exc_type, exc, tb):
        text = "".join(traceback.format_exception(exc_type, exc, tb))
        try:
            with open(CRASH_LOG, "a", encoding="utf-8") as f:
                f.write(text + "\n")
        except OSError:
            pass
        if sys.__stderr__:
            sys.__stderr__.write(text)

    def hook(exc_type, exc, tb):
        log(exc_type, exc, tb)
        try:
            QMessageBox.critical(None, f"{APP_NAME} — error",
                                 f"Something went wrong (the app keeps running):\n\n{exc}\n\nDetails saved to:\n{CRASH_LOG}")
        except Exception:
            pass
    sys.excepthook = hook
    # Dialogs may only be shown from the GUI thread, so background errors are logged only
    threading.excepthook = lambda args: log(args.exc_type, args.exc_value, args.exc_traceback)


def main():
    if hasattr(Qt, "HighDpiScaleFactorRoundingPolicy"):
        QApplication.setHighDpiScaleFactorRoundingPolicy(Qt.HighDpiScaleFactorRoundingPolicy.PassThrough)
    app = QApplication(sys.argv)
    app.setApplicationName(APP_NAME)
    app.setWindowIcon(make_icon("logo", "violet"))
    _install_error_handler()
    win = ANKMediaStudio()
    win.show()
    return app.exec()


if __name__ == "__main__":
    try:
        sys.exit(main())
    except SystemExit:
        raise
    except Exception:
        _show_fatal(f"{APP_NAME} could not start", traceback.format_exc())
        sys.exit(1)
