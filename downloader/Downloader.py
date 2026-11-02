import os, sys, subprocess, re, threading, urllib.parse, webbrowser, datetime, time, shutil, copy
import json, math
import tkinter as tk
import tkinter.font as tkfont
from tkinter import ttk, messagebox, filedialog

# Optional Drag-and-Drop support if user has tkinterdnd2 installed
try:
    from tkinterdnd2 import DND_FILES, TkinterDnD
    HAS_DND = True
except ImportError:
    HAS_DND = False


def natural_sort_key(s):
    """Sorts strings containing numbers in a human-readable way (1, 2, 10, 11)."""
    return [int(text) if text.isdigit() else text.lower() for text in re.split(r'(\d+)', s)]


def parse_time_to_seconds(t_str):
    """Converts 'HH:MM:SS.ms', 'MM:SS.ms', or 'SS.ms' into float seconds."""
    s = str(t_str or "").strip().replace(",", ".")
    if not s:
        return 0.0
    neg = False
    if s.startswith("-"):
        neg = True
        s = s[1:].strip()
    elif s.startswith("+"):
        s = s[1:].strip()
    parts = s.split(":")
    try:
        if len(parts) == 3:
            val = int(parts[0]) * 3600 + int(parts[1]) * 60 + float(parts[2])
        elif len(parts) == 2:
            val = int(parts[0]) * 60 + float(parts[1])
        else:
            val = float(parts[0])
        return -val if neg else val
    except ValueError:
        raise ValueError(f"Invalid time format: '{t_str}'. Use HH:MM:SS.ms, MM:SS, or seconds.")


def format_seconds_to_time(sec, srt_format=False):
    """Formats float seconds into HH:MM:SS.mmm (or HH:MM:SS,mmm for SRT)."""
    if sec < 0:
        sec = 0.0
    hrs = int(sec // 3600)
    mins = int((sec % 3600) // 60)
    secs = sec % 60
    sep = "," if srt_format else "."
    whole_s = int(secs)
    ms = int(round((secs - whole_s) * 1000))
    if ms >= 1000:
        whole_s += 1
        ms -= 1000
    return f"{hrs:02d}:{mins:02d}:{whole_s:02d}{sep}{ms:03d}"


def build_atempo_chain(speed_factor):
    """Builds a valid FFmpeg atempo filter chain for any speed factor (even outside 0.5-2.0)."""
    f = float(speed_factor)
    if abs(f - 1.0) < 0.0001:
        return "anull"
    filters = []
    while f > 2.0:
        filters.append("atempo=2.0")
        f /= 2.0
    while f < 0.5:
        filters.append("atempo=0.5")
        f /= 0.5
    filters.append(f"atempo={f:.6f}")
    return ",".join(filters)


def clean_folder_Title(raw_name):
    """Cleans a movie/file name into a neat folder name, stripping previous sync/merge suffixes."""
    name = os.path.splitext(os.path.basename(str(raw_name or "Movie")))[0]
    for tag in ("_ManualSynced", "_AutoSubSynced", "_DriftRepaired", "_FullManualEdit", "_Stitched_Final", "_Full", "_Manual_Merge"):
        name = name.replace(tag, "")
    name = re.sub(r'_EP\d+(?:-EP\d+)?$', '', name, flags=re.IGNORECASE)
    name = re.sub(r'^(?:Dailymotion_|Narto_Series_|TikTok_Bulk_|TikTok_|Bypass_Video_)', '', name, flags=re.IGNORECASE)
    name = re.sub(r'#\S+', '', name)
    name = re.sub(r'[<>:"/\\|?*\x00-\x1f]', '_', name)
    name = re.sub(r'[\s_]+', '_', name).strip('_. ')
    return name[:65] if name else "General_Movie"


# =========================================================================
# 3D GRAPHICS ENGINE (v1.8.0): glossy buttons, tabs, spheres and icons
# rendered pixel-by-pixel in pure Python (no Pillow needed)
# =========================================================================
def _rgb(hex_c):
    hex_c = hex_c.lstrip("#")
    return tuple(int(hex_c[i:i + 2], 16) for i in (0, 2, 4))

def _mix(a, b, t):
    t = 0.0 if t < 0.0 else (1.0 if t > 1.0 else t)
    return (a[0] + (b[0] - a[0]) * t, a[1] + (b[1] - a[1]) * t, a[2] + (b[2] - a[2]) * t)

def _hexc(c):
    return "#%02x%02x%02x" % tuple(0 if v < 0 else (255 if v > 255 else int(v + 0.5)) for v in c)

def _round_rect_dist(px, py, x0, y0, x1, y1, r):
    """Signed distance from a point to a rounded rectangle (negative inside)."""
    hx, hy = (x1 - x0) / 2.0, (y1 - y0) / 2.0
    qx = abs(px - (x0 + hx)) - (hx - r)
    qy = abs(py - (y0 + hy)) - (hy - r)
    return math.hypot(max(qx, 0.0), max(qy, 0.0)) + min(max(qx, qy), 0.0) - r

def _seg_dist(px, py, ax, ay, bx, by):
    dx, dy = bx - ax, by - ay
    t = max(0.0, min(1.0, ((px - ax) * dx + (py - ay) * dy) / (dx * dx + dy * dy)))
    return math.hypot(px - (ax + t * dx), py - (ay + t * dy))

def _rows_to_photo(master, rows):
    cache = {}
    def hx(c):
        v = cache.get(c)
        if v is None:
            v = cache[c] = _hexc(c)
        return v
    img = tk.PhotoImage(master=master, width=len(rows[0]), height=len(rows))
    img.put(" ".join("{" + " ".join(hx(c) for c in row) + "}" for row in rows))
    return img

def render_glossy_rows(w, h, top, bottom, edge, bg, radius=7, gloss=0.24, shadow=2, pressed=False, flat=False):
    """A beveled glass-like rounded panel with rim light and a soft drop shadow, as pixel rows."""
    # The shading only varies vertically: render a narrow strip and repeat its middle column
    core = int(2 * radius + 6)
    if w > core + 1:
        narrow = render_glossy_rows(core, h, top, bottom, edge, bg, radius, gloss, shadow, pressed, flat)
        half = core // 2
        fill = w - 2 * half
        return [row[:half] + [row[half]] * fill + row[core - half:] for row in narrow]
    top_c, bot_c, edge_c, bg_c = _rgb(top), _rgb(bottom), _rgb(edge), _rgb(bg)
    white, black = (255, 255, 255), (0, 0, 0)
    body_h = h - shadow
    rows = []
    for y in range(h):
        py = y + 0.5
        t = py / max(1.0, body_h)
        base = _mix(bot_c, top_c, t) if pressed else _mix(top_c, bot_c, t)
        if not pressed and not flat and t < 0.5:
            base = _mix(base, white, gloss * (1.0 - t / 0.5))
        row = []
        for x in range(w):
            px = x + 0.5
            col = bg_c
            if shadow:
                ds = _round_rect_dist(px, py, 1.0, float(shadow), w - 1.0, float(h), radius)
                col = _mix(col, black, 0.55 * max(0.0, min(1.0, 0.5 - ds / 1.6)))
            d = _round_rect_dist(px, py, 0.0, 0.0, float(w), float(body_h), radius)
            cov = 0.5 - d
            if cov > 0.0:
                c = base
                if d > -1.15:
                    c = _mix(c, edge_c, 0.8)                          # crisp bevel edge
                elif d > -2.2 and not pressed and not flat:
                    c = _mix(c, white, 0.28 if py < body_h * 0.5 else 0.06)  # rim light
                col = _mix(col, c, cov)
            row.append(col)
        rows.append(row)
    return rows

def render_glossy(master, w, h, top, bottom, edge, bg, **kw):
    return _rows_to_photo(master, render_glossy_rows(w, h, top, bottom, edge, bg, **kw))

def render_sphere(master, size, color, bg):
    """A lit 3D ball with diffuse shading and a specular highlight."""
    c, bg_c = _rgb(color), _rgb(bg)
    dark = (c[0] * 0.28, c[1] * 0.28, c[2] * 0.28)
    r = size / 2.0 - 0.6
    cx = cy = size / 2.0
    lx, ly, lz = -0.45, -0.6, 0.66
    rows = []
    for y in range(size):
        row = []
        for x in range(size):
            dx, dy = (x + 0.5 - cx) / r, (y + 0.5 - cy) / r
            dd = dx * dx + dy * dy
            cov = r - math.sqrt(dd) * r + 0.5
            if cov <= 0:
                row.append(bg_c)
                continue
            nz = math.sqrt(max(0.0, 1.0 - min(1.0, dd)))
            diff = max(0.0, dx * lx + dy * ly + nz * lz)
            col = _mix(dark, c, 0.25 + 0.9 * diff)
            col = _mix(col, (255, 255, 255), 0.85 * diff ** 22)
            if dy > 0.35:
                col = _mix(col, c, 0.25 * (dy - 0.35))                # bounce light
            row.append(_mix(bg_c, col, cov))
        rows.append(row)
    return _rows_to_photo(master, rows)

def render_check(master, size, on, color, bg, round_box=False):
    """3D checkbox (or radio dot when round_box) for ttk indicators."""
    if on:
        top, bot, edge = color, _hexc(_mix(_rgb(color), (0, 0, 0), 0.35)), _hexc(_mix(_rgb(color), (255, 255, 255), 0.3))
    else:
        top, bot, edge = "#1e293b", "#0f172a", "#475569"
    rows = render_glossy_rows(size, size, top, bot, edge, bg, radius=(size / 2.0 - 1 if round_box else 4), shadow=1)
    if on:
        for y in range(size):
            for x in range(size):
                px, py = x + 0.5, y + 0.5
                if round_box:
                    d = math.hypot(px - size / 2.0, py - (size - 1) / 2.0) - size * 0.2
                else:
                    d = min(_seg_dist(px, py, size * 0.25, size * 0.5, size * 0.43, size * 0.68),
                            _seg_dist(px, py, size * 0.43, size * 0.68, size * 0.76, size * 0.3)) - 1.1
                cov = 0.5 - d
                if cov > 0:
                    rows[y][x] = _mix(rows[y][x], (255, 255, 255), cov)
    return _rows_to_photo(master, rows)

def render_app_icon(master, size=64):
    """Glossy blue-violet rounded tile with a white play symbol and a film notch."""
    rows = []
    tri = ((size * 0.38, size * 0.28), (size * 0.38, size * 0.72), (size * 0.74, size * 0.5))
    def tri_dist(px, py):
        signs = set()
        d_min = 1e9
        for i in range(3):
            ax, ay = tri[i]
            bx, by = tri[(i + 1) % 3]
            cross = (bx - ax) * (py - ay) - (by - ay) * (px - ax)
            signs.add(cross >= 0)
            d_min = min(d_min, _seg_dist(px, py, ax, ay, bx, by))
        return -d_min if len(signs) == 1 else d_min
    for y in range(size):
        row = []
        for x in range(size):
            px, py = x + 0.5, y + 0.5
            t = (px + py) / (2.0 * size)
            col = _mix(_rgb("#3b82f6"), _rgb("#8b5cf6"), t)
            if py < size * 0.5:
                col = _mix(col, (255, 255, 255), 0.22 * (1 - py / (size * 0.5)))
            d = _round_rect_dist(px, py, 0, 0, size, size, size * 0.24)
            if d > -1.5:
                col = _mix(col, _rgb("#c4b5fd"), 0.7)
            cov = 0.5 - d
            out = _mix((11, 15, 25), col, cov) if cov > 0 else (11, 15, 25)
            ts = tri_dist(px - 1.5, py - 1.5)                          # play symbol shadow
            if cov > 0 and ts < 1.0:
                out = _mix(out, (20, 10, 60), 0.5 * max(0.0, min(1.0, 0.5 - ts)))
            td = tri_dist(px, py)
            if cov > 0 and td < 0.5:
                out = _mix(out, (255, 255, 255), max(0.0, min(1.0, 0.5 - td)))
            row.append(out)
        rows.append(row)
    return _rows_to_photo(master, rows)

def render_banner(master, w, h, left, mid, right):
    """Horizontal 3-stop gradient with a glass sheen, rendered at half size then zoomed."""
    hw, hh = max(2, w // 2), max(2, h // 2)
    l_c, m_c, r_c = _rgb(left), _rgb(mid), _rgb(right)
    cols = []
    for x in range(hw):
        t = x / max(1, hw - 1)
        cols.append(_mix(l_c, m_c, t / 0.55) if t < 0.55 else _mix(m_c, r_c, (t - 0.55) / 0.45))
    rows = []
    for y in range(hh):
        ty = y / max(1, hh - 1)
        sheen = 0.16 * (1 - ty / 0.5) if ty < 0.5 else 0.0
        shade = 0.25 * max(0.0, (ty - 0.6) / 0.4)
        rows.append([_mix(_mix(c, (255, 255, 255), sheen), (0, 0, 0), shade) for c in cols])
    return _rows_to_photo(master, rows).zoom(2, 2)


class DownloaderApp:
    def __init__(self, root):
        self.root = root
        self.version = "v1.8.0"
        self.root.title(f"Nader Pro Video & Drama Studio {self.version} — Created by Nader Alkhansa")
        self.root.geometry("1200x950")
        self.root.minsize(960, 820)
        self.root.configure(bg="#0b0f19")

        # --- SETUP PRO DARK STUDIO THEME ---
        self.setup_pro_theme()

        # --- PORTABLE PATHING ---
        self.base_dir = os.path.dirname(os.path.abspath(__file__))
        self.output_base = os.path.join(self.base_dir, "Finished_Videos")
        self.log_file = os.path.join(self.output_base, "download_log.txt")
        self.history_file = os.path.join(self.base_dir, "link_history.json")
        self.cookie_jar_file = os.path.join(self.base_dir, "narto_cookies.txt")
        os.makedirs(self.output_base, exist_ok=True)

        self.stop_flag = False
        self.current_process = None
        self.sync_stop_flag = False
        self.sync_process = None
        self.live_audio_process = None
        self.last_output_file = ""
        self.last_output_folder = self.output_base

        # Load Persistent 5-Link History per Source
        self.link_history = self.load_history()
        self.url_widgets = {}

        # Log Management
        self.previous_runs_log = ""
        if os.path.exists(self.log_file):
            with open(self.log_file, "r", encoding="utf-8", errors="ignore") as f:
                self.previous_runs_log = f.read()
        self.current_run_log = ""

        # --- SINGLE-WINDOW NAVIGATION SHELL ---
        self.nav_history = []
        self.current_page_name = "home"
        self.pages = {}

        # Top Persistent Studio Header Bar
        self.header_bar = tk.Frame(self.root, bg="#111827", height=54, highlightthickness=1, highlightbackground="#1f2937")
        self.header_bar.pack(side="top", fill="x")

        # Generated glossy app icon (window + taskbar)
        try:
            self._app_icon = render_app_icon(self.root, 64)
            self._app_icon_small = self._app_icon.subsample(2, 2)
            self.root.iconphoto(True, self._app_icon, self._app_icon_small)
        except Exception:
            pass

        self.back_btn = self.make_3d_pill(self.header_bar, "⬅️ Back", self.navigate_back, kind="blue")
        self.back_btn.pack(side="left", padx=(12, 8), pady=8)

        self.header_title_lbl = tk.Label(
            self.header_bar, text=f"🎬 Nader Video Studio {self.version} — Main Dashboard",
            font=("Arial", 12, "bold"), bg="#111827", fg="#f8fafc"
        )
        self.header_title_lbl.pack(side="left", padx=6)

        # Quick-Switch Navigation Pills on Right of Header
        nav_pills = tk.Frame(self.header_bar, bg="#111827")
        nav_pills.pack(side="right", padx=12)

        self.nav_buttons = {}
        nav_items = [
            ("home", "🏠 Dashboard"),
            ("sync", "🎙️ Voice Sync"),
            ("manual_edit", "🎛️ Full Manual Edit"),
            ("queue", "🌙 5-Movie Queue"),
            ("trim_crop", "✂️ Trim & Crop HD")
        ]
        for key, label in nav_items:
            b = self.make_3d_pill(nav_pills, label, lambda k=key: self.show_page(k))
            b.pack(side="left", padx=2, pady=8)
            self.nav_buttons[key] = b

        # Nav pills get space first; a long page title is clipped instead of pushing the pills off-screen
        self.header_title_lbl.pack_forget()
        self.header_title_lbl.config(anchor="w")
        self.header_title_lbl.pack(side="left", padx=6, fill="x", expand=True)

        # Main Page Container (All pages swap inside here — NO separate windows!)
        self.page_container = tk.Frame(self.root, bg="#0b0f19")
        self.page_container.pack(side="top", fill="both", expand=True)

        # Persistent Footer
        footer_frame = tk.Frame(self.root, bg="#090d16", height=28, highlightthickness=1, highlightbackground="#1e293b")
        footer_frame.pack(side="bottom", fill="x")
        tk.Label(footer_frame, text="Created by Nader Alkhansa • Pro Single-Window Studio Architecture", font=("Arial", 9, "italic"), bg="#090d16", fg="#64748b").pack(side="left", padx=12, pady=3)
        tk.Label(footer_frame, text=self.version, font=("Arial", 9, "bold"), bg="#090d16", fg="#38bdf8").pack(side="right", padx=12, pady=3)

        # Build All 5 Pages Inside the Main Window
        self.build_home_page()
        self.build_voice_sync_page()
        self.build_full_manual_edit_page()
        self.build_narto_queue_page()
        self.build_trim_crop_page()

        # Show Home Page Initially
        self.show_page("home", push_history=False)

        # Clean up background audio on close
        self.root.protocol("WM_DELETE_WINDOW", self.on_app_close)

    def setup_pro_theme(self):
        style = ttk.Style(self.root)
        try:
            style.theme_use("clam")
        except:
            pass

        bg_dark = "#0b0f19"
        card_bg = "#131b2e"
        fg_light = "#f1f5f9"
        accent_blue = "#2563eb"
        accent_hover = "#3b82f6"
        entry_bg = "#1e293b"

        style.configure(".", background=bg_dark, foreground=fg_light, font=("Arial", 9))
        style.configure("TFrame", background=bg_dark)
        style.configure("Card.TFrame", background=card_bg)
        style.configure("TLabel", background=bg_dark, foreground=fg_light)
        style.configure("TLabelframe", background=card_bg, foreground="#38bdf8", bordercolor="#1e293b", relief="solid")
        style.configure("TLabelframe.Label", background=card_bg, foreground="#38bdf8", font=("Arial", 10, "bold"))
        style.configure("TCheckbutton", background=bg_dark, foreground=fg_light, font=("Arial", 9))
        style.map("TCheckbutton", background=[("active", bg_dark)])
        style.configure("TRadiobutton", background=card_bg, foreground=fg_light, font=("Arial", 9))
        style.map("TRadiobutton", background=[("active", card_bg)])

        style.configure(
            "TButton",
            background="#1e293b", foreground="#f8fafc",
            bordercolor="#334155", focuscolor="none",
            font=("Arial", 9, "bold"), padding=(8, 4)
        )
        style.map(
            "TButton",
            background=[("active", accent_hover), ("disabled", "#0f172a")],
            foreground=[("disabled", "#475569")]
        )

        style.configure(
            "Accent.TButton",
            background=accent_blue, foreground="#ffffff",
            bordercolor="#3b82f6", font=("Arial", 9, "bold"), padding=(10, 5)
        )
        style.map("Accent.TButton", background=[("active", accent_hover), ("disabled", "#1e293b")])

        style.configure(
            "Danger.TButton",
            background="#be123c", foreground="#ffffff",
            bordercolor="#e11d48", font=("Arial", 9, "bold"), padding=(10, 5)
        )
        style.map("Danger.TButton", background=[("active", "#f43f5e"), ("disabled", "#1e293b")])

        style.configure("TEntry", fieldbackground=entry_bg, foreground="#ffffff", insertcolor="#ffffff", bordercolor="#334155")
        style.configure("TCombobox", fieldbackground=entry_bg, background="#1e293b", foreground="#ffffff", arrowcolor="#38bdf8")
        style.map("TCombobox", fieldbackground=[("readonly", entry_bg)], foreground=[("readonly", "#ffffff")])
        style.configure("Horizontal.TProgressbar", troughcolor="#1e293b", background="#10b981", bordercolor="#1e293b", lightcolor="#10b981", darkcolor="#059669")
        style.configure("TSeparator", background="#1e293b")
        try:
            self.setup_3d_theme(style)
        except Exception as e:
            print(f"3D theme fallback to flat theme: {e}")

    def setup_3d_theme(self, style):
        """v1.8.0: swaps flat ttk parts for rendered 3D glass images (buttons, tabs, progress, checkboxes)."""
        self._img3d = {}
        R = self.root
        BG = "#0e1422"

        def btn_set(key, top, bot, edge, hov_top, hov_bot, press_top, press_bot):
            self._img3d[key] = {
                "n": render_glossy(R, 22, 24, top, bot, edge, BG, radius=6),
                "a": render_glossy(R, 22, 24, hov_top, hov_bot, edge, BG, radius=6),
                "p": render_glossy(R, 22, 24, press_top, press_bot, edge, BG, radius=6, pressed=True),
                "d": render_glossy(R, 22, 24, "#141b2b", "#101624", "#1e293b", BG, radius=6, flat=True),
            }
            imgs = self._img3d[key]
            el = f"G3D.{key}.border"
            style.element_create(
                el, "image", imgs["n"],
                ("disabled", imgs["d"]), ("pressed", imgs["p"]), ("active", imgs["a"]),
                border=(7, 7, 7, 8), padding=(1, 1, 1, 3), sticky="nsew"
            )
            return el

        layouts = {
            "TButton": btn_set("plain", "#334155", "#1e293b", "#475569", "#3f5270", "#26344d", "#1e293b", "#334155"),
            "Accent.TButton": btn_set("accent", "#3b82f6", "#1d4ed8", "#60a5fa", "#60a5fa", "#2563eb", "#1d4ed8", "#3b82f6"),
            "Danger.TButton": btn_set("danger", "#f43f5e", "#be123c", "#fb7185", "#fb7185", "#e11d48", "#be123c", "#f43f5e"),
            "Success.TButton": btn_set("success", "#10b981", "#047857", "#34d399", "#34d399", "#059669", "#047857", "#10b981"),
        }
        for style_name, el in layouts.items():
            style.layout(style_name, [(el, {"sticky": "nsew", "children": [
                ("Button.padding", {"sticky": "nsew", "children": [("Button.label", {"sticky": "nsew"})]})]})])
        style.configure("Success.TButton", foreground="#ffffff", font=("Arial", 9, "bold"), padding=(10, 5))
        style.map("TButton", foreground=[("disabled", "#475569")])
        style.map("Accent.TButton", foreground=[("disabled", "#475569")])
        style.map("Danger.TButton", foreground=[("disabled", "#475569")])
        style.map("Success.TButton", foreground=[("disabled", "#475569")])

        # Notebook pill tabs
        tab_n = render_glossy(R, 24, 30, "#1e293b", "#111827", "#334155", "#0b0f19", radius=9)
        tab_a = render_glossy(R, 24, 30, "#2b3a55", "#172033", "#475569", "#0b0f19", radius=9)
        tab_s = render_glossy(R, 24, 30, "#3b82f6", "#1e40af", "#93c5fd", "#0b0f19", radius=9)
        self._img3d["tabs"] = (tab_n, tab_a, tab_s)
        style.element_create("G3D.Notebook.tab", "image", tab_n, ("selected", tab_s), ("active", tab_a),
                             border=(10, 10, 10, 10), padding=(4, 2, 4, 4), sticky="nsew")
        style.layout("TNotebook.Tab", [("G3D.Notebook.tab", {"sticky": "nsew", "children": [
            ("Notebook.padding", {"side": "top", "sticky": "nsew", "children": [("Notebook.label", {"side": "top", "sticky": ""})]})]})])
        style.configure("TNotebook", background="#0b0f19", borderwidth=0, tabmargins=(10, 4, 10, 0),
                        bordercolor="#1e293b", lightcolor="#26324a", darkcolor="#05070d")
        style.configure("TNotebook.Tab", padding=(12, 4), font=("Arial", 9, "bold"), foreground="#94a3b8", background="#0b0f19")
        style.map("TNotebook.Tab", foreground=[("selected", "#ffffff"), ("active", "#e2e8f0")])

        # Glass progress bar
        trough = render_glossy(R, 24, 18, "#05070d", "#111827", "#1e293b", "#0e1422", radius=8, pressed=True, shadow=0)
        pbar = render_glossy(R, 24, 18, "#34d399", "#047857", "#6ee7b7", "#05070d", radius=8, shadow=0)
        self._img3d["progress"] = (trough, pbar)
        style.element_create("G3D.Progress.trough", "image", trough, border=(8, 8, 8, 8), sticky="nsew")
        style.element_create("G3D.Progress.pbar", "image", pbar, border=(8, 8, 8, 8), sticky="nsew")
        style.layout("Horizontal.TProgressbar", [("G3D.Progress.trough", {"sticky": "nsew", "children": [
            ("G3D.Progress.pbar", {"side": "left", "sticky": "ns"})]})])
        style.configure("Horizontal.TProgressbar", thickness=18)

        # 3D checkbox and radio indicators (rendered for the dark page and the card background)
        for suffix, bg in (("", "#0b0f19"), ("Card.", "#131b2e"), ("Panel.", "#111a2c")):
            ck = (render_check(R, 16, False, "#3b82f6", bg), render_check(R, 16, True, "#3b82f6", bg))
            rd = (render_check(R, 16, False, "#3b82f6", bg, True), render_check(R, 16, True, "#3b82f6", bg, True))
            self._img3d[f"check{suffix}"] = ck + rd
            style.element_create(f"G3D.{suffix}check", "image", ck[0], ("selected", ck[1]), sticky="w", padding=(0, 0, 6, 0))
            style.element_create(f"G3D.{suffix}radio", "image", rd[0], ("selected", rd[1]), sticky="w", padding=(0, 0, 6, 0))
            for kind, el in (("TCheckbutton", f"G3D.{suffix}check"), ("TRadiobutton", f"G3D.{suffix}radio")):
                base = "Checkbutton" if kind == "TCheckbutton" else "Radiobutton"
                style.layout(f"{suffix}{kind}", [(f"{base}.padding", {"sticky": "nsew", "children": [
                    (el, {"side": "left", "sticky": ""}),
                    (f"{base}.focus", {"side": "left", "sticky": "w", "children": [(f"{base}.label", {"sticky": "nsew"})]})]})])
        style.configure("Card.TCheckbutton", background="#131b2e", foreground="#f1f5f9", font=("Arial", 9))
        style.configure("Card.TRadiobutton", background="#131b2e", foreground="#f1f5f9", font=("Arial", 9))
        style.configure("Panel.TCheckbutton", background="#111a2c", foreground="#f1f5f9", font=("Arial", 9))
        style.configure("Panel.TRadiobutton", background="#111a2c", foreground="#f1f5f9", font=("Arial", 9))
        for s in ("Card.TCheckbutton", "Card.TRadiobutton"):
            style.map(s, background=[("active", "#131b2e")])
        for s in ("Panel.TCheckbutton", "Panel.TRadiobutton"):
            style.map(s, background=[("active", "#111a2c")])

        # Raised 3D panels: lighter top/left bevel, darker bottom/right
        style.configure("TLabelframe", background="#131b2e", bordercolor="#24324d", lightcolor="#2c3b5b", darkcolor="#04060b", relief="raised", borderwidth=2)
        style.configure("Panel.TFrame", background="#111a2c")
        style.configure("Panel.TLabel", background="#111a2c", foreground="#f1f5f9")
        style.configure("Muted.Panel.TLabel", background="#111a2c", foreground="#94a3b8", font=("Arial", 9))
        style.configure("Title.Panel.TLabel", background="#111a2c", foreground="#ffffff", font=("Arial", 13, "bold"))
        style.configure("Panel.TLabelframe", background="#111a2c", bordercolor="#24324d", lightcolor="#2c3b5b", darkcolor="#04060b", relief="raised", borderwidth=2)
        style.configure("Panel.TLabelframe.Label", background="#111a2c", foreground="#38bdf8", font=("Arial", 10, "bold"))
        style.configure("TEntry", bordercolor="#334155", lightcolor="#0b1220", darkcolor="#0b1220")
        style.configure("TCombobox", bordercolor="#334155", lightcolor="#0b1220", darkcolor="#0b1220")
        style.map("TCombobox", bordercolor=[("focus", "#3b82f6")])
        style.configure("TSpinbox", fieldbackground="#1e293b", foreground="#ffffff", background="#1e293b",
                        arrowcolor="#38bdf8", bordercolor="#334155", lightcolor="#0b1220", darkcolor="#0b1220")
        style.map("TSpinbox", fieldbackground=[("readonly", "#1e293b")], foreground=[("readonly", "#ffffff")])
        style.map("TEntry", bordercolor=[("focus", "#3b82f6")])

    # --- 3D pill buttons for the header (tk.Button with a rendered glass image behind the text) ---
    PILL_KINDS = {
        "dark": ("#2b3648", "#161e2e", "#3b4a63"),
        "hover": ("#3b4a63", "#1f2a3d", "#56657f"),
        "blue": ("#4f8ff7", "#1d4ed8", "#93c5fd"),
        "dim": ("#161e2e", "#111827", "#1f2937"),
    }

    def make_3d_pill(self, parent, text, command, kind="dark", bg="#111827"):
        f = tkfont.Font(family="Arial", size=9, weight="bold")
        w = f.measure(text) + 26

        class LazyImgs(dict):
            # Each state image is rendered the first time it is shown
            def __missing__(d, k):
                t, b, e = self.PILL_KINDS[k]
                d[k] = render_glossy(self.root, w, 30, t, b, e, bg, radius=10)
                return d[k]
        imgs = LazyImgs()
        btn = tk.Button(
            parent, text=text, image=imgs[kind], compound="center", font=("Arial", 9, "bold"),
            fg="#ffffff" if kind == "blue" else "#cbd5e1", disabledforeground="#475569",
            bg=bg, activebackground=bg, activeforeground="#ffffff",
            relief="flat", bd=0, highlightthickness=0, cursor="hand2", command=command
        )
        btn._imgs3d = imgs
        btn._kind3d = kind
        btn.bind("<Enter>", lambda e: btn._kind3d == "dark" and str(btn["state"]) != "disabled" and btn.config(image=imgs["hover"]))
        btn.bind("<Leave>", lambda e: btn.config(image=imgs[btn._kind3d]))
        return btn

    def set_pill_kind(self, btn, kind):
        btn._kind3d = kind
        btn.config(image=btn._imgs3d[kind], fg="#ffffff" if kind == "blue" else "#cbd5e1")

    def make_3d_badge(self, parent, glyph, color, bg="#111a2c", size=46):
        """A glossy 3D app-style tile with a glyph on top, for section headers."""
        c = tk.Canvas(parent, width=size, height=size + 3, bg=bg, highlightthickness=0)
        top = _hexc(_mix(_rgb(color), (255, 255, 255), 0.18))
        bot = _hexc(_mix(_rgb(color), (0, 0, 0), 0.45))
        edge = _hexc(_mix(_rgb(color), (255, 255, 255), 0.45))
        img = render_glossy(self.root, size, size + 3, top, bot, edge, bg, radius=12, shadow=3)
        c._img3d = img
        c.create_image(0, 0, image=img, anchor="nw")
        c.create_text(size / 2 + 1, size / 2 + 1, text=glyph, fill="#0b0f19", font=("Arial", 17, "bold"))
        c.create_text(size / 2, size / 2, text=glyph, fill="#ffffff", font=("Arial", 17, "bold"))
        return c


    # =========================================================================
    # SINGLE-WINDOW PAGE ROUTER & BACK BUTTON
    # =========================================================================
    def show_page(self, page_name, push_history=True):
        if page_name not in self.pages:
            return
        # Stop live playback if leaving Full Manual Edit
        if self.current_page_name == "manual_edit" and page_name != "manual_edit":
            self.stop_fme_live_playback()
            self.fme_close_popout(refresh_main=False)

        if push_history and self.current_page_name != page_name:
            self.nav_history.append(self.current_page_name)

        for k, frame in self.pages.items():
            frame.pack_forget()

        self.pages[page_name].pack(fill="both", expand=True)
        self.current_page_name = page_name

        titles = {
            "home": "🏠 Main Downloader Dashboard",
            "sync": "🎙️ Voice & Subtitle Sync Studio (Quick Timer & Auto 2D Sync)",
            "manual_edit": "🎛️ Full Manual 3-Track Edit Studio (Space = Play/Pause • Hold Shift = ✋ Move Track)",
            "queue": "🌙 Narto Drama 5-Movie Overnight Queue (Sequential 1-by-1)",
            "trim_crop": "✂️ HD Multi-Video Trim, Crop & Frame Scrubber Studio"
        }
        self.header_title_lbl.config(text=titles.get(page_name, "🎬 Nader Video Studio"))

        # Highlight active navigation button
        for k, btn in self.nav_buttons.items():
            self.set_pill_kind(btn, "blue" if k == page_name else "dark")

        if page_name == "home":
            self.set_pill_kind(self.back_btn, "dim")
            self.back_btn.config(state="disabled")
        else:
            self.set_pill_kind(self.back_btn, "blue")
            self.back_btn.config(state="normal")

        # Auto-populate video path when entering Sync or Manual Edit if empty
        if page_name == "sync" and not self.sync_vid_var.get().strip() and self.last_output_file and os.path.exists(self.last_output_file):
            self.sync_vid_var.set(self.last_output_file)
            auto_s = os.path.splitext(self.last_output_file)[0] + ".srt"
            if os.path.exists(auto_s):
                self.sync_sub_var.set(auto_s)

        if page_name == "manual_edit":
            cand_vid = self.sync_vid_var.get().strip() or self.last_output_file
            if cand_vid and os.path.exists(cand_vid) and not self.fme_v_path_var.get().strip():
                self.fme_v_path_var.set(cand_vid)
            self.root.after(80, self.fme_draw_timeline_full)

    def navigate_back(self):
        if self.nav_history:
            prev = self.nav_history.pop()
            self.show_page(prev, push_history=False)
        else:
            self.show_page("home", push_history=False)

    def on_app_close(self):
        self.stop_flag = True
        self.sync_stop_flag = True
        self.stop_fme_live_playback()
        self.fme_close_popout(refresh_main=False)
        for proc in list(getattr(self, "narto_claude_procs", ()) or ()):
            try: proc.terminate()
            except: pass
        if self.current_process:
            try: self.current_process.terminate()
            except: pass
        if self.sync_process:
            try: self.sync_process.terminate()
            except: pass
        self.root.destroy()

    # =========================================================================
    # PAGE 0: 🏠 MAIN DOWNLOADER DASHBOARD
    # =========================================================================
    def build_home_page(self):
        page = ttk.Frame(self.page_container)
        self.pages["home"] = page

        # --- 3D HERO BANNER WITH ENGINE HEALTH CHIPS ---
        self.build_home_banner(page)

        # --- SOURCE TABS (one glossy tab per site) ---
        self.home_tabs = ttk.Notebook(page)
        self.home_tabs.pack(fill="x", padx=14, pady=(8, 4))
        self._tab_icons = []

        def add_tab(title, color, glyph, heading, desc, link=None):
            tab = ttk.Frame(self.home_tabs, style="Panel.TFrame", padding=(16, 10, 16, 12))
            head = ttk.Frame(tab, style="Panel.TFrame")
            head.pack(fill="x", pady=(0, 8))
            self.make_3d_badge(head, glyph, color).pack(side="left", padx=(0, 12))
            txt = ttk.Frame(head, style="Panel.TFrame")
            txt.pack(side="left", fill="x")
            ttk.Label(txt, text=heading, style="Title.Panel.TLabel").pack(anchor="w")
            link_lbl = None
            if link:
                link_lbl = tk.Label(txt, text=link, font=("Arial", 9, "underline"), bg="#111a2c", fg="#38bdf8", cursor="hand2")
                link_lbl.pack(anchor="w")
                link_lbl.bind("<Button-1>", lambda e, u=link: webbrowser.open(u if u.startswith("http") else "https://" + u))
            ttk.Label(txt, text=desc, style="Muted.Panel.TLabel").pack(anchor="w")
            icon = render_sphere(self.root, 14, color, "#1a2338")
            self._tab_icons.append(icon)
            self.home_tabs.add(tab, text=f" {title}", image=icon, compound="left")
            return tab, link_lbl

        def btn_row(tab):
            f = ttk.Frame(tab, style="Panel.TFrame")
            f.pack(pady=(6, 0))
            return f

        # 1. SHORTMAX
        tab, self.lbl_shortmax = add_tab(
            "Shortmax", "#f97316", "S", "Shortmax Drama Downloader",
            "Paste a watch link. Browser cookies are tried automatically (Chrome, Edge, Firefox…).",
            link="https://shortmax.shorttw.live"
        )
        self.url_entry1 = self.create_url_row(tab, source_id="1", width=62, style="Panel.TFrame")
        btn_frame1 = btn_row(tab)
        ttk.Button(btn_frame1, text="🛡️ 1. Verify Bot Check", command=lambda: self.open_browser(1)).grid(row=0, column=0, padx=5)
        self.start_btn1 = ttk.Button(btn_frame1, text="⬇️ 2. Start Shortmax", style="Accent.TButton", command=lambda: self.start_thread(1))
        self.start_btn1.grid(row=0, column=1, padx=5)

        # 2. NARTO (ORIGINAL ENGINE — logic untouched)
        tab, self.lbl_narto = add_tab(
            "Narto (Original)", "#ec4899", "N", "narto-drama.com — Original Engine",
            "Your proven one-by-one downloader with token healing and merged .SRT subtitles.",
            link="https://narto-drama.com"
        )
        self.url_entry2 = self.create_url_row(tab, source_id="2", width=62, style="Panel.TFrame")
        btn_frame2 = btn_row(tab)
        self.start_btn2 = ttk.Button(btn_frame2, text="⬇️ Download Narto (Single)", style="Accent.TButton", command=lambda: self.start_thread(2))
        self.start_btn2.grid(row=0, column=0, padx=5)
        self.queue_narto_btn = ttk.Button(btn_frame2, text="🌙 Open 5-Movie Overnight Queue", command=lambda: self.show_page("queue"))
        self.queue_narto_btn.grid(row=0, column=1, padx=5)

        # 3. NARTO — CLAUDE VERSION (parallel turbo engine)
        tab, _ = add_tab(
            "Narto ⚡ Claude Version", "#a855f7", "⚡", "Narto-Drama.com — Claude Version (Turbo)",
            "Downloads several episodes at once with 16 fragments each, auto-refreshing tokens. Same merge and .SRT output.",
        )
        self.url_entry7 = self.create_url_row(tab, source_id="7", width=62, style="Panel.TFrame")
        btn_frame7 = btn_row(tab)
        self.start_btn_narto_claude = ttk.Button(btn_frame7, text="🚀 Turbo Download (Claude Version)", style="Success.TButton", command=self.start_narto_claude_thread)
        self.start_btn_narto_claude.grid(row=0, column=0, padx=5)
        ttk.Label(btn_frame7, text="Episodes at once:", style="Panel.TLabel").grid(row=0, column=1, padx=(14, 4))
        self.narto_claude_parallel_var = tk.IntVar(value=3)
        ttk.Spinbox(btn_frame7, from_=1, to=6, width=4, textvariable=self.narto_claude_parallel_var, state="readonly").grid(row=0, column=2)

        # 4. DAILYMOTION
        tab, self.lbl_dailymotion = add_tab(
            "Dailymotion", "#0ea5e9", "d", "Dailymotion — Highest Quality",
            "Best video + best audio, merged automatically.", link="https://www.dailymotion.com"
        )
        self.url_entry5 = self.create_url_row(tab, source_id="5", width=62, style="Panel.TFrame")
        btn_frame_dm = btn_row(tab)
        self.start_btn_dm = ttk.Button(btn_frame_dm, text="⬇️ Download Dailymotion (Max Quality)", style="Accent.TButton", command=lambda: self.start_thread(5))
        self.start_btn_dm.grid(row=0, column=0, padx=5)

        # 5. TIKTOK
        tab, self.lbl_tiktok = add_tab(
            "TikTok", "#14b8a6", "♪", "TikTok — Single URL or Auto-Bulk File",
            "Bulk mode reads your 'tiktok link graber' text file.", link="https://www.tiktok.com"
        )
        self.url_entry4 = self.create_url_row(tab, source_id="4", width=62, style="Panel.TFrame")
        btn_frame4 = btn_row(tab)
        self.start_btn4 = ttk.Button(btn_frame4, text="⬇️ Download Single TikTok", style="Accent.TButton", command=lambda: self.start_thread(4))
        self.start_btn4.grid(row=0, column=0, padx=5)
        self.start_btn5 = ttk.Button(btn_frame4, text="📦 Auto-Start Bulk TikTok ('tiktok link graber')", command=self.start_bulk_txt)
        self.start_btn5.grid(row=0, column=1, padx=5)

        # 6. DIRECT BYPASS
        tab, _ = add_tab(
            "Direct M3U8/MP4", "#22c55e", "▶", "Direct M3U8 / MP4 Bypass",
            "Paste a RAW .m3u8 or .mp4 link copied from the browser's network tab."
        )
        self.url_entry3 = self.create_url_row(tab, source_id="3", width=62, style="Panel.TFrame")
        btn_frame3 = btn_row(tab)
        self.start_btn3 = ttk.Button(btn_frame3, text="⬇️ Download Single Video", style="Accent.TButton", command=lambda: self.start_thread(3))
        self.start_btn3.grid(row=0, column=0, padx=5)

        # 7. TORRENT & MAGNET
        tab, _ = add_tab(
            "Torrent / Magnet", "#eab308", "⇣", "Torrent & Magnet Downloader (Aria2c 16x)",
            "Magnet link, info-hash, .torrent URL or local file. DHT + PEX + public trackers for peer boosting."
        )
        tor_row = ttk.Frame(tab, style="Panel.TFrame")
        tor_row.pack(pady=1)
        self.url_entry6 = self.build_url_controls_in_frame(tor_row, source_id="6", width=50)
        ttk.Button(tor_row, text="📄 Browse", width=9, command=self.browse_torrent_file).grid(row=0, column=4, padx=2)
        btn_frame6 = btn_row(tab)
        self.start_btn_torrent = ttk.Button(btn_frame6, text="🧲 Download Torrent / Magnet", style="Accent.TButton", command=self.start_torrent_thread)
        self.start_btn_torrent.grid(row=0, column=0, padx=5)
        self.torrent_seed_var = tk.BooleanVar(value=False)
        ttk.Checkbutton(btn_frame6, text="🌱 Keep Seeding After Download (Ratio 1.0 / Max 30 min)", variable=self.torrent_seed_var, style="Panel.TCheckbutton").grid(row=0, column=1, padx=10)

        # --- GLOBAL SETTINGS & ACCELERATOR (raised 3D card) ---
        settings_card = ttk.LabelFrame(page, text="⚙️ Download Settings, Sync-Lock & Subtitles", padding=(12, 6))
        settings_card.pack(fill="x", padx=14, pady=4)

        settings_frame = ttk.Frame(settings_card, style="Card.TFrame")
        settings_frame.pack(pady=2)

        ttk.Label(settings_frame, text="Start Ep:", font=("Arial", 10), background="#131b2e").grid(row=0, column=0, padx=5)
        self.start_entry = ttk.Entry(settings_frame, width=8)
        self.start_entry.grid(row=0, column=1, padx=5)
        self.start_entry.insert(0, "1")

        ttk.Label(settings_frame, text="Total Eps (Auto-Stop):", font=("Arial", 10), background="#131b2e").grid(row=0, column=2, padx=5)
        self.total_entry = ttk.Entry(settings_frame, width=8)
        self.total_entry.grid(row=0, column=3, padx=5)

        self.turbo_var = tk.BooleanVar(value=True)
        self.turbo_check = ttk.Checkbutton(
            settings_frame,
            text="⚡ Turbo Accelerator (16x Threads + Chunk Boost / Aria2c)",
            variable=self.turbo_var, style="Card.TCheckbutton"
        )
        self.turbo_check.grid(row=0, column=4, padx=(18, 5))

        opts_row = ttk.Frame(settings_card, style="Card.TFrame")
        opts_row.pack(pady=2)
        self.sync_lock_var = tk.BooleanVar(value=True)
        ttk.Checkbutton(
            opts_row,
            text="🔒 Sync-Lock Audio/Video On Every Episode & Merge (Prevents Middle Drift)",
            variable=self.sync_lock_var, style="Card.TCheckbutton"
        ).grid(row=0, column=0, padx=6)

        self.auto_sub_var = tk.BooleanVar(value=True)
        ttk.Checkbutton(
            opts_row,
            text="📝 Auto-Save Merged .SRT Subtitles (Narto)",
            variable=self.auto_sub_var, style="Card.TCheckbutton"
        ).grid(row=0, column=1, padx=6)

        # --- PRO STUDIO LAUNCHPAD (OPENS INSIDE SAME WINDOW) ---
        studio_card = ttk.LabelFrame(page, text="✨ Pro Video Studios (Open Inside This Window — Use Top Bar or Back Anytime)", padding=(12, 6))
        studio_card.pack(fill="x", padx=14, pady=4)
        studio_frame = ttk.Frame(studio_card, style="Card.TFrame")
        studio_frame.pack(pady=2)

        ttk.Button(studio_frame, text="🎙️ 1. Voice & Subtitle Sync Studio", style="Accent.TButton", command=lambda: self.show_page("sync")).grid(row=0, column=0, padx=5, pady=2)
        ttk.Button(studio_frame, text="🎛️ 2. Full Manual Edit (3-Track NLE)", style="Accent.TButton", command=lambda: self.show_page("manual_edit")).grid(row=0, column=1, padx=5, pady=2)
        ttk.Button(studio_frame, text="🌙 3. Narto 5-Movie Overnight Queue", command=lambda: self.show_page("queue")).grid(row=0, column=2, padx=5, pady=2)
        ttk.Button(studio_frame, text="✂️ 4. HD Trim & Crop Studio", command=lambda: self.show_page("trim_crop")).grid(row=0, column=3, padx=5, pady=2)

        # --- LIVE STATUS & PROGRESS METRICS ---
        status_card = ttk.LabelFrame(page, text="📡 Live Status", padding=(12, 6))
        status_card.pack(fill="x", padx=14, pady=4)

        self.status_label = tk.Label(status_card, text="Ready to download", font=("Arial", 12, "bold"), bg="#131b2e", fg="#38bdf8")
        self.status_label.pack(pady=(2, 4))

        self.progress_bar = ttk.Progressbar(status_card, orient='horizontal', mode='determinate', length=640)
        self.progress_bar.pack(pady=2)

        self.detail_label = tk.Label(status_card, text="", font=("Courier", 9), bg="#131b2e", fg="#94a3b8")
        self.detail_label.pack(pady=(2, 4))

        # --- CONTROLS ---
        control_frame = ttk.Frame(status_card, style="Card.TFrame")
        control_frame.pack(pady=2)

        self.stop_btn = ttk.Button(control_frame, text="🛑 Stop Download", style="Danger.TButton", command=self.stop_download, state="disabled")
        self.stop_btn.grid(row=0, column=0, padx=4, pady=2)

        self.merge_btn = ttk.Button(control_frame, text="📁 Select Folder to Merge", command=self.merge_folder)
        self.merge_btn.grid(row=0, column=1, padx=4, pady=2)

        self.stitch_btn = ttk.Button(control_frame, text="🔗 Stitch Multiple Videos", command=self.stitch_videos)
        self.stitch_btn.grid(row=0, column=2, padx=4, pady=2)

        ttk.Button(control_frame, text="▶️ Open Last File", command=self.open_last_file).grid(row=0, column=3, padx=4, pady=2)
        ttk.Button(control_frame, text="📂 Open Last Local Folder", command=self.open_last_local_folder).grid(row=0, column=4, padx=4, pady=2)
        ttk.Button(control_frame, text="📜 Open Error Log", command=self.open_log).grid(row=0, column=5, padx=4, pady=2)

    def build_home_banner(self, page):
        h = 76
        c = tk.Canvas(page, height=h, bg="#0b0f19", highlightthickness=0)
        c.pack(fill="x", padx=14, pady=(10, 2))
        bw = max(1200, min(2200, self.root.winfo_screenwidth()))
        left, mid, right = "#1e3a8a", "#5b21b6", "#111827"
        self._banner_img = render_banner(self.root, bw, h, left, mid, right)
        self._banner_logo = getattr(self, "_app_icon", None) or render_app_icon(self.root, 64)
        c.create_image(0, 0, image=self._banner_img, anchor="nw")
        c.create_line(0, 0, bw, 0, fill="#93c5fd")
        c.create_line(0, h - 1, bw, h - 1, fill="#020617")
        c.create_image(18, h // 2, image=self._banner_logo, anchor="w")
        for dx, col in ((2, "#020617"), (0, "#ffffff")):
            c.create_text(94 + dx, 26 + dx, text="Nader Video Studio", font=("Arial", 19, "bold"), fill=col, anchor="w")
        c.create_text(96, 54, text="Download  •  Sync  •  Edit  •  Torrent   —   Created by Nader Alkhansa", font=("Arial", 9), fill="#c7d2fe", anchor="w")

        # Version chip, placed after the title and blended onto the banner colour under it
        chip_x = 94 + tkfont.Font(family="Arial", size=19, weight="bold").measure("Nader Video Studio") + 14
        t = (chip_x + 30) / bw
        chip_bg = _hexc(_mix(_rgb(left), _rgb(mid), t / 0.55))
        self._banner_ver = render_glossy(self.root, 62, 22, "#34d399", "#047857", "#6ee7b7", chip_bg, radius=10, shadow=2)
        c.create_image(chip_x, 26, image=self._banner_ver, anchor="w")
        c.create_text(chip_x + 31, 25, text=self.version, font=("Arial", 9, "bold"), fill="#ffffff")

        # Engine health chips on the right (green = found, red = missing)
        yt = self.get_yt_dlp_path()
        engines = [
            ("yt-dlp", bool(yt and os.path.exists(yt))),
            ("ffmpeg", bool(shutil.which("ffmpeg") or shutil.which("ffmpeg.exe"))),
            ("aria2c", bool(self.get_aria2c_path())),
            ("curl", bool(shutil.which("curl") or shutil.which("curl.exe"))),
        ]
        self._banner_chips = []
        for name, ok in engines:
            txt = f"{'✓' if ok else '✗'} {name}"
            w = tkfont.Font(family="Arial", size=9, weight="bold").measure(txt) + 20
            img = render_glossy(self.root, w, 24, *(("#10b981", "#065f46", "#6ee7b7") if ok else ("#f43f5e", "#9f1239", "#fda4af")), right, radius=11, shadow=2)
            self._banner_chips.append((img, txt, w))

        def place_chips(event=None):
            c.delete("chips")
            x = c.winfo_width() - 16
            for img, txt, w in reversed(self._banner_chips):
                x -= w
                c.create_image(x, h // 2, image=img, anchor="w", tags="chips")
                c.create_text(x + w / 2, h // 2 - 1, text=txt, font=("Arial", 9, "bold"), fill="#ffffff", tags="chips")
                x -= 6
        c.bind("<Configure>", place_chips)


    # =========================================================================
    # PAGE 1: 🎙️ VOICE & SUBTITLE SYNC STUDIO (IN-WINDOW)
    # =========================================================================
    def build_voice_sync_page(self):
        page = ttk.Frame(self.page_container)
        self.pages["sync"] = page

        top_hdr = ttk.Frame(page)
        top_hdr.pack(fill="x", padx=16, pady=(8, 4))
        tk.Label(top_hdr, text="🎙️ Video & Audio Synchronization Studio", font=("Arial", 14, "bold"), bg="#0b0f19", fg="#f8fafc").pack(side="left")
        ttk.Button(
            top_hdr, text="🎛️ Switch to Full Manual Edit (Separate Voice, Music & Video)",
            style="Accent.TButton", command=lambda: self.show_page("manual_edit")
        ).pack(side="right", padx=4)

        self.sync_vid_var = tk.StringVar()
        self.sync_sub_var = tk.StringVar()
        self.sync_last_out = {"path": ""}

        file_box = ttk.LabelFrame(page, text="1. Select ORIGINAL Video & Optional Subtitle File (.srt / .vtt — Leave blank if hardcoded on screen)", padding=10)
        file_box.pack(fill="x", padx=16, pady=4)

        def pick_video_and_auto_sub():
            chosen = filedialog.askopenfilename(initialdir=self.output_base, filetypes=[("Video files", "*.mp4 *.mkv *.mov")])
            if chosen:
                self.sync_vid_var.set(chosen)
                self.fme_v_path_var.set(chosen)
                matching_srt = os.path.splitext(chosen)[0] + ".srt"
                if os.path.exists(matching_srt):
                    self.sync_sub_var.set(matching_srt)

        ttk.Label(file_box, text="Video File (.mp4):", background="#131b2e").grid(row=0, column=0, sticky="w", padx=4, pady=4)
        ttk.Entry(file_box, textvariable=self.sync_vid_var, width=76).grid(row=0, column=1, padx=6, pady=4)
        ttk.Button(file_box, text="📂 Browse Video", command=pick_video_and_auto_sub).grid(row=0, column=2, padx=4, pady=4)

        ttk.Label(file_box, text="Subtitle (.srt/.vtt):", background="#131b2e").grid(row=1, column=0, sticky="w", padx=4, pady=4)
        ttk.Entry(file_box, textvariable=self.sync_sub_var, width=76).grid(row=1, column=1, padx=6, pady=4)
        ttk.Button(
            file_box, text="📂 Browse Subtitle",
            command=lambda: self.sync_sub_var.set(filedialog.askopenfilename(initialdir=self.output_base, filetypes=[("Subtitle files", "*.srt *.vtt *.ass")]) or self.sync_sub_var.get())
        ).grid(row=1, column=2, padx=4, pady=4)

        # --- Option A: Exact Timer Sync ---
        manual_box = ttk.LabelFrame(page, text="2. Option A: Exact Timer Sync (Fixes Whole Movie From Start to End)", padding=10)
        manual_box.pack(fill="x", padx=16, pady=5)

        ttk.Label(manual_box, text="Sync Mode:", font=("Arial", 9, "bold"), background="#131b2e").grid(row=0, column=0, sticky="w", padx=5, pady=2)
        sync_mode_var = tk.StringVar(value="progressive")
        mode_frame = ttk.Frame(manual_box, style="Card.TFrame")
        mode_frame.grid(row=0, column=1, columnspan=3, sticky="w", pady=2)

        ttk.Radiobutton(
            mode_frame,
            text="🔥 Progressive Speed-Lock (Best: Video starts OK at 00:00, then sound drifts further away as time moves)",
            variable=sync_mode_var, value="progressive"
        ).pack(anchor="w")
        ttk.Radiobutton(
            mode_frame,
            text="↔️ Constant Flat Shift Only (Use if sound is off by the exact same seconds everywhere)",
            variable=sync_mode_var, value="flat"
        ).pack(anchor="w")

        ttk.Label(manual_box, text="🎬 Video Exact Time (Subtitle/Lips on Screen):", font=("Arial", 10, "bold"), background="#131b2e").grid(row=1, column=0, sticky="w", padx=5, pady=4)
        v_time1_ent = ttk.Entry(manual_box, width=16)
        v_time1_ent.grid(row=1, column=1, sticky="w", padx=5, pady=4)
        v_time1_ent.insert(0, "00:03:36.000")

        ttk.Label(manual_box, text="🔊 Audio Exact Time (When You Hear the Word):", font=("Arial", 10, "bold"), background="#131b2e").grid(row=2, column=0, sticky="w", padx=5, pady=4)
        a_time1_ent = ttk.Entry(manual_box, width=16)
        a_time1_ent.grid(row=2, column=1, sticky="w", padx=5, pady=4)
        a_time1_ent.insert(0, "00:03:44.500")

        calc_preview_lbl = tk.Label(
            manual_box,
            text="🎯 Whole-Movie Speed-Lock: Audio is drifting 2.36s/min (Speed Ratio: 1.03935x) ➔ Will speed-lock entire movie!",
            font=("Arial", 9, "bold"), bg="#131b2e", fg="#10b981"
        )
        calc_preview_lbl.grid(row=3, column=0, columnspan=4, sticky="w", padx=5, pady=3)

        use_2pt_var = tk.BooleanVar(value=False)
        tk.Checkbutton(
            manual_box,
            text="Optional: Add 2nd Checkpoint Later in Movie (Locks 00:00 ➔ Point 1 ➔ Point 2 ➔ End separately)",
            variable=use_2pt_var, bg="#131b2e", fg="#f1f5f9", selectcolor="#1e293b", activebackground="#131b2e", activeforeground="#ffffff"
        ).grid(row=4, column=0, columnspan=4, sticky="w", padx=5, pady=(4, 2))

        ttk.Label(manual_box, text="🎬 Point 2 Video Time (e.g. around min 15):", background="#131b2e").grid(row=5, column=0, sticky="w", padx=5, pady=2)
        v_time2_ent = ttk.Entry(manual_box, width=16)
        v_time2_ent.grid(row=5, column=1, sticky="w", padx=5, pady=2)
        v_time2_ent.insert(0, "00:15:00.000")

        ttk.Label(manual_box, text="🔊 Point 2 Audio Time (When heard at min 15):", background="#131b2e").grid(row=6, column=0, sticky="w", padx=5, pady=2)
        a_time2_ent = ttk.Entry(manual_box, width=16)
        a_time2_ent.grid(row=6, column=1, sticky="w", padx=5, pady=2)
        a_time2_ent.insert(0, "00:15:35.400")

        def update_calc_banner(*_):
            try:
                tv = parse_time_to_seconds(v_time1_ent.get())
                ta = parse_time_to_seconds(a_time1_ent.get())
                diff = tv - ta
                if sync_mode_var.get() == "progressive" and tv > 5.0 and ta > 5.0:
                    ratio = ta / tv
                    drift_per_min = ((ta - tv) / (tv / 60.0))
                    calc_preview_lbl.config(
                        text=f"🎯 Whole-Movie Speed-Lock: Audio drifts {drift_per_min:+.2f}s/min (Speed Ratio: {ratio:.5f}x) ➔ Locks 00:00, {v_time1_ent.get().strip()}, and rest of movie!",
                        fg="#10b981"
                    )
                else:
                    calc_preview_lbl.config(
                        text=f"🎯 Constant Flat Shift: Shifts entire audio track by {diff:+.3f}s without changing speed.",
                        fg="#38bdf8"
                    )
            except:
                calc_preview_lbl.config(text="⚠️ Enter valid time format (HH:MM:SS.mmm or MM:SS)", fg="#f43f5e")

        v_time1_ent.bind("<KeyRelease>", update_calc_banner)
        a_time1_ent.bind("<KeyRelease>", update_calc_banner)
        sync_mode_var.trace_add("write", update_calc_banner)

        manual_btn_col = ttk.Frame(manual_box, style="Card.TFrame")
        manual_btn_col.grid(row=1, column=2, rowspan=2, padx=16, pady=2)
        test_10s_btn = ttk.Button(manual_btn_col, text="🎧 Preview 20s Test Clip at Video Time", width=34)
        test_10s_btn.pack(pady=3)
        manual_btn = ttk.Button(manual_btn_col, text="⚡ Sync & Save FULL Movie (Start to End)", style="Accent.TButton", width=34)
        manual_btn.pack(pady=3)

        # --- Option B & C: Auto Hardcoded/SRT Subtitle-Voice Alignment ---
        auto_box = ttk.LabelFrame(page, text="3. Option B & C: Auto 2D Speed+Offset Subtitle Sync & Mid-Video Drift Repair", padding=10)
        auto_box.pack(fill="x", padx=16, pady=5)

        ttk.Label(
            auto_box,
            text="• Auto 2D Speed+Offset Subtitle Sync: Works with .SRT files OR Hardcoded On-Screen Subtitles! Automatically tests both\n"
                 "  speed ratios (0.94x–1.06x) and offsets (-15s to +15s) across the entire movie.\n"
                 "• Deep Drift Repair: Rebuilds corrupted timestamps & locks constant frame rate + 48kHz audio clock across the whole video.",
            font=("Arial", 9), background="#131b2e", justify="left"
        ).pack(anchor="w", pady=(0, 8))

        auto_btn_row = ttk.Frame(auto_box, style="Card.TFrame")
        auto_btn_row.pack(fill="x")

        sub_sync_btn = ttk.Button(auto_btn_row, text="📖 Auto-Sync Voice with Subtitles (2D Speed + Offset Lock)", style="Accent.TButton")
        sub_sync_btn.pack(side="left", padx=4)

        drift_repair_btn = ttk.Button(auto_btn_row, text="🔧 Auto-Repair Mid-Video Audio Drift")
        drift_repair_btn.pack(side="left", padx=4)

        sync_status = tk.Label(page, text="Select your ORIGINAL video to begin.", font=("Arial", 10, "bold"), bg="#0b0f19", fg="#38bdf8")
        sync_status.pack(pady=(8, 3))

        sync_prog = ttk.Progressbar(page, orient="horizontal", mode="indeterminate", length=620)
        sync_prog.pack(pady=3)

        open_bar = ttk.Frame(page)
        open_bar.pack(pady=6)

        stop_sync_btn = ttk.Button(open_bar, text="🛑 Stop / Cancel Sync", style="Danger.TButton", state="disabled")
        stop_sync_btn.grid(row=0, column=0, padx=6)

        ttk.Button(
            open_bar, text="▶️ Open Last Synced Video",
            command=lambda: self.open_last_file(self.sync_last_out["path"] or self.last_output_file)
        ).grid(row=0, column=1, padx=6)
        ttk.Button(
            open_bar, text="📂 Open Local Folder of Synced Video",
            command=lambda: self.open_last_local_folder(self.sync_last_out["path"] or self.last_output_file)
        ).grid(row=0, column=2, padx=6)
        ttk.Button(
            open_bar, text="🎛️ Open Full Manual Edit Studio", style="Accent.TButton",
            command=lambda: self.show_page("manual_edit")
        ).grid(row=0, column=3, padx=6)

        def do_stop_sync():
            self.stop_sync_task()
            sync_prog.stop()
            stop_sync_btn.config(state="disabled")
            sync_status.config(text="🛑 Sync process stopped by user.", fg="#f43f5e")

        stop_sync_btn.config(command=do_stop_sync)

        def build_manual_audio_filter(t_v1, t_a1):
            mode = sync_mode_var.get()
            if use_2pt_var.get():
                t_v2 = parse_time_to_seconds(v_time2_ent.get())
                t_a2 = parse_time_to_seconds(a_time2_ent.get())
                if t_v2 > t_v1 + 2.0 and t_a2 > t_a1 + 2.0:
                    if mode == "progressive" and t_v1 > 2.0 and t_a1 > 2.0:
                        ratio1 = t_a1 / t_v1
                        ratio2 = (t_a2 - t_a1) / (t_v2 - t_v1)
                        at1 = build_atempo_chain(ratio1)
                        at2 = build_atempo_chain(ratio2)
                        af = (
                            f"aresample=async=1:first_pts=0,asplit=2[a1][a2];"
                            f"[a1]atrim=0:{t_a1:.3f},asetpts=PTS-STARTPTS,{at1}[p1];"
                            f"[a2]atrim=start={t_a1:.3f},asetpts=PTS-STARTPTS,{at2}[p2];"
                            f"[p1][p2]concat=n=2:v=0:a=1,asetpts=PTS-STARTPTS,apad"
                        )
                        return af, f"2-Point Speed-Lock (Seg1: {ratio1:.5f}x, Seg2: {ratio2:.5f}x)"
                    else:
                        ratio = (t_a2 - t_a1) / (t_v2 - t_v1)
                        offset_sec = t_v1 - (t_a1 / ratio)
                        at_chain = build_atempo_chain(ratio)
                        if offset_sec < 0:
                            cut_s = abs(offset_sec)
                            af = f"aresample=async=1:first_pts=0,{at_chain},atrim=start={cut_s:.3f},asetpts=PTS-STARTPTS,apad"
                        else:
                            d_ms = int(round(offset_sec * 1000))
                            af = f"aresample=async=1:first_pts=0,{at_chain},adelay={d_ms}|{d_ms},asetpts=PTS-STARTPTS,apad"
                        return af, f"2-Point Linear Lock (Speed: {ratio:.5f}x, Offset: {offset_sec:+.2f}s)"

            if mode == "progressive" and t_v1 > 2.0 and t_a1 > 2.0:
                ratio = t_a1 / t_v1
                at_chain = build_atempo_chain(ratio)
                af = f"aresample=async=1:first_pts=0,{at_chain},asetpts=PTS-STARTPTS,apad"
                return af, f"Whole-Movie Speed-Lock ({ratio:.5f}x)"

            offset_sec = t_v1 - t_a1
            if offset_sec < 0:
                cut_sec = abs(offset_sec)
                af = f"aresample=async=1:first_pts=0,atrim=start={cut_sec:.3f},asetpts=PTS-STARTPTS,apad"
            else:
                delay_ms = int(round(offset_sec * 1000))
                if delay_ms > 0:
                    af = f"aresample=async=1:first_pts=0,adelay={delay_ms}|{delay_ms},asetpts=PTS-STARTPTS,apad"
                else:
                    af = "aresample=async=1:first_pts=0,asetpts=PTS-STARTPTS,apad"
            return af, f"Flat Shift ({offset_sec:+.3f}s)"

        def preview_20s_manual_test():
            v_path = self.sync_vid_var.get().strip()
            if not v_path or not os.path.exists(v_path):
                messagebox.showerror("Error", "Please select a valid video file first.")
                return
            try:
                t_v1 = parse_time_to_seconds(v_time1_ent.get())
                t_a1 = parse_time_to_seconds(a_time1_ent.get())
                af_chain, summary_desc = build_manual_audio_filter(t_v1, t_a1)
            except Exception as e:
                messagebox.showerror("Time Format Error", str(e))
                return

            self.sync_stop_flag = False
            stop_sync_btn.config(state="normal")
            sync_prog.start(12)
            preview_start = max(0.0, t_v1 - 2.0)
            temp_test = os.path.join(self.output_base, "_temp_20s_sync_test.mp4")
            sync_status.config(text=f"Generating 20s test preview ({summary_desc})...", fg="#f59e0b")

            def worker():
                cmd = [
                    "ffmpeg", "-y", "-i", v_path, "-af", af_chain,
                    "-ss", f"{preview_start:.3f}", "-t", "20",
                    "-map", "0:v:0", "-map", "0:a:0",
                    "-c:v", "libx264", "-preset", "ultrafast", "-crf", "20",
                    "-c:a", "aac", "-b:a", "192k", temp_test
                ]
                res = self.run_sync_cancellable_ffmpeg(cmd)
                sync_prog.stop()
                stop_sync_btn.config(state="disabled")
                if self.sync_stop_flag:
                    return
                if res.returncode == 0 and os.path.exists(temp_test):
                    sync_status.config(text=f"▶️ Playing 20s Test Clip ({summary_desc})!", fg="#10b981")
                    self.open_last_file(temp_test)
                else:
                    sync_status.config(text="❌ Preview failed. Check Log.", fg="#f43f5e")

            threading.Thread(target=worker, daemon=True).start()

        def run_manual_sync():
            v_path = self.sync_vid_var.get().strip()
            if not v_path or not os.path.exists(v_path):
                messagebox.showerror("Error", "Please select a valid video file first.")
                return
            try:
                t_v1 = parse_time_to_seconds(v_time1_ent.get())
                t_a1 = parse_time_to_seconds(a_time1_ent.get())
                af_chain, summary_desc = build_manual_audio_filter(t_v1, t_a1)
            except Exception as e:
                messagebox.showerror("Time Format Error", str(e))
                return

            self.sync_stop_flag = False
            stop_sync_btn.config(state="normal")
            target_dir = self.get_organized_output_dir(v_path, "2_Voice_Synced")
            clean_base = clean_folder_Title(v_path)
            out_path = os.path.join(target_dir, f"{clean_base}_ManualSynced.mp4")

            sync_status.config(text=f"Applying {summary_desc} to FULL movie -> Saving to organized folder...", fg="#f59e0b")
            sync_prog.start(12)

            def worker():
                try:
                    cmd = [
                        "ffmpeg", "-y", "-i", v_path,
                        "-map", "0:v:0", "-map", "0:a:0",
                        "-c:v", "copy", "-af", af_chain,
                        "-c:a", "aac", "-b:a", "192k", "-ar", "48000",
                        "-shortest", "-movflags", "+faststart", "-avoid_negative_ts", "make_zero",
                        out_path
                    ]
                    res = self.run_sync_cancellable_ffmpeg(cmd)
                    sync_prog.stop()
                    stop_sync_btn.config(state="disabled")
                    if self.sync_stop_flag:
                        return
                    if res.returncode == 0 and os.path.exists(out_path):
                        self.sync_last_out["path"] = out_path
                        self.record_last_output(out_path)
                        sync_status.config(text=f"✅ Full Movie Synced ({summary_desc}): {os.path.basename(out_path)}", fg="#10b981")
                        self.log_message(f"MANUAL VOICE SYNC COMPLETED ({summary_desc}): {out_path}")
                    else:
                        sync_status.config(text="❌ FFmpeg Sync Failed. Check Error Log.", fg="#f43f5e")
                        self.log_message(f"Manual Sync Error:\n{res.stderr}")
                except Exception as ex:
                    sync_prog.stop()
                    stop_sync_btn.config(state="disabled")
                    sync_status.config(text=f"Error: {str(ex)}", fg="#f43f5e")

            threading.Thread(target=worker, daemon=True).start()

        def run_auto_subtitle_sync():
            v_path = self.sync_vid_var.get().strip()
            s_path = self.sync_sub_var.get().strip()
            if not v_path or not os.path.exists(v_path):
                messagebox.showerror("Error", "Please select a video file first.")
                return

            self.sync_stop_flag = False
            stop_sync_btn.config(state="normal")
            sync_status.config(text="Step 1/3: Detecting subtitle timestamps (SRT or Hardcoded On-Screen Text)...", fg="#f59e0b")
            sync_prog.start(12)

            def worker():
                try:
                    temp_sub = s_path
                    extracted_temp = False
                    if not temp_sub or not os.path.exists(temp_sub):
                        auto_srt = os.path.splitext(v_path)[0] + ".srt"
                        if os.path.exists(auto_srt):
                            temp_sub = auto_srt
                        else:
                            temp_sub = os.path.join(self.output_base, "temp_extracted_sub.srt")
                            ext_cmd = ["ffmpeg", "-y", "-i", v_path, "-map", "0:s:0", temp_sub]
                            self.run_sync_cancellable_ffmpeg(ext_cmd)
                            extracted_temp = True

                    if self.sync_stop_flag:
                        return

                    sub_onsets = []
                    sub_source_label = "SRT File"
                    if os.path.exists(temp_sub) and os.path.getsize(temp_sub) > 20:
                        with open(temp_sub, "r", encoding="utf-8", errors="ignore") as sf:
                            sub_text = sf.read()
                        for m in re.finditer(r'(\d{1,2}:\d{2}:\d{2}[,\.]\d{2,3})\s*-->', sub_text):
                            ts_clean = m.group(1).replace(",", ".")
                            try:
                                sub_onsets.append(parse_time_to_seconds(ts_clean))
                            except:
                                pass
                    if extracted_temp and os.path.exists(temp_sub):
                        try: os.remove(temp_sub)
                        except: pass

                    if not sub_onsets and not self.sync_stop_flag:
                        sub_source_label = "Hardcoded On-Screen Subtitles"
                        sub_onsets = self.detect_hardcoded_subtitle_onsets(
                            v_path,
                            status_callback=lambda msg: self.root.after(0, lambda: sync_status.config(text=msg, fg="#f59e0b"))
                        )

                    if self.sync_stop_flag:
                        return

                    self.root.after(0, lambda: sync_status.config(text="Step 2/3: Scanning human speech vocal frequencies (300Hz-3400Hz)...", fg="#f59e0b"))
                    detect_cmd = [
                        "ffmpeg", "-i", v_path,
                        "-af", "highpass=f=300,lowpass=f=3400,silencedetect=noise=-30dB:d=0.22",
                        "-f", "null", "-"
                    ]
                    det_res = self.run_sync_cancellable_ffmpeg(detect_cmd)
                    if self.sync_stop_flag:
                        return
                    voice_onsets = [float(m.group(1)) for m in re.finditer(r'silence_end:\s*(\d+(?:\.\d+)?)', det_res.stderr or "")]

                    target_dir = self.get_organized_output_dir(v_path, "2_Voice_Synced")
                    clean_base = clean_folder_Title(v_path)
                    out_path = os.path.join(target_dir, f"{clean_base}_AutoSubSynced.mp4")

                    if len(sub_onsets) >= 5 and len(voice_onsets) >= 5:
                        self.root.after(0, lambda: sync_status.config(text=f"Step 3/3: Running 2D Speed + Offset Grid Search across {len(sub_onsets)} {sub_source_label}...", fg="#f59e0b"))

                        step_idx = max(1, len(sub_onsets) // 120)
                        sampled_subs = sub_onsets[::step_idx]

                        best_ratio = 1.0
                        best_offset = 0.0
                        best_total_score = -1.0

                        candidate_ratios = [1.0 + (k * 0.001) for k in range(-50, 51)]
                        for r_cand in candidate_ratios:
                            scaled_voice = [vo / r_cand for vo in voice_onsets]
                            bins = {}
                            for st in sampled_subs:
                                for sv in scaled_voice:
                                    diff = st - sv
                                    if -8.0 <= diff <= 8.0:
                                        b_idx = round(diff * 10)
                                        bins[b_idx] = bins.get(b_idx, 0) + 1
                            if bins:
                                top_bin, top_count = max(bins.items(), key=lambda x: x[1])
                                score = top_count + 0.5 * bins.get(top_bin - 1, 0) + 0.5 * bins.get(top_bin + 1, 0)
                                if score > best_total_score:
                                    best_total_score = score
                                    best_ratio = r_cand
                                    best_offset = top_bin / 10.0

                        at_chain = build_atempo_chain(best_ratio)
                        if best_offset < -0.05:
                            cut_s = abs(best_offset)
                            af_filter = f"aresample=async=1:first_pts=0,{at_chain},atrim=start={cut_s:.3f},asetpts=PTS-STARTPTS,apad"
                        elif best_offset > 0.05:
                            d_ms = int(round(best_offset * 1000))
                            af_filter = f"aresample=async=1:first_pts=0,{at_chain},adelay={d_ms}|{d_ms},asetpts=PTS-STARTPTS,apad"
                        else:
                            af_filter = f"aresample=async=1:first_pts=0,{at_chain},asetpts=PTS-STARTPTS,apad"

                        msg_detail = f"2D {sub_source_label} Sync (Speed: {best_ratio:.4f}x, Initial Offset: {best_offset:+.2f}s)"

                        cmd = [
                            "ffmpeg", "-y", "-i", v_path,
                            "-map", "0:v:0", "-map", "0:a:0",
                            "-c:v", "copy", "-af", af_filter,
                            "-c:a", "aac", "-b:a", "192k", "-ar", "48000",
                            "-shortest", "-movflags", "+faststart", "-avoid_negative_ts", "make_zero",
                            out_path
                        ]
                    else:
                        cmd = [
                            "ffmpeg", "-y", "-fflags", "+genpts", "-i", v_path,
                            "-map", "0:v:0", "-map", "0:a:0",
                            "-fps_mode", "cfr", "-c:v", "libx264", "-preset", "fast", "-crf", "18",
                            "-af", "aresample=async=1000:min_hard_comp=0.010000:first_pts=0,apad",
                            "-c:a", "aac", "-b:a", "192k", "-ar", "48000",
                            "-shortest", out_path
                        ]
                        msg_detail = "Full-Video CFR + Audio Clock Drift Repair"

                    res = self.run_sync_cancellable_ffmpeg(cmd)
                    sync_prog.stop()
                    stop_sync_btn.config(state="disabled")
                    if self.sync_stop_flag:
                        return
                    if res.returncode == 0 and os.path.exists(out_path):
                        self.sync_last_out["path"] = out_path
                        self.record_last_output(out_path)
                        sync_status.config(text=f"✅ {msg_detail} -> {os.path.basename(out_path)}", fg="#10b981")
                        self.log_message(f"AUTO VOICE SYNC COMPLETED ({msg_detail}): {out_path}")
                    else:
                        sync_status.config(text="❌ Auto Sync Failed. Check Error Log.", fg="#f43f5e")
                        self.log_message(f"Auto Sync Error:\n{res.stderr}")
                except Exception as ex:
                    sync_prog.stop()
                    stop_sync_btn.config(state="disabled")
                    sync_status.config(text=f"Error: {str(ex)}", fg="#f43f5e")

            threading.Thread(target=worker, daemon=True).start()

        def run_mid_video_drift_repair():
            v_path = self.sync_vid_var.get().strip()
            if not v_path or not os.path.exists(v_path):
                messagebox.showerror("Error", "Please select a video file first.")
                return

            self.sync_stop_flag = False
            stop_sync_btn.config(state="normal")
            target_dir = self.get_organized_output_dir(v_path, "2_Voice_Synced")
            clean_base = clean_folder_Title(v_path)
            out_path = os.path.join(target_dir, f"{clean_base}_DriftRepaired.mp4")

            sync_status.config(text="Rebuilding video/audio timestamps & locking CFR clock across whole video...", fg="#f59e0b")
            sync_prog.start(12)

            def worker():
                cmd = [
                    "ffmpeg", "-y", "-fflags", "+genpts", "-i", v_path,
                    "-map", "0:v:0", "-map", "0:a:0",
                    "-fps_mode", "cfr", "-c:v", "libx264", "-preset", "fast", "-crf", "18",
                    "-af", "aresample=async=1000:min_hard_comp=0.010000:first_pts=0,apad",
                    "-c:a", "aac", "-b:a", "192k", "-ar", "48000",
                    "-shortest", out_path
                ]
                res = self.run_sync_cancellable_ffmpeg(cmd)
                sync_prog.stop()
                stop_sync_btn.config(state="disabled")
                if self.sync_stop_flag:
                    return
                if res.returncode == 0 and os.path.exists(out_path):
                    self.sync_last_out["path"] = out_path
                    self.record_last_output(out_path)
                    sync_status.config(text=f"✅ Mid-Video Drift Repaired: {os.path.basename(out_path)}", fg="#10b981")
                    self.log_message(f"DRIFT REPAIR COMPLETED: {out_path}")
                else:
                    sync_status.config(text="❌ Drift Repair Failed. Check Log.", fg="#f43f5e")
                    self.log_message(f"Drift Repair Error:\n{res.stderr}")

            threading.Thread(target=worker, daemon=True).start()

        test_10s_btn.config(command=preview_20s_manual_test)
        manual_btn.config(command=run_manual_sync)
        sub_sync_btn.config(command=run_auto_subtitle_sync)
        drift_repair_btn.config(command=run_mid_video_drift_repair)

    # =========================================================================
    # PAGE 2: 🎛️ FULL MANUAL EDIT (60FPS TIMELINE + SPACE PLAY/PAUSE + SHIFT HAND DRAG)
    # =========================================================================
    def build_full_manual_edit_page(self):
        page = ttk.Frame(self.page_container)
        self.pages["manual_edit"] = page

        self.fme_state = {
            "video_path": "",
            "duration": 60.0,
            "voice_stem": "",
            "bgm_stem": "",
            "video_clips": [],  # [{id, src_start, duration, tl_start, speed, label}]
            "voice_clips": [],  # [{id, src_start, duration, tl_start, speed, label}]
            "bgm_clips": [],    # [{id, src_start, duration, tl_start, speed, label}]
            "selected_track": "voice",  # "video", "voice", or "bgm"
            "selected_idx": 0,
            "clipboard_clip": None,
            "undo_stack": [],
            "playhead": 0.0,
            "is_playing": False,
            "play_wall_start": 0.0,
            "play_media_start": 0.0,
            "shift_hand_active": False,
            "photo": None,
            "rendering_frame": False,
            "last_frame_req_time": 0.0,
            "drag_mode": None,      # "playhead" or "clip"
            "drag_start_x": None,
            "drag_orig_tl": 0.0,
            "last_saved": "",
            "pop_win": None,        # Toplevel of the pop-out live monitor
            "pop_canvas": None,
            "pop_photo": None,
            "pop_seq": 0,           # newest requested pop-out frame
            "pop_shown_seq": 0,     # newest pop-out frame already on screen
            "pop_resize_job": None
        }

        # --- Top Bar: Load Video & Shortcut Guide ---
        top_box = ttk.LabelFrame(page, text="1. Load Video & Automatic 3-Track Stem Separation (Video Alone + Voice Alone + Music Alone)", padding=6)
        top_box.pack(fill="x", padx=12, pady=3)

        self.fme_v_path_var = tk.StringVar()
        ttk.Label(top_box, text="Video File:", background="#131b2e").grid(row=0, column=0, padx=4, pady=2, sticky="w")
        ttk.Entry(top_box, textvariable=self.fme_v_path_var, width=64).grid(row=0, column=1, padx=4, pady=2)

        sep_mode_var = tk.StringVar(value="separate")
        ttk.Radiobutton(
            top_box, text="🎙️+🎵 Separate Voice & Background Music (3 Independent Tracks)",
            variable=sep_mode_var, value="separate"
        ).grid(row=1, column=0, columnspan=2, sticky="w", padx=4)
        ttk.Radiobutton(
            top_box, text="🔊 Fast Mode: Full Audio on Voice Track (Instant Load)",
            variable=sep_mode_var, value="full"
        ).grid(row=1, column=2, columnspan=2, sticky="w", padx=4)

        # --- 2. Live Player Monitor & Playhead Controls ---
        prev_box = ttk.LabelFrame(page, text="2. Live Monitor & Fast Scrubber (Press SPACE to Play/Pause • Hold SHIFT to Grab & Slide Any Track)", padding=6)
        prev_box.pack(fill="x", padx=12, pady=3)

        self.fme_frame_canvas = tk.Canvas(prev_box, width=310, height=174, bg="#070a12", highlightthickness=1, highlightbackground="#38bdf8")
        self.fme_frame_canvas.grid(row=0, column=0, rowspan=4, padx=(4, 12), pady=2)
        self.fme_frame_canvas.create_text(
            155, 87,
            text="Load video to preview\n• Press SPACE to Play/Pause\n• Hold SHIFT to Drag Tracks",
            fill="#94a3b8", font=("Arial", 9, "bold"), justify="center"
        )

        scrub_ctrl = ttk.Frame(prev_box, style="Card.TFrame")
        scrub_ctrl.grid(row=0, column=1, sticky="ew")
        prev_box.columnconfigure(1, weight=1)

        top_status_row = ttk.Frame(scrub_ctrl, style="Card.TFrame")
        top_status_row.pack(fill="x", pady=(0, 2))

        self.fme_playhead_lbl = tk.Label(
            top_status_row, text="📍 Playhead: 00:00:00.000  /  00:00:00.000",
            font=("Courier", 10, "bold"), bg="#131b2e", fg="#f43f5e"
        )
        self.fme_playhead_lbl.pack(side="left")

        self.fme_hand_badge = tk.Label(
            top_status_row,
            text="✋ Hold SHIFT = Hand Tool (Slide Video, Voice, or Music Alone)",
            font=("Arial", 9, "bold"), bg="#1e293b", fg="#38bdf8", padx=8, pady=2
        )
        self.fme_hand_badge.pack(side="right", padx=4)

        self.fme_playhead_var = tk.DoubleVar(value=0.0)
        self.fme_playhead_scale = tk.Scale(
            scrub_ctrl, variable=self.fme_playhead_var, from_=0.0, to=100.0, resolution=0.02,
            orient="horizontal", length=640, showvalue=False,
            bg="#131b2e", fg="#f8fafc", troughcolor="#0f172a", highlightthickness=0, activebackground="#f43f5e",
            command=lambda val: self.fme_on_scale_drag(float(val))
        )
        self.fme_playhead_scale.pack(fill="x", pady=2)

        ph_btn_row = ttk.Frame(scrub_ctrl, style="Card.TFrame")
        ph_btn_row.pack(fill="x", pady=3)

        self.fme_play_btn = ttk.Button(
            ph_btn_row, text="▶️ Play (Space)", style="Accent.TButton", width=15,
            command=self.toggle_fme_play_pause
        )
        self.fme_play_btn.pack(side="left", padx=(0, 6))

        for lbl_b, d_s in [("⏪ -5s", -5.0), ("-1s", -1.0), ("◀ -0.1s", -0.1), ("▶ +0.1s", 0.1), ("+1s", 1.0), ("⏩ +5s", 5.0)]:
            ttk.Button(ph_btn_row, text=lbl_b, width=7, command=lambda d=d_s: self.fme_step_playhead(d)).pack(side="left", padx=1)

        ttk.Button(
            ph_btn_row, text="🔍 Pop-Out", style="Accent.TButton",
            command=self.fme_toggle_popout
        ).pack(side="left", padx=(10, 1))

        self.fme_hand_lock_var = tk.BooleanVar(value=False)
        tk.Checkbutton(
            ph_btn_row, text="✋ Lock Hand Tool On", variable=self.fme_hand_lock_var,
            bg="#131b2e", fg="#fbbf24", selectcolor="#1e293b", font=("Arial", 9, "bold"),
            command=self.fme_update_hand_mode_ui
        ).pack(side="right", padx=4)

        # --- 3. 60FPS Interactive 3-Track Timeline Canvas ---
        tl_box = ttk.LabelFrame(
            page,
            text="3. 60FPS Multi-Track Timeline — Drag Top Ruler for Playhead • Hold SHIFT (✋) to Drag Video Alone, Voice Alone, or Music Alone",
            padding=6
        )
        tl_box.pack(fill="x", padx=12, pady=3)

        self.fme_tl_canvas = tk.Canvas(tl_box, width=1000, height=182, bg="#0d1322", highlightthickness=1, highlightbackground="#2e384d")
        self.fme_tl_canvas.pack(fill="x", padx=2, pady=2)

        # --- 4. Precision Edit Tools ---
        tools_box = ttk.LabelFrame(page, text="4. Precision Track Controls (Nudge, Exact Sync Shifter, Split/Cut [S], Trim, Copy, Paste, Undo [Ctrl+Z])", padding=6)
        tools_box.pack(fill="x", padx=12, pady=3)

        self.fme_sel_info_lbl = tk.Label(
            tools_box, text="Selected Track: 🗣️ VOICE | (Load a video to start editing)",
            font=("Courier", 9, "bold"), bg="#131b2e", fg="#38bdf8"
        )
        self.fme_sel_info_lbl.pack(anchor="w", pady=(0, 3))

        # Row 1: Track Selector + Fine Nudge
        nudge_row = ttk.Frame(tools_box, style="Card.TFrame")
        nudge_row.pack(fill="x", pady=2)

        ttk.Label(nudge_row, text="Active Track:", font=("Arial", 9, "bold"), background="#131b2e").pack(side="left", padx=(2, 4))
        for t_key, t_lbl in [("video", "🎬 Video Alone"), ("voice", "🗣️ Voice Alone"), ("bgm", "🎵 Music Alone")]:
            ttk.Button(
                nudge_row, text=t_lbl, width=13,
                command=lambda tk_k=t_key: self.fme_select_track(tk_k)
            ).pack(side="left", padx=2)

        ttk.Label(nudge_row, text=" | Slide Selected:", font=("Arial", 9, "bold"), background="#131b2e").pack(side="left", padx=4)
        for lbl_txt, delta_v in [
            ("-5s", -5.0), ("-1s", -1.0), ("-0.2s", -0.2), ("-0.05s", -0.05),
            ("+0.05s", 0.05), ("+0.2s", 0.2), ("+1s", 1.0), ("+5s", 5.0)
        ]:
            ttk.Button(nudge_row, text=lbl_txt, width=6, command=lambda d=delta_v: self.fme_nudge_selected_clip(d)).pack(side="left", padx=1)

        # Row 2: Quick Sync Shifter
        sync_calc_row = ttk.Frame(tools_box, style="Card.TFrame")
        sync_calc_row.pack(fill="x", pady=3)
        ttk.Label(sync_calc_row, text="🎯 Quick Sync Shifter — Word Heard At:", font=("Arial", 9, "bold"), background="#131b2e").pack(side="left", padx=2)
        self.fme_heard_at_ent = ttk.Entry(sync_calc_row, width=12)
        self.fme_heard_at_ent.pack(side="left", padx=2)
        self.fme_heard_at_ent.insert(0, "00:03:44.500")

        ttk.Label(sync_calc_row, text="➔ Should Be At Video Time:", font=("Arial", 9, "bold"), background="#131b2e").pack(side="left", padx=2)
        self.fme_should_be_ent = ttk.Entry(sync_calc_row, width=12)
        self.fme_should_be_ent.pack(side="left", padx=2)
        self.fme_should_be_ent.insert(0, "00:03:36.000")

        ttk.Button(sync_calc_row, text="⚡ Shift Selected Clip by Difference", command=self.fme_shift_clip_by_two_times).pack(side="left", padx=4)
        ttk.Button(sync_calc_row, text="🔥 Speed-Stretch Clip to Match", command=self.fme_stretch_clip_by_two_times).pack(side="left", padx=4)

        # Row 3: Split/Cut, Trim, Copy, Paste, Delete, Undo
        edit_ops_row = ttk.Frame(tools_box, style="Card.TFrame")
        edit_ops_row.pack(fill="x", pady=3)

        ttk.Button(edit_ops_row, text="✂️ Split at Playhead (S)", command=self.fme_split_selected_clip_at_playhead).pack(side="left", padx=2)
        ttk.Button(edit_ops_row, text="⇤ Trim Start to Playhead", command=lambda: self.fme_trim_selected_clip_edge(True)).pack(side="left", padx=2)
        ttk.Button(edit_ops_row, text="⇥ Trim End to Playhead", command=lambda: self.fme_trim_selected_clip_edge(False)).pack(side="left", padx=2)
        ttk.Button(edit_ops_row, text="📋 Copy", command=self.fme_copy_selected_clip).pack(side="left", padx=2)
        ttk.Button(edit_ops_row, text="📥 Paste Here", command=self.fme_paste_clip_at_playhead).pack(side="left", padx=2)
        ttk.Button(edit_ops_row, text="🗑️ Delete (Del)", command=self.fme_delete_selected_clip).pack(side="left", padx=2)
        ttk.Button(edit_ops_row, text="↩️ Undo (Ctrl+Z)", command=self.fme_undo_last_action).pack(side="left", padx=2)
        ttk.Button(edit_ops_row, text="🔄 Reset Tracks", command=self.fme_reset_all_tracks).pack(side="left", padx=2)

        # Row 4: Track Volumes
        vol_row = ttk.Frame(tools_box, style="Card.TFrame")
        vol_row.pack(fill="x", pady=2)
        ttk.Label(vol_row, text="🗣️ Voice Volume (%):", font=("Arial", 9, "bold"), background="#131b2e").pack(side="left", padx=4)
        self.fme_voice_vol_var = tk.DoubleVar(value=100.0)
        ttk.Scale(vol_row, variable=self.fme_voice_vol_var, from_=0.0, to=200.0, orient="horizontal", length=130).pack(side="left", padx=4)

        ttk.Label(vol_row, text="🎵 Music Volume (%):", font=("Arial", 9, "bold"), background="#131b2e").pack(side="left", padx=12)
        self.fme_bgm_vol_var = tk.DoubleVar(value=85.0)
        ttk.Scale(vol_row, variable=self.fme_bgm_vol_var, from_=0.0, to=200.0, orient="horizontal", length=130).pack(side="left", padx=4)

        self.fme_status = tk.Label(page, text="Select a video and click 'Load & Separate Tracks' to begin.", font=("Arial", 10, "bold"), bg="#0b0f19", fg="#38bdf8")
        self.fme_status.pack(pady=(3, 1))
        self.fme_prog = ttk.Progressbar(page, orient="horizontal", mode="indeterminate", length=620)
        self.fme_prog.pack(pady=2)

        # --- Bottom Bar ---
        bot_bar = ttk.Frame(page)
        bot_bar.pack(fill="x", padx=12, pady=3)

        self.stop_fme_btn = ttk.Button(bot_bar, text="🛑 Stop Task", style="Danger.TButton", state="disabled", command=self.fme_stop_all_tasks)
        self.stop_fme_btn.pack(side="left", padx=4)

        ttk.Button(
            bot_bar, text="▶️ Open Last Saved Movie",
            command=lambda: self.open_last_file(self.fme_state["last_saved"] or self.last_output_file)
        ).pack(side="left", padx=4)
        ttk.Button(
            bot_bar, text="📂 Open Local Folder",
            command=lambda: self.open_last_local_folder(self.fme_state["last_saved"] or self.last_output_file)
        ).pack(side="left", padx=4)

        ttk.Button(
            bot_bar, text="🎬 Save Full Movie (Same Full HD Quality)", style="Accent.TButton",
            command=self.fme_export_full_manual_movie
        ).pack(side="right", padx=6)

        ttk.Button(
            bot_bar, text="🎧 Check 15s Video+Audio Pop-Out Preview",
            command=lambda: self.fme_preview_from_playhead(15.0)
        ).pack(side="right", padx=6)

        # Load Video Buttons in Top Box
        ttk.Button(
            top_box, text="📂 Browse Video",
            command=lambda: self.fme_v_path_var.set(filedialog.askopenfilename(initialdir=self.output_base, filetypes=[("Video files", "*.mp4 *.mkv *.mov")]) or self.fme_v_path_var.get())
        ).grid(row=0, column=2, padx=4, pady=2)

        ttk.Button(
            top_box, text="🚀 Load & Separate Tracks", style="Accent.TButton",
            command=lambda: self.fme_load_and_separate_video(sep_mode_var.get())
        ).grid(row=0, column=3, padx=6, pady=2)

        # Bind Canvas Mouse Events (60FPS Playhead + Shift Hand Dragging)
        self.fme_tl_canvas.bind("<ButtonPress-1>", self.fme_on_tl_press)
        self.fme_tl_canvas.bind("<B1-Motion>", self.fme_on_tl_drag)
        self.fme_tl_canvas.bind("<ButtonRelease-1>", self.fme_on_tl_release)
        self.fme_tl_canvas.bind("<Motion>", self.fme_on_tl_hover)

        # Global Keyboard Shortcuts (Active when on manual_edit page & not typing in an Entry)
        self.root.bind("<space>", self.fme_on_key_space)
        self.root.bind("<KeyPress-Shift_L>", self.fme_on_shift_press)
        self.root.bind("<KeyPress-Shift_R>", self.fme_on_shift_press)
        self.root.bind("<KeyRelease-Shift_L>", self.fme_on_shift_release)
        self.root.bind("<KeyRelease-Shift_R>", self.fme_on_shift_release)
        self.root.bind("<Left>", lambda e: self.fme_on_arrow_key(e, -0.1))
        self.root.bind("<Right>", lambda e: self.fme_on_arrow_key(e, 0.1))
        self.root.bind("<s>", self.fme_on_key_split)
        self.root.bind("<S>", self.fme_on_key_split)
        self.root.bind("<Delete>", self.fme_on_key_delete)
        self.root.bind("<BackSpace>", self.fme_on_key_delete)
        self.root.bind("<Control-z>", lambda e: self.fme_undo_last_action())

    # --- Full Manual Edit Helper Methods ---
    def _is_typing_in_entry(self):
        focused = self.root.focus_get()
        return isinstance(focused, (tk.Entry, ttk.Entry, ttk.Combobox))

    def fme_push_undo(self):
        st = self.fme_state
        snapshot = {
            "video_clips": copy.deepcopy(st["video_clips"]),
            "voice_clips": copy.deepcopy(st["voice_clips"]),
            "bgm_clips": copy.deepcopy(st["bgm_clips"])
        }
        st["undo_stack"].append(snapshot)
        if len(st["undo_stack"]) > 25:
            st["undo_stack"].pop(0)

    def fme_undo_last_action(self):
        if self.current_page_name != "manual_edit":
            return
        st = self.fme_state
        if not st["undo_stack"]:
            self.fme_status.config(text="Nothing to undo.", fg="#94a3b8")
            return
        snap = st["undo_stack"].pop()
        st["video_clips"] = snap["video_clips"]
        st["voice_clips"] = snap["voice_clips"]
        st["bgm_clips"] = snap["bgm_clips"]
        self.fme_update_selected_info()
        self.fme_draw_timeline_full()
        if st["is_playing"]:
            self.restart_fme_live_audio_at_playhead()
        self.fme_status.config(text="↩️ Undid last timeline edit.", fg="#38bdf8")

    def fme_on_shift_press(self, event=None):
        if self.current_page_name != "manual_edit":
            return
        self.fme_state["shift_hand_active"] = True
        self.fme_update_hand_mode_ui()

    def fme_on_shift_release(self, event=None):
        if self.current_page_name != "manual_edit":
            return
        self.fme_state["shift_hand_active"] = bool(self.fme_hand_lock_var.get())
        self.fme_update_hand_mode_ui()

    def fme_update_hand_mode_ui(self):
        active = self.fme_state["shift_hand_active"] or bool(self.fme_hand_lock_var.get())
        self.fme_state["shift_hand_active"] = active
        if active:
            self.fme_tl_canvas.config(cursor="fleur")
            self.fme_hand_badge.config(
                text="✋ HAND TOOL ACTIVE: Click & Drag Video, Voice, or Music Track to Slide!",
                bg="#f59e0b", fg="#090d16"
            )
        else:
            self.fme_tl_canvas.config(cursor="arrow")
            self.fme_hand_badge.config(
                text="✋ Hold SHIFT = Hand Tool (Slide Video, Voice, or Music Alone)",
                bg="#1e293b", fg="#38bdf8"
            )

    def fme_on_key_space(self, event=None):
        if self.current_page_name != "manual_edit" or self._is_typing_in_entry():
            return
        self.toggle_fme_play_pause()
        return "break"

    def fme_on_arrow_key(self, event, delta):
        if self.current_page_name != "manual_edit" or self._is_typing_in_entry():
            return
        if self.fme_state["shift_hand_active"]:
            self.fme_nudge_selected_clip(delta)
        else:
            self.fme_step_playhead(delta)

    def fme_on_key_split(self, event=None):
        if self.current_page_name != "manual_edit" or self._is_typing_in_entry():
            return
        self.fme_split_selected_clip_at_playhead()

    def fme_on_key_delete(self, event=None):
        if self.current_page_name != "manual_edit" or self._is_typing_in_entry():
            return
        self.fme_delete_selected_clip()

    def fme_get_track_list(self, track_name=None):
        st = self.fme_state
        t = track_name or st["selected_track"]
        if t == "video":
            return st["video_clips"]
        elif t == "bgm":
            return st["bgm_clips"]
        return st["voice_clips"]

    def fme_get_selected_clip(self):
        clips = self.fme_get_track_list()
        idx = self.fme_state["selected_idx"]
        if 0 <= idx < len(clips):
            return clips[idx]
        return None

    def fme_select_track(self, track_name):
        self.fme_state["selected_track"] = track_name
        self.fme_state["selected_idx"] = 0
        self.fme_update_selected_info()
        self.fme_draw_timeline_full()

    def fme_update_selected_info(self):
        st = self.fme_state
        clip = self.fme_get_selected_clip()
        names = {"video": "🎬 VIDEO ALONE", "voice": "🗣️ VOICE ALONE", "bgm": "🎵 MUSIC ALONE"}
        t_name = names.get(st["selected_track"], "🗣️ VOICE")
        if not clip:
            self.fme_sel_info_lbl.config(text=f"Selected Track: {t_name} | (No clip on this track)")
            return
        tl_s = clip["tl_start"]
        tl_e = tl_s + (clip["duration"] / clip["speed"])
        src_s = clip["src_start"]
        src_e = src_s + clip["duration"]
        net_shift = tl_s - src_s
        self.fme_sel_info_lbl.config(
            text=f"Active: [{t_name} • {clip['label']}]  |  Timeline: {format_seconds_to_time(tl_s)} ➔ {format_seconds_to_time(tl_e)}  "
                 f"|  Net Shift: {net_shift:+.3f}s  |  Speed: {clip['speed']:.4f}x"
        )

    def fme_time_to_x(self, t_sec):
        w = max(960, self.fme_tl_canvas.winfo_width())
        dur = max(1.0, self.fme_state["duration"])
        left_pad = 140
        usable_w = max(100, w - left_pad - 20)
        return left_pad + (t_sec / dur) * usable_w

    def fme_x_to_time(self, x_px):
        w = max(960, self.fme_tl_canvas.winfo_width())
        dur = max(1.0, self.fme_state["duration"])
        left_pad = 140
        usable_w = max(100, w - left_pad - 20)
        rel = (x_px - left_pad) / usable_w
        return max(-dur, min(dur * 1.5, rel * dur))

    def fme_draw_timeline_full(self):
        """Draws the 3 tracks and tags the playhead so playhead movement is 0.05ms instant."""
        c = self.fme_tl_canvas
        c.delete("all")
        st = self.fme_state
        w = max(960, c.winfo_width())
        left_pad = 140
        dur = max(1.0, st["duration"])

        # Top Ruler Scrubbing Zone
        c.create_rectangle(left_pad, 0, w - 15, 24, fill="#161f33", outline="#2e384d")
        c.create_text(10, 12, text="⏱️ TIME RULER", fill="#94a3b8", anchor="w", font=("Arial", 8, "bold"))

        # 3 Track Lanes: Video (28..72), Voice (78..122), BGM (128..172)
        lanes = [
            ("video", 28, 72, "#132038", "🎬 VIDEO TRACK", "#38bdf8"),
            ("voice", 78, 122, "#112822", "🗣️ VOICE TRACK", "#10b981"),
            ("bgm",   128, 172, "#221536", "🎵 MUSIC TRACK", "#c084fc")
        ]
        for t_key, y1, y2, bg_c, lbl, col in lanes:
            is_active_lane = (st["selected_track"] == t_key)
            border_col = col if is_active_lane else "#263248"
            c.create_rectangle(left_pad, y1, w - 15, y2, fill=bg_c, outline=border_col, width=2 if is_active_lane else 1)
            c.create_text(10, (y1 + y2) // 2, text=lbl, fill=col, anchor="w", font=("Arial", 9, "bold"))

        # Ruler Ticks
        for i in range(11):
            t_tick = (dur * i) / 10.0
            x_t = self.fme_time_to_x(t_tick)
            c.create_line(x_t, 18, x_t, 175, fill="#1e293b", dash=(2, 4))
            c.create_text(x_t, 10, text=format_seconds_to_time(t_tick)[:8], fill="#cbd5e1", font=("Courier", 8))

        # Helper to draw clips on a lane
        def draw_lane_clips(clips, t_key, y1, y2, base_fill, sel_fill, outline_c):
            for idx, cl in enumerate(clips):
                x1 = max(left_pad, self.fme_time_to_x(cl["tl_start"]))
                eff_d = cl["duration"] / cl["speed"]
                x2 = min(w - 15, self.fme_time_to_x(cl["tl_start"] + eff_d))
                if x2 <= x1 + 2:
                    x2 = x1 + 6
                is_sel = (st["selected_track"] == t_key and st["selected_idx"] == idx)
                tag_rect = f"rect_{t_key}_{idx}"
                tag_txt = f"txt_{t_key}_{idx}"
                c.create_rectangle(
                    x1, y1 + 4, x2, y2 - 4,
                    fill=sel_fill if is_sel else base_fill,
                    outline="#ffffff" if is_sel else outline_c,
                    width=2 if is_sel else 1,
                    tags=(tag_rect, f"group_{t_key}_{idx}")
                )
                shift_val = cl["tl_start"] - cl["src_start"]
                shift_str = f" ({shift_val:+.2f}s)" if abs(shift_val) >= 0.01 else ""
                c.create_text(
                    x1 + 8, (y1 + y2) // 2,
                    text=f"✋ {cl['label']}{shift_str}",
                    fill="#090d16" if is_sel else "#ffffff",
                    anchor="w", font=("Arial", 8, "bold"),
                    tags=(tag_txt, f"group_{t_key}_{idx}")
                )

        draw_lane_clips(st["video_clips"], "video", 28, 72, "#1d4ed8", "#60a5fa", "#3b82f6")
        draw_lane_clips(st["voice_clips"], "voice", 78, 122, "#047857", "#34d399", "#10b981")
        draw_lane_clips(st["bgm_clips"],   "bgm",   128, 172, "#6d28d9", "#c084fc", "#a855f7")

        # Playhead Line & Handle (Tagged for 0.05ms instant movement!)
        ph_x = self.fme_time_to_x(st["playhead"])
        c.create_line(ph_x, 0, ph_x, 178, fill="#f43f5e", width=2, tags="playhead_line")
        c.create_polygon(ph_x - 7, 0, ph_x + 7, 0, ph_x, 12, fill="#f43f5e", outline="#ffffff", tags="playhead_head")

    def fme_move_playhead_visual_only(self, new_t):
        """Moves only the red playhead line on the canvas in < 0.05ms without redrawing clips!"""
        st = self.fme_state
        dur = max(1.0, st["duration"])
        new_t = max(0.0, min(dur, new_t))
        st["playhead"] = new_t
        ph_x = self.fme_time_to_x(new_t)
        c = self.fme_tl_canvas
        c.coords("playhead_line", ph_x, 0, ph_x, 178)
        c.coords("playhead_head", ph_x - 7, 0, ph_x + 7, 0, ph_x, 12)
        self.fme_playhead_lbl.config(text=f"📍 Playhead: {format_seconds_to_time(new_t)}  /  {format_seconds_to_time(dur)}")
        self.fme_popout_sync_playhead(new_t, dur)

    def fme_on_tl_hover(self, event):
        st = self.fme_state
        if st["shift_hand_active"] or self.fme_hand_lock_var.get():
            self.fme_tl_canvas.config(cursor="fleur")
        elif event.y <= 26:
            self.fme_tl_canvas.config(cursor="sb_h_double_arrow")
        else:
            self.fme_tl_canvas.config(cursor="hand2")

    def fme_on_tl_press(self, event):
        st = self.fme_state
        # Ensure Shift state is detected directly from event modifier bitmask too (0x0001 = Shift)
        shift_held = bool(event.state & 0x0001) or st["shift_hand_active"] or bool(self.fme_hand_lock_var.get())
        clicked_t = max(0.0, min(st["duration"], self.fme_x_to_time(event.x)))
        y = event.y

        # Top ruler (y <= 26) always scrubs playhead immediately
        if y <= 26 and not shift_held:
            st["drag_mode"] = "playhead"
            self.fme_playhead_var.set(clicked_t)
            self.fme_move_playhead_visual_only(clicked_t)
            self.fme_request_preview_frame_throttled(clicked_t)
            return

        # Determine which track lane was clicked
        clicked_track = None
        if 28 <= y <= 72:
            clicked_track = "video"
        elif 78 <= y <= 122:
            clicked_track = "voice"
        elif 128 <= y <= 172:
            clicked_track = "bgm"

        if clicked_track:
            st["selected_track"] = clicked_track
            clips = self.fme_get_track_list(clicked_track)
            hit_idx = None
            for idx, cl in enumerate(clips):
                eff_d = cl["duration"] / cl["speed"]
                if cl["tl_start"] - 0.5 <= clicked_t <= cl["tl_start"] + eff_d + 0.5:
                    hit_idx = idx
                    break
            if hit_idx is None and clips:
                hit_idx = 0

            if hit_idx is not None:
                st["selected_idx"] = hit_idx
                # Allow dragging any clip directly (especially with Shift Hand or direct click on clip)
                self.fme_push_undo()
                st["drag_mode"] = "clip"
                st["drag_start_x"] = event.x
                st["drag_orig_tl"] = clips[hit_idx]["tl_start"]
                self.fme_tl_canvas.config(cursor="fleur")
                self.fme_update_selected_info()
                self.fme_draw_timeline_full()
                return

        # Fallback: move playhead
        st["drag_mode"] = "playhead"
        self.fme_playhead_var.set(clicked_t)
        self.fme_move_playhead_visual_only(clicked_t)
        self.fme_request_preview_frame_throttled(clicked_t)

    def fme_on_tl_drag(self, event):
        st = self.fme_state
        if st["drag_mode"] == "playhead":
            new_t = max(0.0, min(st["duration"], self.fme_x_to_time(event.x)))
            self.fme_playhead_var.set(new_t)
            self.fme_move_playhead_visual_only(new_t)
            self.fme_request_preview_frame_throttled(new_t)
        elif st["drag_mode"] == "clip" and st["drag_start_x"] is not None:
            clip = self.fme_get_selected_clip()
            if clip:
                dt = self.fme_x_to_time(event.x) - self.fme_x_to_time(st["drag_start_x"])
                new_tl = st["drag_orig_tl"] + dt
                clip["tl_start"] = new_tl
                # Fast visual move of the clip rectangle without full canvas rebuild
                t_key = st["selected_track"]
                idx = st["selected_idx"]
                w = max(960, self.fme_tl_canvas.winfo_width())
                left_pad = 140
                x1 = max(left_pad, self.fme_time_to_x(new_tl))
                eff_d = clip["duration"] / clip["speed"]
                x2 = min(w - 15, self.fme_time_to_x(new_tl + eff_d))
                y_map = {"video": (32, 68, 50), "voice": (82, 118, 100), "bgm": (132, 168, 150)}
                y1, y2, ym = y_map.get(t_key, (82, 118, 100))
                self.fme_tl_canvas.coords(f"rect_{t_key}_{idx}", x1, y1, max(x1 + 6, x2), y2)
                self.fme_tl_canvas.coords(f"txt_{t_key}_{idx}", x1 + 8, ym)
                shift_val = clip["tl_start"] - clip["src_start"]
                self.fme_tl_canvas.itemconfig(f"txt_{t_key}_{idx}", text=f"✋ {clip['label']} ({shift_val:+.2f}s)")
                self.fme_update_selected_info()
                if t_key == "video":
                    self.fme_request_preview_frame_throttled(st["playhead"])

    def fme_on_tl_release(self, event):
        st = self.fme_state
        was_mode = st["drag_mode"]
        st["drag_mode"] = None
        st["drag_start_x"] = None
        self.fme_update_hand_mode_ui()

        if was_mode == "playhead":
            self.fme_request_preview_frame_throttled(st["playhead"], force=True)
            if st["is_playing"]:
                self.restart_fme_live_audio_at_playhead()
        elif was_mode == "clip":
            self.fme_draw_timeline_full()
            self.fme_request_preview_frame_throttled(st["playhead"], force=True)
            # If user dragged Video/Voice/Music while playing, hot-reload live audio immediately!
            if st["is_playing"]:
                self.restart_fme_live_audio_at_playhead()

    def fme_on_scale_drag(self, val):
        st = self.fme_state
        self.fme_move_playhead_visual_only(val)
        self.fme_request_preview_frame_throttled(val)
        if st["is_playing"]:
            st["play_wall_start"] = time.time()
            st["play_media_start"] = val

    def fme_step_playhead(self, delta):
        st = self.fme_state
        new_p = max(0.0, min(st["duration"], st["playhead"] + delta))
        self.fme_playhead_var.set(new_p)
        self.fme_move_playhead_visual_only(new_p)
        self.fme_request_preview_frame_throttled(new_p, force=True)
        if st["is_playing"]:
            self.restart_fme_live_audio_at_playhead()

    def fme_get_effective_video_source_time(self, timeline_t):
        """Calculates which frame of the video file is visible at timeline_t based on Track 1 (Video Alone) position."""
        st = self.fme_state
        if not st["video_clips"]:
            return timeline_t
        vc = st["video_clips"][0]
        rel = timeline_t - vc["tl_start"]
        return max(0.0, min(st["duration"] - 0.05, vc["src_start"] + rel * vc["speed"]))

    def fme_request_preview_frame_throttled(self, timeline_sec, force=False):
        st = self.fme_state
        v_file = st["video_path"]
        if not v_file or not os.path.exists(v_file):
            return
        now = time.time()
        if st["rendering_frame"] and not force:
            return
        if not force and (now - st["last_frame_req_time"] < 0.14):
            return

        st["rendering_frame"] = True
        st["last_frame_req_time"] = now
        v_src_sec = self.fme_get_effective_video_source_time(timeline_sec)

        # While the pop-out monitor is open, render at its full window size instead of the small monitor
        pop_c = st["pop_canvas"] if self.fme_popout_is_open() else None
        if pop_c is not None:
            fw = max(160, pop_c.winfo_width())
            fh = max(90, pop_c.winfo_height())
            st["pop_seq"] += 1
            seq = st["pop_seq"]
            temp_ppm = os.path.join(self.output_base, f"_temp_fme_popout_frame_{seq % 4}.ppm")
        else:
            fw, fh = 310, 174
            seq = 0
            temp_ppm = os.path.join(self.output_base, "_temp_fme_fast_frame.ppm")

        def grab_worker():
            cmd = [
                "ffmpeg", "-y", "-ss", f"{v_src_sec:.3f}",
                "-i", v_file,
                "-vf", f"scale={fw}:{fh}:force_original_aspect_ratio=decrease:flags=lanczos,pad={fw}:{fh}:(ow-iw)/2:(oh-ih)/2:black",
                "-frames:v", "1", "-f", "image2", temp_ppm
            ]
            res = self.run_ffmpeg(cmd)
            if res.returncode == 0 and os.path.exists(temp_ppm):
                def upd():
                    try:
                        if pop_c is not None:
                            # Drop late frames so a slow render never jumps the picture backwards
                            if self.fme_popout_is_open() and seq > st["pop_shown_seq"]:
                                img = tk.PhotoImage(file=temp_ppm)
                                st["pop_photo"] = img
                                st["pop_shown_seq"] = seq
                                pop_c.delete("frame")
                                pop_c.create_image(pop_c.winfo_width() // 2, pop_c.winfo_height() // 2, image=img, tags="frame")
                        else:
                            img = tk.PhotoImage(file=temp_ppm)
                            st["photo"] = img
                            self.fme_frame_canvas.delete("all")
                            self.fme_frame_canvas.create_image(155, 87, image=img)
                    except:
                        pass
                    st["rendering_frame"] = False
                self.root.after(0, upd)
            else:
                st["rendering_frame"] = False

        threading.Thread(target=grab_worker, daemon=True).start()

    # --- 🔍 Resizable Pop-Out Live Video Monitor (v1.7.3) ---
    def fme_popout_is_open(self):
        win = self.fme_state.get("pop_win")
        try:
            return win is not None and bool(win.winfo_exists())
        except:
            return False

    def fme_toggle_popout(self):
        if self.fme_popout_is_open():
            self.fme_close_popout()
        else:
            self.fme_open_popout()

    def fme_open_popout(self):
        st = self.fme_state
        if self.fme_popout_is_open():
            st["pop_win"].lift()
            return

        win = tk.Toplevel(self.root)
        win.title("🔍 Live Video Monitor — Nader Video Studio")
        win.configure(bg="#070a12")
        win.minsize(320, 220)
        sw, sh = win.winfo_screenwidth(), win.winfo_screenheight()
        w0, h0 = min(1280, int(sw * 0.8)), min(780, int(sh * 0.8))
        win.geometry(f"{w0}x{h0}+{max(0, (sw - w0) // 2)}+{max(0, (sh - h0) // 2)}")

        canvas = tk.Canvas(win, bg="#000000", highlightthickness=0)
        canvas.pack(side="top", fill="both", expand=True)
        canvas.create_text(
            w0 // 2, h0 // 2 - 40, text="Load a video in Full Manual Edit to preview",
            fill="#94a3b8", font=("Arial", 12, "bold"), tags="frame"
        )

        bar = tk.Frame(win, bg="#111827")
        bar.pack(side="bottom", fill="x")

        self.fme_pop_play_btn = tk.Button(
            bar, text="▶️ Play (Space)", font=("Arial", 10, "bold"), width=14,
            bg="#2563eb", fg="#ffffff", activebackground="#1d4ed8", activeforeground="#ffffff",
            relief="flat", cursor="hand2", command=self.toggle_fme_play_pause
        )
        self.fme_pop_play_btn.pack(side="left", padx=(8, 4), pady=6)
        for lbl_b, d_s in [("⏪ -5s", -5.0), ("◀ -0.1s", -0.1), ("▶ +0.1s", 0.1), ("⏩ +5s", 5.0)]:
            tk.Button(
                bar, text=lbl_b, font=("Arial", 9, "bold"), bg="#1f2937", fg="#cbd5e1",
                activebackground="#334155", relief="flat", cursor="hand2",
                command=lambda d=d_s: self.fme_step_playhead(d)
            ).pack(side="left", padx=1, pady=6)

        self.fme_pop_time_lbl = tk.Label(bar, text="", font=("Courier", 11, "bold"), bg="#111827", fg="#f43f5e")
        self.fme_pop_time_lbl.pack(side="left", padx=10)

        tk.Button(
            bar, text="⛶ Fit Screen", font=("Arial", 9, "bold"), bg="#1f2937", fg="#cbd5e1",
            activebackground="#334155", relief="flat", cursor="hand2",
            command=self.fme_popout_toggle_maximize
        ).pack(side="right", padx=(1, 8), pady=6)

        # Seek bar: drives the same playhead variable as the main scrubber, so both stay locked together
        self._fme_pop_scale_guard = False
        self.fme_pop_scale = tk.Scale(
            bar, from_=0.0, to=max(1.0, st["duration"]), resolution=0.02,
            orient="horizontal", showvalue=False, bg="#111827", troughcolor="#0f172a",
            highlightthickness=0, activebackground="#f43f5e",
            command=self.fme_on_popout_scale
        )
        self.fme_pop_scale.pack(side="left", fill="x", expand=True, padx=6)

        st["pop_win"] = win
        st["pop_canvas"] = canvas
        st["pop_photo"] = None
        st["pop_shown_seq"] = st["pop_seq"]

        win.bind("<Configure>", self.fme_on_popout_resize)
        win.bind("<space>", lambda e: (self.toggle_fme_play_pause(), "break")[1])
        win.bind("<Left>", lambda e: self.fme_step_playhead(-0.1))
        win.bind("<Right>", lambda e: self.fme_step_playhead(0.1))
        win.bind("<F11>", lambda e: self.fme_popout_toggle_maximize())
        win.bind("<Escape>", lambda e: self.fme_close_popout())
        win.protocol("WM_DELETE_WINDOW", self.fme_close_popout)

        self.fme_frame_canvas.delete("all")
        self.fme_frame_canvas.create_text(
            155, 87, text="🔍 Showing in Pop-Out Monitor\n(close it to preview here again)",
            fill="#38bdf8", font=("Arial", 9, "bold"), justify="center"
        )
        self.fme_popout_sync_play_btn()
        self.fme_popout_sync_playhead(st["playhead"], max(1.0, st["duration"]))
        win.after(150, lambda: self.fme_request_preview_frame_throttled(st["playhead"], force=True))

    def fme_close_popout(self, refresh_main=True):
        if not hasattr(self, "fme_state"):
            return
        st = self.fme_state
        win = st.get("pop_win")
        if st.get("pop_resize_job"):
            try: self.root.after_cancel(st["pop_resize_job"])
            except: pass
        st["pop_win"] = None
        st["pop_canvas"] = None
        st["pop_photo"] = None
        st["pop_resize_job"] = None
        if win is not None:
            try: win.destroy()
            except: pass
        for i in range(4):
            try: os.remove(os.path.join(self.output_base, f"_temp_fme_popout_frame_{i}.ppm"))
            except: pass
        if refresh_main:
            self.fme_request_preview_frame_throttled(st["playhead"], force=True)

    def fme_popout_toggle_maximize(self):
        win = self.fme_state.get("pop_win")
        if not self.fme_popout_is_open():
            return
        try:
            if sys.platform == "win32":
                win.state("normal" if win.state() == "zoomed" else "zoomed")
            else:
                win.attributes("-zoomed", not bool(win.attributes("-zoomed")))
        except:
            # macOS / other WMs: fill the screen manually
            win.geometry(f"{win.winfo_screenwidth()}x{win.winfo_screenheight()}+0+0")

    def fme_on_popout_resize(self, event):
        st = self.fme_state
        if event.widget is not st.get("pop_win"):
            return
        # Debounce: re-render the frame at the new size once dragging the window edge settles
        if st.get("pop_resize_job"):
            try: self.root.after_cancel(st["pop_resize_job"])
            except: pass
        st["pop_resize_job"] = self.root.after(
            160, lambda: self.fme_request_preview_frame_throttled(st["playhead"], force=True)
        )

    def fme_on_popout_scale(self, val):
        # Tk calls this on idle even for our own .set() calls, so only act on a real user seek
        val = float(val)
        if self._fme_pop_scale_guard or abs(val - self.fme_state["playhead"]) < 0.05:
            return
        self.fme_playhead_var.set(val)
        self.fme_on_scale_drag(val)

    def fme_popout_sync_playhead(self, t_sec, dur):
        if not self.fme_popout_is_open():
            return
        self.fme_pop_time_lbl.config(text=f"{format_seconds_to_time(t_sec)}  /  {format_seconds_to_time(dur)}")
        self._fme_pop_scale_guard = True
        try:
            if float(self.fme_pop_scale.cget("to")) != float(dur):
                self.fme_pop_scale.config(to=dur)
            self.fme_pop_scale.set(t_sec)
        finally:
            self._fme_pop_scale_guard = False

    def fme_popout_sync_play_btn(self):
        if not self.fme_popout_is_open():
            return
        playing = self.fme_state["is_playing"]
        self.fme_pop_play_btn.config(text="⏸️ Pause (Space)" if playing else "▶️ Play (Space)")

    # --- Live In-App Play / Pause Engine (Spacebar) ---
    def toggle_fme_play_pause(self):
        st = self.fme_state
        if not st["video_path"] or not os.path.exists(st["video_path"]):
            messagebox.showinfo("Load Video", "Please load a video first.")
            return
        if st["is_playing"]:
            self.stop_fme_live_playback()
        else:
            self.start_fme_live_playback()

    def start_fme_live_playback(self):
        st = self.fme_state
        st["is_playing"] = True
        st["play_wall_start"] = time.time()
        st["play_media_start"] = st["playhead"]
        self.fme_play_btn.config(text="⏸️ Pause (Space)")
        self.fme_popout_sync_play_btn()
        self.restart_fme_live_audio_at_playhead()
        self.fme_playback_tick()

    def stop_fme_live_playback(self):
        st = self.fme_state
        st["is_playing"] = False
        if hasattr(self, "fme_play_btn"):
            self.fme_play_btn.config(text="▶️ Play (Space)")
        self.fme_popout_sync_play_btn()
        if self.live_audio_process:
            try:
                self.live_audio_process.terminate()
            except:
                pass
            self.live_audio_process = None

    def restart_fme_live_audio_at_playhead(self):
        """Spawns background ffplay audio stream synced to the current playhead and current Voice/Music track positions."""
        if self.live_audio_process:
            try:
                self.live_audio_process.terminate()
            except:
                pass
            self.live_audio_process = None

        st = self.fme_state
        if not st["is_playing"] or not st["voice_stem"] or not os.path.exists(st["voice_stem"]):
            return

        ffplay_bin = shutil.which("ffplay") or shutil.which("ffplay.exe")
        if not ffplay_bin:
            return

        ph = st["playhead"]
        st["play_wall_start"] = time.time()
        st["play_media_start"] = ph

        # Calculate where in the voice stem corresponds to playhead `ph`
        vc = st["voice_clips"][0] if st["voice_clips"] else None
        if not vc:
            return

        # Audio time at playhead `ph`:
        audio_seek = vc["src_start"] + (ph - vc["tl_start"]) * vc["speed"]
        v_vol = max(0.0, self.fme_voice_vol_var.get() / 100.0)
        at_f = build_atempo_chain(vc["speed"])

        kwargs = {"creationflags": 0x08000000} if sys.platform == "win32" else {}
        if audio_seek >= 0:
            af_str = f"{at_f},volume={v_vol:.2f}"
            cmd = [ffplay_bin, "-nodisp", "-autoexit", "-loglevel", "quiet", "-ss", f"{audio_seek:.3f}", "-af", af_str, st["voice_stem"]]
        else:
            delay_ms = int(round(abs(audio_seek) * 1000))
            af_str = f"adelay={delay_ms}|{delay_ms},{at_f},volume={v_vol:.2f}"
            cmd = [ffplay_bin, "-nodisp", "-autoexit", "-loglevel", "quiet", "-af", af_str, st["voice_stem"]]

        try:
            self.live_audio_process = subprocess.Popen(cmd, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, **kwargs)
        except:
            pass

    def fme_playback_tick(self):
        st = self.fme_state
        if not st["is_playing"] or self.current_page_name != "manual_edit":
            return
        if st["drag_mode"] != "playhead":
            elapsed = time.time() - st["play_wall_start"]
            cur_t = st["play_media_start"] + elapsed
            if cur_t >= st["duration"]:
                self.stop_fme_live_playback()
                return
            self.fme_playhead_var.set(cur_t)
            self.fme_move_playhead_visual_only(cur_t)
            self.fme_request_preview_frame_throttled(cur_t)

        self.root.after(33, self.fme_playback_tick)

    # --- Track Editing Operations in Full Manual Edit ---
    def fme_nudge_selected_clip(self, delta_sec):
        clip = self.fme_get_selected_clip()
        if not clip:
            return
        self.fme_push_undo()
        clip["tl_start"] += delta_sec
        self.fme_update_selected_info()
        self.fme_draw_timeline_full()
        self.fme_request_preview_frame_throttled(self.fme_state["playhead"], force=True)
        if self.fme_state["is_playing"]:
            self.restart_fme_live_audio_at_playhead()

    def fme_shift_clip_by_two_times(self):
        clip = self.fme_get_selected_clip()
        if not clip:
            return
        try:
            t_heard = parse_time_to_seconds(self.fme_heard_at_ent.get())
            t_should = parse_time_to_seconds(self.fme_should_be_ent.get())
            delta = t_should - t_heard
            self.fme_nudge_selected_clip(delta)
            self.fme_status.config(
                text=f"✅ Shifted {self.fme_state['selected_track'].upper()} track by {delta:+.3f}s (so {self.fme_heard_at_ent.get()} lands at {self.fme_should_be_ent.get()}).",
                fg="#10b981"
            )
        except Exception as ex:
            messagebox.showerror("Time Error", str(ex))

    def fme_stretch_clip_by_two_times(self):
        clip = self.fme_get_selected_clip()
        if not clip:
            return
        try:
            t_heard = parse_time_to_seconds(self.fme_heard_at_ent.get())
            t_should = parse_time_to_seconds(self.fme_should_be_ent.get())
            rel_heard = t_heard - clip["tl_start"]
            rel_should = t_should - clip["tl_start"]
            if rel_heard <= 0.5 or rel_should <= 0.5:
                messagebox.showerror("Range Error", "Both timestamps must be after the selected clip's start time.")
                return
            self.fme_push_undo()
            factor = rel_heard / rel_should
            clip["speed"] = max(0.5, min(2.0, clip["speed"] * factor))
            self.fme_update_selected_info()
            self.fme_draw_timeline_full()
            if self.fme_state["is_playing"]:
                self.restart_fme_live_audio_at_playhead()
            self.fme_status.config(
                text=f"✅ Speed-stretched clip to {clip['speed']:.5f}x so {self.fme_heard_at_ent.get()} locks onto {self.fme_should_be_ent.get()}!",
                fg="#10b981"
            )
        except Exception as ex:
            messagebox.showerror("Time Error", str(ex))

    def fme_split_selected_clip_at_playhead(self):
        clips = self.fme_get_track_list()
        clip = self.fme_get_selected_clip()
        if not clip:
            return
        ph = self.fme_state["playhead"]
        eff_dur = clip["duration"] / clip["speed"]
        if not (clip["tl_start"] + 0.2 < ph < clip["tl_start"] + eff_dur - 0.2):
            messagebox.showinfo("Split Clip", "Place the Red Playhead inside the selected clip before pressing Split (S).")
            return
        self.fme_push_undo()
        rel_tl = ph - clip["tl_start"]
        src_split_offset = rel_tl * clip["speed"]

        part2 = {
            "id": int(time.time() * 1000) % 100000,
            "src_start": clip["src_start"] + src_split_offset,
            "duration": clip["duration"] - src_split_offset,
            "tl_start": ph,
            "speed": clip["speed"],
            "label": f"{self.fme_state['selected_track'].capitalize()}_P{len(clips) + 1}"
        }
        clip["duration"] = src_split_offset
        clips.insert(self.fme_state["selected_idx"] + 1, part2)
        self.fme_state["selected_idx"] += 1
        self.fme_update_selected_info()
        self.fme_draw_timeline_full()
        self.fme_status.config(
            text=f"✂️ Split at {format_seconds_to_time(ph)}! Selected 2nd piece — hold SHIFT and drag it freely.",
            fg="#10b981"
        )

    def fme_trim_selected_clip_edge(self, is_start=True):
        clip = self.fme_get_selected_clip()
        if not clip:
            return
        ph = self.fme_state["playhead"]
        eff_dur = clip["duration"] / clip["speed"]
        tl_end = clip["tl_start"] + eff_dur
        self.fme_push_undo()
        if is_start:
            if not (clip["tl_start"] < ph < tl_end - 0.2):
                messagebox.showinfo("Trim Start", "Place the playhead inside the clip to trim its start.")
                return
            cut_tl = ph - clip["tl_start"]
            clip["src_start"] += cut_tl * clip["speed"]
            clip["duration"] -= cut_tl * clip["speed"]
            clip["tl_start"] = ph
        else:
            if not (clip["tl_start"] + 0.2 < ph < tl_end):
                messagebox.showinfo("Trim End", "Place the playhead inside the clip to trim its end.")
                return
            new_eff = ph - clip["tl_start"]
            clip["duration"] = new_eff * clip["speed"]
        self.fme_update_selected_info()
        self.fme_draw_timeline_full()

    def fme_copy_selected_clip(self):
        clip = self.fme_get_selected_clip()
        if clip:
            self.fme_state["clipboard_clip"] = dict(clip)
            self.fme_status.config(text=f"📋 Copied {clip['label']} to clipboard.", fg="#38bdf8")

    def fme_paste_clip_at_playhead(self):
        st = self.fme_state
        if not st["clipboard_clip"]:
            messagebox.showinfo("Paste", "Copy a clip first.")
            return
        self.fme_push_undo()
        clips = self.fme_get_track_list()
        new_c = dict(st["clipboard_clip"])
        new_c["id"] = int(time.time() * 1000) % 100000
        new_c["tl_start"] = st["playhead"]
        new_c["label"] = f"Copy_{len(clips) + 1}"
        clips.append(new_c)
        st["selected_idx"] = len(clips) - 1
        self.fme_update_selected_info()
        self.fme_draw_timeline_full()

    def fme_delete_selected_clip(self):
        clips = self.fme_get_track_list()
        idx = self.fme_state["selected_idx"]
        if 0 <= idx < len(clips):
            self.fme_push_undo()
            clips.pop(idx)
            self.fme_state["selected_idx"] = max(0, len(clips) - 1)
            self.fme_update_selected_info()
            self.fme_draw_timeline_full()

    def fme_reset_all_tracks(self):
        st = self.fme_state
        dur = st["duration"]
        st["video_clips"] = [{"id": 10, "src_start": 0.0, "duration": dur, "tl_start": 0.0, "speed": 1.0, "label": "Video_HD"}]
        st["voice_clips"] = [{"id": 20, "src_start": 0.0, "duration": dur, "tl_start": 0.0, "speed": 1.0, "label": "Voice_Track"}]
        if st["bgm_stem"] and os.path.exists(st["bgm_stem"]):
            st["bgm_clips"] = [{"id": 30, "src_start": 0.0, "duration": dur, "tl_start": 0.0, "speed": 1.0, "label": "Music_BGM"}]
        else:
            st["bgm_clips"] = []
        st["selected_track"] = "voice"
        st["selected_idx"] = 0
        self.fme_update_selected_info()
        self.fme_draw_timeline_full()

    def fme_stop_all_tasks(self):
        self.stop_fme_live_playback()
        self.stop_sync_task()
        self.fme_prog.stop()
        self.stop_fme_btn.config(state="disabled")
        self.fme_status.config(text="🛑 Task stopped.", fg="#f43f5e")

    def fme_load_and_separate_video(self, sep_mode="separate"):
        v_file = self.fme_v_path_var.get().strip()
        if not v_file or not os.path.exists(v_file):
            messagebox.showerror("Error", "Please select a valid video file first.")
            return

        self.stop_fme_live_playback()
        st = self.fme_state
        st["video_path"] = v_file
        dur = self.get_media_duration(v_file)
        st["duration"] = max(1.0, dur)
        self.fme_playhead_scale.config(to=st["duration"])
        self.fme_playhead_var.set(0.0)
        st["playhead"] = 0.0

        work_dir = os.path.join(self.output_base, "_temp_fme_stems")
        os.makedirs(work_dir, exist_ok=True)
        voice_out = os.path.join(work_dir, "voice_stem.m4a")
        bgm_out = os.path.join(work_dir, "bgm_stem.m4a")
        full_out = os.path.join(work_dir, "full_stem.m4a")

        self.sync_stop_flag = False
        self.stop_fme_btn.config(state="normal")
        self.fme_prog.start(12)
        self.fme_status.config(text="Separating Video, Voice & Background Music Tracks...", fg="#f59e0b")

        def worker():
            try:
                if sep_mode == "separate":
                    cmd_v = [
                        "ffmpeg", "-y", "-i", v_file, "-vn",
                        "-af", "pan=stereo|c0=0.5*c0+0.5*c1|c1=0.5*c0+0.5*c1,highpass=f=180,lowpass=f=3800",
                        "-c:a", "aac", "-b:a", "192k", "-ar", "48000", voice_out
                    ]
                    self.run_sync_cancellable_ffmpeg(cmd_v)
                    if self.sync_stop_flag:
                        return

                    cmd_b = [
                        "ffmpeg", "-y", "-i", v_file, "-vn",
                        "-af", "pan=stereo|c0=0.5*c0-0.5*c1|c1=0.5*c1-0.5*c0,lowpass=f=12000",
                        "-c:a", "aac", "-b:a", "160k", "-ar", "48000", bgm_out
                    ]
                    self.run_sync_cancellable_ffmpeg(cmd_b)
                    if self.sync_stop_flag:
                        return

                    st["voice_stem"] = voice_out
                    st["bgm_stem"] = bgm_out
                else:
                    cmd_f = [
                        "ffmpeg", "-y", "-i", v_file, "-vn",
                        "-af", "aresample=async=1:first_pts=0",
                        "-c:a", "aac", "-b:a", "192k", "-ar", "48000", full_out
                    ]
                    self.run_sync_cancellable_ffmpeg(cmd_f)
                    if self.sync_stop_flag:
                        return
                    st["voice_stem"] = full_out
                    st["bgm_stem"] = ""

                self.fme_prog.stop()
                self.stop_fme_btn.config(state="disabled")
                self.root.after(0, lambda: (
                    self.fme_reset_all_tracks(),
                    self.fme_request_preview_frame_throttled(0.0, force=True),
                    self.fme_status.config(
                        text="✅ Ready! Press SPACE to Play/Pause • Hold SHIFT (✋) and drag Video, Voice, or Music directly!",
                        fg="#10b981"
                    )
                ))
            except Exception as ex:
                err_txt = str(ex)
                self.fme_prog.stop()
                self.stop_fme_btn.config(state="disabled")
                self.root.after(0, lambda: self.fme_status.config(text=f"Error: {err_txt}", fg="#f43f5e"))

        threading.Thread(target=worker, daemon=True).start()

    def fme_build_export_filter_complex(self):
        """
        Builds the FFmpeg filter_complex that honors independent shifts on:
        - Track 1 (Video Alone offset)
        - Track 2 (Voice Alone clips)
        - Track 3 (Background Music Alone clips)
        """
        st = self.fme_state
        filter_parts = []
        mix_labels = []
        v_vol = max(0.0, self.fme_voice_vol_var.get() / 100.0)
        b_vol = max(0.0, self.fme_bgm_vol_var.get() / 100.0)

        # If the user slid the Video Track itself (e.g. moved Video +2.0s or -2.0s),
        # shifting Video by +V is equivalent to shifting Audio by -V relative to the untouched Full HD video stream!
        vid_clip = st["video_clips"][0] if st["video_clips"] else {"tl_start": 0.0, "src_start": 0.0}
        video_net_shift = vid_clip["tl_start"] - vid_clip["src_start"]

        for idx, vc in enumerate(st["voice_clips"]):
            rel_tl = vc["tl_start"] - video_net_shift
            s_start = max(0.0, vc["src_start"])
            s_dur = max(0.1, vc["duration"])
            if rel_tl < 0:
                cut_front = abs(rel_tl) * vc["speed"]
                s_start += cut_front
                s_dur = max(0.1, s_dur - cut_front)
                delay_ms = 0
            else:
                delay_ms = int(round(rel_tl * 1000))

            s_end = s_start + s_dur
            at_f = build_atempo_chain(vc["speed"])
            lbl = f"vc{idx}"
            chain = f"[1:a]atrim={s_start:.3f}:{s_end:.3f},asetpts=PTS-STARTPTS,{at_f},volume={v_vol:.2f}"
            if delay_ms > 0:
                chain += f",adelay={delay_ms}|{delay_ms}"
            chain += f"[{lbl}]"
            filter_parts.append(chain)
            mix_labels.append(f"[{lbl}]")

        if st["bgm_stem"] and os.path.exists(st["bgm_stem"]) and b_vol > 0.01:
            for idx, bc in enumerate(st["bgm_clips"]):
                rel_tl = bc["tl_start"] - video_net_shift
                s_start = max(0.0, bc["src_start"])
                s_dur = max(0.1, bc["duration"])
                if rel_tl < 0:
                    cut_front = abs(rel_tl) * bc["speed"]
                    s_start += cut_front
                    s_dur = max(0.1, s_dur - cut_front)
                    delay_ms = 0
                else:
                    delay_ms = int(round(rel_tl * 1000))

                s_end = s_start + s_dur
                at_f = build_atempo_chain(bc["speed"])
                lbl = f"bc{idx}"
                chain = f"[2:a]atrim={s_start:.3f}:{s_end:.3f},asetpts=PTS-STARTPTS,{at_f},volume={b_vol:.2f}"
                if delay_ms > 0:
                    chain += f",adelay={delay_ms}|{delay_ms}"
                chain += f"[{lbl}]"
                filter_parts.append(chain)
                mix_labels.append(f"[{lbl}]")

        if not mix_labels:
            return None

        if len(mix_labels) == 1:
            filter_parts.append(f"{mix_labels[0]}apad[aout]")
        else:
            joined = "".join(mix_labels)
            filter_parts.append(f"{joined}amix=inputs={len(mix_labels)}:duration=longest:dropout_transition=0,volume={len(mix_labels)},apad[aout]")

        return ";".join(filter_parts)

    def fme_preview_from_playhead(self, dur_sec=15.0):
        st = self.fme_state
        if not st["video_path"] or not st["voice_stem"] or not os.path.exists(st["voice_stem"]):
            messagebox.showinfo("Load Video First", "Click '🚀 Load & Separate Tracks' first.")
            return

        self.stop_fme_live_playback()
        fc = self.fme_build_export_filter_complex()
        if not fc:
            return

        ph = st["playhead"]
        temp_prev = os.path.join(self.output_base, "_temp_fme_preview_15s.mp4")
        self.sync_stop_flag = False
        self.stop_fme_btn.config(state="normal")
        self.fme_prog.start(12)
        self.fme_status.config(text=f"Rendering {int(dur_sec)}s preview at Playhead ({format_seconds_to_time(ph)})...", fg="#f59e0b")

        def worker():
            cmd = ["ffmpeg", "-y", "-i", st["video_path"], "-i", st["voice_stem"]]
            if st["bgm_stem"] and os.path.exists(st["bgm_stem"]):
                cmd.extend(["-i", st["bgm_stem"]])
            cmd.extend([
                "-filter_complex", fc,
                "-map", "0:v:0", "-map", "[aout]",
                "-ss", f"{ph:.3f}", "-t", f"{dur_sec:.1f}",
                "-c:v", "libx264", "-preset", "ultrafast", "-crf", "20",
                "-c:a", "aac", "-b:a", "192k", temp_prev
            ])
            res = self.run_sync_cancellable_ffmpeg(cmd)
            self.fme_prog.stop()
            self.stop_fme_btn.config(state="disabled")
            if self.sync_stop_flag:
                return
            if res.returncode == 0 and os.path.exists(temp_prev):
                self.fme_status.config(text=f"▶️ Playing 15s preview from {format_seconds_to_time(ph)}!", fg="#10b981")
                self.open_last_file(temp_prev)
            else:
                self.fme_status.config(text="❌ Preview failed. Check Error Log.", fg="#f43f5e")

        threading.Thread(target=worker, daemon=True).start()

    def fme_export_full_manual_movie(self):
        st = self.fme_state
        if not st["video_path"] or not st["voice_stem"] or not os.path.exists(st["voice_stem"]):
            messagebox.showinfo("Load Video First", "Click '🚀 Load & Separate Tracks' first.")
            return

        self.stop_fme_live_playback()
        fc = self.fme_build_export_filter_complex()
        if not fc:
            return

        target_dir = self.get_organized_output_dir(st["video_path"], "2_Voice_Synced")
        clean_base = clean_folder_Title(st["video_path"])
        out_path = os.path.join(target_dir, f"{clean_base}_FullManualEdit.mp4")

        self.sync_stop_flag = False
        self.stop_fme_btn.config(state="normal")
        self.fme_prog.start(12)
        self.fme_status.config(text="Saving Full HD Movie (-c:v copy, zero quality loss) with edited tracks...", fg="#f59e0b")

        def worker():
            cmd = ["ffmpeg", "-y", "-i", st["video_path"], "-i", st["voice_stem"]]
            if st["bgm_stem"] and os.path.exists(st["bgm_stem"]):
                cmd.extend(["-i", st["bgm_stem"]])
            cmd.extend([
                "-filter_complex", fc,
                "-map", "0:v:0", "-map", "[aout]",
                "-c:v", "copy",
                "-c:a", "aac", "-b:a", "192k", "-ar", "48000",
                "-shortest", "-movflags", "+faststart", "-avoid_negative_ts", "make_zero",
                out_path
            ])
            res = self.run_sync_cancellable_ffmpeg(cmd)
            self.fme_prog.stop()
            self.stop_fme_btn.config(state="disabled")
            if self.sync_stop_flag:
                return
            if res.returncode == 0 and os.path.exists(out_path):
                st["last_saved"] = out_path
                self.record_last_output(out_path)
                self.fme_status.config(text=f"✅ Saved Full HD Movie: {os.path.basename(out_path)}", fg="#10b981")
                self.log_message(f"FULL MANUAL EDIT COMPLETED: {out_path}")
            else:
                self.fme_status.config(text="❌ Export failed. Check Error Log.", fg="#f43f5e")
                self.log_message(f"Full Manual Edit Export Error:\n{res.stderr}")

        threading.Thread(target=worker, daemon=True).start()

    # =========================================================================
    # PAGE 3: 🌙 OVERNIGHT 5-MOVIE NARTO SEQUENTIAL QUEUE (IN-WINDOW)
    # =========================================================================
    def build_narto_queue_page(self):
        page = ttk.Frame(self.page_container)
        self.pages["queue"] = page

        tk.Label(
            page, text="🌙 Narto Drama 5-Movie Overnight Queue (Sequential 1-by-1)",
            font=("Arial", 14, "bold"), bg="#0b0f19", fg="#f8fafc"
        ).pack(pady=(12, 2))
        tk.Label(
            page,
            text="Paste up to 5 Narto series links with their Start & End episodes. They will download strictly 1-by-1 into Date/Movie folders.",
            font=("Arial", 9), bg="#0b0f19", fg="#94a3b8"
        ).pack(pady=(0, 10))

        slots_frame = ttk.Frame(page)
        slots_frame.pack(fill="x", padx=18, pady=4)

        self.queue_slots = []
        for i in range(5):
            row = ttk.LabelFrame(slots_frame, text=f"Movie Slot #{i+1}", padding=(10, 6))
            row.pack(fill="x", pady=5)

            url_holder = ttk.Frame(row, style="Card.TFrame")
            url_holder.grid(row=0, column=0, padx=(0, 8))
            url_combo = self.build_url_controls_in_frame(url_holder, source_id="2", width=46, register_main=False)

            ttk.Label(row, text="From Ep:", background="#131b2e").grid(row=0, column=1, padx=3)
            from_ent = ttk.Entry(row, width=6)
            from_ent.grid(row=0, column=2, padx=3)
            from_ent.insert(0, "1")

            ttk.Label(row, text="To Ep:", background="#131b2e").grid(row=0, column=3, padx=3)
            to_ent = ttk.Entry(row, width=6)
            to_ent.grid(row=0, column=4, padx=3)

            status_lbl = tk.Label(row, text="⏳ Idle", width=16, font=("Arial", 9, "bold"), bg="#131b2e", fg="#94a3b8")
            status_lbl.grid(row=0, column=5, padx=8)

            self.queue_slots.append({
                "url": url_combo,
                "from": from_ent,
                "to": to_ent,
                "status": status_lbl
            })

        q_status_lbl = tk.Label(page, text="Ready to start overnight queue.", font=("Arial", 11, "bold"), bg="#0b0f19", fg="#38bdf8")
        q_status_lbl.pack(pady=10)

        btn_bar = ttk.Frame(page)
        btn_bar.pack(pady=6)

        start_q_btn = ttk.Button(btn_bar, text="🚀 Start Overnight Queue (1-by-1)", style="Accent.TButton")
        start_q_btn.grid(row=0, column=0, padx=6)

        stop_q_btn = ttk.Button(btn_bar, text="🛑 Stop Queue", style="Danger.TButton", state="disabled", command=self.stop_download)
        stop_q_btn.grid(row=0, column=1, padx=6)

        ttk.Button(btn_bar, text="▶️ Open Last File", command=self.open_last_file).grid(row=0, column=2, padx=6)
        ttk.Button(btn_bar, text="📂 Open Last Local Folder", command=self.open_last_local_folder).grid(row=0, column=3, padx=6)

        def run_overnight_queue():
            active_jobs = []
            for idx, slot in enumerate(self.queue_slots):
                raw_u = slot["url"].get().strip()
                if raw_u:
                    active_jobs.append((idx, slot, self.sanitize_url(raw_u)))
                else:
                    slot["status"].config(text="⏭️ Empty", fg="#64748b")

            if not active_jobs:
                messagebox.showinfo("Queue Empty", "Please paste at least 1 Narto link in the slots.")
                return

            self.stop_flag = False
            start_q_btn.config(state="disabled")
            stop_q_btn.config(state="normal")
            self.disable_buttons_for_run()

            def worker():
                completed_count = 0
                for idx, slot, clean_url in active_jobs:
                    if self.stop_flag:
                        slot["status"].config(text="🛑 Stopped", fg="#f43f5e")
                        break

                    from_val = slot["from"].get().strip()
                    to_val = slot["to"].get().strip()

                    self.start_entry.delete(0, tk.END)
                    self.start_entry.insert(0, from_val if from_val.isdigit() else "1")
                    self.total_entry.delete(0, tk.END)
                    if to_val.isdigit():
                        self.total_entry.insert(0, to_val)

                    slot["status"].config(text="⬇️ Downloading...", fg="#38bdf8")
                    q_status_lbl.config(text=f"Running Slot #{idx+1} of {len(active_jobs)}...", fg="#38bdf8")
                    self.save_to_history("2", clean_url)

                    self.log_message(f"{'='*50}\n--- OVERNIGHT QUEUE SLOT #{idx+1} ({from_val} to {to_val or 'Full'}) ---\nURL: {clean_url}")
                    self.download_process(clean_url, 2, keep_buttons_locked=True)

                    if self.stop_flag:
                        slot["status"].config(text="🛑 Interrupted", fg="#f59e0b")
                        break
                    else:
                        slot["status"].config(text="✅ Completed", fg="#10b981")
                        completed_count += 1
                        time.sleep(3)

                self.reset_buttons()
                start_q_btn.config(state="normal")
                stop_q_btn.config(state="disabled")
                if self.stop_flag:
                    q_status_lbl.config(text=f"Queue stopped. Completed {completed_count}/{len(active_jobs)} movies.", fg="#f59e0b")
                else:
                    q_status_lbl.config(text=f"🎉 All {completed_count} queued movies finished!", fg="#10b981")

            threading.Thread(target=worker, daemon=True).start()

        start_q_btn.config(command=run_overnight_queue)

    # =========================================================================
    # PAGE 4: ✂️ HD MULTI-VIDEO TRIM & CROP STUDIO (IN-WINDOW)
    # =========================================================================
    def build_trim_crop_page(self):
        page = ttk.Frame(self.page_container)
        self.pages["trim_crop"] = page

        tk.Label(page, text="✂️ HD Multi-Video Trim, Crop & Visual Frame Scrubber Studio", font=("Arial", 13, "bold"), bg="#0b0f19", fg="#f8fafc").pack(pady=(6, 1))
        tk.Label(
            page,
            text="Add videos, scrub frames visually with the slider to set exact Trim Start/End times, preview crop live, and export in Full HD.",
            font=("Arial", 9), bg="#0b0f19", fg="#94a3b8"
        ).pack(pady=(0, 4))

        pool_frame = ttk.LabelFrame(page, text="1. Source Videos Pool (Drag & Drop Files Here or Click Add Videos)", padding=6)
        pool_frame.pack(fill="x", padx=14, pady=3)

        pool_list = tk.Listbox(pool_frame, height=4, width=105, selectmode=tk.SINGLE, bg="#0f172a", fg="#f8fafc", selectbackground="#2563eb")
        pool_list.grid(row=0, column=0, rowspan=3, padx=(0, 8), pady=2)

        source_videos = []
        scrubber_state = {"duration": 0.0, "current_video": "", "photo": None, "rendering": False}
        studio_last_out = {"path": ""}

        scrubber_frame = ttk.LabelFrame(page, text="2. Visual Frame-by-Frame Scrubber & Live Crop Preview", padding=6)
        scrubber_frame.pack(fill="x", padx=14, pady=3)

        preview_canvas = tk.Canvas(scrubber_frame, width=320, height=176, bg="#070a12", highlightthickness=1, highlightbackground="#38bdf8")
        preview_canvas.grid(row=0, column=0, rowspan=4, padx=(4, 12), pady=2)
        preview_canvas.create_text(160, 88, text="Select a video above\nto scrub frames live", fill="#94a3b8", font=("Arial", 10, "bold"), justify="center")

        scrub_right = ttk.Frame(scrubber_frame, style="Card.TFrame")
        scrub_right.grid(row=0, column=1, sticky="ew")
        scrubber_frame.columnconfigure(1, weight=1)

        time_readout_lbl = tk.Label(scrub_right, text="Current Frame: 00:00:00.000  /  Total: 00:00:00.000", font=("Courier", 10, "bold"), bg="#131b2e", fg="#38bdf8")
        time_readout_lbl.pack(anchor="w", pady=(0, 4))

        scrub_var = tk.DoubleVar(value=0.0)
        scrub_scale = tk.Scale(
            scrub_right, variable=scrub_var, from_=0.0, to=100.0, resolution=0.05,
            orient="horizontal", length=580, showvalue=False,
            bg="#131b2e", fg="#f8fafc", troughcolor="#0f172a", highlightthickness=0
        )
        scrub_scale.pack(fill="x", pady=2)

        step_bar = ttk.Frame(scrub_right, style="Card.TFrame")
        step_bar.pack(fill="x", pady=4)

        edit_frame = ttk.LabelFrame(page, text="3. Configure Trim Segment & Crop for Selected Video", padding=6)
        edit_frame.pack(fill="x", padx=14, pady=3)

        ttk.Label(edit_frame, text="Trim Start (HH:MM:SS.mmm):", font=("Arial", 9, "bold"), background="#131b2e").grid(row=0, column=0, padx=4, pady=3, sticky="w")
        trim_start_ent = ttk.Entry(edit_frame, width=14)
        trim_start_ent.grid(row=0, column=1, padx=4, pady=3, sticky="w")
        trim_start_ent.insert(0, "00:00:00.000")

        ttk.Label(edit_frame, text="Trim End (Blank = To End):", font=("Arial", 9, "bold"), background="#131b2e").grid(row=0, column=2, padx=4, pady=3, sticky="w")
        trim_end_ent = ttk.Entry(edit_frame, width=14)
        trim_end_ent.grid(row=0, column=3, padx=4, pady=3, sticky="w")

        ttk.Label(edit_frame, text="Crop Mode:", font=("Arial", 9, "bold"), background="#131b2e").grid(row=1, column=0, padx=4, pady=3, sticky="w")
        crop_mode_var = tk.StringVar(value="No Crop (Original)")
        crop_combo = ttk.Combobox(
            edit_frame, textvariable=crop_mode_var, width=28, state="readonly",
            values=[
                "No Crop (Original)",
                "Cut Pixels from Edges (Top/Bottom/Left/Right)",
                "Center 9:16 Vertical (TikTok/Shorts)",
                "Center 16:9 Widescreen",
                "Center 1:1 Square"
            ]
        )
        crop_combo.grid(row=1, column=1, columnspan=2, padx=4, pady=3, sticky="w")

        edge_frame = ttk.Frame(edit_frame, style="Card.TFrame")
        edge_frame.grid(row=2, column=0, columnspan=4, sticky="w", padx=4, pady=2)

        ttk.Label(edge_frame, text="Cut Top (px):", background="#131b2e").grid(row=0, column=0, padx=2)
        cut_top = ttk.Entry(edge_frame, width=6)
        cut_top.grid(row=0, column=1, padx=4)
        cut_top.insert(0, "0")

        ttk.Label(edge_frame, text="Cut Bottom (px):", background="#131b2e").grid(row=0, column=2, padx=2)
        cut_bot = ttk.Entry(edge_frame, width=6)
        cut_bot.grid(row=0, column=3, padx=4)
        cut_bot.insert(0, "0")

        ttk.Label(edge_frame, text="Cut Left (px):", background="#131b2e").grid(row=0, column=4, padx=2)
        cut_left = ttk.Entry(edge_frame, width=6)
        cut_left.grid(row=0, column=5, padx=4)
        cut_left.insert(0, "0")

        ttk.Label(edge_frame, text="Cut Right (px):", background="#131b2e").grid(row=0, column=6, padx=2)
        cut_right = ttk.Entry(edge_frame, width=6)
        cut_right.grid(row=0, column=7, padx=4)
        cut_right.insert(0, "0")

        def build_crop_filter():
            mode = crop_mode_var.get()
            if mode == "No Crop (Original)":
                return ""
            elif mode == "Cut Pixels from Edges (Top/Bottom/Left/Right)":
                try:
                    t = int(cut_top.get() or 0)
                    b = int(cut_bot.get() or 0)
                    l = int(cut_left.get() or 0)
                    r = int(cut_right.get() or 0)
                except:
                    return ""
                if t == 0 and b == 0 and l == 0 and r == 0:
                    return ""
                return f"crop=in_w-{l+r}:in_h-{t+b}:{l}:{t}"
            elif mode == "Center 9:16 Vertical (TikTok/Shorts)":
                return "crop='min(in_w,in_h*9/16)':'min(in_h,in_w*16/9)'"
            elif mode == "Center 16:9 Widescreen":
                return "crop='min(in_w,in_h*16/9)':'min(in_h,in_w*9/16)'"
            elif mode == "Center 1:1 Square":
                return "crop='min(in_w,in_h)':'min(in_w,in_h)'"
            return ""

        def render_frame_at_time(sec_val):
            v_file = scrubber_state["current_video"]
            if not v_file or not os.path.exists(v_file) or scrubber_state["rendering"]:
                return
            scrubber_state["rendering"] = True
            dur = scrubber_state["duration"]
            sec_val = max(0.0, min(sec_val, max(0.0, dur - 0.05)))
            time_readout_lbl.config(
                text=f"Current Frame: {format_seconds_to_time(sec_val)}  /  Total: {format_seconds_to_time(dur)}"
            )
            crop_f = build_crop_filter()

            def grab_worker():
                temp_ppm = os.path.join(self.output_base, "_temp_scrub_preview.ppm")
                vf_parts = []
                if crop_f:
                    vf_parts.append(crop_f)
                vf_parts.append("scale=320:176:force_original_aspect_ratio=decrease,pad=320:176:(ow-iw)/2:(oh-ih)/2:black")
                cmd = [
                    "ffmpeg", "-y", "-ss", f"{sec_val:.3f}",
                    "-i", v_file, "-vf", ",".join(vf_parts),
                    "-frames:v", "1", "-f", "image2", temp_ppm
                ]
                res = self.run_ffmpeg(cmd)
                if res.returncode == 0 and os.path.exists(temp_ppm):
                    def update_canvas():
                        try:
                            img = tk.PhotoImage(file=temp_ppm)
                            scrubber_state["photo"] = img
                            preview_canvas.delete("all")
                            preview_canvas.create_image(160, 88, image=img)
                        except:
                            pass
                        scrubber_state["rendering"] = False
                    self.root.after(0, update_canvas)
                else:
                    scrubber_state["rendering"] = False

            threading.Thread(target=grab_worker, daemon=True).start()

        scrub_scale.bind("<ButtonRelease-1>", lambda e: render_frame_at_time(scrub_var.get()))
        crop_combo.bind("<<ComboboxSelected>>", lambda e: render_frame_at_time(scrub_var.get()))

        def step_scrubber(delta_sec):
            if not scrubber_state["current_video"]:
                return
            new_t = max(0.0, min(scrubber_state["duration"], scrub_var.get() + delta_sec))
            scrub_var.set(new_t)
            render_frame_at_time(new_t)

        def set_trim_from_scrubber(is_start=True):
            t_formatted = format_seconds_to_time(scrub_var.get())
            if is_start:
                trim_start_ent.delete(0, tk.END)
                trim_start_ent.insert(0, t_formatted)
            else:
                trim_end_ent.delete(0, tk.END)
                trim_end_ent.insert(0, t_formatted)

        ttk.Button(step_bar, text="⏪ -1s", width=8, command=lambda: step_scrubber(-1.0)).pack(side="left", padx=2)
        ttk.Button(step_bar, text="◀ -1 Frame", width=11, command=lambda: step_scrubber(-0.04)).pack(side="left", padx=2)
        ttk.Button(step_bar, text="▶ +1 Frame", width=11, command=lambda: step_scrubber(0.04)).pack(side="left", padx=2)
        ttk.Button(step_bar, text="⏩ +1s", width=8, command=lambda: step_scrubber(1.0)).pack(side="left", padx=2)
        ttk.Button(step_bar, text="🔄 Refresh Crop Frame", width=18, command=lambda: render_frame_at_time(scrub_var.get())).pack(side="left", padx=6)

        mark_bar = ttk.Frame(scrub_right, style="Card.TFrame")
        mark_bar.pack(fill="x", pady=4)
        ttk.Button(mark_bar, text="📍 Set Current Frame as Trim Start", command=lambda: set_trim_from_scrubber(True)).pack(side="left", padx=4)
        ttk.Button(mark_bar, text="🏁 Set Current Frame as Trim End", command=lambda: set_trim_from_scrubber(False)).pack(side="left", padx=4)

        def on_pool_select(event=None):
            sel = pool_list.curselection()
            if not sel:
                return
            v_file = source_videos[sel[0]]
            scrubber_state["current_video"] = v_file
            dur = self.get_media_duration(v_file)
            scrubber_state["duration"] = max(0.1, dur)
            scrub_scale.config(to=scrubber_state["duration"])
            scrub_var.set(0.0)
            render_frame_at_time(0.0)

        pool_list.bind("<<ListboxSelect>>", on_pool_select)

        def add_files_to_pool(file_paths):
            for fp in file_paths:
                clean_fp = fp.strip("{}").strip('"')
                if os.path.exists(clean_fp) and clean_fp not in source_videos:
                    source_videos.append(clean_fp)
                    pool_list.insert(tk.END, f"{len(source_videos)}. {os.path.basename(clean_fp)}  ({clean_fp})")
            if source_videos and not pool_list.curselection():
                pool_list.selection_set(0)
                on_pool_select()

        if HAS_DND:
            try:
                pool_list.drop_target_register(DND_FILES)
                pool_list.dnd_bind('<<Drop>>', lambda e: add_files_to_pool(self.root.tk.splitlist(e.data)))
            except:
                pass

        ttk.Button(
            pool_frame, text="➕ Add Videos (Multi-Select)", style="Accent.TButton", width=24,
            command=lambda: add_files_to_pool(filedialog.askopenfilenames(initialdir=self.output_base, filetypes=[("Video files", "*.mp4 *.mkv *.mov *.webm")]))
        ).grid(row=0, column=1, pady=2)

        def remove_selected_pool():
            sel = pool_list.curselection()
            if sel:
                idx = sel[0]
                pool_list.delete(idx)
                source_videos.pop(idx)

        ttk.Button(pool_frame, text="❌ Remove Selected Video", width=24, command=remove_selected_pool).grid(row=1, column=1, pady=2)
        ttk.Button(pool_frame, text="🗑️ Clear Pool", width=24, command=lambda: (pool_list.delete(0, tk.END), source_videos.clear())).grid(row=2, column=1, pady=2)

        timeline_segments = []

        def preview_selected_segment():
            sel = pool_list.curselection()
            if not sel:
                messagebox.showinfo("Select Video", "Click a video in the Source Pool first.")
                return
            v_file = source_videos[sel[0]]
            s_time = trim_start_ent.get().strip() or "00:00:00"
            e_time = trim_end_ent.get().strip()
            crop_f = build_crop_filter()

            ffplay_bin = shutil.which("ffplay") or shutil.which("ffplay.exe")
            if not ffplay_bin:
                self.open_last_file(v_file)
                return

            cmd = [ffplay_bin, "-autoexit", "-ss", s_time]
            if e_time:
                try:
                    dur = max(1.0, parse_time_to_seconds(e_time) - parse_time_to_seconds(s_time))
                    cmd.extend(["-t", f"{dur:.2f}"])
                except:
                    pass
            if crop_f:
                cmd.extend(["-vf", crop_f])
            cmd.append(v_file)
            subprocess.Popen(cmd)

        tl_frame = ttk.LabelFrame(page, text="4. Multi-Clip Trim Timeline (Segments will be merged in this exact order)", padding=6)
        tl_frame.pack(fill="both", expand=True, padx=14, pady=3)

        tl_list = tk.Listbox(tl_frame, height=5, width=105, bg="#0f172a", fg="#f8fafc", selectbackground="#2563eb")
        tl_list.grid(row=0, column=0, rowspan=4, padx=(0, 8), pady=2)

        def refresh_tl_listbox():
            tl_list.delete(0, tk.END)
            for i, seg in enumerate(timeline_segments, 1):
                c_desc = seg["crop_filter"] if seg["crop_filter"] else "Original Size"
                tl_list.insert(
                    tk.END,
                    f"Clip #{i}: {os.path.basename(seg['video'])} | Trim: {seg['start']} -> {seg['end'] or 'END'} | Crop: {c_desc}"
                )

        def add_segment_to_timeline():
            sel = pool_list.curselection()
            if not sel:
                messagebox.showinfo("Select Video", "Please select a video from the Source Pool (Box 1) first.")
                return
            v_file = source_videos[sel[0]]
            s_str = trim_start_ent.get().strip() or "00:00:00"
            e_str = trim_end_ent.get().strip()
            try:
                s_sec = parse_time_to_seconds(s_str)
                if e_str:
                    e_sec = parse_time_to_seconds(e_str)
                    if e_sec <= s_sec:
                        messagebox.showerror("Invalid Trim", "Trim End time must be greater than Trim Start time.")
                        return
            except Exception as ex:
                messagebox.showerror("Invalid Time", str(ex))
                return

            timeline_segments.append({
                "video": v_file,
                "start": s_str,
                "end": e_str,
                "crop_filter": build_crop_filter()
            })
            refresh_tl_listbox()

        def add_all_pool_videos_untouched():
            for v_file in source_videos:
                timeline_segments.append({
                    "video": v_file,
                    "start": trim_start_ent.get().strip() or "00:00:00",
                    "end": trim_end_ent.get().strip(),
                    "crop_filter": build_crop_filter()
                })
            refresh_tl_listbox()

        action_edit_frame = ttk.Frame(edit_frame, style="Card.TFrame")
        action_edit_frame.grid(row=0, column=4, rowspan=3, padx=10)
        ttk.Button(action_edit_frame, text="▶️ Play Segment (ffplay)", width=24, command=preview_selected_segment).pack(pady=2)
        ttk.Button(action_edit_frame, text="➕ Add Trim Segment to Timeline", style="Accent.TButton", width=24, command=add_segment_to_timeline).pack(pady=2)
        ttk.Button(action_edit_frame, text="📥 Add All Pool Videos to Timeline", width=24, command=add_all_pool_videos_untouched).pack(pady=2)

        def move_seg(delta):
            sel = tl_list.curselection()
            if not sel: return
            i = sel[0]
            new_i = i + delta
            if 0 <= new_i < len(timeline_segments):
                timeline_segments[i], timeline_segments[new_i] = timeline_segments[new_i], timeline_segments[i]
                refresh_tl_listbox()
                tl_list.selection_set(new_i)

        def remove_seg():
            sel = tl_list.curselection()
            if sel:
                timeline_segments.pop(sel[0])
                refresh_tl_listbox()

        ttk.Button(tl_frame, text="⬆️ Move Clip Up", width=22, command=lambda: move_seg(-1)).grid(row=0, column=1, pady=2)
        ttk.Button(tl_frame, text="⬇️ Move Clip Down", width=22, command=lambda: move_seg(1)).grid(row=1, column=1, pady=2)
        ttk.Button(tl_frame, text="❌ Delete Clip", width=22, command=remove_seg).grid(row=2, column=1, pady=2)
        ttk.Button(tl_frame, text="🗑️ Clear Timeline", width=22, command=lambda: (timeline_segments.clear(), refresh_tl_listbox())).grid(row=3, column=1, pady=2)

        exp_frame = ttk.Frame(page)
        exp_frame.pack(fill="x", padx=14, pady=4)

        ttk.Label(exp_frame, text="HD Resolution:", font=("Arial", 10, "bold")).pack(side="left", padx=4)
        hd_res_var = tk.StringVar(value="Keep Cropped/Original HD Size")
        ttk.Combobox(
            exp_frame, textvariable=hd_res_var, width=28, state="readonly",
            values=[
                "Keep Cropped/Original HD Size",
                "1080x1920 Full HD Vertical (9:16)",
                "1920x1080 Full HD Landscape (16:9)",
                "1080x1080 Full HD Square (1:1)"
            ]
        ).pack(side="left", padx=4)

        ttk.Button(
            exp_frame, text="▶️ Open Last File",
            command=lambda: self.open_last_file(studio_last_out["path"] or self.last_output_file)
        ).pack(side="left", padx=4)
        ttk.Button(
            exp_frame, text="📂 Open Local Folder",
            command=lambda: self.open_last_local_folder(studio_last_out["path"] or self.last_output_file)
        ).pack(side="left", padx=4)

        tc_status = tk.Label(page, text="Add segments to timeline and click Export HD Video.", font=("Arial", 10, "bold"), bg="#0b0f19", fg="#38bdf8")
        tc_status.pack(pady=2)

        tc_prog = ttk.Progressbar(page, orient="horizontal", mode="determinate", length=580)
        tc_prog.pack(pady=2)

        def export_hd_timeline():
            if not timeline_segments:
                messagebox.showinfo("Empty Timeline", "Please add at least 1 trim segment to the timeline (Box 4).")
                return

            first_vid = timeline_segments[0]["video"]
            target_dir = self.get_organized_output_dir(first_vid, "3_Trimmed_Cropped_HD")
            clean_base = clean_folder_Title(first_vid)
            save_path = os.path.join(target_dir, f"{clean_base}_HD_Trimmed_{datetime.datetime.now().strftime('%H%M%S')}.mp4")

            res_choice = hd_res_var.get()
            tc_prog["value"] = 0

            def worker():
                temp_edit_dir = os.path.join(target_dir, "temp_hd_editor")
                os.makedirs(temp_edit_dir, exist_ok=True)
                rendered_clips = []

                try:
                    total_segs = len(timeline_segments)
                    for idx, seg in enumerate(timeline_segments, 1):
                        tc_status.config(text=f"Rendering Sync-Locked HD Segment {idx}/{total_segs}...", fg="#f59e0b")
                        clip_out = os.path.join(temp_edit_dir, f"seg_{idx:03d}.mp4")

                        vf_parts = []
                        if seg["crop_filter"]:
                            vf_parts.append(seg["crop_filter"])

                        if "1080x1920" in res_choice:
                            vf_parts.append("scale=1080:1920:force_original_aspect_ratio=decrease,pad=1080:1920:(ow-iw)/2:(oh-ih)/2,setsar=1")
                        elif "1920x1080" in res_choice:
                            vf_parts.append("scale=1920:1080:force_original_aspect_ratio=decrease,pad=1920:1080:(ow-iw)/2:(oh-ih)/2,setsar=1")
                        elif "1080x1080" in res_choice:
                            vf_parts.append("scale=1080:1080:force_original_aspect_ratio=decrease,pad=1080:1080:(ow-iw)/2:(oh-ih)/2,setsar=1")
                        else:
                            vf_parts.append("scale='trunc(iw/2)*2':'trunc(ih/2)*2',setsar=1")

                        vf_chain = ",".join(vf_parts)

                        cmd = ["ffmpeg", "-y", "-fflags", "+genpts", "-ss", seg["start"]]
                        if seg["end"]:
                            cmd.extend(["-to", seg["end"]])
                        cmd.extend([
                            "-i", seg["video"],
                            "-vf", vf_chain,
                            "-fps_mode", "cfr", "-r", "30",
                            "-video_track_timescale", "90000",
                            "-c:v", "libx264", "-preset", "fast", "-crf", "18", "-pix_fmt", "yuv420p",
                            "-af", "aresample=async=1000:min_hard_comp=0.010000:first_pts=0,apad",
                            "-c:a", "aac", "-b:a", "192k", "-ar", "48000", "-ac", "2",
                            "-shortest", "-avoid_negative_ts", "make_zero", clip_out
                        ])

                        res = self.run_ffmpeg(cmd)
                        if res.returncode != 0 or not os.path.exists(clip_out):
                            tc_status.config(text=f"❌ Failed on Segment {idx}. Check Error Log.", fg="#f43f5e")
                            self.log_message(f"HD Editor Segment {idx} Error:\n{res.stderr}")
                            return

                        rendered_clips.append(clip_out)
                        tc_prog["value"] = int((idx / (total_segs + 1)) * 100)

                    tc_status.config(text="Merging all HD segments into organized folder...", fg="#f59e0b")
                    m_res = self.concat_video_files_synced(rendered_clips, save_path, normalize_first=False)

                    for rc in rendered_clips:
                        try: os.remove(rc)
                        except: pass
                    try:
                        os.rmdir(temp_edit_dir)
                    except:
                        pass

                    if m_res.returncode == 0 and os.path.exists(save_path):
                        studio_last_out["path"] = save_path
                        self.record_last_output(save_path)
                        tc_prog["value"] = 100
                        tc_status.config(text=f"✅ HD Movie Saved: {os.path.basename(save_path)}", fg="#10b981")
                        self.log_message(f"HD TRIM & CROP EXPORT COMPLETED: {save_path}")
                    else:
                        tc_status.config(text="❌ Final Merge Failed. Check Error Log.", fg="#f43f5e")
                        self.log_message(f"HD Merge Error:\n{m_res.stderr}")
                except Exception as ex:
                    tc_status.config(text=f"Error: {str(ex)}", fg="#f43f5e")

            threading.Thread(target=worker, daemon=True).start()

        ttk.Button(exp_frame, text="🎬 Export Full HD Video", style="Accent.TButton", command=export_hd_timeline).pack(side="right", padx=6)

    # =========================================================================
    # ORGANIZED FOLDER BUILDER, URL HISTORY & CORE NARTO v1.6.1 ENGINE
    # =========================================================================
    def get_organized_output_dir(self, movie_name_or_path, action_type="1_Downloaded_Merged"):
        date_folder = datetime.datetime.now().strftime("%Y-%m-%d")
        clean_movie = clean_folder_Title(movie_name_or_path)
        target_dir = os.path.join(self.output_base, date_folder, clean_movie, action_type)
        os.makedirs(target_dir, exist_ok=True)
        return target_dir

    def record_last_output(self, file_path):
        if file_path and os.path.exists(file_path):
            self.last_output_file = os.path.abspath(file_path)
            self.last_output_folder = os.path.dirname(self.last_output_file)

    def find_newest_video_fallback(self):
        if self.last_output_file and os.path.exists(self.last_output_file):
            return self.last_output_file
        newest_file = ""
        newest_mtime = 0
        for root_dir, _, files in os.walk(self.output_base):
            if "temp_" in root_dir:
                continue
            for f in files:
                if f.lower().endswith(".mp4") and not f.endswith(".synclock.mp4") and not f.startswith("_temp_"):
                    full_p = os.path.join(root_dir, f)
                    try:
                        mt = os.path.getmtime(full_p)
                        if mt > newest_mtime:
                            newest_mtime = mt
                            newest_file = full_p
                    except:
                        pass
        if newest_file:
            self.last_output_file = newest_file
            self.last_output_folder = os.path.dirname(newest_file)
        return newest_file

    def open_last_file(self, custom_path=None):
        target = custom_path if (custom_path and os.path.exists(custom_path)) else self.find_newest_video_fallback()
        if not target or not os.path.exists(target):
            messagebox.showinfo("No File Found", "No finished or fixed video file found yet.")
            return
        try:
            if sys.platform == "win32":
                os.startfile(target)
            elif sys.platform == "darwin":
                subprocess.run(["open", target])
            else:
                subprocess.run(["xdg-open", target])
        except Exception as e:
            messagebox.showerror("Error", f"Could not open file:\n{str(e)}")

    def open_last_local_folder(self, custom_path=None):
        target = custom_path if (custom_path and os.path.exists(custom_path)) else self.find_newest_video_fallback()
        try:
            if target and os.path.exists(target):
                if sys.platform == "win32":
                    subprocess.run(["explorer", "/select,", os.path.normpath(target)])
                elif sys.platform == "darwin":
                    subprocess.run(["open", "-R", target])
                else:
                    subprocess.run(["xdg-open", os.path.dirname(target)])
            else:
                folder = self.last_output_folder if os.path.exists(self.last_output_folder) else self.output_base
                if sys.platform == "win32":
                    os.startfile(folder)
                elif sys.platform == "darwin":
                    subprocess.run(["open", folder])
                else:
                    subprocess.run(["xdg-open", folder])
        except Exception as e:
            messagebox.showerror("Error", f"Could not open folder:\n{str(e)}")

    def get_media_duration(self, file_path):
        if not os.path.exists(file_path):
            return 0.0
        ffprobe_bin = shutil.which("ffprobe") or shutil.which("ffprobe.exe")
        kwargs = {"creationflags": 0x08000000} if sys.platform == "win32" else {}
        if ffprobe_bin:
            try:
                res = subprocess.run(
                    [ffprobe_bin, "-v", "error", "-show_entries", "format=duration", "-of", "default=noprint_wrappers=1:nokey=1", file_path],
                    capture_output=True, text=True, **kwargs
                )
                val = float(res.stdout.strip())
                if val > 0:
                    return val
            except:
                pass
        res = self.run_ffmpeg(["ffmpeg", "-i", file_path])
        m = re.search(r"Duration:\s*(\d+):(\d+):(\d+(?:\.\d+)?)", res.stderr or "")
        if m:
            return int(m.group(1)) * 3600 + int(m.group(2)) * 60 + float(m.group(3))
        return 0.0

    def normalize_clip_for_sync(self, file_path):
        if not self.sync_lock_var.get() or not os.path.exists(file_path):
            return file_path

        norm_path = file_path + ".synclock.mp4"
        cmd = [
            "ffmpeg", "-y", "-i", file_path,
            "-map", "0:v:0", "-map", "0:a:0?",
            "-c:v", "copy", "-video_track_timescale", "90000",
            "-af", "aresample=async=1000:min_hard_comp=0.010000:first_pts=0,apad",
            "-c:a", "aac", "-b:a", "192k", "-ar", "48000", "-ac", "2",
            "-shortest", "-avoid_negative_ts", "make_zero", norm_path
        ]
        res = self.run_ffmpeg(cmd)
        if res.returncode == 0 and self.is_valid_video_file(norm_path):
            try: os.replace(norm_path, file_path)
            except: pass
        else:
            if os.path.exists(norm_path):
                try: os.remove(norm_path)
                except: pass
        return file_path

    def concat_video_files_synced(self, file_list, final_output, normalize_first=False, status_prefix="Merging"):
        if normalize_first and self.sync_lock_var.get():
            total = len(file_list)
            for idx, fpath in enumerate(file_list, 1):
                if self.stop_flag:
                    break
                self.update_status(f"{status_prefix}: Sync-locking clip {idx}/{total}...", "#f59e0b")
                self.normalize_clip_for_sync(fpath)

        list_file = final_output + ".concat_list.txt"
        with open(list_file, "w", encoding="utf-8") as f:
            for vid in file_list:
                f.write(f"file '{vid.replace(chr(92), '/')}'\n")

        ffmpeg_cmd = [
            "ffmpeg", "-y", "-f", "concat", "-safe", "0",
            "-i", list_file, "-c", "copy",
            "-movflags", "+faststart", "-avoid_negative_ts", "make_zero",
            final_output
        ]
        res = self.run_ffmpeg(ffmpeg_cmd)
        if os.path.exists(list_file):
            try: os.remove(list_file)
            except: pass
        if res.returncode == 0 and os.path.exists(final_output):
            self.record_last_output(final_output)
        return res

    def extract_narto_subtitle_url(self, domain, narto_playlist, episode, html=""):
        sub_candidates = []

        def add_sub(u, lang_hint=""):
            if not u or not isinstance(u, str):
                return
            u = u.replace("\\/", "/").strip()
            if not u.startswith("http"):
                if u.startswith("/"):
                    u = f"https://{domain}{u}"
                else:
                    return
            is_en = 1 if ("en" in lang_hint.lower() or "eng" in u.lower()) else 0
            sub_candidates.append((is_en, u))

        if narto_playlist:
            ep_item = next((item for item in narto_playlist if item.get('route_episode_number') == episode or item.get('number') == episode), None)
            if ep_item and isinstance(ep_item, dict):
                for k in ("subtitle_url", "sub_url", "vtt_url", "srt_url", "caption_url", "captions_url", "subtitle"):
                    val = ep_item.get(k)
                    if isinstance(val, str):
                        add_sub(val, "en")
                for list_k in ("subtitles", "episode_multi_subtitle", "multi_subtitles", "captions", "subtitle_list"):
                    sub_list = ep_item.get(list_k)
                    if isinstance(sub_list, list):
                        for item in sub_list:
                            if isinstance(item, dict):
                                lang = str(item.get("lang") or item.get("language") or item.get("label") or item.get("code") or "")
                                for uk in ("url", "subtitle_url", "src", "file", "vtt_url", "srt_url"):
                                    if item.get(uk):
                                        add_sub(item.get(uk), lang)
                    elif isinstance(sub_list, dict):
                        for lang, u_val in sub_list.items():
                            if isinstance(u_val, str):
                                add_sub(u_val, str(lang))

        if html:
            m_init_sub = re.search(r'const\s+initialSubtitleUrl\s*=\s*"([^"]+)";', html)
            if m_init_sub and m_init_sub.group(1):
                add_sub(m_init_sub.group(1), "en")

        if not sub_candidates:
            return ""
        sub_candidates.sort(key=lambda x: x[0], reverse=True)
        return sub_candidates[0][1]

    def parse_and_shift_subtitle_cues(self, raw_sub_text, offset_seconds):
        if not raw_sub_text or len(raw_sub_text.strip()) < 10:
            return []
        text = raw_sub_text.replace("\r\n", "\n").replace("\r", "\n")
        text = re.sub(r"^WEBVTT[^\n]*\n+", "", text, flags=re.IGNORECASE)
        blocks = re.split(r"\n\s*\n", text.strip())
        shifted_cues = []

        time_pattern = re.compile(
            r"((?:\d{1,2}:)?\d{2}:\d{2}[,\.]\d{2,3})\s*-->\s*((?:\d{1,2}:)?\d{2}:\d{2}[,\.]\d{2,3})"
        )

        for b in blocks:
            lines = [ln.strip() for ln in b.splitlines() if ln.strip()]
            if not lines:
                continue
            time_line_idx = -1
            m_time = None
            for i, ln in enumerate(lines):
                m = time_pattern.search(ln)
                if m:
                    time_line_idx = i
                    m_time = m
                    break
            if m_time is None or time_line_idx == -1:
                continue
            cue_lines = lines[time_line_idx + 1:]
            if not cue_lines:
                continue
            try:
                start_s = parse_time_to_seconds(m_time.group(1)) + offset_seconds
                end_s = parse_time_to_seconds(m_time.group(2)) + offset_seconds
                shifted_cues.append((
                    format_seconds_to_time(start_s, srt_format=True),
                    format_seconds_to_time(end_s, srt_format=True),
                    "\n".join(cue_lines)
                ))
            except:
                pass
        return shifted_cues

    def detect_hardcoded_subtitle_onsets(self, v_path, status_callback=None):
        if status_callback:
            status_callback("Scanning video frames for hardcoded on-screen subtitles (bottom text band)...")
        vf_expr = (
            "fps=10,"
            "crop=iw*0.76:ih*0.16:iw*0.12:ih*0.73,"
            "lutyuv=y='if(gt(val,235),255,0)',"
            "signalstats,metadata=mode=print"
        )
        cmd = ["ffmpeg", "-i", v_path, "-vf", vf_expr, "-an", "-f", "null", "-"]
        res = self.run_sync_cancellable_ffmpeg(cmd)
        if self.sync_stop_flag or not res:
            return []
        output = (res.stdout or "") + "\n" + (res.stderr or "")

        pts_times = []
        yavg_vals = []
        cur_t = None
        for line in output.splitlines():
            if "pts_time:" in line:
                m_t = re.search(r"pts_time:\s*(\d+(?:\.\d+)?)", line)
                if m_t:
                    cur_t = float(m_t.group(1))
            elif "lavfi.signalstats.YAVG=" in line and cur_t is not None:
                m_y = re.search(r"YAVG=\s*(\d+(?:\.\d+)?)", line)
                if m_y:
                    pts_times.append(cur_t)
                    yavg_vals.append(float(m_y.group(1)))
                    cur_t = None

        if len(yavg_vals) < 10:
            return []

        onsets = []
        last_onset = -1.0
        for i in range(1, len(yavg_vals)):
            prev_y = yavg_vals[i - 1]
            curr_y = yavg_vals[i]
            t = pts_times[i]
            if ((prev_y < 1.5 and curr_y >= 2.2) or (curr_y - prev_y >= 2.0 and curr_y >= 3.0)) and (t - last_onset >= 0.45):
                onsets.append(t)
                last_onset = t
        return onsets

    def run_sync_cancellable_ffmpeg(self, cmd):
        kwargs = {"creationflags": 0x08000000} if sys.platform == "win32" else {}
        try:
            self.sync_process = subprocess.Popen(
                cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                text=True, encoding="utf-8", errors="ignore", **kwargs
            )
            stdout, stderr = self.sync_process.communicate()
            rc = self.sync_process.returncode
            self.sync_process = None

            class ResObj:
                pass
            r = ResObj()
            r.returncode = rc
            r.stdout = stdout
            r.stderr = stderr
            return r
        except Exception as e:
            self.sync_process = None
            class ResObj:
                pass
            r = ResObj()
            r.returncode = -1
            r.stdout = ""
            r.stderr = str(e)
            return r

    def stop_sync_task(self):
        self.sync_stop_flag = True
        if self.sync_process:
            try:
                self.sync_process.terminate()
            except:
                pass

    def load_history(self):
        default_hist = {"1": [], "2": [], "3": [], "4": [], "5": [], "6": [], "7": []}
        if os.path.exists(self.history_file):
            try:
                with open(self.history_file, "r", encoding="utf-8") as f:
                    data = json.load(f)
                    for k in default_hist:
                        if k in data and isinstance(data[k], list):
                            default_hist[k] = data[k][:5]
            except:
                pass
        return default_hist

    def save_to_history(self, source_id, url):
        s_id = str(source_id)
        if not url:
            return
        hist = self.link_history.get(s_id, [])
        if url in hist:
            hist.remove(url)
        hist.insert(0, url)
        self.link_history[s_id] = hist[:5]
        try:
            with open(self.history_file, "w", encoding="utf-8") as f:
                json.dump(self.link_history, f, indent=2)
        except:
            pass
        if s_id in self.url_widgets:
            self.url_widgets[s_id]['values'] = self.link_history[s_id]

    def create_url_row(self, parent, source_id, width=48, style="TFrame"):
        row_frame = ttk.Frame(parent, style=style)
        row_frame.pack(pady=1)
        return self.build_url_controls_in_frame(row_frame, source_id, width=width)

    def build_url_controls_in_frame(self, row_frame, source_id, width=48, register_main=True):
        combo = ttk.Combobox(row_frame, width=width, values=self.link_history.get(source_id, []))
        combo.grid(row=0, column=0, padx=(0, 4))
        if register_main:
            self.url_widgets[source_id] = combo

        def do_paste():
            try:
                clip = self.root.clipboard_get().strip()
                combo.delete(0, tk.END)
                combo.insert(0, clip)
            except:
                pass

        def do_clear():
            combo.delete(0, tk.END)

        def show_history_menu(event):
            menu = tk.Menu(self.root, tearoff=0, bg="#1e293b", fg="#f8fafc", activebackground="#2563eb", activeforeground="#ffffff")
            items = self.link_history.get(source_id, [])
            if not items:
                menu.add_command(label="(No history yet)", state="disabled")
            else:
                for idx, item_url in enumerate(items, 1):
                    display = item_url if len(item_url) <= 65 else item_url[:62] + "..."
                    menu.add_command(
                        label=f"{idx}. {display}",
                        command=lambda u=item_url: (combo.delete(0, tk.END), combo.insert(0, u))
                    )
                menu.add_separator()
                def clear_hist():
                    self.link_history[source_id] = []
                    combo['values'] = []
                    try:
                        with open(self.history_file, "w", encoding="utf-8") as f:
                            json.dump(self.link_history, f, indent=2)
                    except:
                        pass
                menu.add_command(label="🗑️ Clear History", command=clear_hist)
            menu.tk_popup(event.x_root, event.y_root)

        paste_btn = ttk.Button(row_frame, text="📋 Paste", width=8, command=do_paste)
        paste_btn.grid(row=0, column=1, padx=2)

        del_btn = ttk.Button(row_frame, text="❌ Delete", width=8, command=do_clear)
        del_btn.grid(row=0, column=2, padx=2)

        hist_btn = ttk.Button(row_frame, text="🕒 History", width=9)
        hist_btn.grid(row=0, column=3, padx=2)
        hist_btn.bind("<Button-1>", show_history_menu)

        return combo

    def get_yt_dlp_path(self):
        sys_path = shutil.which("yt-dlp") or shutil.which("yt-dlp.exe")
        if sys_path:
            return sys_path

        if sys.platform == "win32":
            return os.path.join(self.base_dir, "venv", "Scripts", "yt-dlp.exe")
        else:
            return os.path.join(self.base_dir, "venv", "bin", "yt-dlp")

    def get_fast_accelerator_args(self):
        """v1.8.0 speed profile for Shortmax, Dailymotion, TikTok and Direct (Narto Original keeps get_accelerator_args).
        HLS/DASH go through yt-dlp's native downloader with 16 parallel fragments (faster and safer than aria2c
        for segmented streams); plain files go through aria2c with 16 connections."""
        if not self.turbo_var.get():
            return self.get_accelerator_args()
        args = ["-N", "16", "--buffer-size", "1M", "--http-chunk-size", "10M",
                "--retries", "10", "--fragment-retries", "10", "--newline"]
        aria_path = self.get_aria2c_path()
        if aria_path:
            args.extend([
                "--downloader", aria_path,
                "--downloader", "m3u8,dash:native",
                "--downloader-args", "aria2c:-x 16 -s 16 -k 1M --file-allocation=none --max-tries=5 --retry-wait=1 --summary-interval=1"
            ])
        return args

    # --- Shortmax: cookie + browser-impersonation fallback chain (v1.8.0) ---
    SHORTMAX_COOKIE_ERR = re.compile(
        r"(could not (find|copy)[^\n]*cookie|failed to decrypt|dpapi|cookie[^\n]*(locked|permission)|"
        r"unsupported browser|keyring|could not find [a-z]+ cookies database)", re.IGNORECASE
    )

    def shortmax_cookie_chain(self):
        chain = []
        cookie_file = os.path.join(self.base_dir, "shortmax_cookies.txt")
        if os.path.exists(cookie_file):
            chain.append(["--cookies", cookie_file])
        browsers = ["chrome", "edge", "firefox", "brave", "opera"]
        if sys.platform == "darwin":
            browsers.insert(0, "safari")
        chain += [["--cookies-from-browser", b] for b in browsers]
        chain.append([])  # last resort: no cookies
        return chain

    def shortmax_impersonate_available(self, yt_dlp_path):
        cached = getattr(self, "_sm_impersonate_ok", None)
        if cached is not None:
            return cached
        ok = False
        try:
            kwargs = {"creationflags": 0x08000000} if sys.platform == "win32" else {}
            res = subprocess.run([yt_dlp_path, "--list-impersonate-targets"], capture_output=True, text=True,
                                 encoding="utf-8", errors="ignore", timeout=40, **kwargs)
            for ln in (res.stdout or "").splitlines():
                if ln.strip().lower().startswith("chrome") and "unavailable" not in ln.lower():
                    ok = True
                    break
        except Exception:
            ok = False
        self._sm_impersonate_ok = ok
        if not ok:
            self.log_message("Shortmax: browser impersonation unavailable (curl_cffi missing) — continuing without it. "
                             "For best results use the official yt-dlp.exe or: pip install \"yt-dlp[default,curl-cffi]\"")
        return ok

    def shortmax_auth_args(self, yt_dlp_path):
        chain = self.shortmax_cookie_chain()
        idx = min(getattr(self, "_sm_cookie_idx", 0), len(chain) - 1)
        args = list(chain[idx])
        if self.shortmax_impersonate_available(yt_dlp_path):
            args += ["--impersonate", "chrome", "--extractor-args", "generic:impersonate"]
        return args

    def shortmax_recover_from_error(self, err):
        """True when the failure was cookies/impersonation and the next attempt uses a different setup."""
        if "impersonate target" in err.lower() and getattr(self, "_sm_impersonate_ok", None):
            self._sm_impersonate_ok = False
            self.log_message("Shortmax: impersonation failed, retrying without it.")
            return True
        # A Cloudflare 403 means this browser's cookies don't carry a passed check: try the next browser
        if self.SHORTMAX_COOKIE_ERR.search(err) or "cloudflare" in err.lower():
            chain = self.shortmax_cookie_chain()
            idx = getattr(self, "_sm_cookie_idx", 0)
            if idx < len(chain) - 1:
                self._sm_cookie_idx = idx + 1
                nxt = " ".join(chain[idx + 1]) or "no cookies"
                self.log_message(f"Shortmax: cookie source failed ({' '.join(chain[idx])}). Trying: {nxt}")
                self.update_status(f"Shortmax: trying cookies from {nxt.replace('--cookies-from-browser ', '')}...", "orange")
                return True
        return False

    def get_accelerator_args(self, use_aria=True):
        if not self.turbo_var.get():
            return ["-N", "4", "--newline"]

        args = ["-N", "16", "--buffer-size", "16K", "--http-chunk-size", "10M", "--newline"]

        if use_aria:
            aria_path = shutil.which("aria2c") or shutil.which("aria2c.exe")
            if aria_path:
                args.extend([
                    "--downloader", "aria2c",
                    "--downloader-args", "aria2c:-x 16 -s 16 -k 1M"
                ])
        return args

    def is_valid_video_file(self, file_path):
        if not os.path.exists(file_path):
            return False
        try:
            size = os.path.getsize(file_path)
            if size < 102400:
                return False
            with open(file_path, "rb") as f:
                header = f.read(512)
            head_lower = header.lower().lstrip()
            for bad_sig in (b"<!doctype", b"<html", b"<head", b"<script", b"webvtt", b'{"error"', b'{"ok":false'):
                if head_lower.startswith(bad_sig):
                    return False
            return True
        except:
            return False

    def run_yt_dlp_with_progress(self, yt_dlp_cmd):
        self.progress_bar['value'] = 0
        self.detail_label.config(text="Connecting to media server...")
        self.root.update_idletasks()

        err_accumulator = []

        try:
            kwargs = {}
            if sys.platform == "win32":
                kwargs["creationflags"] = 0x08000000

            self.current_process = subprocess.Popen(
                yt_dlp_cmd,
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                text=True,
                bufsize=1,
                universal_newlines=True,
                **kwargs
            )

            for line in self.current_process.stdout:
                if self.stop_flag:
                    self.current_process.terminate()
                    break

                line = line.strip()
                if not line: continue

                err_accumulator.append(line)
                if len(err_accumulator) > 25:
                    err_accumulator.pop(0)

                if "[download]" in line and "%" in line:
                    pct_match = re.search(r'(\d+\.\d+)%', line)
                    if pct_match:
                        try: self.progress_bar['value'] = float(pct_match.group(1))
                        except: pass
                    self.detail_label.config(text=line.replace("[download]", "").strip())
                    self.root.update_idletasks()

                elif "DL:" in line and "%" in line:
                    pct_match = re.search(r'\((\d+)%\)', line)
                    if pct_match:
                        try: self.progress_bar['value'] = float(pct_match.group(1))
                        except: pass
                    clean_aria = re.sub(r'\[#\w+\s+', '', line).replace(']', '')
                    self.detail_label.config(text=f"Aria2c: {clean_aria}")
                    self.root.update_idletasks()

            self.current_process.wait()

            if self.stop_flag:
                return False, "User stopped process."

            if self.current_process.returncode == 0:
                self.progress_bar['value'] = 100
                self.detail_label.config(text="Download Complete.")
                return True, ""
            else:
                return False, "\n".join(err_accumulator)

        except Exception as e:
            return False, str(e)

    def log_message(self, msg):
        timestamp = datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S")
        formatted_msg = f"[{timestamp}] [{self.version}] {msg}\n"

        if "error" in msg.lower() or "failed" in msg.lower() or "exception" in msg.lower() or "crash" in msg.lower():
            formatted_msg = f"\n\n{formatted_msg}\n\n"

        self.current_run_log += formatted_msg

        try:
            with open(self.log_file, "w", encoding="utf-8") as f:
                f.write(self.current_run_log + "\n\n" + self.previous_runs_log)
        except:
            pass

    def reset_buttons(self):
        self.start_btn1.config(state="normal")
        self.start_btn2.config(state="normal")
        self.start_btn3.config(state="normal")
        self.start_btn4.config(state="normal")
        self.start_btn5.config(state="normal")
        self.start_btn_dm.config(state="normal")
        self.start_btn_torrent.config(state="normal")
        self.start_btn_narto_claude.config(state="normal")
        self.stop_btn.config(state="disabled")
        self.stitch_btn.config(state="normal")
        self.merge_btn.config(state="normal")
        self.progress_bar['value'] = 0
        self.detail_label.config(text="")

    def disable_buttons_for_run(self):
        self.start_btn1.config(state="disabled")
        self.start_btn2.config(state="disabled")
        self.start_btn3.config(state="disabled")
        self.start_btn4.config(state="disabled")
        self.start_btn5.config(state="disabled")
        self.start_btn_dm.config(state="disabled")
        self.start_btn_torrent.config(state="disabled")
        self.start_btn_narto_claude.config(state="disabled")
        self.stop_btn.config(state="normal")
        self.stitch_btn.config(state="disabled")
        self.merge_btn.config(state="disabled")

    def open_browser(self, source):
        raw_url = self.url_entry1.get().strip() if source == 1 else self.url_entry2.get().strip()
        if raw_url:
            url = self.sanitize_url(raw_url)
            webbrowser.open(url)
            self.update_status("Solve captcha in Browser, completely QUIT, then Start.", "#f59e0b")
        else:
            messagebox.showerror("Error", "Please paste a URL first.")

    def open_folder(self):
        self.open_last_local_folder()

    def open_log(self):
        if os.path.exists(self.log_file):
            try:
                if sys.platform == "win32":
                    os.startfile(self.log_file)
                else:
                    subprocess.run(["open", self.log_file])
            except Exception as e:
                messagebox.showerror("Error", f"Could not open log file:\n{str(e)}")
        else:
            messagebox.showinfo("Log", "No errors logged yet.")

    def stop_download(self):
        self.stop_flag = True
        self.update_status("Stopping... (Canceling active task)", "#f43f5e")
        for proc in list(getattr(self, "narto_claude_procs", ()) or ()):
            try: proc.terminate()
            except: pass
        if self.current_process:
            try:
                self.current_process.terminate()
            except:
                pass

    def run_ffmpeg(self, cmd):
        kwargs = {}
        if sys.platform == "win32":
            kwargs["creationflags"] = 0x08000000
        return subprocess.run(cmd, capture_output=True, text=True, encoding="utf-8", errors="ignore", **kwargs)

    def stitch_videos(self):
        vid_files = filedialog.askopenfilenames(initialdir=self.output_base, title="Select Videos to Stitch", filetypes=[("MP4 files", "*.mp4")])
        if not vid_files or len(vid_files) < 2:
            messagebox.showinfo("Info", "Please select at least 2 videos to stitch.")
            return

        vid_files = list(sorted(vid_files, key=natural_sort_key))

        self.update_status(f"Sync-locking & stitching {len(vid_files)} videos...", "#f59e0b")
        self.root.update()

        def run_stitch():
            base_name = clean_folder_Title(vid_files[0])
            target_dir = self.get_organized_output_dir(base_name, "4_Stitched_Merged")
            final_output = os.path.join(target_dir, f"{base_name}_Stitched_Final.mp4")
            try:
                res = self.concat_video_files_synced(vid_files, final_output, normalize_first=True, status_prefix="Stitching")
                if res.returncode == 0:
                    self.record_last_output(final_output)
                    self.update_status("Success! Videos Stitched (Sync-Locked).", "#10b981")
                    self.log_message(f"STITCH COMPLETED: Saved to {final_output}")
                else:
                    self.update_status("Stitch Error. Check Log.", "#f43f5e")
                    self.log_message(f"FFMPEG Error: {res.stderr}")
            except Exception as e:
                self.update_status("Stitch Error. Is FFMPEG installed?", "#f43f5e")
                self.log_message(f"Stitch Error: {str(e)}")

        threading.Thread(target=run_stitch, daemon=True).start()

    def merge_folder(self):
        folder = filedialog.askdirectory(initialdir=self.output_base, title="Select Temp Folder to Merge")
        if not folder: return

        mp4_files = [f for f in os.listdir(folder) if f.endswith('.mp4') and not f.endswith('.synclock.mp4')]
        mp4_files.sort(key=natural_sort_key)

        if not mp4_files:
            messagebox.showerror("Error", "No MP4 files found in selected folder.")
            return

        series_name = clean_folder_Title(os.path.basename(folder).replace("temp_", ""))
        target_dir = self.get_organized_output_dir(series_name, "4_Stitched_Merged")
        full_paths = []
        ep_numbers = []
        for mp4 in mp4_files:
            full_paths.append(os.path.join(folder, mp4))
            match = re.search(r'ep_(\d+)', mp4)
            if match:
                ep_numbers.append(int(match.group(1)))

        if ep_numbers:
            first_ep = ep_numbers[0]
            last_ep = ep_numbers[-1]
            range_str = f"EP{first_ep}" if first_ep == last_ep else f"EP{first_ep}-EP{last_ep}"
            final_output = os.path.join(target_dir, f"{series_name}_{range_str}.mp4")
        else:
            last_ep = len(mp4_files)
            final_output = os.path.join(target_dir, f"{series_name}_Manual_Merge.mp4")

        self.update_status(f"Sync-locking & merging {len(full_paths)} files...", "#f59e0b")
        self.root.update()

        def run_merge():
            try:
                res = self.concat_video_files_synced(full_paths, final_output, normalize_first=True, status_prefix="Manual Merge")
                if res.returncode == 0:
                    self.record_last_output(final_output)
                    for fp in full_paths:
                        try: os.remove(fp)
                        except: pass
                    try:
                        os.rmdir(folder)
                    except:
                        pass
                    self.update_status(f"Success! Sync-Locked Merge up to Ep {last_ep}.", "#10b981")
                else:
                    self.update_status("Merge Error. Check Log.", "#f43f5e")
                    self.log_message(f"Merge FFMPEG Error: {res.stderr}")
            except Exception as e:
                self.update_status("Merge Error. Is FFMPEG installed?", "#f43f5e")
                self.log_message(f"Merge Error (FFMPEG missing?): {str(e)}")

        threading.Thread(target=run_merge, daemon=True).start()

    def start_bulk_txt(self):
        candidate_dirs = [
            self.base_dir,
            os.path.expanduser("~/Desktop/Dramadownload"),
            os.path.expanduser("~/Downloads")
        ]
        found_files = []
        for d in candidate_dirs:
            if os.path.exists(d):
                for fname in ("tiktok link graber.txt", "tiktok link graber.rtf"):
                    fpath = os.path.join(d, fname)
                    if os.path.exists(fpath):
                        found_files.append(fpath)

        target_file = None
        if found_files:
            target_file = max(found_files, key=os.path.getmtime)
        else:
            target_file = filedialog.askopenfilename(initialdir=self.base_dir, title="Select file with URLs", filetypes=[("Text/RTF files", "*.*")])

        if not target_file: return

        self.stop_flag = False

        if self.current_run_log:
            self.previous_runs_log = self.current_run_log + "\n\n" + self.previous_runs_log
            self.current_run_log = ""

        self.disable_buttons_for_run()

        run_header = f"{'='*50}\n--- STARTING BULK TXT DOWNLOAD ---\nFile: {target_file}"
        self.log_message(run_header)
        threading.Thread(target=self.download_bulk_process, args=(target_file,), daemon=True).start()

    def download_bulk_process(self, txt_file):
        try:
            with open(txt_file, "r", encoding="utf-8", errors="ignore") as f:
                content = f.read()

            raw_urls = re.findall(r'(https?://[^\s"\'<>\\}]+)', content)

            urls = []
            for u in raw_urls:
                if 'tiktok.com' in u and u not in urls:
                    urls.append(u)

            if not urls:
                self.update_status("No valid TikTok URLs found in file.", "#f43f5e")
                self.reset_buttons()
                return

            user_match = re.search(r'@([\w\.-]+)', urls[0])
            series_folder_name = f"TikTok_{user_match.group(1)}" if user_match else "TikTok_Bulk_Series"

            start_entry_val = self.start_entry.get().strip()
            start_ep = int(start_entry_val) if start_entry_val.isdigit() and int(start_entry_val) > 0 else 1

            total_entry_val = self.total_entry.get().strip()
            total_target = int(total_entry_val) if total_entry_val.isdigit() else len(urls)

            end_idx = min(total_target, len(urls))
            urls_to_download = urls[start_ep - 1 : end_idx]

            if not urls_to_download:
                self.update_status(f"Error: Only {len(urls)} links found, can't start at {start_ep}.", "#f43f5e")
                self.reset_buttons()
                return

            target_dir = self.get_organized_output_dir(series_folder_name, "1_Downloaded_Merged")
            temp_dir = os.path.join(target_dir, "temp_Bulk_Download")
            os.makedirs(temp_dir, exist_ok=True)

            yt_dlp_path = self.get_yt_dlp_path()
            if not yt_dlp_path:
                self.update_status("Error: Engine missing.", "#f43f5e")
                self.reset_buttons()
                return

            downloaded_files = []
            episode = start_ep
            last_saved_ep = None
            accel_args = self.get_fast_accelerator_args()

            for url in urls_to_download:
                if self.stop_flag:
                    self.update_status(f"Interrupted at Ep {episode}. Merging...", "#f59e0b")
                    break

                self.update_status(f"Downloading Link {episode}/{len(urls)}...", "#38bdf8")
                file_name = os.path.join(temp_dir, f"ep_{episode:03d}.mp4")

                yt_dlp_cmd = [
                    yt_dlp_path,
                    "--cookies-from-browser", "chrome",
                    *accel_args,
                    "-o", file_name, url
                ]

                max_retries = 3
                success = False
                err = ""

                for attempt in range(max_retries):
                    if self.stop_flag:
                        break

                    succ, stderr = self.run_yt_dlp_with_progress(yt_dlp_cmd)

                    if succ and self.is_valid_video_file(file_name):
                        self.normalize_clip_for_sync(file_name)
                        downloaded_files.append(file_name)
                        last_saved_ep = episode
                        self.log_message(f"Success: Link {episode} downloaded & sync-locked.")
                        success = True
                        episode += 1
                        time.sleep(2.5)
                        break
                    else:
                        if os.path.exists(file_name):
                            try: os.remove(file_name)
                            except: pass
                        err = stderr
                        self.log_message(f"Attempt {attempt+1} failed for Link {episode}: {err}")
                        time.sleep(2)

                if not success and not self.stop_flag:
                    self.log_message(f"Link {episode} failed after retries. Stopping to prevent missing episodes.")
                    break

            if not downloaded_files:
                self.update_status("Error: All links failed.", "#f43f5e")
                self.reset_buttons()
                return

            self.update_status(f"Merging parts up to Ep {last_saved_ep}...", "#f59e0b")
            range_str = f"EP{start_ep}-EP{last_saved_ep}" if start_ep != last_saved_ep else f"EP{start_ep}"
            final_output = os.path.join(target_dir, f"{series_folder_name}_{range_str}.mp4")

            res = self.concat_video_files_synced(downloaded_files, final_output, normalize_first=False)

            if res.returncode != 0:
                 self.log_message(f"FFMPEG ERROR:\n{res.stderr}")
            else:
                self.record_last_output(final_output)
                for file in downloaded_files:
                    try: os.remove(file)
                    except: pass
                try: os.rmdir(temp_dir)
                except: pass

            self.update_status(f"Success! Bulk Merged up to Ep {last_saved_ep}.", "#10b981")
            self.log_message(f"COMPLETED: Saved to {final_output}")

        except Exception as e:
            import traceback
            tb = traceback.format_exc()
            self.log_message(f"SYSTEM CRASH:\n{tb}")
            self.update_status("System Error. Click 'Open Error Log'.", "#f43f5e")

        self.reset_buttons()

    def sanitize_url(self, raw_url):
        u = raw_url.strip()

        match = re.search(r'(https?://[^\s\]\)]+)', u)
        if match:
            u = match.group(1)

        if "detail/" in u and "narto-drama" not in u:
            watch_part = u[u.find("detail/"):]
            u = f"https://narto-drama.com/{watch_part}"
        elif not u.startswith("http://") and not u.startswith("https://"):
            u = "https://" + u

        if u.count('?') > 1:
            first_q = u.find('?')
            u = u[:first_q+1] + u[first_q+1:].replace('?', '&')

        return u

    def start_thread(self, source):
        self.stop_flag = False

        if self.current_run_log:
            self.previous_runs_log = self.current_run_log + "\n\n" + self.previous_runs_log
            self.current_run_log = ""

        if source == 1:
            raw_url = self.url_entry1.get().strip()
        elif source == 2:
            raw_url = self.url_entry2.get().strip()
        elif source == 4:
            raw_url = self.url_entry4.get().strip()
        elif source == 5:
            raw_url = self.url_entry5.get().strip()
        else:
            raw_url = self.url_entry3.get().strip()

        if not raw_url:
            messagebox.showerror("Error", "Please enter a valid URL")
            return

        url = self.sanitize_url(raw_url)
        self.save_to_history(source, url)
        self.disable_buttons_for_run()

        accel_mode = "Turbo (16x)" if self.turbo_var.get() else "Standard (4x)"
        if source == 1:
            self._sm_cookie_idx = 0  # you may have just passed the bot check: try your browsers again
        run_header = f"{'='*50}\n--- STARTING NEW DOWNLOAD (Source {source} | {accel_mode}) ---\nURL: {url}"
        self.log_message(run_header)

        try:
            threading.Thread(target=self.download_process, args=(url, source), daemon=True).start()
        except Exception as e:
            self.log_message(f"Thread dispatch error: {str(e)}")
            self.update_status("URL formatting error. Check log.", "#f43f5e")
            self.reset_buttons()

    # =========================================================================
    # ⚡ NARTO-DRAMA.COM — CLAUDE VERSION (PARALLEL TURBO ENGINE) — v1.8.0
    # Reuses the original engine's read-only helpers (page scraper, stream candidates,
    # refresh-source token healing, subtitle finder) but downloads several episodes at
    # once, skips the fixed waits, and refreshes tokens before they go stale.
    # The original Narto engine (download_process, source 2) is not changed.
    # =========================================================================
    NARTO_CLAUDE_TOKEN_MAX_AGE = 120  # seconds before the playlist (and its stream tokens) is re-fetched
    NARTO_UA = "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/126.0.0.0 Safari/537.36"

    def start_narto_claude_thread(self):
        self.stop_flag = False

        if self.current_run_log:
            self.previous_runs_log = self.current_run_log + "\n\n" + self.previous_runs_log
            self.current_run_log = ""

        raw_url = self.url_entry7.get().strip()
        if not raw_url:
            messagebox.showerror("Error", "Please enter a narto-drama.com watch URL")
            return

        url = self.sanitize_url(raw_url)
        self.save_to_history(7, url)
        try:
            workers = max(1, min(6, int(self.narto_claude_parallel_var.get())))
        except Exception:
            workers = 3
        self.disable_buttons_for_run()
        self.log_message(f"{'='*50}\n--- STARTING NARTO CLAUDE VERSION ({workers} episodes at once) ---\nURL: {url}")
        threading.Thread(target=self.narto_claude_process, args=(url, workers), daemon=True).start()

    def narto_claude_accel_args(self, is_hls, workers):
        if not self.turbo_var.get():
            return ["-N", "4", "--newline"]
        # Spread connections over the parallel episodes so the CDN is not flooded (≈32 in total)
        frags = min(16, max(6, 32 // max(1, workers)))
        args = ["-N", str(frags), "--buffer-size", "1M", "--retries", "10", "--fragment-retries", "10", "--newline"]
        aria_path = self.get_aria2c_path()
        if aria_path and not is_hls:
            args += ["--downloader", aria_path, "--downloader-args", "aria2c:-x 16 -s 16 -k 1M --file-allocation=none --max-tries=5 --retry-wait=1"]
        return args

    def run_ytdlp_tracked(self, cmd, on_pct):
        """Runs one yt-dlp download (several can run at once). Returns (ok, last output lines)."""
        tail = []
        kwargs = {"creationflags": 0x08000000} if sys.platform == "win32" else {}
        try:
            proc = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, bufsize=1,
                                    encoding="utf-8", errors="ignore", **kwargs)
        except Exception as e:
            return False, str(e)
        self.narto_claude_procs.add(proc)
        try:
            for line in proc.stdout:
                if self.stop_flag:
                    proc.terminate()
                    break
                line = line.strip()
                if not line:
                    continue
                tail.append(line)
                if len(tail) > 25:
                    tail.pop(0)
                m = re.search(r'(\d+(?:\.\d+)?)%', line)
                if m and ("[download]" in line or "DL:" in line):
                    try: on_pct(float(m.group(1)))
                    except: pass
            proc.wait()
        finally:
            self.narto_claude_procs.discard(proc)
        return (proc.returncode == 0 and not self.stop_flag), "\n".join(tail)

    def narto_claude_process(self, url, workers):
        t0 = time.time()
        self.narto_claude_procs = set()
        net_lock = threading.Lock()     # curl shares one cookie jar file: one page/API request at a time
        state_lock = threading.Lock()
        ui = lambda fn: self.root.after(0, fn)
        ticker = {"on": True}

        def set_status(text, color="blue"):
            ui(lambda: self.update_status(text, color))

        try:
            yt_dlp_path = self.get_yt_dlp_path()
            if not yt_dlp_path or not os.path.exists(yt_dlp_path):
                set_status("Error: yt-dlp engine missing. Run terminal setup.", "red")
                return

            parsed = urllib.parse.urlparse(url)
            domain = parsed.netloc or "narto-drama.com"
            path_parts = [p for p in parsed.path.split('/') if p]
            if not path_parts:
                set_status("Error: Invalid Narto URL structure", "red")
                return
            if path_parts[-1].isdigit():
                path_parts.pop()
            series_slug = path_parts[-1] if path_parts else "Unknown_Series"
            series_name = f"Narto_Series_{series_slug}".replace('-', '_').title()
            base_watch_path = "/" + "/".join(path_parts)

            target_dir = self.get_organized_output_dir(series_name, "1_Downloaded_Merged")
            temp_dir = os.path.join(target_dir, f"temp_claude_{series_name}")
            os.makedirs(temp_dir, exist_ok=True)

            start_val = self.start_entry.get().strip()
            start_ep = int(start_val) if start_val.isdigit() and int(start_val) > 0 else 1
            total_val = self.total_entry.get().strip()
            total_target = int(total_val) if total_val.isdigit() else None

            set_status("⚡ Claude Turbo: loading series data...")
            with net_lock:
                meta = self.scrape_webpage_playlist(domain, base_watch_path, start_ep, bust_cache=True)
            shared = {"meta": meta, "ep": start_ep, "fetched": time.time()}

            ep_numbers = set()
            for it in (meta.get("playlist") or []):
                for n in (it.get("route_episode_number"), it.get("number")):
                    if str(n).isdigit():
                        ep_numbers.add(int(n))
            if total_target:
                last_ep = total_target
            elif ep_numbers:
                last_ep = max(ep_numbers)
            elif meta.get("direct_url"):
                last_ep = start_ep
            else:
                set_status("Could not read the episode list. Try the Original engine tab.", "red")
                self.log_message(f"Narto Claude: no playlist found on {meta.get('page_url')}")
                return
            if last_ep < start_ep:
                set_status(f"Nothing to download: Total Eps ({last_ep}) is below Start Ep ({start_ep}).", "red")
                return

            total_eps = last_ep - start_ep + 1
            self.log_message(f"Narto Claude: episodes {start_ep}-{last_ep} ({total_eps}), {workers} at once.")

            def current_meta(ep, force=False):
                with net_lock:
                    if force or time.time() - shared["fetched"] > self.NARTO_CLAUDE_TOKEN_MAX_AGE:
                        m = self.scrape_webpage_playlist(domain, base_watch_path, ep, bust_cache=True)
                        if m.get("playlist") or m.get("direct_url"):
                            shared.update(meta=m, ep=ep, fetched=time.time())
                            self.log_message(f"Narto Claude: tokens refreshed (page ep {ep}).")
                    return shared["meta"], shared["ep"]

            def candidates_for(ep, force=False):
                m, page_ep = current_meta(ep, force)
                return self.collect_narto_candidates(m.get("playlist"), ep, m.get("direct_url", "") if page_ep == ep else "")

            progress = {}      # ep -> percent for running downloads
            results = {}       # ep -> "ok" | "locked" | "failed" | "stopped"
            subs_raw = {}      # ep -> raw subtitle text
            errors = {}
            sched = {"next": start_ep, "stop_at": last_ep}

            def download_episode(ep):
                cands = candidates_for(ep)
                if not cands:
                    cands = candidates_for(ep, force=True)
                if not cands:
                    self.log_message(f"Narto Claude: Episode {ep} is Locked/VIP or unavailable.")
                    return "locked"

                file_name = os.path.join(temp_dir, f"ep_{ep:03d}.mp4")
                for leftover in (file_name, file_name + ".part"):
                    if os.path.exists(leftover):
                        try: os.remove(leftover)
                        except: pass

                tried = set()
                for attempt in range(5):
                    if self.stop_flag:
                        return "stopped"
                    stream = next((u for u in cands if u not in tried), cands[-1])
                    is_hls = ".m3u8" in stream.lower() or "dbxhls" in stream.lower()
                    cmd = [yt_dlp_path, "--user-agent", self.NARTO_UA, "--referer", f"https://{domain}/",
                           *self.narto_claude_accel_args(is_hls, workers), "-o", file_name, stream]
                    ok, err = self.run_ytdlp_tracked(cmd, lambda p, e=ep: progress.__setitem__(e, p))
                    if self.stop_flag:
                        return "stopped"
                    if ok and self.is_valid_video_file(file_name):
                        self.normalize_clip_for_sync(file_name)
                        if self.auto_sub_var.get():
                            with net_lock:
                                m, page_ep = shared["meta"], shared["ep"]
                                sub_u = self.extract_narto_subtitle_url(domain, m.get("playlist"), ep, m.get("raw_html", "") if page_ep == ep else "")
                                if sub_u:
                                    subs_raw[ep] = self.curl_fetch(sub_u, headers={"Referer": f"https://{domain}/"})
                        return "ok"

                    if os.path.exists(file_name):
                        try: os.remove(file_name)
                        except: pass
                    tried.add(stream)
                    errors[ep] = err or "Downloaded file was invalid or <100KB."
                    if any(code in errors[ep] for code in ("410", "500", "403", "404", "invalid")):
                        self.log_message(f"Narto Claude: Ep {ep} stream rejected, healing token via refresh-source...")
                        with net_lock:
                            page_copy = dict(shared["meta"])
                            fresh = self.trigger_narto_refresh_source(domain, base_watch_path, ep, page_copy, stream)
                            if page_copy.get("playlist"):
                                shared["meta"] = dict(shared["meta"], playlist=page_copy["playlist"])
                                shared["fetched"] = time.time()
                        for fc in fresh:
                            if fc not in cands:
                                cands.append(fc)
                        if any(u not in tried for u in cands):
                            continue
                    time.sleep(1.0)
                self.log_message(f"Narto Claude: Episode {ep} failed after retries:\n{errors.get(ep, '')}")
                return "failed"

            def worker(delay):
                time.sleep(delay)  # stagger starts so the site isn't hit all at once
                while not self.stop_flag:
                    with state_lock:
                        ep = sched["next"]
                        if ep > sched["stop_at"]:
                            return
                        sched["next"] += 1
                        progress[ep] = 0.0
                    try:
                        res = download_episode(ep)
                    except Exception as e:
                        errors[ep] = str(e)
                        res = "failed"
                    with state_lock:
                        results[ep] = res
                        progress.pop(ep, None)
                        if res != "ok":
                            # Like the original: never merge past a missing episode
                            sched["stop_at"] = min(sched["stop_at"], ep - 1)

            def tick():
                if not ticker["on"]:
                    return
                with state_lock:
                    done = sum(1 for r in results.values() if r == "ok")
                    running = sorted(progress.items())
                frac = sum(p for _, p in running) / 100.0
                pct = min(100.0, (done + frac) / max(1, total_eps) * 100.0)
                self.progress_bar['value'] = pct
                elapsed = int(time.time() - t0)
                self.status_label.config(text=f"⚡ Claude Turbo: {done}/{total_eps} episodes done  •  {elapsed // 60}:{elapsed % 60:02d}", fg="#a855f7")
                self.detail_label.config(text="   ".join(f"Ep {e} ▸ {p:.0f}%" for e, p in running[:6]) or "Preparing...")
                self.root.after(300, tick)
            ui(tick)

            threads = [threading.Thread(target=worker, args=(i * 0.6,), daemon=True) for i in range(workers)]
            for th in threads:
                th.start()
            for th in threads:
                th.join()
            ticker["on"] = False

            ok_eps = []
            e = start_ep
            while results.get(e) == "ok":
                ok_eps.append(e)
                e += 1

            if not ok_eps:
                if self.stop_flag:
                    set_status("Stopped. No complete episodes to merge.", "orange")
                else:
                    set_status(f"Ep {start_ep} failed. Check log.", "red")
                    self.log_message(f"Narto Claude FAILED ON EPISODE {start_ep}:\n{errors.get(start_ep, results.get(start_ep, ''))}")
                return

            first, last = ok_eps[0], ok_eps[-1]
            set_status(f"⚡ Merging {len(ok_eps)} sync-locked episodes (Ep {first}-Ep {last})...", "orange")
            files = [os.path.join(temp_dir, f"ep_{n:03d}.mp4") for n in ok_eps]

            if first == 1 and last == last_ep and last > 1 and not self.stop_flag:
                final_output = os.path.join(target_dir, f"{series_name}_Full_Claude.mp4")
            elif first == last:
                final_output = os.path.join(target_dir, f"{series_name}_EP{first}_Claude.mp4")
            else:
                final_output = os.path.join(target_dir, f"{series_name}_EP{first}-EP{last}_Claude.mp4")

            # Subtitles: shift each episode's cues by the running duration, in episode order
            merged_cues = []
            offset = 0.0
            for n, fpath in zip(ok_eps, files):
                if subs_raw.get(n):
                    merged_cues.extend(self.parse_and_shift_subtitle_cues(subs_raw[n], offset))
                offset += self.get_media_duration(fpath)

            res = self.concat_video_files_synced(files, final_output, normalize_first=False)
            if res.returncode != 0:
                self.log_message(f"Narto Claude FFMPEG ERROR:\n{res.stderr}")
                set_status("Merge failed. Episodes kept in the temp folder. Check log.", "red")
                return

            self.record_last_output(final_output)
            for fpath in files:
                try: os.remove(fpath)
                except: pass
            try: os.rmdir(temp_dir)
            except: pass

            if merged_cues:
                srt_output = os.path.splitext(final_output)[0] + ".srt"
                try:
                    with open(srt_output, "w", encoding="utf-8") as sf:
                        for idx_cue, (st, et, txt) in enumerate(merged_cues, 1):
                            sf.write(f"{idx_cue}\n{st} --> {et}\n{txt}\n\n")
                    self.log_message(f"Narto Claude SUBTITLES SAVED: {srt_output} ({len(merged_cues)} lines)")
                except Exception as sub_ex:
                    self.log_message(f"Subtitle save warning: {str(sub_ex)}")

            took = time.time() - t0
            ep_txt = f"Ep {first}" if first == last else f"Ep {first}-{last}"
            prefix = "⏹️ Stopped — kept" if self.stop_flag else "✅ Claude Turbo:"
            summary = f"{prefix} {ep_txt} merged in {int(took // 60)}m {int(took % 60)}s ({took / len(ok_eps):.1f}s per episode)"
            self.log_message(f"{summary}\nCOMPLETED: Saved to {final_output}")
            ui(lambda: (self.update_status(summary, "green"), self.progress_bar.configure(value=100)))

        except Exception:
            import traceback
            self.log_message(f"Narto Claude CRASH:\n{traceback.format_exc()}")
            set_status("Narto Claude stopped on an error. Check log.", "red")
        finally:
            ticker["on"] = False
            self.narto_claude_procs = set()
            ui(self.reset_buttons)

    # =========================================================================
    # 🧲 TORRENT & MAGNET LINK DOWNLOADER (ARIA2C 16x ENGINE) — v1.7.3
    # =========================================================================
    FALLBACK_BT_TRACKERS = [
        "udp://tracker.opentrackr.org:1337/announce",
        "udp://open.demonii.com:1337/announce",
        "udp://open.stealth.si:80/announce",
        "udp://tracker.torrent.eu.org:451/announce",
        "udp://exodus.desync.com:6969/announce",
        "udp://tracker.openbittorrent.com:6969/announce",
        "udp://explodie.org:6969/announce",
        "udp://tracker.theoks.net:6969/announce",
        "udp://tracker.dler.org:6969/announce",
        "udp://opentracker.io:6969/announce",
        "https://tracker.tamersunion.org:443/announce",
        "http://tracker.opentrackr.org:1337/announce",
    ]

    def get_aria2c_path(self):
        sys_path = shutil.which("aria2c") or shutil.which("aria2c.exe")
        if sys_path:
            return sys_path
        for cand in ("aria2c.exe", "aria2c"):
            local = os.path.join(self.base_dir, cand)
            if os.path.exists(local):
                return local
        return None

    def get_public_bt_trackers(self):
        """Fresh public tracker list (peer boosting), cached for the session, with a built-in fallback."""
        cached = getattr(self, "_bt_tracker_cache", None)
        if cached:
            return cached
        trackers = []
        try:
            import urllib.request
            req = urllib.request.Request(
                "https://cdn.jsdelivr.net/gh/ngosang/trackerslist@master/trackers_best.txt",
                headers={"User-Agent": "Mozilla/5.0"}
            )
            with urllib.request.urlopen(req, timeout=6) as resp:
                body = resp.read().decode("utf-8", errors="ignore")
            trackers = [ln.strip() for ln in body.splitlines() if re.match(r'^(udp|https?|wss?)://', ln.strip())]
        except:
            trackers = []
        merged = []
        for t in trackers + self.FALLBACK_BT_TRACKERS:
            if t not in merged:
                merged.append(t)
        self._bt_tracker_cache = merged[:40]
        return self._bt_tracker_cache

    def normalize_torrent_source(self, raw):
        """Returns (source, kind) for a magnet link, bare info-hash, .torrent URL or local .torrent file."""
        src = raw.strip().strip('"').strip("'")
        if not src:
            return None, None
        if src.lower().startswith("magnet:?"):
            return src, "magnet"
        if re.fullmatch(r'[A-Fa-f0-9]{40}|[A-Za-z2-7]{32}', src):
            return f"magnet:?xt=urn:btih:{src}", "magnet"
        if re.match(r'^https?://', src, re.I):
            return src, "url"
        if os.path.isfile(src) and src.lower().endswith(".torrent"):
            return os.path.abspath(src), "file"
        return None, None

    def browse_torrent_file(self):
        f = filedialog.askopenfilename(title="Select .torrent File", filetypes=[("Torrent Files", "*.torrent"), ("All Files", "*.*")])
        if f:
            self.url_entry6.delete(0, tk.END)
            self.url_entry6.insert(0, f)

    def start_torrent_thread(self):
        self.stop_flag = False

        if self.current_run_log:
            self.previous_runs_log = self.current_run_log + "\n\n" + self.previous_runs_log
            self.current_run_log = ""

        src, kind = self.normalize_torrent_source(self.url_entry6.get())
        if not src:
            messagebox.showerror("Torrent", "Please enter a magnet link, a .torrent URL, or pick a local .torrent file.")
            return

        aria_path = self.get_aria2c_path()
        if not aria_path:
            messagebox.showerror(
                "Aria2c Missing",
                "The torrent downloader needs aria2c.\n\n"
                "Windows: winget install aria2.aria2  (or put aria2c.exe next to this script)\n"
                "macOS: brew install aria2\n"
                "Linux: sudo apt install aria2"
            )
            return

        self.save_to_history(6, src)
        self.disable_buttons_for_run()
        self.log_message(f"{'='*50}\n--- STARTING NEW TORRENT DOWNLOAD ({kind} | Aria2c 16x) ---\nSource: {src[:300]}")

        try:
            threading.Thread(target=self.torrent_download_process, args=(src, kind, aria_path), daemon=True).start()
        except Exception as e:
            self.log_message(f"Torrent thread dispatch error: {str(e)}")
            self.update_status("Could not start torrent download. Check log.", "red")
            self.reset_buttons()

    def build_aria2c_torrent_cmd(self, aria_path, src, target_dir, seed=False, trackers=None):
        cmd = [
            aria_path,
            "--dir", target_dir,
            # 16-connection engine (used for .torrent URLs and any web seeds)
            "--max-connection-per-server=16", "--split=16", "--min-split-size=1M",
            # Peer boosting: DHT, PEX, local discovery, unlimited peers, extra trackers
            "--enable-dht=true", "--enable-dht6=true", "--bt-enable-lpd=true",
            "--enable-peer-exchange=true", "--bt-max-peers=0",
            "--bt-request-peer-speed-limit=50M",
            "--bt-tracker-connect-timeout=10", "--bt-tracker-timeout=10",
            "--listen-port=6881-6999", "--dht-listen-port=6881-6999",
            "--follow-torrent=true", "--bt-save-metadata=true",
            "--bt-remove-unselected-file=false",
            "--file-allocation=none", "--continue=true", "--auto-file-renaming=false",
            "--summary-interval=1", "--console-log-level=warn",
            "--human-readable=true", "--enable-color=false",
        ]
        if trackers:
            cmd.append("--bt-tracker=" + ",".join(trackers))
        if seed:
            cmd += ["--seed-ratio=1.0", "--seed-time=30"]
        else:
            cmd += ["--seed-time=0"]
        cmd.append(src)
        return cmd

    def parse_aria2c_readout(self, line):
        """Parses '[#ab12cd 120MiB/1.4GiB(8%) CN:44 SD:12 DL:6.1MiB ETA:3m40s]' style readouts."""
        m = re.search(r'\[#\w+\s+([^\]]*)\]', line)
        if not m:
            return None
        body = m.group(1)
        info = {"pct": None, "text": body}
        pct = re.search(r'\((\d+)%\)', body)
        if pct:
            info["pct"] = float(pct.group(1))
        for key in ("CN", "SD", "DL", "UL", "ETA"):
            km = re.search(rf'\b{key}:(\S+)', body)
            info[key] = km.group(1) if km else ""
        sm = re.search(r'SEED\(([\d.]+)\)', body)
        info["seeding"] = sm.group(1) if sm else None
        info["size"] = body.split()[0] if body else ""
        return info

    def torrent_download_process(self, src, kind, aria_path):
        try:
            timestamp = datetime.datetime.now().strftime("%Y%m%d_%H%M%S")
            target_dir = self.get_organized_output_dir("Torrents", f"Torrent_{timestamp}")

            self.update_status("🧲 Fetching fresh tracker list for peer boosting...", "blue")
            trackers = self.get_public_bt_trackers()
            cmd = self.build_aria2c_torrent_cmd(aria_path, src, target_dir, seed=self.torrent_seed_var.get(), trackers=trackers)
            self.log_message(f"Torrent target: {target_dir} | trackers: {len(trackers)} | seed: {self.torrent_seed_var.get()}")

            self.progress_bar['value'] = 0
            self.detail_label.config(text="Connecting to DHT and trackers...")
            self.update_status("🧲 Finding peers (magnet metadata first)..." if kind == "magnet" else "🧲 Starting torrent download...", "blue")

            kwargs = {"creationflags": 0x08000000} if sys.platform == "win32" else {}
            self.current_process = subprocess.Popen(
                cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                text=True, bufsize=1, universal_newlines=True, errors="ignore", **kwargs
            )

            tail = []
            for line in self.current_process.stdout:
                if self.stop_flag:
                    self.current_process.terminate()
                    break
                line = line.strip()
                if not line:
                    continue
                tail.append(line)
                if len(tail) > 30:
                    tail.pop(0)

                info = self.parse_aria2c_readout(line)
                if not info:
                    if "[METADATA]" in line or "Download complete" in line or "ERROR" in line or "error" in line.lower():
                        self.detail_label.config(text=line[:110])
                    continue

                if info["seeding"] is not None:
                    self.progress_bar['value'] = 100
                    self.update_status(f"🌱 Seeding (ratio {info['seeding']})... Press Stop to end early.", "green")
                    self.detail_label.config(text=f"Peers: {info['CN'] or '0'}  •  UL: {info['UL'] or '0B'}")
                else:
                    if info["pct"] is not None:
                        self.progress_bar['value'] = info["pct"]
                    peers = info["CN"] or "0"
                    seeds = info["SD"] or "0"
                    self.update_status(f"🧲 Downloading torrent... {int(info['pct'] or 0)}%", "blue")
                    self.detail_label.config(
                        text=f"{info['size']}  •  DL: {info['DL'] or '0B'}  •  Seeds: {seeds}  •  Peers: {peers}  •  ETA: {info['ETA'] or '--'}"
                    )
                self.root.update_idletasks()

            self.current_process.wait()
            rc = self.current_process.returncode
            self.current_process = None

            if self.stop_flag:
                self.update_status("Torrent stopped. Start it again to resume where it left off.", "orange")
                self.log_message("Torrent stopped by user (partial data kept for resume).")
                self.last_output_folder = target_dir
                return

            if rc == 0:
                # Newest/largest file downloaded becomes the "last file" for the studios
                best, best_size = None, -1
                for root_dir, _dirs, files in os.walk(target_dir):
                    for fn in files:
                        if fn.endswith((".aria2", ".torrent")):
                            continue
                        fp = os.path.join(root_dir, fn)
                        try:
                            sz = os.path.getsize(fp)
                        except:
                            continue
                        if sz > best_size:
                            best, best_size = fp, sz
                if best:
                    self.record_last_output(best)
                self.last_output_folder = target_dir
                self.progress_bar['value'] = 100
                self.update_status("✅ Torrent download complete!", "green")
                self.log_message(f"Torrent complete: {best or target_dir}")
            else:
                self.last_output_folder = target_dir
                self.update_status(f"Torrent failed (aria2c code {rc}). Check log.", "red")
                self.log_message(f"Torrent failed (aria2c exit {rc}):\n" + "\n".join(tail))
        except Exception as e:
            self.update_status("Torrent error. Check log.", "red")
            self.log_message(f"Torrent exception: {str(e)}")
        finally:
            self.current_process = None
            self.root.after(0, self.reset_buttons)

    def update_status(self, text, color="#38bdf8"):
        color_map = {"blue": "#38bdf8", "green": "#10b981", "red": "#f43f5e", "orange": "#f59e0b", "black": "#f8fafc"}
        c = color_map.get(color, color)
        self.status_label.config(text=text, fg=c)
        self.root.update_idletasks()

    def curl_fetch(self, target_url, headers=None, method="GET", json_payload=None):
        cmd = [
            "curl", "-s", "-L",
            "-c", self.cookie_jar_file,
            "-b", self.cookie_jar_file,
            "-A", "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/126.0.0.0 Safari/537.36",
            "-H", "Cache-Control: no-cache, no-store, must-revalidate",
            "-H", "Pragma: no-cache"
        ]
        if method.upper() == "POST":
            cmd.extend(["-X", "POST"])
        if headers:
            for k, v in headers.items():
                cmd.extend(["-H", f"{k}: {v}"])
        if json_payload is not None:
            cmd.extend(["-H", "Content-Type: application/json", "-H", "Accept: application/json"])
            cmd.extend(["--data-raw", json.dumps(json_payload)])
        cmd.append(target_url)

        kwargs = {}
        if sys.platform == "win32":
            kwargs["creationflags"] = 0x08000000

        res = subprocess.run(cmd, capture_output=True, text=True, encoding="utf-8", errors="ignore", **kwargs)
        return res.stdout if res.returncode == 0 else ""

    def is_valid_stream_url(self, u):
        if not u or not isinstance(u, str) or not u.startswith("http"):
            return False
        low = u.lower()
        bad_patterns = (
            "/detail/watch/", "/detail/dummy/", "/tag/", "/genre/", "/search",
            "/auth/", "/me/", "/poster/", ".jpg", ".jpeg", ".png", ".webp",
            ".gif", ".svg", ".vtt", ".srt", ".ass", ".css", ".js", ".woff",
            "get-subtitle", "refresh-captions", "refresh-source", "google", "facebook", "tiktok.com/@"
        )
        for bp in bad_patterns:
            if bp in low:
                return False
        return True

    def scrape_webpage_playlist(self, domain, base_watch_path, current_ep, bust_cache=False):
        cb_str = f"&_cb={int(time.time() * 1000)}" if bust_cache else ""
        page_url = f"https://{domain}{base_watch_path}/{current_ep}?lang=en-US{cb_str}"
        html = self.curl_fetch(page_url, headers={"Referer": f"https://{domain}/"})

        page_meta = {
            "playlist": None,
            "direct_url": "",
            "csrf_token": "",
            "movie_id": "",
            "refresh_endpoints": [],
            "page_url": page_url,
            "raw_html": html or ""
        }

        if html:
            m_csrf = re.search(r'<meta\s+name=["\']csrf-token["\']\s+content=["\']([^"\']+)["\']', html)
            if m_csrf:
                page_meta["csrf_token"] = m_csrf.group(1)

            m_mid = re.search(r'<meta\s+name=["\']nd-current-movie-id["\']\s+content=["\']([^"\']+)["\']', html)
            if m_mid:
                page_meta["movie_id"] = m_mid.group(1)

            m_list = re.search(r'const\s+episodeItemsRaw\s*=\s*(\[.*?\]);', html, re.DOTALL)
            if m_list:
                try:
                    page_meta["playlist"] = json.loads(m_list.group(1))
                except:
                    pass

            m_direct = re.search(r'const\s+initialSourceUrl\s*=\s*"([^"]+)";', html)
            if m_direct:
                try:
                    d_url = json.loads(f'"{m_direct.group(1)}"')
                except:
                    d_url = m_direct.group(1).replace('\\/', '/')
                if self.is_valid_stream_url(d_url):
                    page_meta["direct_url"] = d_url

            clean_html = html.replace('\\/', '/')
            raw_endpoints = re.findall(r'["\']((?:https?://[^"\']+|/[a-zA-Z0-9_\-/]*?)refresh[-_]?source[^"\']*)["\']', clean_html, re.IGNORECASE)
            for ep_url in raw_endpoints:
                if "caption" in ep_url.lower() or "subtitle" in ep_url.lower():
                    continue
                full_ep_url = ep_url if ep_url.startswith("http") else f"https://{domain}{ep_url if ep_url.startswith('/') else '/' + ep_url}"
                if full_ep_url not in page_meta["refresh_endpoints"]:
                    page_meta["refresh_endpoints"].append(full_ep_url)

        return page_meta

    def collect_narto_candidates(self, narto_playlist, episode, direct_url=""):
        candidates = []
        def add_cand(u):
            if self.is_valid_stream_url(u) and u not in candidates:
                candidates.append(u)

        if narto_playlist:
            ep_item = next((item for item in narto_playlist if item.get('route_episode_number') == episode or item.get('number') == episode), None)
            if ep_item:
                for key in ('play_url', 'stream_url', 'video_url', 'hls_url', 'mp4_url', 'source_url', 'backup_url', 'raw_url'):
                    add_cand(ep_item.get(key, ''))
                multi_res = ep_item.get('multi_resolutions')
                if isinstance(multi_res, list):
                    for r in multi_res:
                        if isinstance(r, dict):
                            add_cand(r.get('stream_url', ''))
                            add_cand(r.get('url', ''))

        add_cand(direct_url)
        return candidates

    def trigger_narto_refresh_source(self, domain, base_watch_path, episode, page_meta, dead_url):
        fresh_streams = []
        def add_fresh(u):
            if self.is_valid_stream_url(u) and u not in fresh_streams and u != dead_url:
                fresh_streams.append(u)

        playlist = page_meta.get("playlist") or []
        ep_item = next((item for item in playlist if item.get('route_episode_number') == episode or item.get('number') == episode), {}) or {}

        ep_id = ep_item.get("id") or ep_item.get("episode_id") or ""
        movie_id = page_meta.get("movie_id") or ep_item.get("movie_id") or ""
        csrf_token = page_meta.get("csrf_token") or ""
        series_slug = base_watch_path.strip("/").split("/")[-1]

        payload = {}
        for k, v in ep_item.items():
            if isinstance(v, (str, int, float, bool)) and k not in ("play_url",):
                payload[k] = v
        if movie_id:
            payload["movie_id"] = int(movie_id) if str(movie_id).isdigit() else movie_id
        if ep_id:
            payload["episode_id"] = int(ep_id) if str(ep_id).isdigit() else ep_id
            payload["id"] = payload["episode_id"]
        payload.update({
            "episode_number": episode,
            "route_episode_number": episode,
            "episode": episode,
            "ep": episode,
            "slug": series_slug,
            "lang": "en-US",
            "url": dead_url,
            "play_url": dead_url,
            "source_url": dead_url,
            "current_url": dead_url,
            "failed_url": dead_url,
            "force": True,
            "refresh": True
        })

        endpoints = list(page_meta.get("refresh_endpoints") or [])
        for fallback_path in (
            f"https://{domain}{base_watch_path}/{episode}/refresh-source",
            f"https://{domain}{base_watch_path}/refresh-source",
            f"https://{domain}/detail/watch/refresh-source",
            f"https://{domain}/player/refresh-source",
            f"https://{domain}/refresh-source"
        ):
            if fallback_path not in endpoints:
                endpoints.append(fallback_path)

        headers = {
            "X-Requested-With": "XMLHttpRequest",
            "Referer": page_meta.get("page_url") or f"https://{domain}{base_watch_path}/{episode}?lang=en-US",
            "Origin": f"https://{domain}"
        }
        if csrf_token:
            headers["X-CSRF-TOKEN"] = csrf_token

        for ep_url in endpoints:
            if self.stop_flag:
                break
            resp_text = self.curl_fetch(ep_url, headers=headers, method="POST", json_payload=payload)
            if not resp_text or "{" not in resp_text:
                continue
            try:
                data = json.loads(resp_text)
                def extract_from_json(obj):
                    if isinstance(obj, dict):
                        for k, v in obj.items():
                            if k in ('play_url', 'stream_url', 'video_url', 'hls_url', 'mp4_url', 'source_url', 'url') and isinstance(v, str):
                                add_fresh(v.replace('\\/', '/'))
                            else:
                                extract_from_json(v)
                    elif isinstance(obj, list):
                        for item in obj:
                            extract_from_json(item)
                extract_from_json(data)
                if fresh_streams:
                    self.log_message(f"refresh-source succeeded via {ep_url}")
                    break
            except:
                pass

        refreshed_meta = self.scrape_webpage_playlist(domain, base_watch_path, episode, bust_cache=True)
        if refreshed_meta.get("playlist"):
            page_meta["playlist"] = refreshed_meta["playlist"]
        for c in self.collect_narto_candidates(refreshed_meta.get("playlist"), episode, refreshed_meta.get("direct_url", "")):
            add_fresh(c)

        return fresh_streams

    def download_process(self, url, source, keep_buttons_locked=False):
        current_ep_tracker = 1
        last_saved_ep = None

        try:
            parsed_url = urllib.parse.urlparse(url)
            domain = parsed_url.netloc or "narto-drama.com"

            yt_dlp_path = self.get_yt_dlp_path()
            if not yt_dlp_path:
                self.update_status("Error: Engine missing. Run terminal setup.", "red")
                if not keep_buttons_locked:
                    self.reset_buttons()
                return

            accel_args = self.get_accelerator_args()
            if source != 2:
                # v1.8.0 speed profile; Narto Original (source 2) keeps its proven settings
                accel_args = self.get_fast_accelerator_args()

            # --- DIRECT M3U8 BYPASS LOGIC ---
            if source == 3:
                self.update_status("Downloading Direct Stream (Turbo)...", "blue")
                timestamp = datetime.datetime.now().strftime("%Y%m%d_%H%M%S")
                target_dir = self.get_organized_output_dir(f"Bypass_{timestamp}", "1_Downloaded_Merged")
                file_name = os.path.join(target_dir, f"Bypass_Video_{timestamp}.mp4")

                yt_dlp_cmd = [
                    yt_dlp_path,
                    *accel_args,
                    "-o", file_name,
                    url
                ]

                succ, err = self.run_yt_dlp_with_progress(yt_dlp_cmd)

                if succ and self.is_valid_video_file(file_name):
                    self.record_last_output(file_name)
                    self.update_status("Success! Direct video saved.", "green")
                    self.log_message(f"COMPLETED: Saved to {file_name}")
                else:
                    self.update_status("Failed to download direct link. Check Log.", "red")
                    self.log_message(f"Direct Download Error: {err}")

                if not keep_buttons_locked:
                    self.reset_buttons()
                return

            # --- TIKTOK SINGLE VIDEO LOGIC ---
            if source == 4:
                self.update_status("Downloading TikTok Video...", "blue")

                match = re.search(r'video/(\d+)', url)
                video_id = match.group(1) if match else datetime.datetime.now().strftime("%Y%m%d_%H%M%S")
                target_dir = self.get_organized_output_dir(f"TikTok_{video_id}", "1_Downloaded_Merged")
                file_name = os.path.join(target_dir, f"TikTok_{video_id}.mp4")

                yt_dlp_cmd = [
                    yt_dlp_path,
                    *accel_args,
                    "-o", file_name,
                    url
                ]

                succ, err = self.run_yt_dlp_with_progress(yt_dlp_cmd)

                if succ and self.is_valid_video_file(file_name):
                    self.record_last_output(file_name)
                    self.update_status("Success! TikTok Video Saved.", "green")
                    self.log_message(f"COMPLETED: Saved to {file_name}")
                else:
                    self.update_status("Failed to download TikTok. Check Log.", "red")
                    self.log_message(f"TikTok Download Error: {err}")

                if not keep_buttons_locked:
                    self.reset_buttons()
                return

            # --- DAILYMOTION HIGHEST QUALITY LOGIC ---
            if source == 5:
                self.update_status("Fetching Dailymotion Title & Max Quality Stream...", "blue")
                dm_title = "Dailymotion_Movie"
                try:
                    kwargs = {"creationflags": 0x08000000} if sys.platform == "win32" else {}
                    p_res = subprocess.run([yt_dlp_path, "--get-title", url], capture_output=True, text=True, timeout=15, **kwargs)
                    if p_res.returncode == 0 and p_res.stdout.strip():
                        dm_title = clean_folder_Title(p_res.stdout.strip().splitlines()[0])
                except:
                    pass

                target_dir = self.get_organized_output_dir(dm_title, "1_Downloaded_Merged")
                output_template = os.path.join(target_dir, f"{dm_title}_%(id)s.%(ext)s")

                yt_dlp_cmd = [
                    yt_dlp_path,
                    "-f", "bestvideo+bestaudio/best",
                    "--merge-output-format", "mp4",
                    *accel_args,
                    "-o", output_template,
                    url
                ]

                succ, err = self.run_yt_dlp_with_progress(yt_dlp_cmd)

                if succ:
                    mp4s = [os.path.join(target_dir, f) for f in os.listdir(target_dir) if f.lower().endswith(".mp4")]
                    if mp4s:
                        latest_dm = max(mp4s, key=os.path.getmtime)
                        self.record_last_output(latest_dm)
                    self.update_status("Success! Dailymotion Video Saved.", "green")
                    self.log_message(f"DAILYMOTION COMPLETED: Saved to {target_dir}")
                else:
                    self.update_status("Failed to download Dailymotion. Check Log.", "red")
                    self.log_message(f"Dailymotion Download Error: {err}")

                if not keep_buttons_locked:
                    self.reset_buttons()
                return

            # --- SHORTMAX AUTOMATION ---
            if source == 1:
                match = re.search(r'id=(\d+)', url)
                if not match:
                    self.update_status("Error: Could not find Drama ID in URL", "red")
                    if not keep_buttons_locked:
                        self.reset_buttons()
                    return

                drama_id = match.group(1)
                slug_match = re.search(r'slug=([^&]+)', url)
                series_name = slug_match.group(1).replace('-', '_').title() if slug_match else f"Drama_{drama_id}"

                lang_match = re.search(r'lang=([^&]+)', url)
                lang_str = f"&lang={lang_match.group(1)}" if lang_match else ""

                def get_ep_url(ep):
                    return f"https://{domain}/index.php?page=watch&id={drama_id}{lang_str}&ep={ep}"

            # --- NARTO PARSER & HEALER (UNTOUCHED v1.6.1) ---
            else:
                path = parsed_url.path
                path_parts = [p for p in path.split('/') if p]
                if not path_parts:
                    self.update_status("Error: Invalid Narto URL structure", "red")
                    if not keep_buttons_locked:
                        self.reset_buttons()
                    return

                if path_parts[-1].isdigit():
                    path_parts.pop()

                series_slug = path_parts[-1] if path_parts else "Unknown_Series"
                series_name = f"Narto_Series_{series_slug}".replace('-', '_').title()

                base_watch_path = "/" + "/".join(path_parts)

                def get_ep_url(ep):
                    return f"https://{domain}{base_watch_path}/{ep}"

            target_dir = self.get_organized_output_dir(series_name, "1_Downloaded_Merged")
            temp_dir = os.path.join(target_dir, f"temp_{series_name}")
            os.makedirs(temp_dir, exist_ok=True)

            start_entry_val = self.start_entry.get().strip()
            episode = int(start_entry_val) if start_entry_val.isdigit() and int(start_entry_val) > 0 else 1
            initial_start_episode = episode
            current_ep_tracker = episode

            total_entry_val = self.total_entry.get().strip()
            total_target = int(total_entry_val) if total_entry_val.isdigit() else None

            downloaded_files = []
            merged_subtitle_cues = []
            cumulative_duration_sec = 0.0
            narto_playlist = []
            page_meta = {}
            episodes_since_refresh = 0

            if source == 2:
                self.update_status("Loading series data...", "blue")
                page_meta = self.scrape_webpage_playlist(domain, base_watch_path, episode, bust_cache=True)
                narto_playlist = page_meta.get("playlist") or []
                if narto_playlist:
                    self.log_message(f"Playlist loaded with {len(narto_playlist)} episodes.")
                    if page_meta.get("refresh_endpoints"):
                        self.log_message(f"Detected Narto refresh endpoint(s): {page_meta['refresh_endpoints']}")
                    if not total_target:
                        total_target = len(narto_playlist)
                else:
                    self.log_message("Warning: Could not parse initial playlist. Falling back to direct scrapes.")

            while True:
                current_ep_tracker = episode
                if self.stop_flag:
                    self.update_status(f"Stopped at Ep {episode}. Merging saved files...", "orange")
                    break

                if total_target and episode > total_target:
                    self.log_message("Reached total target episodes. Stopping.")
                    break

                self.update_status(f"Downloading Episode {episode}...", "blue")
                candidate_urls = []

                if source == 1:
                    candidate_urls = [get_ep_url(episode)]
                else:
                    if episodes_since_refresh >= 10:
                        self.log_message(f"10 episodes processed. Re-fetching webpage to refresh tokens...")
                        page_meta = self.scrape_webpage_playlist(domain, base_watch_path, episode, bust_cache=True)
                        if page_meta.get("playlist"):
                            narto_playlist = page_meta["playlist"]
                            self.log_message("Webpage tokens successfully refreshed.")
                            episodes_since_refresh = 0

                    candidate_urls = self.collect_narto_candidates(
                        narto_playlist,
                        episode,
                        page_meta.get("direct_url", "") if episode == initial_start_episode else ""
                    )

                    if not candidate_urls:
                        page_meta = self.scrape_webpage_playlist(domain, base_watch_path, episode, bust_cache=True)
                        if page_meta.get("playlist"):
                            narto_playlist = page_meta["playlist"]
                        candidate_urls = self.collect_narto_candidates(narto_playlist, episode, page_meta.get("direct_url", ""))

                    if not candidate_urls:
                        self.log_message(f"Episode {episode} is Locked/VIP or unavailable.")
                        break

                file_name = os.path.join(temp_dir, f"ep_{episode:03d}.mp4")
                if os.path.exists(file_name):
                    try: os.remove(file_name)
                    except: pass

                success = False
                err = ""
                max_retries = 9 if source == 1 else 4
                tried_dead_urls = set()

                for attempt in range(max_retries):
                    if self.stop_flag:
                        break

                    current_stream_url = next((u for u in candidate_urls if u not in tried_dead_urls), candidate_urls[-1])

                    if source == 1:
                        yt_dlp_cmd = [
                            yt_dlp_path,
                            *self.shortmax_auth_args(yt_dlp_path),
                            "--referer", f"https://{domain}/",
                            *accel_args,
                            "-o", file_name, current_stream_url
                        ]
                    else:
                        is_hls = ".m3u8" in current_stream_url.lower() or "dbxhls" in current_stream_url.lower()
                        retry_accel = self.get_accelerator_args(use_aria=(attempt == 0 and not is_hls))
                        yt_dlp_cmd = [
                            yt_dlp_path,
                            "--user-agent", "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/126.0.0.0 Safari/537.36",
                            *retry_accel,
                            "-o", file_name, current_stream_url
                        ]

                    try:
                        succ, stderr = self.run_yt_dlp_with_progress(yt_dlp_cmd)

                        if self.stop_flag:
                            break

                        if succ and self.is_valid_video_file(file_name):
                            self.normalize_clip_for_sync(file_name)
                            ep_dur = self.get_media_duration(file_name)

                            if source == 2 and self.auto_sub_var.get():
                                sub_u = self.extract_narto_subtitle_url(domain, narto_playlist, episode, page_meta.get("raw_html", ""))
                                if sub_u:
                                    raw_sub = self.curl_fetch(sub_u, headers={"Referer": f"https://{domain}/"})
                                    cues = self.parse_and_shift_subtitle_cues(raw_sub, cumulative_duration_sec)
                                    if cues:
                                        merged_subtitle_cues.extend(cues)

                            cumulative_duration_sec += ep_dur
                            downloaded_files.append(file_name)
                            last_saved_ep = episode
                            self.log_message(f"Success: Episode {episode} downloaded & sync-locked ({os.path.getsize(file_name)//1024} KB, {ep_dur:.2f}s).")
                            success = True
                            episode += 1
                            episodes_since_refresh += 1
                            time.sleep(2.0)
                            break
                        else:
                            if os.path.exists(file_name):
                                try: os.remove(file_name)
                                except: pass
                            err = stderr if stderr else "Downloaded file was invalid or <100KB."
                            tried_dead_urls.add(current_stream_url)

                            if source == 1 and self.shortmax_recover_from_error(err):
                                continue
                            if source == 1 and "cloudflare" in err.lower():
                                self.log_message(
                                    "Shortmax: blocked by the site's Cloudflare bot check (HTTP 403). "
                                    "Retrying will not help. Pass the check in your browser, quit the browser, then start again."
                                )
                                break

                            if source == 2 and any(code in err for code in ("410", "500", "403", "404", "invalid")):
                                err_snippet = next((line for line in err.splitlines() if "HTTP Error" in line), "Stream Expired/Error")
                                self.log_message(f"Stream rejected on Episode {episode} ({err_snippet}). Triggering Narto refresh-source...")
                                self.update_status(f"Ep {episode}: Refreshing stream token from server...", "orange")

                                ep_meta = self.scrape_webpage_playlist(domain, base_watch_path, episode, bust_cache=True)
                                if ep_meta.get("playlist"):
                                    page_meta = ep_meta
                                    narto_playlist = ep_meta["playlist"]

                                fresh_cands = self.trigger_narto_refresh_source(domain, base_watch_path, episode, page_meta, current_stream_url)
                                if page_meta.get("playlist"):
                                    narto_playlist = page_meta["playlist"]

                                for fc in fresh_cands:
                                    if fc not in candidate_urls:
                                        candidate_urls.append(fc)

                                untried = [u for u in candidate_urls if u not in tried_dead_urls]
                                if untried:
                                    self.log_message(f"Acquired fresh stream URL for Episode {episode}. Retrying...")
                                    episodes_since_refresh = 0
                                    continue

                            self.log_message(f"Attempt {attempt+1} failed for Episode {episode}: {err}")
                            time.sleep(2)
                    except Exception as e:
                        err = str(e)
                        self.log_message(f"Execution Error on ep {episode}: {err}")
                        time.sleep(2)

                if not success and not self.stop_flag:
                    if not downloaded_files:
                        self.log_message(f"FAILED ON EPISODE {episode}. Final Error:\n{err}")
                        if source == 1 and "cloudflare" in err.lower():
                            self.update_status("Shortmax blocked by Cloudflare bot check (403). See log.", "red")
                        else:
                            self.update_status(f"Ep {episode} Failed. Check Log.", "red")
                        if not keep_buttons_locked:
                            self.reset_buttons()
                        return
                    else:
                        self.log_message(f"Episode {episode} failed after all refresh attempts. Stopping to prevent missing episodes and merging Ep {initial_start_episode}-Ep {last_saved_ep}...")
                        break

            if not downloaded_files:
                if not self.stop_flag:
                    self.update_status(f"No files downloaded. Failed on Ep {current_ep_tracker}.", "red")
                if not keep_buttons_locked:
                    self.reset_buttons()
                return

            self.update_status(f"Merging {len(downloaded_files)} sync-locked episodes (Ep {initial_start_episode}-Ep {last_saved_ep})...", "orange")

            if initial_start_episode == 1 and not self.stop_flag and (not total_target or last_saved_ep == total_target) and last_saved_ep > 1:
                final_output = os.path.join(target_dir, f"{series_name}_Full.mp4")
            elif initial_start_episode == last_saved_ep:
                range_str = f"EP{initial_start_episode}"
                final_output = os.path.join(target_dir, f"{series_name}_{range_str}.mp4")
            else:
                range_str = f"EP{initial_start_episode}-EP{last_saved_ep}"
                final_output = os.path.join(target_dir, f"{series_name}_{range_str}.mp4")

            res = self.concat_video_files_synced(downloaded_files, final_output, normalize_first=False)

            if res.returncode != 0:
                 self.log_message(f"FFMPEG ERROR:\n{res.stderr}")
            else:
                self.record_last_output(final_output)
                for file in downloaded_files:
                    try: os.remove(file)
                    except: pass
                try: os.rmdir(temp_dir)
                except: pass

            if merged_subtitle_cues:
                srt_output = os.path.splitext(final_output)[0] + ".srt"
                try:
                    with open(srt_output, "w", encoding="utf-8") as sf:
                        for idx_cue, (st, et, txt) in enumerate(merged_subtitle_cues, 1):
                            sf.write(f"{idx_cue}\n{st} --> {et}\n{txt}\n\n")
                    self.log_message(f"SUBTITLES SAVED: {srt_output} ({len(merged_subtitle_cues)} lines)")
                except Exception as sub_ex:
                    self.log_message(f"Subtitle save warning: {str(sub_ex)}")

            self.update_status(f"Success! Sync-Locked Merge Ep {initial_start_episode} to Ep {last_saved_ep}.", "green")
            self.log_message(f"COMPLETED: Saved to {final_output}")

        except Exception as e:
            import traceback
            tb = traceback.format_exc()
            self.log_message(f"SYSTEM CRASH:\n{tb}")
            saved_str = f"Last saved: Ep {last_saved_ep}" if last_saved_ep else "No episodes saved"
            self.update_status(f"Stopped at Ep {current_ep_tracker}. {saved_str}. Check Log.", "red")

        if not keep_buttons_locked:
            self.reset_buttons()


if __name__ == "__main__":
    root = TkinterDnD.Tk() if HAS_DND else tk.Tk()
    app = DownloaderApp(root)
    root.mainloop()