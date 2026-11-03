import os, sys, subprocess, re, threading, urllib.parse, webbrowser, datetime, time, shutil, copy
import json, math
import urllib.request
import tkinter as tk
import tkinter.font as tkfont
from tkinter import ttk, messagebox, filedialog
import tkinter.simpledialog

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

def render_check(master, size, on, color, bg, round_box=False, off=None):
    """3D checkbox (or radio dot when round_box) for ttk indicators."""
    if on:
        top, bot, edge = color, _hexc(_mix(_rgb(color), (0, 0, 0), 0.35)), _hexc(_mix(_rgb(color), (255, 255, 255), 0.3))
    else:
        top, bot, edge = off or ("#1e293b", "#0f172a", "#475569")
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


# =============================================================================
# 🎬 NADER PLAYER (v1.9.1): fast external player (mpv engine) + control panel
# Voice-sync fixing, Arabic subtitles, auto-sync subtitles to the voice, speed,
# voice boost, resume where you stopped. Falls back to VLC or the system player.
# =============================================================================
import socket as _socket
import hashlib as _hashlib


def find_mpv(base_dir=""):
    names = ["mpv.exe", "mpv.com"] if sys.platform == "win32" else ["mpv"]
    for n in names:
        p = shutil.which(n)
        if p:
            return p
    cands = []
    if sys.platform == "win32":
        la = os.environ.get("LOCALAPPDATA", "")
        pf = [os.environ.get("ProgramFiles", r"C:\Program Files"), os.environ.get("ProgramFiles(x86)", r"C:\Program Files (x86)")]
        cands += [os.path.join(base_dir, "mpv", "mpv.exe"), os.path.join(base_dir, "mpv.exe"),
                  os.path.join(la, "Microsoft", "WinGet", "Links", "mpv.exe"),
                  os.path.join(os.path.expanduser("~"), "scoop", "shims", "mpv.exe")]
        cands += [os.path.join(p, "mpv", "mpv.exe") for p in pf]
        winget_pk = os.path.join(la, "Microsoft", "WinGet", "Packages")
        if os.path.isdir(winget_pk):
            for d in os.listdir(winget_pk):
                if "mpv" in d.lower():
                    for root_dir, _, files in os.walk(os.path.join(winget_pk, d)):
                        if "mpv.exe" in files:
                            cands.append(os.path.join(root_dir, "mpv.exe"))
    elif sys.platform == "darwin":
        cands += ["/Applications/mpv.app/Contents/MacOS/mpv", "/opt/homebrew/bin/mpv", "/usr/local/bin/mpv",
                  os.path.join(base_dir, "mpv.app", "Contents", "MacOS", "mpv")]
    for c in cands:
        if c and os.path.isfile(c):
            return c
    return ""


def find_vlc():
    p = shutil.which("vlc")
    if p:
        return p
    for c in (r"C:\Program Files\VideoLAN\VLC\vlc.exe", r"C:\Program Files (x86)\VideoLAN\VLC\vlc.exe",
              "/Applications/VLC.app/Contents/MacOS/VLC"):
        if os.path.isfile(c):
            return c
    return ""


def parse_srt(text):
    cues = []
    blocks = re.split(r"\n\s*\n", text.replace("\r\n", "\n").replace("\r", "\n").strip())
    tre = re.compile(r"(\d+):(\d+):(\d+)[,.](\d+)\s*-->\s*(\d+):(\d+):(\d+)[,.](\d+)")
    for b in blocks:
        lines = b.split("\n")
        for i, ln in enumerate(lines):
            m = tre.search(ln)
            if m:
                g = [int(x) for x in m.groups()]
                st = g[0] * 3600 + g[1] * 60 + g[2] + g[3] / 1000.0
                en = g[4] * 3600 + g[5] * 60 + g[6] + g[7] / 1000.0
                body = "\n".join(lines[i + 1:]).strip()
                if body:
                    cues.append([st, en, body])
                break
    return cues


def write_srt(cues, path):
    def f(t):
        t = max(0.0, t)
        return f"{int(t // 3600):02d}:{int(t % 3600 // 60):02d}:{int(t % 60):02d},{int(round((t % 1) * 1000)) % 1000:03d}"
    with open(path, "w", encoding="utf-8") as fh:
        for i, (st, en, body) in enumerate(cues, 1):
            fh.write(f"{i}\n{f(st)} --> {f(en)}\n{body}\n\n")


def translate_lines(lines, target="ar", progress=None):
    """Free web translation (Google gtx endpoint), in batches. Returns the translated lines (same count)."""
    out = []
    sep = "\n"
    i = 0
    while i < len(lines):
        batch, size = [], 0
        while i < len(lines) and size + len(lines[i]) < 3800 and len(batch) < 60:
            batch.append(lines[i].replace("\n", " "))
            size += len(lines[i]) + 1
            i += 1
        if not batch:
            batch = [lines[i][:3800]]
            i += 1
        q = urllib.parse.quote(sep.join(batch))
        url = f"https://translate.googleapis.com/translate_a/single?client=gtx&sl=auto&tl={target}&dt=t&q={q}"
        req = urllib.request.Request(url, headers={"User-Agent": "Mozilla/5.0"})
        data = json.loads(urllib.request.urlopen(req, timeout=30).read().decode("utf-8"))
        text = "".join(seg[0] for seg in data[0] if seg and seg[0])
        parts = text.split("\n")
        if len(parts) != len(batch):      # rare: the service merged lines — translate this batch one by one
            parts = []
            for line in batch:
                u = f"https://translate.googleapis.com/translate_a/single?client=gtx&sl=auto&tl={target}&dt=t&q={urllib.parse.quote(line)}"
                d = json.loads(urllib.request.urlopen(urllib.request.Request(u, headers={"User-Agent": "Mozilla/5.0"}), timeout=30).read().decode("utf-8"))
                parts.append("".join(seg[0] for seg in d[0] if seg and seg[0]))
        out += [p.strip() for p in parts]
        if progress:
            progress(len(out), len(lines))
    return out


class MpvClient:
    """Tiny JSON-IPC client for mpv (named pipe on Windows, unix socket elsewhere). Request/response only."""
    def __init__(self, address):
        self.address = address
        self.lock = threading.Lock()
        self.conn = None
        self.req = 0
        self._buf = b""

    def connect(self, timeout=8.0):
        end = time.time() + timeout
        while time.time() < end:
            try:
                if sys.platform == "win32":
                    self.conn = open(self.address, "r+b", buffering=0)
                else:
                    s = _socket.socket(_socket.AF_UNIX, _socket.SOCK_STREAM)
                    s.connect(self.address)
                    s.settimeout(3.0)
                    self.conn = s
                self._send_raw({"command": ["disable_event", "all"], "request_id": 0})
                self._read_reply(0)
                return True
            except Exception:
                self.conn = None
                time.sleep(0.2)
        return False

    def _send_raw(self, obj):
        data = (json.dumps(obj) + "\n").encode("utf-8")
        if sys.platform == "win32":
            self.conn.write(data)
        else:
            self.conn.sendall(data)

    def _readline(self):
        while b"\n" not in self._buf:
            chunk = self.conn.read(4096) if sys.platform == "win32" else self.conn.recv(4096)
            if not chunk:
                raise ConnectionError("mpv closed")
            self._buf += chunk
        line, self._buf = self._buf.split(b"\n", 1)
        return line

    def _read_reply(self, rid):
        for _ in range(50):
            msg = json.loads(self._readline().decode("utf-8", "ignore") or "{}")
            if msg.get("request_id") == rid:
                return msg
        return {}

    def command(self, *args):
        if self.conn is None:
            return None
        with self.lock:
            try:
                self.req += 1
                rid = self.req
                self._send_raw({"command": list(args), "request_id": rid})
                msg = self._read_reply(rid)
                return msg.get("data") if msg.get("error") == "success" else None
            except Exception:
                self.conn = None
                return None

    def get(self, prop):
        return self.command("get_property", prop)

    def set(self, prop, value):
        return self.command("set_property", prop, value)

    def close(self):
        try:
            if self.conn:
                self.conn.close()
        except Exception:
            pass
        self.conn = None


class NaderPlayer:
    """Opens a video in mpv and shows a control panel with the 'power' tools."""
    def __init__(self, app, video_path):
        self.app = app
        self.path = os.path.abspath(video_path)
        self.meta = app.lib_meta.setdefault(self.path, {})
        self.proc = None
        self.client = None
        self.sub_path = ""
        self.win = None
        self.mpv = find_mpv(app.base_dir)
        if not self.mpv:
            if not app.offer_install_mpv():
                return
            self.mpv = find_mpv(app.base_dir)
            if not self.mpv:
                app.play_with_fallback(self.path)
                return
        self.start()

    # --------------------------------------------------------------- engine
    def start(self):
        state_dir = os.path.join(self.app.base_dir, ".player_state")
        os.makedirs(state_dir, exist_ok=True)
        tag = _hashlib.md5(self.path.encode("utf-8")).hexdigest()[:10]
        self.ipc = rf"\\.\pipe\nader_player_{tag}" if sys.platform == "win32" else os.path.join(state_dir, f"ipc_{tag}.sock")
        if sys.platform != "win32" and os.path.exists(self.ipc):
            try: os.remove(self.ipc)
            except OSError: pass
        cmd = [self.mpv, self.path, f"--input-ipc-server={self.ipc}", "--force-window=yes", "--keep-open=yes",
               "--save-position-on-quit", f"--watch-later-directory={state_dir}", "--sub-auto=fuzzy", "--slang=ar,ara,en,eng",
               "--hwdec=auto-safe", "--autofit-larger=90%x90%", f"--title=Nader Player — {os.path.basename(self.path)}",
               "--sub-font-size=46", "--sub-border-size=3", "--osd-font-size=34",
               f"--audio-delay={float(self.meta.get('audio_delay', 0.0)):.3f}"]
        cmd += getattr(self.app, "_player_extra_args", [])
        kwargs = {"creationflags": 0x08000000} if sys.platform == "win32" else {}
        try:
            self.proc = subprocess.Popen(cmd, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, **kwargs)
        except Exception as e:
            messagebox.showerror("Nader Player", f"Could not start the player:\n{e}")
            return
        self.client = MpvClient(self.ipc)
        self.build_panel()
        threading.Thread(target=self._connect, daemon=True).start()

    def _connect(self):
        ok = self.client.connect(10)
        self.app.root.after(0, lambda: self._on_connected(ok))

    def _on_connected(self, ok):
        if not self.win or not self.win.winfo_exists():
            return
        if not ok:
            self.status.config(text="Could not talk to the player window (it still plays).")
            return
        self.status.config(text="Ready. Tip: the panel stays next to the video — move it anywhere.")
        sub = self._existing_sub()
        if sub:
            self.sub_path = sub
        self._tick()

    def _existing_sub(self):
        base = os.path.splitext(self.path)[0]
        for cand in (base + ".ar.srt", base + ".srt", base + ".en.srt"):
            if os.path.exists(cand):
                return cand
        return ""

    # ---------------------------------------------------------------- panel
    def build_panel(self):
        app = self.app
        self.win = w = tk.Toplevel(app.root)
        w.title("🎬 Nader Player — Controls")
        w.configure(bg="#0f172a")
        w.resizable(False, False)
        try: w.attributes("-topmost", True)
        except Exception: pass
        w.protocol("WM_DELETE_WINDOW", self.close)
        BG, FG, MUTED = "#0f172a", "#f1f5f9", "#94a3b8"

        def section(text):
            tk.Label(w, text=text, bg=BG, fg="#38bdf8", font=("Arial", 10, "bold"), anchor="w").pack(fill="x", padx=12, pady=(8, 2))
            f = tk.Frame(w, bg=BG)
            f.pack(fill="x", padx=12)
            return f

        tk.Label(w, text=os.path.basename(self.path), bg=BG, fg=FG, font=("Arial", 11, "bold"), wraplength=520, justify="left").pack(fill="x", padx=12, pady=(10, 0))
        self.time_lbl = tk.Label(w, text="--:-- / --:--", bg=BG, fg="#fbbf24", font=("Courier", 12, "bold"))
        self.time_lbl.pack(anchor="w", padx=12)

        r = section("▶ Playback")
        for txt, fn in (("⏪ 10s", lambda: self.cmd("seek", -10)), ("⏯ Play / Pause", lambda: self.cmd("cycle", "pause")),
                        ("10s ⏩", lambda: self.cmd("seek", 10)), ("⛶ Full Screen", lambda: self.cmd("cycle", "fullscreen")),
                        ("📸 Snapshot", lambda: self.cmd("screenshot"))):
            ttk.Button(r, text=txt, command=fn).pack(side="left", padx=2)
        r2 = tk.Frame(w, bg=BG)
        r2.pack(fill="x", padx=12, pady=(4, 0))
        tk.Label(r2, text="Speed:", bg=BG, fg=FG).pack(side="left")
        self.speed_var = tk.StringVar(value="1.0×")
        cb = ttk.Combobox(r2, textvariable=self.speed_var, values=["0.5×", "0.75×", "1.0×", "1.25×", "1.5×", "1.75×", "2.0×"], width=6, state="readonly")
        cb.pack(side="left", padx=4)
        cb.bind("<<ComboboxSelected>>", lambda e: self.client.set("speed", float(self.speed_var.get().rstrip("×"))))
        self.boost_var = tk.BooleanVar(value=False)
        ttk.Checkbutton(r2, text="🔊 Voice boost (quiet dialogue louder)", variable=self.boost_var, command=self.toggle_boost).pack(side="left", padx=10)

        r = section("🎙️ Voice sync — fix sound that is early or late")
        for txt, d in (("-0.5s", -0.5), ("-0.1s", -0.1), ("-0.02s", -0.02)):
            ttk.Button(r, text=txt, width=6, command=lambda d=d: self.shift_audio(d)).pack(side="left", padx=1)
        self.audio_lbl = tk.Label(r, text="0 ms", bg=BG, fg="#fbbf24", font=("Arial", 10, "bold"), width=9)
        self.audio_lbl.pack(side="left", padx=4)
        for txt, d in (("+0.02s", 0.02), ("+0.1s", 0.1), ("+0.5s", 0.5)):
            ttk.Button(r, text=txt, width=6, command=lambda d=d: self.shift_audio(d)).pack(side="left", padx=1)
        ttk.Button(r, text="Reset", command=lambda: self.shift_audio(None)).pack(side="left", padx=6)
        tk.Label(w, text="Voice comes BEFORE the lips → press +   •   voice comes AFTER the lips → press −   (saved for this video)",
                 bg=BG, fg=MUTED, font=("Arial", 8)).pack(anchor="w", padx=12)

        r = section("💬 Subtitles")
        ttk.Button(r, text="🇸🇦 Arabic", style="Accent.TButton", command=self.arabic_subs).pack(side="left", padx=2)
        ttk.Button(r, text="✨ Auto-sync to voice", command=self.auto_sync_subs).pack(side="left", padx=2)
        ttk.Button(r, text="📂 Load .srt", command=self.load_srt_dialog).pack(side="left", padx=2)
        ttk.Button(r, text="🔎 Find online", command=self.find_online).pack(side="left", padx=2)
        r3 = tk.Frame(w, bg=BG)
        r3.pack(fill="x", padx=12, pady=(4, 0))
        ttk.Button(r3, text="On / Off", command=lambda: self.cmd("cycle", "sub-visibility")).pack(side="left", padx=2)
        ttk.Button(r3, text="Next track", command=lambda: self.cmd("cycle", "sub")).pack(side="left", padx=2)
        tk.Label(r3, text="  Timing:", bg=BG, fg=FG).pack(side="left")
        ttk.Button(r3, text="−0.1s", width=6, command=lambda: self.shift_sub(-0.1)).pack(side="left", padx=1)
        self.sub_lbl = tk.Label(r3, text="0 ms", bg=BG, fg="#fbbf24", font=("Arial", 10, "bold"), width=8)
        self.sub_lbl.pack(side="left")
        ttk.Button(r3, text="+0.1s", width=6, command=lambda: self.shift_sub(0.1)).pack(side="left", padx=1)
        tk.Label(r3, text="  Size:", bg=BG, fg=FG).pack(side="left")
        ttk.Button(r3, text="A−", width=3, command=lambda: self.cmd("add", "sub-scale", -0.1)).pack(side="left", padx=1)
        ttk.Button(r3, text="A+", width=3, command=lambda: self.cmd("add", "sub-scale", 0.1)).pack(side="left", padx=1)

        self.status = tk.Label(w, text="Starting the player…", bg=BG, fg=MUTED, font=("Arial", 9), wraplength=540, justify="left", anchor="w")
        self.status.pack(fill="x", padx=12, pady=(10, 10))
        self.audio_delay = float(self.meta.get("audio_delay", 0.0))
        self.audio_lbl.config(text=f"{self.audio_delay * 1000:+.0f} ms")
        if getattr(app, "_theme_now", "dark") == "light":
            app._remap_tree(w, True)

    # ------------------------------------------------------------- actions
    def cmd(self, *args):
        threading.Thread(target=lambda: self.client.command(*args), daemon=True).start()

    def say(self, text):
        self.app.root.after(0, lambda: self.win and self.win.winfo_exists() and self.status.config(text=text))

    def _tick(self):
        if not self.win or not self.win.winfo_exists():
            return
        if self.proc and self.proc.poll() is not None:
            self.close()
            return

        def work():
            pos, dur = self.client.get("time-pos"), self.client.get("duration")
            if pos is not None:
                self.meta["position"] = pos
                self.meta["duration"] = dur

                def show():
                    if self.win and self.win.winfo_exists():
                        self.time_lbl.config(text=f"{self._fmt(pos)} / {self._fmt(dur or 0)}")
                self.app.root.after(0, show)
        threading.Thread(target=work, daemon=True).start()
        self.win.after(1000, self._tick)

    @staticmethod
    def _fmt(t):
        t = int(t or 0)
        return f"{t // 3600}:{t % 3600 // 60:02d}:{t % 60:02d}" if t >= 3600 else f"{t // 60:02d}:{t % 60:02d}"

    def shift_audio(self, d):
        self.audio_delay = 0.0 if d is None else round(self.audio_delay + d, 3)
        self.client.set("audio-delay", self.audio_delay)
        self.audio_lbl.config(text=f"{self.audio_delay * 1000:+.0f} ms")
        self.meta["audio_delay"] = self.audio_delay
        self.app.save_lib_meta()
        self.cmd("show-text", f"Voice sync {self.audio_delay * 1000:+.0f} ms", 1500)

    def shift_sub(self, d):
        cur = self.client.get("sub-delay") or 0.0
        new = round(cur + d, 3)
        self.client.set("sub-delay", new)
        self.sub_lbl.config(text=f"{new * 1000:+.0f} ms")

    def toggle_boost(self):
        if self.boost_var.get():
            self.client.command("af", "add", "@boost:lavfi=[dynaudnorm=f=150:g=15:p=0.9]")
        else:
            self.client.command("af", "remove", "@boost")

    def load_sub(self, path, title=""):
        self.sub_path = path
        self.client.command("sub-add", path, "select", title or os.path.basename(path))
        self.say(f"Subtitles loaded: {os.path.basename(path)}")

    def load_srt_dialog(self):
        p = filedialog.askopenfilename(title="Choose subtitles", filetypes=[("Subtitles", "*.srt *.vtt *.ass *.ssa"), ("All", "*.*")],
                                       initialdir=os.path.dirname(self.path))
        if p:
            self.load_sub(p)

    def _source_cues(self):
        """Subtitle lines to work from: the .srt next to the video, else the video's own subtitle track."""
        sub = self.sub_path or self._existing_sub()
        if sub and os.path.exists(sub):
            return parse_srt(open(sub, encoding="utf-8", errors="ignore").read()), sub
        tmp = os.path.splitext(self.path)[0] + ".embedded.srt"
        r = self.app.run_ffmpeg(["ffmpeg", "-y", "-i", self.path, "-map", "0:s:0", tmp])
        if r.returncode == 0 and os.path.exists(tmp):
            cues = parse_srt(open(tmp, encoding="utf-8", errors="ignore").read())
            try: os.remove(tmp)
            except OSError: pass
            return cues, ""
        return [], ""

    def arabic_subs(self):
        out = os.path.splitext(self.path)[0] + ".ar.srt"
        if os.path.exists(out):
            self.load_sub(out, "العربية")
            return

        def work():
            if self.app.settings.get("opensubtitles_key"):
                self.say("Looking for Arabic subtitles online…")
                if self.app.opensubtitles_download(self.app.library_title(self.path), "ar", out):
                    self.app.root.after(0, lambda: self.load_sub(out, "العربية"))
                    return
            cues, _src = self._source_cues()
            if not cues:
                self.say("No subtitles to translate in this video. Load an English .srt (📂) or use '🔎 Find online', then press 🇸🇦 again.\n"
                         "Tip: ANK Media Studio can make subtitles from the voice (AI Subtitles).")
                return
            self.say(f"Translating {len(cues)} lines to Arabic…")
            try:
                ar = translate_lines([c[2] for c in cues], "ar", progress=lambda a, b: self.say(f"Translating to Arabic… {a}/{b}"))
            except Exception as e:
                self.say(f"Translation failed (internet needed): {e}")
                return
            write_srt([[c[0], c[1], t or c[2]] for c, t in zip(cues, ar)], out)
            self.app.root.after(0, lambda: self.load_sub(out, "العربية"))
        threading.Thread(target=work, daemon=True).start()

    def auto_sync_subs(self):
        """Lines the subtitles up with the voice around the current scene (±3 s)."""
        def work():
            cues, _ = self._source_cues()
            if len(cues) < 5:
                self.say("Load subtitles first, then press ✨ Auto-sync.")
                return
            pos = float(self.client.get("time-pos") or 0.0)
            dur = float(self.client.get("duration") or 0.0)
            start = max(0.0, min(pos - 90, max(0.0, dur - 240)))
            self.say("Listening to the voice to line up the subtitles…")
            lag = self.app.estimate_sub_lag(self.path, [(c[0], c[1]) for c in cues], start, 240)
            if lag is None:
                self.say("Not enough dialogue here to compare — try again during a talking scene.")
                return
            self.client.set("sub-delay", lag)
            self.app.root.after(0, lambda: self.sub_lbl.config(text=f"{lag * 1000:+.0f} ms"))
            self.client.command("show-text", f"Subtitles synced {lag * 1000:+.0f} ms", 2000)
            self.say(f"Subtitles moved {lag * 1000:+.0f} ms to match the voice.")
        threading.Thread(target=work, daemon=True).start()

    def find_online(self):
        if not self.app.settings.get("opensubtitles_key"):
            key = tk.simpledialog.askstring(
                "OpenSubtitles", "Searching subtitles online uses OpenSubtitles.com (free).\n\n"
                "1. Make a free account at opensubtitles.com\n2. Open 'API consumers' and create a key\n3. Paste the API key here:",
                parent=self.win)
            if not key:
                return
            self.app.settings["opensubtitles_key"] = key.strip()
            self.app.save_settings()
        lang = tk.simpledialog.askstring("Find subtitles", "Language code (ar = Arabic, en = English):", initialvalue="ar", parent=self.win) or "ar"
        title = tk.simpledialog.askstring("Find subtitles", "Search for (title):", initialvalue=self.app.library_title(self.path), parent=self.win)
        if not title:
            return
        out = os.path.splitext(self.path)[0] + f".{lang}.srt"

        def work():
            self.say(f"Searching OpenSubtitles for '{title}' ({lang})…")
            if self.app.opensubtitles_download(title, lang, out):
                self.app.root.after(0, lambda: self.load_sub(out))
            else:
                self.say("Nothing found online for this title. For Arabic, use 🇸🇦 (translates the English subtitles).")
        threading.Thread(target=work, daemon=True).start()

    def close(self):
        try:
            self.app.save_lib_meta()
        except Exception:
            pass
        if self.client:
            self.client.command("quit-watch-later") if self.proc and self.proc.poll() is None else None
            self.client.close()
        if self.win and self.win.winfo_exists():
            self.win.destroy()
        self.win = None
        try:
            self.app.root.after(300, self.app.refresh_library)
        except Exception:
            pass



class DownloaderApp:
    def __init__(self, root):
        self.root = root
        self.version = "v1.9.3"
        self.root.title(f"Nader Pro Video & Drama Studio {self.version} — Created by Nader Alkhansa")
        self.root.geometry("1200x950")
        self.root.minsize(960, 820)
        self.root.configure(bg="#0b0f19")

        # --- PORTABLE PATHING + SAVED SETTINGS ---
        self.base_dir = os.path.dirname(os.path.abspath(__file__))
        self.load_settings()
        self._theme_now = "dark"
        self._queue_running = False

        # --- SETUP PRO STUDIO THEME (dark first; light / auto applied after the pages exist) ---
        self.setup_pro_theme()

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
            ("home", "🏠 Home"),
            ("dlqueue", "📋 Queue"),
            ("library", "📚 Library"),
            ("find", "🔍 Find"),
            ("sync", "🎙️ Sync"),
            ("manual_edit", "🎛️ Edit"),
            ("queue", "🌙 Narto 5"),
            ("trim_crop", "✂️ Trim"),
            ("settings", "⚙️ Settings"),
        ]
        for key, label in nav_items:
            b = self.make_3d_pill(nav_pills, label, lambda k=key: self.show_page(k))
            b.pack(side="left", padx=1, pady=8)
            self.nav_buttons[key] = b
        self.theme_pill = self.make_3d_pill(nav_pills, {"auto": "🌓", "dark": "🌙", "light": "☀️"}.get(self.settings.get("theme"), "🌓 Auto"),
                                            self.cycle_theme)
        self.theme_pill.pack(side="left", padx=(8, 2), pady=8)
        self.setup_info_mode(nav_pills)

        # Nav pills get space first; a long page title is clipped instead of pushing the pills off-screen
        # v1.9.0: the page title gets its own slim bar so all navigation pills fit
        self.header_title_lbl.pack_forget()
        self.title_bar = tk.Frame(self.root, bg="#0d1322", height=26)
        self.title_bar.pack(side="top", fill="x")
        self.header_title_lbl = tk.Label(self.title_bar, text="", font=("Arial", 10, "bold"), bg="#0d1322", fg="#cbd5e1", anchor="w")
        self.header_title_lbl.pack(side="left", padx=16, pady=3, fill="x", expand=True)

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
        self.build_extra_pages()
        self.attach_field_help()
        self.apply_saved_settings()
        self.apply_ui_theme(force=True)
        self.root.after(20000, self._watch_os_theme)

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
        w = f.measure(text) + 18

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
        c._ank_badge = (color, size)
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
            "trim_crop": "✂️ HD Multi-Video Trim, Crop & Frame Scrubber Studio",
            "dlqueue": "📋 Download Queue (runs overnight, resumes after restart)",
            "library": "📚 Library — everything you downloaded",
            "settings": "⚙️ Settings & Engine Health",
            "find": "🔍 Find by Image — upload a picture, get the series and its direct links",
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

        if getattr(self, "_theme_now", "dark") == "light":
            self._remap_tree(self.pages[page_name], True)   # widgets made since the theme switch
        if page_name == "library":
            self.refresh_library()
        if page_name == "settings" and not self.health_tree.get_children():
            self.refresh_health()

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
        self.save_settings()
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
        ttk.Button(settings_frame, text="➕ Add to Queue", command=self.queue_add_current_dashboard).grid(row=0, column=5, padx=(12, 0))

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

        _mw, _mh = self.FME_MONITOR_SIZES.get(self.settings.get("fme_monitor", "Small"), (310, 174))
        self.fme_frame_canvas = tk.Canvas(prev_box, width=_mw, height=_mh, bg="#070a12", highlightthickness=1, highlightbackground="#38bdf8")
        self.fme_frame_canvas.grid(row=0, column=0, rowspan=4, padx=(4, 12), pady=2)
        self.fme_frame_canvas.create_text(
            _mw // 2, _mh // 2,
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

        # v1.9.0: second row keeps every control visible when the monitor is made bigger
        ph_btn_row2 = ttk.Frame(scrub_ctrl, style="Card.TFrame")
        ph_btn_row2.pack(fill="x", pady=(0, 3))
        ttk.Button(
            ph_btn_row2, text="🔍 Pop-Out (F11 = full screen)", style="Accent.TButton",
            command=self.fme_toggle_popout
        ).pack(side="left", padx=(0, 1))
        ttk.Label(ph_btn_row2, text="  🖥️ Monitor size:", background="#131b2e").pack(side="left")
        self.fme_mon_size_var = tk.StringVar(value=self.settings.get("fme_monitor", "Small"))
        mon_cb = ttk.Combobox(ph_btn_row2, textvariable=self.fme_mon_size_var, values=list(self.FME_MONITOR_SIZES),
                              state="readonly", width=8)
        mon_cb.pack(side="left", padx=(4, 1))
        mon_cb.bind("<<ComboboxSelected>>", lambda e: self.fme_set_monitor_size(self.fme_mon_size_var.get()))

        self.fme_hand_lock_var = tk.BooleanVar(value=False)
        tk.Checkbutton(
            ph_btn_row2, text="✋ Lock Hand Tool On", variable=self.fme_hand_lock_var,
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
            fw, fh = self.fme_monitor_dims()
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
                            mw, mh = self.fme_monitor_dims()
                            self.fme_frame_canvas.create_image(mw // 2, mh // 2, image=img)
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


    FME_MONITOR_SIZES = {"Small": (310, 174), "Medium": (420, 236), "Large": (540, 304)}

    def fme_monitor_dims(self):
        return self.FME_MONITOR_SIZES.get(self.settings.get("fme_monitor", "Small"), (310, 174))

    def fme_set_monitor_size(self, name):
        """Resizes the Full Manual Edit monitor (Pop-Out gives a free-size window)."""
        if name not in self.FME_MONITOR_SIZES:
            return
        self.settings["fme_monitor"] = name
        self.save_settings()
        w, h = self.FME_MONITOR_SIZES[name]
        self.fme_frame_canvas.config(width=w, height=h)
        if not self.fme_popout_is_open():
            self.fme_frame_canvas.delete("all")
            self.fme_frame_canvas.create_text(w // 2, h // 2, text="…", fill="#94a3b8")
            self.fme_request_preview_frame_throttled(self.fme_state["playhead"], force=True)
        # A bigger monitor needs a taller window: maximise if the page no longer fits
        self.root.update_idletasks()
        page = self.pages.get("manual_edit")
        if page is not None and page.winfo_reqheight() > self.page_container.winfo_height() + 4:
            try:
                self.root.state("zoomed") if sys.platform == "win32" else self.root.attributes("-zoomed", True)
            except Exception:
                self.root.geometry(f"{self.root.winfo_width()}x{min(self.root.winfo_screenheight() - 60, self.root.winfo_height() + page.winfo_reqheight() - self.page_container.winfo_height())}")

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
            self.fme_monitor_dims()[0] // 2, self.fme_monitor_dims()[1] // 2, text="🔍 Showing in Pop-Out Monitor\n(close it to preview here again)",
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
            name = os.path.basename(self.last_output_file)
            if "_resume" not in self.last_output_file and not name.startswith(("temp", "_temp")) and ".uniform" not in name and ".synclock" not in name:
                self.library_note_output(self.last_output_file)
            if not getattr(self, "_queue_running", False) and "_resume" not in self.last_output_file and not name.startswith(("temp", "_temp")) \
                    and ".uniform" not in name and ".synclock" not in name and time.time() - getattr(self, "_last_notify", 0) > 5:
                self._last_notify = time.time()
                try:
                    self.root.after(0, lambda n=name: self.notify("Download finished ✅", n))
                except Exception:
                    pass

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
            "-af", "aresample=async=1:min_hard_comp=0.010000:first_pts=0,apad",
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
        """
        v1.9.0 EXACT-SYNC MERGE.
        Video is joined with a pure stream copy (bit-exact). Each episode's audio is rebuilt as lossless PCM that is
        exactly as long as that episode's video and keeps its original offset to the picture, then the whole track is
        encoded once. Tiny per-episode differences (AAC priming, HLS start offsets, short/long audio) can no longer add
        up into drift. Falls back to the classic copy-merge if anything goes wrong.
        """
        if normalize_first and self.sync_lock_var.get():
            total = len(file_list)
            for idx, fpath in enumerate(file_list, 1):
                if self.stop_flag:
                    break
                self.update_status(f"{status_prefix}: Sync-locking clip {idx}/{total}...", "#f59e0b")
                self.normalize_clip_for_sync(fpath)
        res = None
        if self.sync_lock_var.get():
            try:
                res = self._concat_exact_sync(file_list, final_output, status_prefix)
            except Exception as e:
                self.log_message(f"Exact-sync merge error ({e}); using the classic merge.")
                res = None
            if res is not None and res.returncode != 0:
                self.log_message(f"Exact-sync merge failed; using the classic merge.\n{(res.stderr or '')[-600:]}")
                res = None
        if res is None:
            res = self._concat_copy_classic(file_list, final_output)
        if res.returncode == 0 and os.path.exists(final_output):
            self.record_last_output(final_output)
            self.verify_merge_sync(final_output, file_list_count=len(file_list))
        return res

    def _concat_copy_classic(self, file_list, final_output):
        list_file = final_output + ".concat_list.txt"
        with open(list_file, "w", encoding="utf-8") as f:
            for vid in file_list:
                f.write(f"file '{vid.replace(chr(92), '/')}'\n")
        res = self.run_ffmpeg(["ffmpeg", "-y", "-f", "concat", "-safe", "0", "-i", list_file, "-c", "copy",
                               "-movflags", "+faststart", "-avoid_negative_ts", "make_zero", final_output])
        try: os.remove(list_file)
        except: pass
        return res

    def _stream_starts(self, path):
        """(video start, audio start or None) in seconds, from ffprobe."""
        ffprobe = shutil.which("ffprobe") or shutil.which("ffprobe.exe")
        if not ffprobe:
            return 0.0, 0.0
        kwargs = {"creationflags": 0x08000000} if sys.platform == "win32" else {}
        r = subprocess.run([ffprobe, "-v", "error", "-show_entries", "stream=codec_type,start_time:stream_disposition=attached_pic",
                            "-of", "json", path], capture_output=True, text=True, encoding="utf-8", errors="ignore", **kwargs)
        vs, a_s = None, None
        for st in json.loads(r.stdout or "{}").get("streams", []):
            try:
                t = float(st.get("start_time", 0) or 0)
            except ValueError:
                t = 0.0
            if st.get("codec_type") == "video" and vs is None and not st.get("disposition", {}).get("attached_pic"):
                vs = t
            elif st.get("codec_type") == "audio" and a_s is None:
                a_s = t
        return (vs or 0.0), a_s

    def _concat_exact_sync(self, file_list, final_output, status_prefix="Merging"):
        work = final_output + ".parts"
        os.makedirs(work, exist_ok=True)
        v_parts, a_parts = [], []
        try:
            total = len(file_list)
            for i, src in enumerate(file_list, 1):
                if self.stop_flag:
                    return None
                self.update_status(f"{status_prefix}: exact-sync {i}/{total} (video copy + sample-exact audio)...", "#f59e0b")
                vpart = os.path.join(work, f"v{i:04d}.mp4")
                apart = os.path.join(work, f"a{i:04d}.wav")
                r = self.run_ffmpeg(["ffmpeg", "-y", "-i", src, "-map", "0:v:0", "-an", "-sn", "-dn", "-c:v", "copy",
                                     "-video_track_timescale", "90000", "-avoid_negative_ts", "make_zero", vpart])
                if r.returncode != 0 or not os.path.exists(vpart):
                    return r
                vdur = self.get_media_duration(vpart)
                if vdur <= 0:
                    return None
                vs, a_s = self._stream_starts(src)
                if a_s is None:
                    cmd = ["ffmpeg", "-y", "-f", "lavfi", "-i", f"anullsrc=r=48000:cl=stereo", "-t", f"{vdur:.6f}",
                           "-c:a", "pcm_s16le", apart]
                else:
                    off = a_s - vs   # >0: sound starts after the picture, <0: sound starts before it
                    chain = ["asetpts=PTS-STARTPTS", "aresample=48000:async=1:min_hard_comp=0.010000:first_pts=0"]
                    if off > 0.0005:
                        ms = int(round(off * 1000))
                        chain.append(f"adelay={ms}|{ms}")
                    elif off < -0.0005:
                        chain += [f"atrim=start={-off:.6f}", "asetpts=PTS-STARTPTS"]
                    chain += ["apad", f"atrim=end={vdur:.6f}", "asetpts=PTS-STARTPTS"]
                    cmd = ["ffmpeg", "-y", "-i", src, "-map", "0:a:0", "-vn", "-af", ",".join(chain),
                           "-ac", "2", "-ar", "48000", "-c:a", "pcm_s16le", apart]
                r = self.run_ffmpeg(cmd)
                if r.returncode != 0 or not os.path.exists(apart):
                    return r
                v_parts.append(vpart)
                a_parts.append(apart)
            vlist, alist = os.path.join(work, "v.txt"), os.path.join(work, "a.txt")
            for lst, parts in ((vlist, v_parts), (alist, a_parts)):
                with open(lst, "w", encoding="utf-8") as f:
                    for p in parts:
                        f.write(f"file '{p.replace(chr(92), '/')}'\n")
            self.update_status(f"{status_prefix}: joining {len(v_parts)} clip(s) with locked sound...", "#f59e0b")
            return self.run_ffmpeg(["ffmpeg", "-y", "-f", "concat", "-safe", "0", "-i", vlist, "-f", "concat", "-safe", "0", "-i", alist,
                                    "-map", "0:v:0", "-map", "1:a:0", "-c:v", "copy", "-c:a", "aac", "-b:a", "192k", "-ar", "48000",
                                    "-ac", "2", "-movflags", "+faststart", final_output])
        finally:
            shutil.rmtree(work, ignore_errors=True)

    # ---------------------------------------------------- automatic sync check
    def _stream_durations(self, path):
        ffprobe = shutil.which("ffprobe") or shutil.which("ffprobe.exe")
        if not ffprobe:
            return None, None
        kwargs = {"creationflags": 0x08000000} if sys.platform == "win32" else {}
        r = subprocess.run([ffprobe, "-v", "error", "-show_entries", "stream=codec_type,duration", "-of", "json", path],
                           capture_output=True, text=True, encoding="utf-8", errors="ignore", **kwargs)
        v = a = None
        for st in json.loads(r.stdout or "{}").get("streams", []):
            try:
                d = float(st.get("duration"))
            except (TypeError, ValueError):
                continue
            if st.get("codec_type") == "video" and v is None:
                v = d
            elif st.get("codec_type") == "audio" and a is None:
                a = d
        return v, a

    def verify_merge_sync(self, final_output, file_list_count=0):
        """Checks the merged file in the background: sound length = picture length, and (when an .srt is
        saved next to it) that the voice lines up with the subtitles at the start and at the end."""
        def work():
            try:
                v, a = self._stream_durations(final_output)
                if v and a:
                    diff = abs(v - a)
                    ok = diff < 0.12
                    self.log_message(f"Sync check: picture {v:.3f}s, sound {a:.3f}s → difference {diff * 1000:.0f} ms "
                                     f"{'✅ in sync' if ok else '⚠️ lengths differ'} ({os.path.basename(final_output)})")
                srt = os.path.splitext(final_output)[0] + ".srt"
                for _ in range(40):      # the subtitles are written right after the merge
                    if os.path.exists(srt) or self.stop_flag:
                        break
                    time.sleep(1.5)
                if os.path.exists(srt):
                    res = self.check_voice_vs_subtitles(final_output, srt)
                    if res:
                        self.log_message(res)
            except Exception as e:
                self.log_message(f"Sync check skipped: {e}")
        threading.Thread(target=work, daemon=True).start()

    @staticmethod
    def _srt_cues(path):
        cues = []
        try:
            txt = open(path, "r", encoding="utf-8", errors="ignore").read()
        except OSError:
            return cues
        for m in re.finditer(r"(\d+):(\d+):(\d+)[,.](\d+)\s*-->\s*(\d+):(\d+):(\d+)[,.](\d+)", txt):
            g = [int(x) for x in m.groups()]
            st = g[0] * 3600 + g[1] * 60 + g[2] + g[3] / 1000.0
            en = g[4] * 3600 + g[5] * 60 + g[6] + g[7] / 1000.0
            if en > st:
                cues.append((st, en))
        return cues

    def check_voice_vs_subtitles(self, video_path, srt_path, window_sec=420):
        """Finds how far the voice is from the subtitles (best match of speech loudness vs. subtitle times)
        near the start and near the end. Equal small offsets = no drift."""
        cues = self._srt_cues(srt_path)
        if len(cues) < 20:
            return ""
        dur = self.get_media_duration(video_path)
        rate = 50  # loudness samples per second (20 ms)
        kwargs = {"creationflags": 0x08000000} if sys.platform == "win32" else {}

        # Decode the sound continuously from the beginning, the way video players do (seeking would hide drift)
        import array
        step = 8000 // rate
        full_env = []
        proc = subprocess.Popen(["ffmpeg", "-v", "error", "-i", video_path, "-map", "0:a:0", "-ac", "1", "-ar", "8000",
                                 "-af", "highpass=f=200,lowpass=f=3500", "-f", "s16le", "-"], stdout=subprocess.PIPE, **kwargs)
        chunk_bytes = step * 2 * 500
        rest = b""
        while True:
            data = proc.stdout.read(chunk_bytes)
            if not data:
                break
            data = rest + data
            usable = len(data) // (step * 2) * (step * 2)
            rest = data[usable:]
            pcm = array.array("h")
            pcm.frombytes(data[:usable])
            for k in range(0, len(pcm), step):
                seg = pcm[k:k + step:4]
                full_env.append(sum(map(abs, seg)) / max(1, len(seg)))
        proc.wait()

        def envelope(start, length):
            return full_env[int(start * rate):int((start + length) * rate)]

        def best_lag(start, length):
            env = envelope(start, length)
            if len(env) < rate * 30:
                return None
            srt_mask = [0.0] * len(env)
            for st, en in cues:
                a, b = int((st - start) * rate), int((en - start) * rate)
                for k in range(max(0, a), min(len(env), b)):
                    srt_mask[k] = 1.0
            idx = [k for k, m in enumerate(srt_mask) if m]
            if len(idx) < rate:
                return None
            mean = sum(env) / len(env)
            env = [x - mean for x in env]
            best, best_score = 0, None
            max_lag = int(2.5 * rate)
            n = len(env)
            for lag in range(-max_lag, max_lag + 1):
                score = sum(env[k + lag] for k in idx if 0 <= k + lag < n)
                if best_score is None or score > best_score:
                    best, best_score = lag, score
            return best / rate

        length = min(window_sec, dur / 2) if dur else window_sec
        start_lag = best_lag(0.0, length)
        end_lag = best_lag(max(0.0, dur - length), length) if dur > length * 1.5 else None
        if start_lag is None:
            return ""
        msg = f"Voice/subtitle check: voice is {start_lag * 1000:+.0f} ms from the subtitles at the start"
        if end_lag is not None:
            drift = end_lag - start_lag
            msg += f", {end_lag * 1000:+.0f} ms at the end → drift {drift * 1000:+.0f} ms "
            msg += "✅ voice stays with the subtitles" if abs(drift) <= 0.25 else "⚠️ the voice drifts from the subtitles (check the source episodes)"
        return msg

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
            # 1. Try exported browser cookies first (bypasses Cloudflare challenge immediately)
            chain.append(["--cookies", cookie_file])
        # 2. Try clean curl_cffi Chrome impersonation next
        chain.append([])
        # 3. Fall back to live browser cookie stores
        browsers = ["chrome", "edge", "firefox", "brave", "opera"]
        if sys.platform == "darwin":
            browsers.insert(0, "safari")
        chain += [["--cookies-from-browser", b] for b in browsers]
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

    @staticmethod
    def is_http_403(err):
        return bool(re.search(r"HTTP Error 403|403: Forbidden|status code 403", err or "", re.IGNORECASE))

    def shortmax_recover_from_error(self, err):
        """True when the failure was cookies/impersonation and the next attempt uses a different setup."""
        if "impersonate target" in err.lower() and getattr(self, "_sm_impersonate_ok", None):
            self._sm_impersonate_ok = False
            self.log_message("Shortmax: impersonation failed, retrying without it.")
            return True
        # A Cloudflare 403 means this browser's cookies don't carry a passed check: try the next browser
        # v1.9.2: Shortmax now answers a plain "HTTP Error 403: Forbidden" (no 'Cloudflare' word) — same meaning
        if self.SHORTMAX_COOKIE_ERR.search(err) or "cloudflare" in err.lower() or self.is_http_403(err):
            chain = self.shortmax_cookie_chain()
            idx = getattr(self, "_sm_cookie_idx", 0)
            if idx < len(chain) - 1:
                self._sm_cookie_idx = idx + 1
                nxt = " ".join(chain[idx + 1]) or "browser impersonation (no cookies)"
                self.log_message(f"Shortmax: cookie source failed ({' '.join(chain[idx])}). Trying: {nxt}")
                self.update_status(f"Shortmax: trying cookies from {nxt.replace('--cookies-from-browser ', '')}...", "orange")
                return True
        return False


    # =========================================================================
    # 🎵 TIKTOK ENGINE (v1.9.0): no-cookie first, H.264 preferred, safe merging
    # =========================================================================
    TIKTOK_LOGIN_ERR = re.compile(r"(log ?in|cookies|private|age|unavailable for|requires? authentication|status code 10216)", re.IGNORECASE)

    def tiktok_auth_chain(self):
        """Public videos need no cookies; login cookies are only a fallback (Chrome's can't be read on Windows)."""
        chain = [[]]
        cookie_file = os.path.join(self.base_dir, "tiktok_cookies.txt")
        if os.path.exists(cookie_file):
            chain.append(["--cookies", cookie_file])
        browsers = ["edge", "firefox", "chrome", "brave"]
        if sys.platform == "darwin":
            browsers.insert(0, "safari")
        chain += [["--cookies-from-browser", b] for b in browsers]
        return chain

    def tiktok_format_args(self):
        # H.264 + AAC plays everywhere (TikTok sometimes serves H.265 that Windows players can't open)
        return ["-S", "vcodec:h264,res,acodec:aac", "--merge-output-format", "mp4", "--no-playlist"]

    def download_tiktok_one(self, yt_dlp_path, url, file_name, accel_args, max_attempts=None):
        """Downloads one TikTok, walking the login chain only when TikTok asks for it. Returns (ok, error)."""
        chain = self.tiktok_auth_chain()
        idx = min(getattr(self, "_tt_auth_idx", 0), len(chain) - 1)
        attempts = max_attempts or (len(chain) + 1)
        err = ""
        for attempt in range(attempts):
            if self.stop_flag:
                return False, "User stopped process."
            cmd = [yt_dlp_path, *chain[idx], *self.tiktok_format_args(), *accel_args, "-o", file_name, url]
            succ, err = self.run_yt_dlp_with_progress(cmd)
            if succ and self.is_valid_video_file(file_name):
                self._tt_auth_idx = idx
                return True, ""
            if os.path.exists(file_name):
                try: os.remove(file_name)
                except: pass
            needs_login = bool(self.TIKTOK_LOGIN_ERR.search(err or "")) or bool(self.SHORTMAX_COOKIE_ERR.search(err or ""))
            if needs_login and idx < len(chain) - 1:
                idx += 1
                self.log_message(f"TikTok: trying login source {' '.join(chain[idx])}")
                continue
            time.sleep(1.5)
        return False, err

    def probe_media(self, path):
        """Video/audio facts for merging (ffprobe, or ffmpeg's banner as a fallback)."""
        info = {"video": False, "audio": False, "vcodec": "", "w": 0, "h": 0, "fps": 0.0, "acodec": "", "sr": 0, "ch": 0}
        ffprobe = shutil.which("ffprobe") or shutil.which("ffprobe.exe")
        kwargs = {"creationflags": 0x08000000} if sys.platform == "win32" else {}
        if ffprobe:
            try:
                res = subprocess.run([ffprobe, "-v", "error", "-show_streams", "-of", "json", path], capture_output=True,
                                     text=True, encoding="utf-8", errors="ignore", **kwargs)
                for st in json.loads(res.stdout or "{}").get("streams", []):
                    if st.get("codec_type") == "video" and not info["video"] and st.get("disposition", {}).get("attached_pic", 0) == 0:
                        num, _, den = (st.get("avg_frame_rate") or "0/1").partition("/")
                        info.update(video=True, vcodec=st.get("codec_name", ""), w=int(st.get("width", 0)), h=int(st.get("height", 0)),
                                    fps=round(float(num) / float(den or 1), 2) if float(den or 1) else 0.0)
                    elif st.get("codec_type") == "audio" and not info["audio"]:
                        info.update(audio=True, acodec=st.get("codec_name", ""), sr=int(st.get("sample_rate", 0) or 0), ch=int(st.get("channels", 0) or 0))
                return info
            except Exception:
                pass
        res = self.run_ffmpeg(["ffmpeg", "-hide_banner", "-i", path])
        txt = res.stderr or ""
        mv = re.search(r"Video: (\w+).*?(\d{2,5})x(\d{2,5})", txt)
        if mv:
            fps = re.search(r"(\d+(?:\.\d+)?) fps", txt)
            info.update(video=True, vcodec=mv.group(1), w=int(mv.group(2)), h=int(mv.group(3)), fps=float(fps.group(1)) if fps else 0.0)
        ma = re.search(r"Audio: (\w+), (\d+) Hz, (\w+)", txt)
        if ma:
            info.update(audio=True, acodec=ma.group(1), sr=int(ma.group(2)), ch=2 if "stereo" in ma.group(3) else 1)
        return info

    def merge_clips_uniform(self, files, final_output, status_prefix="Merging"):
        """
        Joins clips that may differ in size, codec, frame rate or audio (typical for TikTok).
        Matching clips are joined instantly; otherwise each is converted to one uniform format first.
        Returns (ok, message).
        """
        infos = [(f, self.probe_media(f)) for f in files]
        usable = [(f, i) for f, i in infos if i["video"]]
        skipped = [os.path.basename(f) for f, i in infos if not i["video"]]
        if skipped:
            self.log_message(f"Merge: skipped {len(skipped)} file(s) without video (photo/audio posts): {', '.join(skipped)}")
        if not usable:
            return False, "None of the downloads contain video."
        first = usable[0][1]
        same = all(i["vcodec"] == "h264" and (i["w"], i["h"]) == (first["w"], first["h"]) and abs(i["fps"] - first["fps"]) < 0.05
                   and i["audio"] and i["acodec"] == "aac" and i["sr"] == first["sr"] and i["ch"] == first["ch"] for _, i in usable)
        work_files = [f for f, _ in usable]
        tmp_files = []
        if not same:
            portrait = sum(1 for _, i in usable if i["h"] >= i["w"]) >= len(usable) / 2
            W, H = (1080, 1920) if portrait else (1920, 1080)
            vf = (f"[0:v]split[a][b];[a]scale={W}:{H}:force_original_aspect_ratio=increase,crop={W}:{H},boxblur=20:2[bg];"
                  f"[b]scale={W}:{H}:force_original_aspect_ratio=decrease[fg];[bg][fg]overlay=(W-w)/2:(H-h)/2,fps=30,format=yuv420p,setsar=1[v]")
            work_files = []
            for k, (f, info) in enumerate(usable, 1):
                if self.stop_flag:
                    return False, "Stopped."
                self.update_status(f"{status_prefix}: making clip {k}/{len(usable)} uniform ({W}×{H})...", "#f59e0b")
                out = f + ".uniform.mp4"
                cmd = ["ffmpeg", "-y", "-i", f]
                if not info["audio"]:
                    cmd += ["-f", "lavfi", "-i", "anullsrc=r=48000:cl=stereo"]
                cmd += ["-filter_complex", vf, "-map", "[v]", "-map", "0:a:0" if info["audio"] else "1:a:0",
                        "-c:v", "libx264", "-preset", "veryfast", "-crf", "20",
                        "-c:a", "aac", "-ar", "48000", "-ac", "2", "-b:a", "160k", "-shortest", "-movflags", "+faststart", out]
                res = self.run_ffmpeg(cmd)
                if res.returncode != 0 or not os.path.exists(out):
                    self.log_message(f"Merge: could not convert {os.path.basename(f)}:\n{(res.stderr or '')[-800:]}")
                    continue
                work_files.append(out)
                tmp_files.append(out)
            if not work_files:
                return False, "Could not convert any clip for merging."
        self.update_status(f"{status_prefix}: joining {len(work_files)} clips...", "#f59e0b")
        res = self.concat_video_files_synced(work_files, final_output, normalize_first=False, status_prefix=status_prefix)
        for t in tmp_files:
            try: os.remove(t)
            except: pass
        if res.returncode != 0 or not os.path.exists(final_output):
            return False, (res.stderr or "")[-800:]
        self.record_last_output(final_output)
        return True, f"Merged {len(work_files)} clip(s)" + (" (converted to a uniform format)" if not same else "") + \
            (f", skipped {len(skipped)} without video" if skipped else "")


    # =========================================================================
    # ⚙️ v1.9.0 — SETTINGS (SAVED), THEMES, NOTIFICATIONS, QUEUE, LIBRARY, HEALTH
    # =========================================================================
    SETTINGS_DEFAULTS = {
        "theme": "auto", "max_quality": "best", "speed_limit": "", "notify": True,
        "queue_end_action": "notify", "schedule_on": False, "schedule_from": "01:00", "schedule_to": "07:00",
        "turbo": True, "sync_lock": True, "auto_sub": True, "narto_workers": 3, "output_dir": "",
        "fme_monitor": "Small", "info_mode": False, "opensubtitles_key": "",
    }

    def load_settings(self):
        self.settings_path = os.path.join(self.base_dir, "downloader_settings.json")
        self.settings = dict(self.SETTINGS_DEFAULTS)
        try:
            with open(self.settings_path, "r", encoding="utf-8") as f:
                saved = json.load(f)
            self.settings.update({k: v for k, v in saved.items() if k in self.SETTINGS_DEFAULTS})
        except Exception:
            pass

    def save_settings(self):
        try:
            for key, var in (("turbo", getattr(self, "turbo_var", None)), ("sync_lock", getattr(self, "sync_lock_var", None)),
                             ("auto_sub", getattr(self, "auto_sub_var", None))):
                if var is not None:
                    self.settings[key] = bool(var.get())
            if hasattr(self, "narto_claude_parallel_var"):
                self.settings["narto_workers"] = int(self.narto_claude_parallel_var.get())
            with open(self.settings_path, "w", encoding="utf-8") as f:
                json.dump(self.settings, f, indent=2)
        except Exception:
            pass

    def apply_saved_settings(self):
        """Puts saved choices back into the dashboard after it is built."""
        self.turbo_var.set(self.settings["turbo"])
        self.sync_lock_var.set(self.settings["sync_lock"])
        self.auto_sub_var.set(self.settings["auto_sub"])
        try:
            self.narto_claude_parallel_var.set(int(self.settings["narto_workers"]))
        except Exception:
            pass
        out_dir = self.settings.get("output_dir")
        if out_dir and os.path.isdir(out_dir):
            self.output_base = out_dir
            self.last_output_folder = out_dir
        for var in (self.turbo_var, self.sync_lock_var, self.auto_sub_var, self.narto_claude_parallel_var):
            var.trace_add("write", lambda *_: self.save_settings())

    # ---------------------------------------------------------------- themes
    THEME_BG_MAP = {
        "#0b0f19": "#eef2f7", "#131b2e": "#ffffff", "#111a2c": "#f6f8fb", "#1e293b": "#e2e8f0", "#0f172a": "#dbe3ee",
        "#090d16": "#e2e8f0", "#1f2937": "#dfe6ef", "#334155": "#c3cddb", "#2e384d": "#c3cddb", "#0e1422": "#f3f6fa",
    }
    THEME_FG_MAP = {
        "#f8fafc": "#0f172a", "#f1f5f9": "#0f172a", "#ffffff": "#0f172a", "#e2e8f0": "#1e293b", "#cbd5e1": "#334155",
        "#94a3b8": "#526075", "#64748b": "#526075", "#38bdf8": "#0369a1", "#10b981": "#047857", "#f59e0b": "#b45309",
        "#fbbf24": "#b45309", "#a855f7": "#7e22ce", "#f43f5e": "#be123c", "#475569": "#64748b",
    }
    KEEP_DARK = {"#111827", "#070a12", "#0d1322", "#000000"}     # header bar, monitors and editing timelines

    @staticmethod
    def os_prefers_dark() -> bool:
        try:
            if sys.platform == "win32":
                import winreg
                key = winreg.OpenKey(winreg.HKEY_CURRENT_USER, r"Software\Microsoft\Windows\CurrentVersion\Themes\Personalize")
                return winreg.QueryValueEx(key, "AppsUseLightTheme")[0] == 0
            if sys.platform == "darwin":
                r = subprocess.run(["defaults", "read", "-g", "AppleInterfaceStyle"], capture_output=True, text=True, timeout=5)
                return "dark" in r.stdout.lower()
            r = subprocess.run(["gsettings", "get", "org.gnome.desktop.interface", "color-scheme"], capture_output=True, text=True, timeout=5)
            if r.returncode == 0:
                return "dark" in r.stdout.lower()
        except Exception:
            pass
        return True

    def resolved_theme(self) -> str:
        choice = self.settings.get("theme", "auto")
        return ("dark" if self.os_prefers_dark() else "light") if choice == "auto" else choice

    def theme_fg(self, color: str) -> str:
        if getattr(self, "_theme_now", "dark") == "light":
            return self.THEME_FG_MAP.get(str(color).lower(), color)
        return color

    def set_theme_choice(self, choice: str):
        self.settings["theme"] = choice
        self.save_settings()
        self.apply_ui_theme(force=True)
        if hasattr(self, "theme_pill"):
            self.theme_pill.config(text={"auto": "🌓", "dark": "🌙", "light": "☀️"}[choice])
        if hasattr(self, "theme_choice_var"):
            self.theme_choice_var.set(choice)

    def cycle_theme(self):
        order = ["auto", "dark", "light"]
        self.set_theme_choice(order[(order.index(self.settings.get("theme", "auto")) + 1) % 3])


    # =========================================================================
    # ℹ️ INFO MODE (v1.9.2): turn it on with the ℹ️ button, then point at anything
    # =========================================================================
    HELP_EXACT = {
        "⬅️ Back": ("Back", "Returns to the page you were on before."),
        "🏠 Home": ("Home / Dashboard", "The main downloader: paste a link in one of the site tabs and press its Start / Download button."),
        "📋 Queue": ("Download Queue", "Line up many downloads (series, TikTok lists, torrents). They run one after another, survive a restart, "
                                     "resume where they stopped, can run only at night, and can notify you or shut the PC down when finished."),
        "📚 Library": ("Library", "All your finished videos as posters, like a streaming app. Play them in Nader Player (voice-sync fix, "
                                 "Arabic subtitles), share them (AirDrop, Bluetooth, Blip) or delete them."),
        "🔍 Find": ("Find by Image", "Upload or paste a picture (poster, TikTok screenshot). The app reads the name, searches Narto, "
                                    "Dailymotion and YouTube, and shows posters that look the same plus titles with the same name — "
                                    "click one to open its play page in your browser."),
        "🎙️ Sync": ("Voice & Subtitle Sync Studio", "Fixes a finished movie whose sound or subtitles are early/late: one exact shift, "
                                                    "automatic speed + offset matching, or repair of drift that starts in the middle."),
        "🎛️ Edit": ("Full Manual Edit", "3-track editor: video, voice and background music are separated so you can slide, cut, trim, "
                                       "copy or mute each one alone, then save the full movie in the same HD quality."),
        "🌙 Narto 5": ("Narto 5-Movie Overnight Queue", "The original overnight queue for up to 5 Narto series, downloaded one by one."),
        "✂️ Trim": ("Trim & Crop HD", "Cut parts out of one or many videos, crop black bars or edges, and join the pieces in the order you choose."),
        "⚙️ Settings": ("Settings & Health", "Theme, maximum quality, speed limit, notifications, save folder, and the status of every engine "
                                            "(yt-dlp, FFmpeg, aria2c). Includes one-click Update yt-dlp."),
        "🌓": ("Theme: Auto", "Follows your computer's dark/light setting. Click to switch to Dark, again for Light."),
        "🌙": ("Theme: Dark", "Dark colours. Click to switch to Light."),
        "☀️": ("Theme: Light", "Light colours. Click to go back to Auto (follow the computer)."),
        "ℹ️ Info": ("Info mode", "While this is ON, pointing at any button, tab or box shows what it does. Click it again to turn the info off."),
        "Shortmax": ("Shortmax tab", "Downloads a Shortmax series episode by episode and merges them. If the site shows its bot check, press "
                                     "'1. Verify Bot Check', pass it in your browser, then '2. Start Shortmax'. A shortmax_cookies.txt next to the app is used first."),
        "Narto (Original)": ("Narto (Original) tab", "The original, proven narto-drama.com downloader: one episode at a time, stream tokens "
                                                     "refreshed automatically, subtitles merged into one .srt."),
        "Narto ⚡ Claude Version": ("Narto ⚡ Claude Version tab", "Faster narto-drama.com downloader: several episodes at the same time "
                                                                 "(choose how many), same token healing and subtitles, resumes if stopped."),
        "Dailymotion": ("Dailymotion tab", "Downloads a Dailymotion video in the best quality available."),
        "TikTok": ("TikTok tab", "One TikTok video, or a whole list from 'tiktok link graber.txt' merged into one video. "
                                 "Videos of different sizes are made uniform so the merge never breaks."),
        "Direct M3U8/MP4": ("Direct link tab", "Any direct video link (.m3u8 stream or .mp4 file) — e.g. one you copied from your browser's network tab."),
        "Torrent / Magnet": ("Torrent tab", "Downloads a magnet link or .torrent file with the fast aria2c engine. Optional seeding after download."),
    }
    HELP_KEYS = [
        ("Verify Bot Check", "Verify bot check", "Opens the site in your browser. Pass the check there (play an episode), close the browser, then press Start."),
        ("Start Shortmax", "Start Shortmax", "Downloads every episode from the Start Ep (up to Total Eps if set), sync-locks each one and merges them into one movie."),
        ("Download Narto", "Download Narto (Original)", "Starts the original narto-drama.com downloader with the Start / Total episodes below."),
        ("Turbo Download (Claude", "Turbo download (Claude version)", "Downloads several Narto episodes at once (see 'Episodes at once'), then merges them with locked sound."),
        ("Episodes at once", "Episodes at once", "How many Narto episodes download at the same time. 3 is a good balance; more can be faster on a strong connection."),
        ("Dailymotion (Max", "Download Dailymotion", "Downloads the Dailymotion link in the best quality."),
        ("Single TikTok", "Download single TikTok", "Downloads the one TikTok link (H.264 so it plays everywhere)."),
        ("Bulk TikTok", "Bulk TikTok", "Reads 'tiktok link graber.txt' (next to the app, on the Desktop/Dramadownload or in Downloads), downloads every link and merges them."),
        ("Single Video", "Download direct video", "Downloads the direct .m3u8 / .mp4 link."),
        ("Torrent / Magnet", "Download torrent", "Starts the torrent / magnet download with aria2c (many connections, DHT and extra trackers)."),
        ("Keep Seeding", "Keep seeding", "After the download, keeps sharing it with others for up to 30 minutes or until you uploaded as much as you downloaded."),
        ("Paste", "Paste", "Puts the link from your clipboard into the box."),
        ("History", "History", "Your last links for this site — pick one to use it again."),
        ("Clear History", "Clear history", "Forgets the saved links of this site."),
        ("Browse", "Browse", "Choose a file from your computer."),
        ("Turbo Accelerator", "Turbo Accelerator", "Uses many connections at once (and aria2c when possible) for much faster downloads. Turn off on a weak connection."),
        ("Sync-Lock", "Sync-Lock (keeps the voice in sync)", "Every episode's sound is locked to its picture and the merge rebuilds the sound sample-exactly, "
                                                           "so the voice never drifts away from the video. An automatic check is written to the log after each merge."),
        ("Auto-Save Merged .SRT", "Save subtitles", "Saves the Narto subtitles of all episodes as one .srt next to the movie, shifted to the right times."),
        ("Add to Queue", "Add to Queue", "Puts the link of the open tab (with Start / Total episodes) into the Download Queue instead of starting now."),
        ("Add Current Dashboard Link", "Add dashboard link", "Copies the link from the dashboard tab that is open into the queue."),
        ("Start Queue", "Start Queue", "Downloads every pending item, one by one."),
        ("Pause After Current", "Pause queue", "Lets the current download finish, then stops. Press Start Queue to continue."),
        ("Retry", "Retry", "Marks the selected (failed) item as pending again."),
        ("Remove", "Remove", "Removes the selected item from the queue."),
        ("Clear Finished", "Clear finished", "Removes all finished items from the list."),
        ("Only download between", "Schedule", "Downloads only between these hours (e.g. at night). Outside them the queue waits."),
        ("Stop Download", "Stop", "Stops the running download. Finished episodes are kept and merged."),
        ("Select Folder to Merge", "Merge a folder", "Joins all videos in a folder you choose into one movie (with locked sound)."),
        ("Stitch Multiple Videos", "Stitch videos", "Pick several videos and join them in the order you choose."),
        ("Open Last File", "Open last file", "Plays the last finished video."),
        ("Open Last Local Folder", "Open folder", "Opens the folder of the last finished video."),
        ("Open Error Log", "Error log", "Shows the log with every step and error (useful when something fails)."),
        ("Voice & Subtitle Sync Studio", "Sync Studio", "Opens the studio that fixes sound/subtitle timing in a finished movie."),
        ("Full Manual Edit", "Full Manual Edit", "Opens the 3-track editor (video, voice, music)."),
        ("Overnight Queue", "Narto overnight queue", "Opens the 5-series Narto overnight queue."),
        ("Trim & Crop", "Trim & Crop", "Opens the trim, crop and join studio."),
        ("Pop-Out", "Pop-out monitor", "Opens the preview in its own window — drag its edges to make it as big as you like, F11 for full screen."),
        ("Monitor size", "Monitor size", "Makes the preview inside the editor smaller or bigger."),
        ("Load & Separate", "Load & separate", "Loads the video and splits it into video, voice and background music tracks."),
        ("Separate Voice & Background", "Separate tracks", "Uses AI to split voice and music so each can be moved alone (slower, best quality)."),
        ("Fast Mode", "Fast mode", "Keeps the full sound on the voice track — loads instantly, no separation."),
        ("Play (Space)", "Play / Pause", "Plays or pauses the preview (Space key)."),
        ("Lock Hand Tool", "Hand tool lock", "Keeps the hand tool on so you can drag tracks without holding Shift."),
        ("Split at Playhead", "Split", "Cuts the selected track at the red playhead line (S key)."),
        ("Trim Start to Playhead", "Trim start", "Removes the part of the selected clip before the playhead."),
        ("Trim End to Playhead", "Trim end", "Removes the part of the selected clip after the playhead."),
        ("Copy", "Copy", "Copies the selected clip."),
        ("Paste Here", "Paste here", "Pastes the copied clip at the playhead."),
        ("Delete (Del)", "Delete clip", "Deletes the selected clip (Del key)."),
        ("Undo", "Undo", "Undoes the last edit (Ctrl+Z)."),
        ("Reset Tracks", "Reset tracks", "Puts all tracks back as they were after loading."),
        ("Shift Selected Clip by Difference", "Quick sync shift", "Moves the selected track by the difference between when a word is heard and when it should be heard."),
        ("Speed-Stretch", "Speed-stretch", "Slightly speeds up / slows down the clip so it ends exactly where it should (fixes slow drift)."),
        ("Save Full Movie", "Save movie", "Saves the edited movie in the same Full HD quality (no re-compression of the picture)."),
        ("Check 15s", "15 s preview", "Plays 15 seconds from the playhead with the edited sound, to check before saving."),
        ("Sync & Save FULL Movie", "Sync & save", "Applies the timing fix to the whole movie and saves a new copy."),
        ("Preview 20s", "20 s test clip", "Makes a 20-second test with the fix so you can check it first."),
        ("Auto-Sync Voice with Subtitles", "Auto-sync voice", "Listens to the dialogue and matches it to the subtitles automatically (speed + offset)."),
        ("Auto-Repair Mid-Video", "Repair drift", "Fixes sound that is fine at the start but slowly goes out of sync later."),
        ("Constant Flat Shift", "Flat shift", "Use when the sound is off by the same amount everywhere."),
        ("Add Videos", "Add videos", "Adds videos to the pool (you can also drag & drop them)."),
        ("Add Trim Segment", "Add segment", "Adds the selected part (with crop) to the timeline below."),
        ("Export HD Video", "Export", "Joins all timeline segments into one HD video."),
        ("Set Current Frame as Trim Start", "Set start", "Uses the frame you see as the start of the cut."),
        ("Set Current Frame as Trim End", "Set end", "Uses the frame you see as the end of the cut."),
        ("Play Any Video", "Play any video", "Opens any video file from your computer in Nader Player."),
        ("Resume", "Resume", "Continues the video where you stopped last time."),
        ("Play", "Play", "Opens the video in Nader Player: voice-sync fix, Arabic subtitles, auto-sync, speed, voice boost."),
        ("Share", "Share", "Send the video with AirDrop (Mac), Bluetooth or Blip, copy it, or show it in its folder."),
        ("🗑", "Delete", "Deletes the video from your computer (asks 'Are you sure?' first)."),
        ("Arabic", "Arabic subtitles", "Loads Arabic subtitles: an existing .ar.srt, OpenSubtitles (if you added a key) or a translation of the video's subtitles."),
        ("Auto-sync to voice", "Auto-sync subtitles", "Listens to the dialogue around the current scene and moves the subtitles to match the voice."),
        ("Load .srt", "Load subtitles", "Choose a subtitle file to show on the video."),
        ("Find online", "Find subtitles online", "Searches OpenSubtitles.com (needs a free API key, asked once)."),
        ("Voice boost", "Voice boost", "Makes quiet dialogue louder and loud scenes softer — great at night."),
        ("Full Screen", "Full screen", "Switches the player to full screen."),
        ("Snapshot", "Snapshot", "Saves a picture of the current frame."),
        ("Update yt-dlp", "Update yt-dlp", "Updates the download engine and its browser-impersonation part. Fixes most 'it stopped working' problems."),
        ("Check Again", "Check engines", "Checks again which engines are installed and working."),
        ("Change Folder", "Save folder", "Choose where finished videos are saved."),
        ("Choose Image", "Choose image", "Pick a picture from your computer to search with."),
        ("Paste Image", "Paste image", "Uses the picture you copied (e.g. a screenshot) to search."),
        ("Search Everywhere", "Search", "Searches every ticked site for the name and compares their posters with your picture."),
        ("▶ Open", "Open", "Opens the play page of this result in your browser."),
        ("Notify me", "Notifications", "Shows a desktop notification when a download finishes."),
        ("Frame", "Step one frame", "Moves exactly one video frame back or forward — for finding the perfect cut point."),
        ("Auto — follow", "Theme: Auto", "Follows your computer's dark / light setting."),
        ("Optional: Add 2nd Checkpoint", "Second checkpoint", "A second matching point later in the movie, so the fix can also correct sound that slowly drifts."),
        ("Open Last", "Open last result", "Plays the last movie this studio saved."),
        ("Open Local Folder", "Open folder", "Opens the folder where this studio saved its result."),
        ("Delete", "Delete", "Deletes the selected clip / item."),
        ("Move Clip Up", "Move up", "Moves the selected segment earlier in the final video."),
        ("Move Clip Down", "Move down", "Moves the selected segment later in the final video."),
        ("Export Full HD", "Export", "Joins all segments into one Full HD video."),
        ("Video Alone", "Select video track", "Selects the picture track — the slide / cut buttons then act on the video only."),
        ("Voice Alone", "Select voice track", "Selects the voice track — move or cut the dialogue without touching picture or music."),
        ("Music Alone", "Select music track", "Selects the background-music track — move, cut or mute the music alone."),
        ("File…", "Choose file", "Pick a TikTok link list (.txt) or a .torrent file for the queue."),
        ("Add All Pool Videos", "Add all", "Adds every video of the pool to the timeline as whole segments."),
        ("Refresh Crop Frame", "Refresh", "Redraws the crop preview with the current values."),
        ("Progressive Speed-Lock", "Progressive speed-lock", "Best for drift: gently changes the sound speed so it matches at both checkpoints."),
        ("Stop / Cancel", "Stop", "Stops the job that is running."),
        ("Stop Queue", "Stop queue", "Stops the overnight queue after stopping the running movie."),
        ("Stop Task", "Stop", "Stops the editing job that is running."),
        ("Dark", "Theme: Dark", "Dark colours."),
        ("Light", "Theme: Light", "Light colours."),
        ("🔄", "Refresh", "Reloads the list."),
        ("⬆️", "Move up", "Moves the selected queue item up (it will download sooner)."),
        ("⬇️", "Move down", "Moves the selected queue item down."),
    ]

    def setup_info_mode(self, nav_parent):
        self.info_pill = self.make_3d_pill(nav_parent, "ℹ️ Info", self.toggle_info_mode)
        self.info_pill.pack(side="left", padx=(8, 2), pady=8)
        self._info_tip = None
        self._info_job = None
        self._info_target = None
        self.root.bind_all("<Enter>", self._info_enter, add="+")
        self.root.bind_all("<Leave>", self._info_leave, add="+")
        self.root.bind_all("<Motion>", self._info_motion, add="+")
        self.root.bind_all("<ButtonPress>", lambda e: self._info_hide(), add="+")
        if self.settings.get("info_mode"):
            self.set_pill_kind(self.info_pill, "blue")

    def toggle_info_mode(self):
        on = not self.settings.get("info_mode", False)
        self.settings["info_mode"] = on
        self.save_settings()
        self.set_pill_kind(self.info_pill, "blue" if on else "dark")
        self._info_hide()
        self.update_status("ℹ️ Info is ON — point at any button, tab or box to see what it does." if on else "Info is off.",
                           "blue" if on else "orange")

    def _help_for(self, w, x_root=None, y_root=None):
        h = getattr(w, "_help", None)
        if h:
            return h
        text = ""
        try:
            if isinstance(w, ttk.Notebook) and x_root is not None:
                idx = w.index(f"@{x_root - w.winfo_rootx()},{y_root - w.winfo_rooty()}")
                text = w.tab(idx, "text")
            else:
                text = str(w.cget("text"))
        except Exception:
            return None
        t = text.strip()
        if not t:
            return None
        if t in self.HELP_EXACT:
            return self.HELP_EXACT[t]
        if re.fullmatch(r"[⏩⏪▶◀\s]*[+\-−]?\d+(\.\d+)?s", t):
            return ("Jump / nudge " + re.sub(r"[⏩⏪▶◀\s]", "", t),
                    "Moves the playhead by this many seconds. In 'Slide Selected' it moves only the selected track (video, voice or music) "
                    "— use it to fix sound that is early or late.")
        for key, title, body in self.HELP_KEYS:
            if key.lower() in t.lower():
                return title, body
        return None

    def _info_enter(self, e):
        if not self.settings.get("info_mode"):
            return
        self._info_schedule(e.widget, e.x_root, e.y_root)

    def _info_motion(self, e):
        if not self.settings.get("info_mode"):
            return
        if isinstance(e.widget, ttk.Notebook):
            h = self._help_for(e.widget, e.x_root, e.y_root)
            if h != getattr(self, "_info_shown", None):
                self._info_hide()
                self._info_schedule(e.widget, e.x_root, e.y_root)
        elif self._info_tip is not None and e.widget is self._info_target:
            self._info_tip.geometry(f"+{e.x_root + 16}+{e.y_root + 20}")

    def _info_schedule(self, w, x, y):
        if not isinstance(w, tk.Misc) or w is self._info_tip:
            return
        if self._info_job:
            self.root.after_cancel(self._info_job)
        self._info_target = w
        self._info_job = self.root.after(300, lambda: self._info_show(w, x, y))

    def _info_leave(self, e):
        if e.widget is self._info_target:
            self._info_hide()

    def _info_hide(self):
        if getattr(self, "_info_job", None):
            self.root.after_cancel(self._info_job)
            self._info_job = None
        if getattr(self, "_info_tip", None) is not None:
            try: self._info_tip.destroy()
            except Exception: pass
        self._info_tip = None
        self._info_shown = None

    def _info_show(self, w, x, y):
        self._info_job = None
        if not self.settings.get("info_mode"):
            return
        try:
            h = self._help_for(w, x, y)
        except Exception:
            h = None
        if not h:
            return
        self._info_hide()
        light = getattr(self, "_theme_now", "dark") == "light"
        bg, fg, acc = ("#ffffff", "#0f172a", "#0369a1") if light else ("#111827", "#e2e8f0", "#38bdf8")
        tip = tk.Toplevel(self.root)
        tip.overrideredirect(True)
        try: tip.attributes("-topmost", True)
        except Exception: pass
        box = tk.Frame(tip, bg=bg, highlightthickness=1, highlightbackground=acc)
        box.pack()
        tk.Label(box, text="ℹ️  " + h[0], bg=bg, fg=acc, font=("Arial", 10, "bold"), anchor="w", justify="left").pack(fill="x", padx=10, pady=(7, 2))
        tk.Label(box, text=h[1], bg=bg, fg=fg, font=("Arial", 9), wraplength=360, justify="left", anchor="w").pack(fill="x", padx=10, pady=(0, 8))
        tip.update_idletasks()
        sx = min(x + 16, self.root.winfo_screenwidth() - tip.winfo_reqwidth() - 8)
        sy = y + 20 if y + 20 + tip.winfo_reqheight() < self.root.winfo_screenheight() else y - tip.winfo_reqheight() - 12
        tip.geometry(f"+{sx}+{sy}")
        self._info_tip = tip
        self._info_shown = h

    def attach_field_help(self):
        """Help for boxes that have no text of their own."""
        fields = [
            ("url_entry1", ("Shortmax link", "Paste a Shortmax watch link here (any episode of the series).")),
            ("url_entry2", ("Narto link", "Paste a narto-drama.com watch link (any episode of the series).")),
            ("url_entry7", ("Narto link (Claude version)", "Paste a narto-drama.com watch link; several episodes download at once.")),
            ("url_entry5", ("Dailymotion link", "Paste a Dailymotion video link.")),
            ("url_entry4", ("TikTok link", "Paste a TikTok video link.")),
            ("url_entry3", ("Direct link", "Paste a direct .m3u8 or .mp4 link.")),
            ("url_entry6", ("Magnet / torrent", "Paste a magnet link, a .torrent URL, or press Browse for a .torrent file.")),
            ("start_entry", ("Start episode", "The first episode to download (1 = from the beginning).")),
            ("total_entry", ("Total episodes", "Stop after this episode number. Leave empty to download until the last episode.")),
            ("lib_search", ("Search", "Type part of a title to filter your library.")),
            ("find_title", ("Name to search", "The name read from your picture. Fix or shorten it if needed, then press Enter.")),
            ("q_url_entry", ("Queue link", "Link (or file) to add to the queue — choose the site on the left first.")),
        ]
        for attr, h in fields:
            w = getattr(self, attr, None)
            if w is not None:
                try: w._help = h
                except Exception: pass

    def _watch_os_theme(self):
        if self.settings.get("theme") == "auto":
            self.apply_ui_theme()
        self.root.after(20000, self._watch_os_theme)

    def apply_ui_theme(self, force=False):
        name = self.resolved_theme()
        if not force and name == getattr(self, "_theme_now", "dark"):
            return
        self._theme_now = name
        light = name == "light"
        style = ttk.Style(self.root)
        P = {"bg": "#eef2f7" if light else "#0b0f19", "card": "#ffffff" if light else "#131b2e",
             "panel": "#f6f8fb" if light else "#111a2c", "field": "#ffffff" if light else "#1e293b",
             "text": "#0f172a" if light else "#f1f5f9", "muted": "#526075" if light else "#94a3b8",
             "accent": "#0369a1" if light else "#38bdf8", "border": "#cdd6e3" if light else "#24324d",
             "hi": "#ffffff" if light else "#2c3b5b", "lo": "#aeb9cb" if light else "#04060b", "btnbg": "#f3f6fa" if light else "#0e1422"}
        style.configure(".", background=P["bg"], foreground=P["text"])
        style.configure("TFrame", background=P["bg"])
        style.configure("Card.TFrame", background=P["card"])
        style.configure("TLabel", background=P["bg"], foreground=P["text"])
        style.configure("TCheckbutton", background=P["bg"], foreground=P["text"])
        style.map("TCheckbutton", background=[("active", P["bg"])])
        style.configure("TRadiobutton", background=P["card"], foreground=P["text"])
        style.map("TRadiobutton", background=[("active", P["card"])])
        style.configure("TButton", foreground=P["text"])
        style.configure("TEntry", fieldbackground=P["field"], foreground=P["text"], insertcolor=P["text"])
        style.configure("TCombobox", fieldbackground=P["field"], background=P["field"], foreground=P["text"])
        style.map("TCombobox", fieldbackground=[("readonly", P["field"])], foreground=[("readonly", P["text"])])
        style.configure("TSpinbox", fieldbackground=P["field"], foreground=P["text"], background=P["field"])
        style.map("TSpinbox", fieldbackground=[("readonly", P["field"])], foreground=[("readonly", P["text"])])
        style.configure("TLabelframe", background=P["card"], bordercolor=P["border"], lightcolor=P["hi"], darkcolor=P["lo"])
        style.configure("TLabelframe.Label", background=P["card"], foreground=P["accent"])
        style.configure("Panel.TFrame", background=P["panel"])
        style.configure("Panel.TLabel", background=P["panel"], foreground=P["text"])
        style.configure("Muted.Panel.TLabel", background=P["panel"], foreground=P["muted"])
        style.configure("Title.Panel.TLabel", background=P["panel"], foreground=P["text"])
        style.configure("Panel.TLabelframe", background=P["panel"], bordercolor=P["border"], lightcolor=P["hi"], darkcolor=P["lo"])
        style.configure("Panel.TLabelframe.Label", background=P["panel"], foreground=P["accent"])
        for st, bgk in (("Card.TCheckbutton", "card"), ("Card.TRadiobutton", "card"), ("Panel.TCheckbutton", "panel"), ("Panel.TRadiobutton", "panel")):
            style.configure(st, background=P[bgk], foreground=P["text"])
            style.map(st, background=[("active", P[bgk])])
        style.configure("TNotebook", background=P["bg"], bordercolor=P["border"], lightcolor=P["hi"], darkcolor=P["lo"])
        style.configure("TNotebook.Tab", foreground="#334155" if light else "#94a3b8", background=P["bg"])
        style.map("TNotebook.Tab", foreground=[("selected", "#ffffff"), ("active", "#0f172a" if light else "#e2e8f0")])
        style.configure("Treeview", background=P["field"], fieldbackground=P["field"], foreground=P["text"], rowheight=24,
                        bordercolor=P["border"])
        style.map("Treeview", background=[("selected", "#2563eb")], foreground=[("selected", "#ffffff")])
        style.configure("Treeview.Heading", background=P["card"], foreground=P["text"], font=("Arial", 9, "bold"))
        self._retint_3d_images(light, P)
        self.root.configure(bg=P["bg"])
        self._remap_tree(self.root, light)
        if hasattr(self, "status_label"):
            self.status_label.config(fg=self.theme_fg(self.status_label.cget("fg")) if light else self.status_label.cget("fg"))

    def _copy_into(self, img, new):
        img.blank()
        img.tk.call(img, "copy", new)

    def _retint_3d_images(self, light, P):
        imgs = getattr(self, "_img3d", None)
        if not imgs:
            return
        R, BG = self.root, P["btnbg"]
        plain = (("#ffffff", "#dfe6ef", "#b9c4d4", "#ffffff", "#d4e2fb", "#cfd8e5", "#eef2f7") if light else
                 ("#334155", "#1e293b", "#475569", "#3f5270", "#26344d", "#1e293b", "#334155"))
        dis = ("#eef1f5", "#e3e8ef", "#d7dee8") if light else ("#141b2b", "#101624", "#1e293b")
        sets = {"plain": plain, "accent": ("#3b82f6", "#1d4ed8", "#60a5fa", "#60a5fa", "#2563eb", "#1d4ed8", "#3b82f6"),
                "danger": ("#f43f5e", "#be123c", "#fb7185", "#fb7185", "#e11d48", "#be123c", "#f43f5e"),
                "success": ("#10b981", "#047857", "#34d399", "#34d399", "#059669", "#047857", "#10b981")}
        for key, (top, bot, edge, ht, hb, pt, pb) in sets.items():
            d = imgs.get(key)
            if not d:
                continue
            self._copy_into(d["n"], render_glossy(R, 22, 24, top, bot, edge, BG, radius=6))
            self._copy_into(d["a"], render_glossy(R, 22, 24, ht, hb, edge, BG, radius=6))
            self._copy_into(d["p"], render_glossy(R, 22, 24, pt, pb, edge, BG, radius=6, pressed=True))
            self._copy_into(d["d"], render_glossy(R, 22, 24, dis[0], dis[1], dis[2], BG, radius=6, flat=True))
        if "tabs" in imgs:
            tn, ta, ts = imgs["tabs"]
            tab_bg = P["bg"]
            self._copy_into(tn, render_glossy(R, 24, 30, *(("#ffffff", "#e4eaf2", "#c9d3e1") if light else ("#1e293b", "#111827", "#334155")), tab_bg, radius=9))
            self._copy_into(ta, render_glossy(R, 24, 30, *(("#ffffff", "#dbe6f5", "#93c5fd") if light else ("#2b3a55", "#172033", "#475569")), tab_bg, radius=9))
            self._copy_into(ts, render_glossy(R, 24, 30, "#3b82f6", "#1e40af", "#93c5fd", tab_bg, radius=9))
        if "progress" in imgs:
            tr, _pb = imgs["progress"]
            self._copy_into(tr, render_glossy(R, 24, 18, *(("#d5dde8", "#eef2f7", "#c3cddb") if light else ("#05070d", "#111827", "#1e293b")),
                                              P["card"] if light else "#0e1422", radius=8, pressed=True, shadow=0))
        off = ("#ffffff", "#e6ebf2", "#94a3b8") if light else ("#1e293b", "#0f172a", "#475569")
        for suffix, bg in (("", P["bg"]), ("Card.", P["card"]), ("Panel.", P["panel"])):
            group = imgs.get(f"check{suffix}")
            if not group:
                continue
            news = (render_check(R, 16, False, "#3b82f6", bg, off=off), render_check(R, 16, True, "#3b82f6", bg),
                    render_check(R, 16, False, "#3b82f6", bg, True, off=off), render_check(R, 16, True, "#3b82f6", bg, True))
            for old, new in zip(group, news):
                self._copy_into(old, new)

    def _remap_tree(self, widget, light):
        self._remap_widget(widget, light)
        for child in widget.winfo_children():
            self._remap_tree(child, light)

    def _remap_widget(self, w, light):
        if w is self.root:
            return
        orig = getattr(w, "_ank_orig", None)
        if orig is None:
            orig = {}
            for opt in ("bg", "background", "fg", "foreground", "activebackground", "highlightbackground", "selectcolor",
                        "troughcolor", "insertbackground", "disabledforeground"):
                try:
                    val = w.cget(opt)
                except Exception:
                    continue
                val = str(val)
                if val.startswith("#") and len(val) == 7:
                    orig[opt] = val.lower()
            try:
                w._ank_orig = orig
            except Exception:
                return
        if getattr(w, "_ank_badge", None):
            glyph_color, size = w._ank_badge
            bg = "#f6f8fb" if light else "#111a2c"
            top = _hexc(_mix(_rgb(glyph_color), (255, 255, 255), 0.18))
            bot = _hexc(_mix(_rgb(glyph_color), (0, 0, 0), 0.45))
            edge = _hexc(_mix(_rgb(glyph_color), (255, 255, 255), 0.45))
            self._copy_into(w._img3d, render_glossy(self.root, size, size + 3, top, bot, edge, bg, radius=12, shadow=3))
        bg_now = orig.get("bg") or orig.get("background")
        new_bg = self.THEME_BG_MAP.get(bg_now, bg_now) if (light and bg_now) else bg_now
        bg_is_light = bool(new_bg) and new_bg not in self.KEEP_DARK and sum(_rgb(new_bg)) > 500
        for opt, val in orig.items():
            target = val
            if light:
                if opt in ("bg", "background", "activebackground", "highlightbackground", "selectcolor", "troughcolor"):
                    target = self.THEME_BG_MAP.get(val, val) if val not in self.KEEP_DARK else val
                elif opt in ("fg", "foreground", "insertbackground", "disabledforeground") and bg_is_light:
                    target = self.THEME_FG_MAP.get(val, val)
            try:
                w.configure(**{opt: target})
            except Exception:
                pass

    # --------------------------------------------------------- notifications
    def notify(self, title: str, message: str):
        """Desktop notification (Windows balloon / macOS / Linux) plus a gentle bell."""
        try:
            self.root.bell()
        except Exception:
            pass
        if not self.settings.get("notify", True):
            return
        try:
            if sys.platform == "win32":
                t = title.replace("'", "''")
                m = message.replace("'", "''")
                ps = ("Add-Type -AssemblyName System.Windows.Forms; Add-Type -AssemblyName System.Drawing; "
                      "$n=New-Object System.Windows.Forms.NotifyIcon; $n.Icon=[System.Drawing.SystemIcons]::Information; "
                      f"$n.Visible=$true; $n.ShowBalloonTip(8000,'{t}','{m}',[System.Windows.Forms.ToolTipIcon]::Info); "
                      "Start-Sleep -s 9; $n.Dispose()")
                subprocess.Popen(["powershell", "-NoProfile", "-WindowStyle", "Hidden", "-Command", ps], creationflags=0x08000000)
            elif sys.platform == "darwin":
                subprocess.Popen(["osascript", "-e", f'display notification "{message}" with title "{title}"'])
            elif shutil.which("notify-send"):
                subprocess.Popen(["notify-send", title, message])
        except Exception:
            pass

    # ---------------------------------------- global speed limit & quality
    def with_global_args(self, cmd):
        """Adds the Settings speed limit and maximum quality to any yt-dlp command."""
        cmd = list(cmd)
        extra = []
        lim = str(self.settings.get("speed_limit") or "").strip()
        if lim:
            extra += ["--limit-rate", lim]
        q = self.settings.get("max_quality", "best")
        if q != "best":
            sort = "+size,+br,+res" if q == "smallest" else f"res:{q}"
            if "-S" in cmd:
                i = cmd.index("-S") + 1
                parts = cmd[i].split(",")
                cmd[i] = ",".join([sort if p == "res" else p for p in parts]) if "res" in parts else ",".join(parts + [sort])
            else:
                extra += ["-S", sort]
        return [cmd[0]] + extra + cmd[1:] if extra else cmd

    # --------------------------------------------------------- library
    VIDEO_FILE_EXTS = (".mp4", ".mkv", ".webm", ".mov", ".m4v", ".ts")

    def scan_library(self):
        series = {}
        base = self.output_base
        for root_dir, dirs, files in os.walk(base):
            dirs[:] = [d for d in dirs if d != "_resume" and not d.startswith("temp")]
            for fn in files:
                if not fn.lower().endswith(self.VIDEO_FILE_EXTS) or fn.endswith((".part", ".synclock.mp4", ".uniform.mp4")):
                    continue
                fp = os.path.join(root_dir, fn)
                try:
                    st = os.stat(fp)
                except OSError:
                    continue
                if st.st_size < 200 * 1024:
                    continue
                rel = os.path.relpath(fp, base).split(os.sep)
                name = rel[1] if len(rel) >= 3 else (rel[0] if len(rel) >= 2 else os.path.splitext(fn)[0])
                entry = series.setdefault(name, {"name": name, "files": [], "size": 0, "mtime": 0})
                entry["files"].append(fp)
                entry["size"] += st.st_size
                entry["mtime"] = max(entry["mtime"], st.st_mtime)
        return sorted(series.values(), key=lambda e: -e["mtime"])

    @staticmethod
    def _norm_key(s: str) -> str:
        return re.sub(r"[^a-z0-9]+", "", (s or "").lower())

    def series_key_from_url(self, url: str) -> str:
        try:
            p = urllib.parse.urlparse(url)
        except Exception:
            return ""
        q = urllib.parse.parse_qs(p.query)
        if "shortmax" in p.netloc:
            return (q.get("slug") or q.get("id") or [""])[0]
        if "narto" in p.netloc:
            parts = [x for x in p.path.split("/") if x and not x.isdigit()]
            return parts[-1] if parts else ""
        m = re.search(r"video/(\d+)", url)
        if m:
            return m.group(1)
        m = re.search(r"dailymotion\.com/video/(\w+)", url)
        return m.group(1) if m else ""

    def confirm_not_duplicate(self, url: str) -> bool:
        key = self._norm_key(self.series_key_from_url(url))
        if len(key) < 3:
            return True
        for e in self.scan_library():
            if key in self._norm_key(e["name"]) or any(key in self._norm_key(os.path.basename(f)) for f in e["files"]):
                when = datetime.datetime.fromtimestamp(e["mtime"]).strftime("%Y-%m-%d %H:%M")
                return messagebox.askyesno("Already downloaded",
                                           f"'{e['name']}' is already in your library ({len(e['files'])} file(s), last on {when}).\n\nDownload it again?")
        return True

    # --------------------------------------------------------- health / updates
    def ytdlp_update_command(self):
        path = self.get_yt_dlp_path()
        if path and os.path.exists(path):
            folder = os.path.dirname(path)
            for py in (os.path.join(folder, "python.exe"), os.path.join(folder, "python"), os.path.join(folder, "python3"),
                       os.path.join(os.path.dirname(folder), "python.exe")):
                if os.path.isfile(py):
                    return [py, "-m", "pip", "install", "-U", "yt-dlp[default,curl-cffi]"]
            return [path, "-U"]
        return [sys.executable, "-m", "pip", "install", "-U", "yt-dlp[default,curl-cffi]"]

    def engine_versions(self):
        kwargs = {"creationflags": 0x08000000} if sys.platform == "win32" else {}

        def first_line(cmd):
            try:
                r = subprocess.run(cmd, capture_output=True, text=True, encoding="utf-8", errors="ignore", timeout=30, **kwargs)
                out = (r.stdout or r.stderr or "").strip().splitlines()
                return out[0][:80] if out and r.returncode == 0 else "not working"
            except Exception:
                return "not found"
        yt = self.get_yt_dlp_path()
        rows = [("yt-dlp", first_line([yt, "--version"]) if yt and os.path.exists(yt) else "not found")]
        imp = "not found"
        if yt and os.path.exists(yt):
            try:
                r = subprocess.run([yt, "--list-impersonate-targets"], capture_output=True, text=True, encoding="utf-8",
                                   errors="ignore", timeout=40, **kwargs)
                imp = "ready (Chrome impersonation available)" if any(ln.strip().lower().startswith("chrome") and "unavailable" not in ln.lower()
                                                                     for ln in r.stdout.splitlines()) else "missing — click Update yt-dlp"
            except Exception:
                imp = "unknown"
        rows.append(("curl_cffi (impersonation)", imp))
        rows.append(("FFmpeg", first_line(["ffmpeg", "-version"]) if shutil.which("ffmpeg") else "not found"))
        aria = self.get_aria2c_path()
        rows.append(("aria2c", first_line([aria, "--version"]) if aria else "not found (optional)"))
        rows.append(("curl", first_line(["curl", "--version"]) if shutil.which("curl") else "not found"))
        rows.append(("Python", sys.version.split()[0]))
        return rows

    # --------------------------------------------------------- pages
    def build_extra_pages(self):
        self.build_dl_queue_page()
        self.build_library_page()
        self.build_find_page()
        self.build_settings_page()

    def _page_header(self, page, text, sub):
        hdr = ttk.Frame(page)
        hdr.pack(fill="x", padx=14, pady=(10, 4))
        tk.Label(hdr, text=text, font=("Arial", 15, "bold"), bg="#0b0f19", fg="#f8fafc").pack(anchor="w")
        tk.Label(hdr, text=sub, font=("Arial", 9), bg="#0b0f19", fg="#94a3b8").pack(anchor="w")

    # ---- Queue page ----
    QUEUE_TYPES = [("narto_claude", "Narto ⚡ Claude (turbo)"), ("narto", "Narto (Original)"), ("shortmax", "Shortmax"),
                   ("tiktok", "TikTok (single)"), ("tiktok_bulk", "TikTok bulk (.txt file)"), ("dailymotion", "Dailymotion"),
                   ("direct", "Direct M3U8 / MP4"), ("torrent", "Torrent / Magnet")]

    def build_dl_queue_page(self):
        page = ttk.Frame(self.page_container)
        self.pages["dlqueue"] = page
        self._page_header(page, "📋 Download Queue", "Add as many series as you like — they download one after another, "
                                                     "survive restarts, and resume where they stopped.")
        add = ttk.LabelFrame(page, text="➕ Add a download", padding=(12, 6))
        add.pack(fill="x", padx=14, pady=4)
        row1 = ttk.Frame(add, style="Card.TFrame")
        row1.pack(fill="x", pady=2)
        self.q_type_var = tk.StringVar(value=self.QUEUE_TYPES[0][1])
        ttk.Combobox(row1, textvariable=self.q_type_var, values=[t for _, t in self.QUEUE_TYPES], state="readonly", width=24).pack(side="left", padx=(0, 6))
        self.q_url_entry = ttk.Entry(row1, width=60)
        self.q_url_entry.pack(side="left", fill="x", expand=True)
        ttk.Button(row1, text="📋 Paste", command=lambda: (self.q_url_entry.delete(0, tk.END),
                                                         self.q_url_entry.insert(0, self.root.clipboard_get().strip()))).pack(side="left", padx=4)
        ttk.Button(row1, text="📄 File…", command=self._queue_pick_file).pack(side="left")
        row2 = ttk.Frame(add, style="Card.TFrame")
        row2.pack(fill="x", pady=4)
        ttk.Label(row2, text="Start Ep:", background="#131b2e").pack(side="left")
        self.q_start = ttk.Entry(row2, width=6)
        self.q_start.insert(0, "1")
        self.q_start.pack(side="left", padx=(4, 12))
        ttk.Label(row2, text="Total Eps (blank = all):", background="#131b2e").pack(side="left")
        self.q_total = ttk.Entry(row2, width=6)
        self.q_total.pack(side="left", padx=(4, 12))
        ttk.Button(row2, text="➕ Add to Queue", style="Accent.TButton", command=self._queue_add_from_form).pack(side="left", padx=6)
        ttk.Button(row2, text="➕ Add Current Dashboard Link", command=self.queue_add_current_dashboard).pack(side="left")

        lst = ttk.LabelFrame(page, text="Queue", padding=(10, 6))
        lst.pack(fill="both", expand=True, padx=14, pady=4)
        cols = ("type", "link", "eps", "status")
        self.q_tree = ttk.Treeview(lst, columns=cols, show="headings", height=10)
        for c, w_, title in (("type", 170, "Type"), ("link", 520, "Link / file"), ("eps", 90, "Episodes"), ("status", 200, "Status")):
            self.q_tree.heading(c, text=title)
            self.q_tree.column(c, width=w_, anchor="w")
        self.q_tree.pack(fill="both", expand=True)
        btns = ttk.Frame(lst, style="Card.TFrame")
        btns.pack(fill="x", pady=(6, 0))
        self.q_start_btn = ttk.Button(btns, text="▶️ Start Queue", style="Success.TButton", command=self.start_dl_queue)
        self.q_start_btn.pack(side="left", padx=2)
        ttk.Button(btns, text="⏸️ Pause After Current", command=self._queue_pause).pack(side="left", padx=2)
        ttk.Button(btns, text="⬆️", width=3, command=lambda: self._queue_move(-1)).pack(side="left", padx=2)
        ttk.Button(btns, text="⬇️", width=3, command=lambda: self._queue_move(1)).pack(side="left", padx=2)
        ttk.Button(btns, text="🔁 Retry", command=self._queue_retry).pack(side="left", padx=2)
        ttk.Button(btns, text="🗑️ Remove", command=self._queue_remove).pack(side="left", padx=2)
        ttk.Button(btns, text="🧹 Clear Finished", command=self._queue_clear_done).pack(side="left", padx=2)

        opts = ttk.LabelFrame(page, text="⏰ Schedule & when finished", padding=(12, 6))
        opts.pack(fill="x", padx=14, pady=(4, 10))
        r = ttk.Frame(opts, style="Card.TFrame")
        r.pack(fill="x")
        self.q_sched_var = tk.BooleanVar(value=bool(self.settings.get("schedule_on")))
        ttk.Checkbutton(r, text="Only download between", variable=self.q_sched_var, style="Card.TCheckbutton",
                        command=self._queue_save_options).pack(side="left")
        self.q_from = ttk.Entry(r, width=6)
        self.q_from.insert(0, self.settings.get("schedule_from", "01:00"))
        self.q_from.pack(side="left", padx=4)
        ttk.Label(r, text="and", background="#131b2e").pack(side="left")
        self.q_to = ttk.Entry(r, width=6)
        self.q_to.insert(0, self.settings.get("schedule_to", "07:00"))
        self.q_to.pack(side="left", padx=4)
        ttk.Label(r, text="   When the queue finishes:", background="#131b2e").pack(side="left", padx=(10, 4))
        self.q_end_var = tk.StringVar(value={"none": "Do nothing", "notify": "Notify me", "shutdown": "Shut down the PC"}[self.settings.get("queue_end_action", "notify")])
        cb = ttk.Combobox(r, textvariable=self.q_end_var, values=["Do nothing", "Notify me", "Shut down the PC"], state="readonly", width=18)
        cb.pack(side="left")
        cb.bind("<<ComboboxSelected>>", lambda e: self._queue_save_options())
        for e_ in (self.q_from, self.q_to):
            e_.bind("<FocusOut>", lambda e: self._queue_save_options())
        self.queue_path = os.path.join(self.base_dir, "download_queue.json")
        self.dl_queue = []
        self._queue_running = False
        self._queue_pause_req = False
        self._load_queue()

    def _queue_pick_file(self):
        f = filedialog.askopenfilename(title="Choose a TikTok link list or .torrent", filetypes=[("Lists / torrents", "*.txt *.rtf *.torrent"), ("All files", "*.*")])
        if f:
            self.q_url_entry.delete(0, tk.END)
            self.q_url_entry.insert(0, f)
            if f.lower().endswith(".torrent"):
                self.q_type_var.set("Torrent / Magnet")
            elif f.lower().endswith((".txt", ".rtf")):
                self.q_type_var.set("TikTok bulk (.txt file)")

    def _queue_type_key(self, title):
        return next((k for k, t in self.QUEUE_TYPES if t == title), "direct")

    def _load_queue(self):
        try:
            with open(self.queue_path, "r", encoding="utf-8") as f:
                self.dl_queue = json.load(f)
        except Exception:
            self.dl_queue = []
        for j in self.dl_queue:
            if j.get("status") in ("Running", "Waiting for schedule"):
                j["status"] = "Pending (will resume)"
        self._refresh_queue_view()

    def _save_queue(self):
        try:
            with open(self.queue_path, "w", encoding="utf-8") as f:
                json.dump(self.dl_queue, f, indent=2)
        except Exception:
            pass

    def _refresh_queue_view(self):
        if not hasattr(self, "q_tree"):
            return
        sel = self.q_tree.selection()
        self.q_tree.delete(*self.q_tree.get_children())
        titles = dict(self.QUEUE_TYPES)
        for i, j in enumerate(self.dl_queue):
            eps = f"{j.get('start', 1)}–{j.get('total') or 'all'}" if j["type"] not in ("tiktok", "dailymotion", "direct", "torrent") else "—"
            self.q_tree.insert("", "end", iid=str(i), values=(titles.get(j["type"], j["type"]), j["url"], eps, j.get("status", "Pending")))
        for s in sel:
            if self.q_tree.exists(s):
                self.q_tree.selection_add(s)

    def queue_add(self, jtype, url, start=1, total="", check_duplicate=True):
        url = (url or "").strip()
        if not url:
            messagebox.showerror("Queue", "Paste a link (or choose a file) first.")
            return False
        if jtype not in ("tiktok_bulk", "torrent") and check_duplicate and not self.confirm_not_duplicate(url):
            return False
        self.dl_queue.append({"type": jtype, "url": url, "start": int(start) if str(start).isdigit() else 1,
                              "total": str(total).strip(), "status": "Pending", "added": time.time()})
        self._save_queue()
        self._refresh_queue_view()
        self.update_status(f"Added to queue ({len(self.dl_queue)} item(s)). Open 📋 Queue to start.", "green")
        return True

    def _queue_add_from_form(self):
        if self.queue_add(self._queue_type_key(self.q_type_var.get()), self.q_url_entry.get(), self.q_start.get(), self.q_total.get()):
            self.q_url_entry.delete(0, tk.END)

    def queue_add_current_dashboard(self):
        """Queues whatever link is in the dashboard tab that is open, with the current Start/Total episodes."""
        tab = self.home_tabs.index("current")
        mapping = {0: ("shortmax", self.url_entry1), 1: ("narto", self.url_entry2), 2: ("narto_claude", self.url_entry7),
                   3: ("dailymotion", self.url_entry5), 4: ("tiktok", self.url_entry4), 5: ("direct", self.url_entry3),
                   6: ("torrent", self.url_entry6)}
        jtype, entry = mapping.get(tab, ("direct", self.url_entry3))
        self.queue_add(jtype, entry.get(), self.start_entry.get(), self.total_entry.get())

    def _queue_selected_index(self):
        sel = self.q_tree.selection()
        return int(sel[0]) if sel else -1

    def _queue_move(self, d):
        i = self._queue_selected_index()
        j = i + d
        if 0 <= i < len(self.dl_queue) and 0 <= j < len(self.dl_queue):
            self.dl_queue[i], self.dl_queue[j] = self.dl_queue[j], self.dl_queue[i]
            self._save_queue()
            self._refresh_queue_view()
            self.q_tree.selection_set(str(j))

    def _queue_remove(self):
        i = self._queue_selected_index()
        if 0 <= i < len(self.dl_queue) and self.dl_queue[i].get("status") != "Running":
            self.dl_queue.pop(i)
            self._save_queue()
            self._refresh_queue_view()

    def _queue_retry(self):
        i = self._queue_selected_index()
        if 0 <= i < len(self.dl_queue) and self.dl_queue[i].get("status") != "Running":
            self.dl_queue[i]["status"] = "Pending"
            self._save_queue()
            self._refresh_queue_view()

    def _queue_clear_done(self):
        self.dl_queue = [j for j in self.dl_queue if not j.get("status", "").startswith("Done")]
        self._save_queue()
        self._refresh_queue_view()

    def _queue_pause(self):
        self._queue_pause_req = True
        self.update_status("Queue will pause after the current download.", "orange")

    def _queue_save_options(self):
        self.settings["schedule_on"] = bool(self.q_sched_var.get())
        self.settings["schedule_from"] = self.q_from.get().strip() or "01:00"
        self.settings["schedule_to"] = self.q_to.get().strip() or "07:00"
        self.settings["queue_end_action"] = {"Do nothing": "none", "Notify me": "notify", "Shut down the PC": "shutdown"}[self.q_end_var.get()]
        self.save_settings()

    def _in_schedule(self) -> bool:
        if not self.settings.get("schedule_on"):
            return True
        try:
            now = datetime.datetime.now().time()
            a = datetime.datetime.strptime(self.settings["schedule_from"], "%H:%M").time()
            b = datetime.datetime.strptime(self.settings["schedule_to"], "%H:%M").time()
            return (a <= now < b) if a <= b else (now >= a or now < b)
        except Exception:
            return True

    def _on_main(self, fn):
        """Runs fn on the Tk thread and waits for it (used by the queue worker)."""
        done = threading.Event()
        box = {}

        def call():
            try:
                box["r"] = fn()
            finally:
                done.set()
        self.root.after(0, call)
        done.wait(30)
        return box.get("r")

    def start_dl_queue(self):
        if self._queue_running:
            return
        if not any(j.get("status", "").startswith("Pending") for j in self.dl_queue):
            messagebox.showinfo("Queue", "Nothing pending in the queue.")
            return
        self._queue_running = True
        self._queue_pause_req = False
        self.q_start_btn.config(state="disabled")
        self.disable_buttons_for_run()
        threading.Thread(target=self._queue_worker, daemon=True).start()

    def _queue_worker(self):
        finished = 0
        try:
            while True:
                job = next((j for j in self.dl_queue if j.get("status", "").startswith("Pending")), None)
                if job is None or self._queue_pause_req:
                    break
                while not self._in_schedule() and not self._queue_pause_req:
                    job["status"] = "Waiting for schedule"
                    self.root.after(0, self._refresh_queue_view)
                    self.root.after(0, lambda: self.update_status(f"Queue waiting until {self.settings['schedule_from']}…", "orange"))
                    time.sleep(20)
                if self._queue_pause_req:
                    job["status"] = "Pending"
                    break
                job["status"] = "Running"
                self._save_queue()
                self.root.after(0, self._refresh_queue_view)
                ok = self._run_queue_job(job)
                if self.stop_flag:
                    job["status"] = "Pending (stopped — resumes next start)"
                    self._save_queue()
                    break
                job["status"] = "Done ✅" if ok else "Failed ❌ (see log)"
                job["finished"] = time.time()
                if ok:
                    finished += 1
                self._save_queue()
                self.root.after(0, self._refresh_queue_view)
        finally:
            self._queue_running = False
            self.root.after(0, self._refresh_queue_view)
            self.root.after(0, lambda: (self.q_start_btn.config(state="normal"), self.reset_buttons()))
            pending = any(j.get("status", "").startswith("Pending") for j in self.dl_queue)
            if not pending and not self.stop_flag and not self._queue_pause_req:
                self.root.after(0, lambda: self._queue_finished(finished))

    def _queue_finished(self, finished):
        action = self.settings.get("queue_end_action", "notify")
        msg = f"Download queue finished — {finished} item(s) downloaded."
        self.update_status(msg, "green")
        self.log_message(msg)
        if action in ("notify", "shutdown"):
            self.notify("Nader Downloader", msg)
        if action == "shutdown":
            if sys.platform == "win32":
                subprocess.Popen(["shutdown", "/s", "/t", "120", "/c", "Nader Downloader finished the queue. Shutting down in 2 minutes."],
                                 creationflags=0x08000000)
                cancel_cmd = ["shutdown", "/a"]
            elif sys.platform == "darwin":
                subprocess.Popen(["osascript", "-e", 'delay 120', "-e", 'tell app "System Events" to shut down'])
                cancel_cmd = None
            else:
                subprocess.Popen(["shutdown", "-h", "+2"])
                cancel_cmd = ["shutdown", "-c"]
            if messagebox.askyesno("Shutting down", "The computer will shut down in 2 minutes.\n\nCancel the shutdown?") and cancel_cmd:
                subprocess.Popen(cancel_cmd)

    def _run_queue_job(self, job) -> bool:
        before = (self.last_output_file, os.path.getmtime(self.last_output_file) if self.last_output_file and os.path.exists(self.last_output_file) else 0)
        self.stop_flag = False

        def prep():
            self.start_entry.delete(0, tk.END)
            self.start_entry.insert(0, str(job.get("start", 1)))
            self.total_entry.delete(0, tk.END)
            self.total_entry.insert(0, str(job.get("total", "")))
            self.update_status(f"Queue: {dict(self.QUEUE_TYPES).get(job['type'])} — {job['url'][:70]}", "blue")
        self._on_main(prep)
        self.log_message(f"{'='*50}\n--- QUEUE JOB: {job['type']} ---\n{job['url']}")
        self._current_dl_url = job["url"] if job["type"] not in ("tiktok_bulk", "torrent") else ""
        t = job["type"]
        try:
            if t == "narto_claude":
                self.narto_claude_process(self.sanitize_url(job["url"]), max(1, min(6, int(self.settings.get("narto_workers", 3)))))
            elif t == "tiktok_bulk":
                self.download_bulk_process(job["url"])
            elif t == "torrent":
                src, kind = self.normalize_torrent_source(job["url"])
                aria = self.get_aria2c_path()
                if not src or not aria:
                    self.log_message("Queue: torrent skipped (invalid link or aria2c missing).")
                    return False
                self.torrent_download_process(src, kind, aria)
            else:
                source = {"shortmax": 1, "narto": 2, "tiktok": 4, "dailymotion": 5, "direct": 3}[t]
                self.download_process(self.sanitize_url(job["url"]), source, keep_buttons_locked=True)
        except Exception as e:
            self.log_message(f"Queue job crashed: {e}")
            return False
        after = self.last_output_file
        return bool(after) and os.path.exists(after) and (after != before[0] or os.path.getmtime(after) > before[1])

    # ---- Library page ----
    # =========================================================================
    # 📚 LIBRARY (v1.9.1) — streaming-style poster wall, Nader Player, share, delete
    # =========================================================================
    POSTER_W, POSTER_H = 176, 250

    def load_lib_meta(self):
        self.lib_meta_path = os.path.join(self.base_dir, "library_meta.json")
        try:
            with open(self.lib_meta_path, "r", encoding="utf-8") as f:
                self.lib_meta = json.load(f)
        except Exception:
            self.lib_meta = {}
        self.poster_dir = os.path.join(self.base_dir, ".library_posters")
        os.makedirs(self.poster_dir, exist_ok=True)

    def save_lib_meta(self):
        try:
            with open(self.lib_meta_path, "w", encoding="utf-8") as f:
                json.dump(self.lib_meta, f, indent=1, ensure_ascii=False)
        except Exception:
            pass

    def library_note_output(self, path):
        """Remembers where a finished video came from and fetches its poster in the background."""
        if not hasattr(self, "lib_meta"):
            return
        path = os.path.abspath(path)
        m = self.lib_meta.setdefault(path, {})
        url = getattr(self, "_current_dl_url", "")
        if url and not m.get("url"):
            m["url"] = url
        m.setdefault("added", time.time())
        self.save_lib_meta()
        threading.Thread(target=self.ensure_poster, args=(path, True), daemon=True).start()

    def library_title(self, path):
        name = os.path.splitext(os.path.basename(path))[0]
        name = re.sub(r"_(Full|EP\d+(-EP\d+)?)(_Claude)?$", "", name)
        name = re.sub(r"^(Narto_Series_|Shortmax_|TikTok_)", "", name, flags=re.IGNORECASE)
        return re.sub(r"[_\-]+", " ", name).strip() or os.path.basename(path)

    def _poster_path(self, video):
        import hashlib
        return os.path.join(self.poster_dir, hashlib.md5(os.path.abspath(video).encode("utf-8")).hexdigest()[:16] + ".png")

    def _image_url_from_page(self, url):
        """Poster from the link we downloaded: yt-dlp thumbnail for video sites, else the page's share image."""
        host = urllib.parse.urlparse(url).netloc.lower()
        yt = self.get_yt_dlp_path()
        if yt and os.path.exists(yt) and any(h in host for h in ("tiktok", "dailymotion", "youtube", "youtu.be", "vimeo", "facebook", "instagram")):
            try:
                kwargs = {"creationflags": 0x08000000} if sys.platform == "win32" else {}
                r = subprocess.run([yt, "--get-thumbnail", "--no-playlist", "--no-warnings", url], capture_output=True, text=True,
                                   timeout=40, encoding="utf-8", errors="ignore", **kwargs)
                for ln in r.stdout.splitlines():
                    if ln.startswith("http"):
                        return ln.strip()
            except Exception:
                pass
        try:
            req = urllib.request.Request(url, headers={"User-Agent": self.NARTO_UA, "Accept-Language": "en"})
            html = urllib.request.urlopen(req, timeout=15).read(600000).decode("utf-8", "ignore")
        except Exception:
            return ""
        for pat in (r'<meta[^>]+property=["\']og:image["\'][^>]+content=["\']([^"\']+)',
                    r'<meta[^>]+content=["\']([^"\']+)["\'][^>]+property=["\']og:image',
                    r'<meta[^>]+name=["\']twitter:image["\'][^>]+content=["\']([^"\']+)',
                    r'"(?:poster|cover|cover_url|vertical_cover|thumb|thumbnail)"\s*:\s*"([^"]+\.(?:jpg|jpeg|png|webp)[^"]*)"',
                    r'poster=["\']([^"\']+)'):
            m = re.search(pat, html, re.IGNORECASE)
            if m:
                u = m.group(1).replace("\\/", "/").replace("&amp;", "&")
                return urllib.parse.urljoin(url, u)
        return ""

    def ensure_poster(self, video, refresh_after=False, force=False):
        out = self._poster_path(video)
        if os.path.exists(out) and not force:
            return out
        vf = (f"scale={self.POSTER_W}:{self.POSTER_H}:force_original_aspect_ratio=increase,"
              f"crop={self.POSTER_W}:{self.POSTER_H}")
        made = False
        url = self.lib_meta.get(os.path.abspath(video), {}).get("url", "")
        if url:
            img_url = self._image_url_from_page(url)
            if img_url:
                try:
                    tmp = out + ".dl"
                    req = urllib.request.Request(img_url, headers={"User-Agent": self.NARTO_UA, "Referer": url})
                    with open(tmp, "wb") as f:
                        f.write(urllib.request.urlopen(req, timeout=20).read(8 * 1024 * 1024))
                    r = self.run_ffmpeg(["ffmpeg", "-y", "-i", tmp, "-vf", vf, "-frames:v", "1", out])
                    made = r.returncode == 0 and os.path.exists(out)
                    os.remove(tmp)
                except Exception:
                    made = False
        if not made:   # a frame from the video itself
            dur = self.get_media_duration(video)
            t = max(1.0, min(dur * 0.12, 90.0)) if dur else 1.0
            r = self.run_ffmpeg(["ffmpeg", "-y", "-ss", f"{t:.2f}", "-i", video, "-vf", vf, "-frames:v", "1", out])
            made = r.returncode == 0 and os.path.exists(out)
        if made and refresh_after:
            try:
                self.root.after(0, lambda: self._update_card_poster(video))
            except Exception:
                pass
        return out if made else ""

    # ------------------------------------------------------------------ page
    def build_library_page(self):
        page = ttk.Frame(self.page_container)
        self.pages["library"] = page
        self.load_lib_meta()
        top = tk.Frame(page, bg="#0b0f19")
        top.pack(fill="x", padx=14, pady=(10, 4))
        tk.Label(top, text="📚 My Library", font=("Arial", 16, "bold"), bg="#0b0f19", fg="#f8fafc").pack(side="left")
        self.lib_summary = tk.Label(top, text="", font=("Arial", 9, "bold"), bg="#0b0f19", fg="#94a3b8")
        self.lib_summary.pack(side="left", padx=12)
        ttk.Button(top, text="🎬 Play Any Video…", command=self._lib_play_other).pack(side="right", padx=2)
        ttk.Button(top, text="🔄", width=3, command=self.refresh_library).pack(side="right", padx=2)
        self.lib_sort = tk.StringVar(value="Newest")
        sc = ttk.Combobox(top, textvariable=self.lib_sort, values=["Newest", "Name", "Biggest", "Continue watching"], state="readonly", width=16)
        sc.pack(side="right", padx=6)
        sc.bind("<<ComboboxSelected>>", lambda e: self.refresh_library())
        self.lib_search = ttk.Entry(top, width=26)
        self.lib_search.pack(side="right", padx=4)
        self.lib_search.bind("<KeyRelease>", lambda e: self._lib_search_later())
        tk.Label(top, text="🔎", bg="#0b0f19", fg="#94a3b8").pack(side="right")

        wrap = tk.Frame(page, bg="#0b0f19")
        wrap.pack(fill="both", expand=True, padx=8, pady=(0, 8))
        self.lib_canvas = tk.Canvas(wrap, bg="#0b0f19", highlightthickness=0)
        vs = ttk.Scrollbar(wrap, orient="vertical", command=self.lib_canvas.yview)
        self.lib_canvas.configure(yscrollcommand=vs.set)
        vs.pack(side="right", fill="y")
        self.lib_canvas.pack(side="left", fill="both", expand=True)
        self.lib_grid = tk.Frame(self.lib_canvas, bg="#0b0f19")
        self._lib_win = self.lib_canvas.create_window(0, 0, window=self.lib_grid, anchor="nw")
        self.lib_grid.bind("<Configure>", lambda e: self.lib_canvas.configure(scrollregion=self.lib_canvas.bbox("all")))
        self.lib_canvas.bind("<Configure>", self._lib_on_resize)
        for wdg in (self.lib_canvas, self.lib_grid):
            wdg.bind("<MouseWheel>", lambda e: self.lib_canvas.yview_scroll(int(-e.delta / 120) or (-1 if e.delta > 0 else 1), "units"))
            wdg.bind("<Button-4>", lambda e: self.lib_canvas.yview_scroll(-3, "units"))
            wdg.bind("<Button-5>", lambda e: self.lib_canvas.yview_scroll(3, "units"))
        self._lib_cols = 0
        self._lib_cards = {}
        self._lib_items = []
        self._lib_imgs = {}

    def _lib_search_later(self):
        if getattr(self, "_lib_search_job", None):
            self.root.after_cancel(self._lib_search_job)
        self._lib_search_job = self.root.after(250, self.refresh_library)

    def _lib_on_resize(self, event):
        self.lib_canvas.itemconfigure(self._lib_win, width=event.width)
        cols = max(1, event.width // (self.POSTER_W + 26))
        if cols != self._lib_cols:
            self._lib_cols = cols
            self._lib_layout()

    def _lib_files(self):
        items = []
        for e in self.scan_library():
            for f in e["files"]:
                try:
                    st = os.stat(f)
                except OSError:
                    continue
                m = self.lib_meta.get(os.path.abspath(f), {})
                items.append({"path": os.path.abspath(f), "title": self.library_title(f), "size": st.st_size,
                              "mtime": m.get("added", st.st_mtime), "pos": m.get("position", 0), "dur": m.get("duration", 0)})
        return items

    def refresh_library(self):
        if not hasattr(self, "lib_grid"):
            return
        q = self.lib_search.get().strip().lower()
        items = [i for i in self._lib_files() if not q or q in i["title"].lower() or q in os.path.basename(i["path"]).lower()]
        order = self.lib_sort.get()
        if order == "Name":
            items.sort(key=lambda i: natural_sort_key(i["title"]))
        elif order == "Biggest":
            items.sort(key=lambda i: -i["size"])
        elif order == "Continue watching":
            items = [i for i in items if i["pos"] and (not i["dur"] or i["pos"] < i["dur"] - 30)]
            items.sort(key=lambda i: -i["mtime"])
        else:
            items.sort(key=lambda i: -i["mtime"])
        self._lib_items = items
        total = sum(i["size"] for i in items)
        self.lib_summary.config(text=f"{len(items)} video{'s' if len(items) != 1 else ''}  •  {total / 1073741824:.2f} GB")
        for c in self._lib_cards.values():
            c.destroy()
        self._lib_cards = {}
        for it in items:
            self._lib_cards[it["path"]] = self._lib_make_card(it)
        self._lib_layout()
        if not items:
            card = tk.Label(self.lib_grid, text="Nothing here yet.\nFinished downloads appear here with their poster.",
                            bg="#0b0f19", fg="#94a3b8", font=("Arial", 12), pady=60)
            self._lib_cards["_empty"] = card
            card.grid(row=0, column=0, padx=20, sticky="w")
        if getattr(self, "_theme_now", "dark") == "light":
            self._remap_tree(self.lib_grid, True)
        missing = [it["path"] for it in items if not os.path.exists(self._poster_path(it["path"]))]
        if missing:
            threading.Thread(target=lambda: [self.ensure_poster(p, True) for p in missing], daemon=True).start()

    def _lib_layout(self):
        cols = max(1, self._lib_cols or 5)
        for k, it in enumerate(self._lib_items):
            card = self._lib_cards.get(it["path"])
            if card:
                card.grid(row=k // cols, column=k % cols, padx=8, pady=8, sticky="n")

    def _poster_image(self, path):
        pp = self._poster_path(path)
        if os.path.exists(pp):
            try:
                return tk.PhotoImage(file=pp)
            except Exception:
                pass
        if not hasattr(self, "_lib_placeholder"):
            self._lib_placeholder = render_glossy(self.root, self.POSTER_W, self.POSTER_H, "#334155", "#111827", "#475569", "#131b2e", radius=10, shadow=0)
        return self._lib_placeholder

    def _lib_make_card(self, it):
        path = it["path"]
        card = tk.Frame(self.lib_grid, bg="#131b2e", highlightthickness=1, highlightbackground="#24324d")
        img = self._poster_image(path)
        self._lib_imgs[path] = img
        poster = tk.Label(card, image=img, bg="#131b2e", cursor="hand2", bd=0)
        poster.pack(padx=6, pady=(6, 2))
        poster.bind("<Button-1>", lambda e: self.play_video(path))
        card._poster = poster
        if it["pos"] and it["dur"] and it["pos"] < it["dur"] - 30:
            bar = tk.Frame(card, bg="#334155", height=4, width=self.POSTER_W)
            bar.pack(padx=6)
            bar.pack_propagate(False)
            tk.Frame(bar, bg="#f43f5e", height=4, width=max(4, int(self.POSTER_W * it["pos"] / it["dur"]))).pack(side="left")
        tk.Label(card, text=it["title"], bg="#131b2e", fg="#f8fafc", font=("Arial", 10, "bold"), wraplength=self.POSTER_W,
                 justify="left", anchor="w").pack(fill="x", padx=8)
        eps = re.search(r"(EP\d+(?:-EP\d+)?|Full)", os.path.basename(path))
        info = f"{eps.group(1) + '  •  ' if eps else ''}{it['size'] / 1048576:.0f} MB  •  {datetime.datetime.fromtimestamp(it['mtime']).strftime('%d %b %Y')}"
        tk.Label(card, text=info, bg="#131b2e", fg="#94a3b8", font=("Arial", 8)).pack(anchor="w", padx=8)
        row = tk.Frame(card, bg="#131b2e")
        row.pack(fill="x", padx=6, pady=(4, 8))
        resume = it["pos"] and it["dur"] and it["pos"] < it["dur"] - 30
        ttk.Button(row, text="▶ Resume" if resume else "▶ Play", style="Accent.TButton", command=lambda: self.play_video(path)).pack(side="left")
        share = ttk.Button(row, text="📤 Share", width=8)
        share.configure(command=lambda b=share: self._lib_share_menu(path, b))
        share.pack(side="left", padx=3)
        ttk.Button(row, text="🗑", width=3, style="Danger.TButton", command=lambda: self._lib_delete_file(path)).pack(side="left")
        menu = tk.Menu(card, tearoff=0)
        menu.add_command(label="▶ Play in Nader Player", command=lambda: self.play_video(path))
        menu.add_command(label="🎛️ Open in Full Manual Edit", command=lambda: (self.fme_v_path_var.set(path), self.show_page("manual_edit")))
        menu.add_command(label="📂 Show in folder", command=lambda: self.open_last_local_folder(os.path.dirname(path)))
        menu.add_command(label="🖼️ Change poster…", command=lambda: self._lib_change_poster(path))
        menu.add_command(label="🔄 Get poster again", command=lambda: threading.Thread(target=self.ensure_poster, args=(path, True, True), daemon=True).start())
        for w_ in (card, poster):
            w_.bind("<Button-3>", lambda e, m=menu: m.tk_popup(e.x_root, e.y_root))
            w_.bind("<Button-2>", lambda e, m=menu: m.tk_popup(e.x_root, e.y_root))
        for w_ in [card] + list(card.winfo_children()):
            w_.bind("<MouseWheel>", lambda e: self.lib_canvas.yview_scroll(int(-e.delta / 120) or (-1 if e.delta > 0 else 1), "units"), add="+")
            w_.bind("<Button-4>", lambda e: self.lib_canvas.yview_scroll(-3, "units"), add="+")
            w_.bind("<Button-5>", lambda e: self.lib_canvas.yview_scroll(3, "units"), add="+")
        return card

    def _update_card_poster(self, path):
        card = getattr(self, "_lib_cards", {}).get(path)
        if card is None or not card.winfo_exists():
            return
        img = self._poster_image(path)
        self._lib_imgs[path] = img
        card._poster.config(image=img)

    def _lib_change_poster(self, path):
        src = filedialog.askopenfilename(title="Choose a poster image", filetypes=[("Images", "*.jpg *.jpeg *.png *.webp *.gif"), ("All", "*.*")])
        if not src:
            return
        vf = f"scale={self.POSTER_W}:{self.POSTER_H}:force_original_aspect_ratio=increase,crop={self.POSTER_W}:{self.POSTER_H}"
        self.run_ffmpeg(["ffmpeg", "-y", "-i", src, "-vf", vf, "-frames:v", "1", self._poster_path(path)])
        self._update_card_poster(path)

    def _lib_play_other(self):
        f = filedialog.askopenfilename(title="Play a video", filetypes=[("Videos", "*.mp4 *.mkv *.webm *.mov *.avi *.ts *.m4v"), ("All", "*.*")])
        if f:
            self.play_video(f)

    # --------------------------------------------------------------- player
    def play_video(self, path):
        if not os.path.exists(path):
            messagebox.showerror("Play", "This file is no longer on the disk.")
            self.refresh_library()
            return
        NaderPlayer(self, path)

    def offer_install_mpv(self):
        """Nader Player runs on the free mpv engine. Returns True if an install was started and finished."""
        if not messagebox.askyesno("Nader Player", "Nader Player uses the free, very fast 'mpv' video engine, which is not on this computer yet.\n\n"
                                                   "Install it now?\n\n(No = play with VLC or your normal player instead)"):
            return False
        if sys.platform == "win32" and shutil.which("winget"):
            self.update_status("Installing the mpv engine with winget… (a window may ask for permission)", "orange")
            r = subprocess.run(["winget", "install", "-e", "--id", "shinchiro.mpv", "--accept-source-agreements", "--accept-package-agreements"],
                               capture_output=True, text=True, encoding="utf-8", errors="ignore")
            if find_mpv(self.base_dir):
                self.update_status("mpv installed. Enjoy Nader Player!", "green")
                return True
            self.log_message(f"winget mpv install output:\n{(r.stdout or '')[-1500:]}\n{(r.stderr or '')[-800:]}")
        elif sys.platform == "darwin" and shutil.which("brew"):
            self.update_status("Installing mpv with Homebrew…", "orange")
            subprocess.run(["brew", "install", "mpv"], capture_output=True)
            if find_mpv(self.base_dir):
                return True
        webbrowser.open("https://mpv.io/installation/")
        messagebox.showinfo("Nader Player", "Your browser opened the mpv download page.\n\n"
                                            "Windows: download the 'mpv' build, unzip it and put the 'mpv' folder next to Downloader.py "
                                            "(…\\mpv\\mpv.exe). Mac: install mpv.app into Applications.\n\nThis video will now open in your normal player.")
        return False

    def play_with_fallback(self, path):
        vlc = find_vlc()
        if vlc:
            args = [vlc, path]
            srt = os.path.splitext(path)[0] + ".ar.srt"
            if not os.path.exists(srt):
                srt = os.path.splitext(path)[0] + ".srt"
            if os.path.exists(srt):
                args += [f"--sub-file={srt}"]
            delay = float(self.lib_meta.get(os.path.abspath(path), {}).get("audio_delay", 0.0))
            if delay:
                args += [f"--audio-desync={int(delay * 1000)}"]
            subprocess.Popen(args)
        else:
            self.open_last_file(path)

    # ------------------------------------------------------------ subtitles
    def opensubtitles_download(self, query, lang, out_path):
        key = self.settings.get("opensubtitles_key")
        if not key:
            return False
        headers = {"Api-Key": key, "User-Agent": f"NaderDownloader {self.version}", "Accept": "application/json",
                   "Content-Type": "application/json"}
        try:
            q = urllib.parse.urlencode({"query": query, "languages": lang})
            req = urllib.request.Request(f"https://api.opensubtitles.com/api/v1/subtitles?{q}", headers=headers)
            data = json.loads(urllib.request.urlopen(req, timeout=25).read().decode("utf-8"))
            for item in data.get("data", []):
                files = item.get("attributes", {}).get("files", [])
                if not files:
                    continue
                body = json.dumps({"file_id": files[0]["file_id"], "sub_format": "srt"}).encode("utf-8")
                req = urllib.request.Request("https://api.opensubtitles.com/api/v1/download", data=body, headers=headers, method="POST")
                link = json.loads(urllib.request.urlopen(req, timeout=25).read().decode("utf-8")).get("link")
                if link:
                    raw = urllib.request.urlopen(urllib.request.Request(link, headers={"User-Agent": "Mozilla/5.0"}), timeout=30).read()
                    with open(out_path, "wb") as f:
                        f.write(raw)
                    return True
        except Exception as e:
            self.log_message(f"OpenSubtitles: {e}")
        return False

    def estimate_sub_lag(self, video, cues, start, length, rate=50):
        """Seconds the subtitles must be delayed so they line up with the voice (None if not enough dialogue)."""
        import array
        kwargs = {"creationflags": 0x08000000} if sys.platform == "win32" else {}
        r = subprocess.run(["ffmpeg", "-v", "error", "-ss", f"{start:.3f}", "-t", f"{length:.3f}", "-i", video, "-map", "0:a:0",
                            "-ac", "1", "-ar", "8000", "-af", "highpass=f=200,lowpass=f=3500", "-f", "s16le", "-"], capture_output=True, **kwargs)
        pcm = array.array("h")
        pcm.frombytes(r.stdout[: len(r.stdout) // 2 * 2])
        step = 8000 // rate
        env = [sum(map(abs, pcm[k:k + step:4])) / max(1, len(pcm[k:k + step:4])) for k in range(0, len(pcm) - step + 1, step)]
        if len(env) < rate * 20:
            return None
        mask = [0] * len(env)
        for st, en in cues:
            for k in range(max(0, int((st - start) * rate)), min(len(env), int((en - start) * rate))):
                mask[k] = 1
        idx = [k for k, m in enumerate(mask) if m]
        if len(idx) < rate:
            return None
        mean = sum(env) / len(env)
        env = [x - mean for x in env]
        n, best, best_score = len(env), 0, None
        for lag in range(-3 * rate, 3 * rate + 1):
            score = sum(env[k + lag] for k in idx if 0 <= k + lag < n)
            if best_score is None or score > best_score:
                best, best_score = lag, score
        return best / rate

    # ----------------------------------------------------------------- share
    def _find_blip(self):
        """Where Blip is. On Windows Blip is a Microsoft Store app: it must be started through its App ID
        (like the Start menu does) — running its .exe directly crashes it (Java 'kernel32' error)."""
        if sys.platform == "win32":
            try:
                r = subprocess.run(["powershell", "-NoProfile", "-Command",
                                    "Get-StartApps | Where-Object { $_.Name -like '*Blip*' } | Select-Object -First 1 -ExpandProperty AppID"],
                                   capture_output=True, text=True, timeout=20, creationflags=0x08000000)
                app_id = (r.stdout or "").strip()
                if app_id:
                    return "appid:" + app_id
            except Exception:
                pass
            try:
                r = subprocess.run(["powershell", "-NoProfile", "-Command",
                                    "Get-AppxPackage *Blip* | Select-Object -First 1 -ExpandProperty PackageFamilyName"],
                                   capture_output=True, text=True, timeout=20, creationflags=0x08000000)
                fam = (r.stdout or "").strip()
                if fam:
                    return "appid:" + fam + "!App"
            except Exception:
                pass
            la = os.environ.get("LOCALAPPDATA", "")
            pf = os.environ.get("ProgramFiles", r"C:\Program Files")
            for c in (os.path.join(la, "Programs", "Blip", "Blip.exe"), os.path.join(la, "Programs", "blip", "Blip.exe"),
                      os.path.join(pf, "Blip", "Blip.exe")):
                if os.path.isfile(c):
                    return c
            return ""
        if sys.platform == "darwin":
            for c in ("/Applications/Blip.app", os.path.expanduser("~/Applications/Blip.app")):
                if os.path.isdir(c):
                    return c
            return ""
        return shutil.which("blip") or ""

    def _copy_file_to_clipboard(self, path):
        try:
            if sys.platform == "win32":
                p = path.replace("'", "''")
                subprocess.Popen(["powershell", "-NoProfile", "-Command", f"Set-Clipboard -LiteralPath '{p}'"], creationflags=0x08000000)
            elif sys.platform == "darwin":
                subprocess.Popen(["osascript", "-e", f'set the clipboard to (POSIX file "{path}")'])
            else:
                self.root.clipboard_clear()
                self.root.clipboard_append(path)
            return True
        except Exception:
            return False

    def _lib_share_menu(self, path, widget):
        m = tk.Menu(self.root, tearoff=0)
        if sys.platform == "darwin":
            m.add_command(label="📡 AirDrop", command=lambda: self.share_airdrop(path))
        m.add_command(label="🔵 Bluetooth", command=lambda: self.share_bluetooth(path))
        m.add_command(label="⚡ Blip", command=lambda: self.share_blip(path))
        m.add_separator()
        m.add_command(label="📋 Copy file (paste anywhere)", command=lambda: self._copy_file_to_clipboard(path) and
                      self.update_status("Video copied — paste it into a chat, folder or app.", "green"))
        m.add_command(label="📂 Show in folder", command=lambda: self.open_last_local_folder(os.path.dirname(path)))
        m.tk_popup(widget.winfo_rootx(), widget.winfo_rooty() + widget.winfo_height())

    def share_airdrop(self, path):
        js = ("ObjC.import('AppKit'); var s=$.NSSharingService.sharingServiceNamed($.NSSharingServiceNameSendViaAirDrop);"
              f"s.performWithItems($([$.NSURL.fileURLWithPath({json.dumps(path)})])); delay(300);")
        try:
            subprocess.Popen(["osascript", "-l", "JavaScript", "-e", js])
            self.update_status("AirDrop opened — pick the iPhone/Mac to send to.", "green")
        except Exception:
            subprocess.Popen(["open", "-R", path])

    def share_bluetooth(self, path):
        try:
            if sys.platform == "win32":
                self._copy_file_to_clipboard(path)
                subprocess.Popen(["fsquirt.exe"])
                messagebox.showinfo("Bluetooth", "Windows Bluetooth transfer opened.\n\nChoose 'Send files' → your phone → 'Browse…'. "
                                                 "The video's folder is opened for you too:\n" + path)
                self.open_last_local_folder(os.path.dirname(path))
            elif sys.platform == "darwin":
                subprocess.Popen(["open", "-a", "Bluetooth File Exchange", path])
            elif shutil.which("bluetooth-sendto"):
                subprocess.Popen(["bluetooth-sendto", path])
            else:
                messagebox.showinfo("Bluetooth", "No Bluetooth sender found on this computer.")
        except Exception as e:
            messagebox.showerror("Bluetooth", str(e))

    def share_blip(self, path):
        blip = self._find_blip()
        if not blip:
            if messagebox.askyesno("Blip", "Blip isn't installed on this computer.\n\nDownload it now (free, blip.net)?"):
                webbrowser.open("https://blip.net")
            return
        try:
            self._copy_file_to_clipboard(path)
            if blip.startswith("appid:"):
                # Same as clicking Blip in the Start menu (never pass the file: Store apps can't take it that way)
                subprocess.Popen(["explorer.exe", "shell:AppsFolder\\" + blip[len("appid:"):]])
            elif sys.platform == "darwin":
                subprocess.Popen(["open", "-a", blip])
            else:
                subprocess.Popen([blip], cwd=os.path.dirname(blip) or None)
            self.open_last_local_folder(os.path.dirname(path))
            messagebox.showinfo("Blip", "Blip is opening, and the video is already copied.\n\n"
                                        "In Blip choose your phone, then paste (Ctrl+V / ⌘V) — or drag the video from the folder "
                                        "that just opened onto your phone in Blip.\n\n" + os.path.basename(path))
        except Exception as e:
            messagebox.showerror("Blip", str(e))

    # ---------------------------------------------------------------- delete
    def _lib_delete_file(self, path):
        name = os.path.basename(path)
        size = os.path.getsize(path) / 1048576 if os.path.exists(path) else 0
        if not messagebox.askyesno("Delete video", f"Are you sure you want to delete this video?\n\n{name}\n({size:.0f} MB)\n\n"
                                                   "It will be removed from your computer.", icon="warning"):
            return
        base = os.path.splitext(path)[0]
        for extra in [path, self._poster_path(path)] + [base + s for s in (".srt", ".ar.srt", ".en.srt")]:
            try:
                os.remove(extra)
            except OSError:
                pass
        self.lib_meta.pop(os.path.abspath(path), None)
        self.save_lib_meta()
        try:
            folder = os.path.dirname(path)
            if not os.listdir(folder):
                os.rmdir(folder)
        except OSError:
            pass
        self.refresh_library()
        self.update_status(f"Deleted {name}", "orange")







    # ---- Settings & health page ----
    def build_settings_page(self):
        page = ttk.Frame(self.page_container)
        self.pages["settings"] = page
        self._page_header(page, "⚙️ Settings & Health", "Your choices are saved automatically.")
        cols = ttk.Frame(page)
        cols.pack(fill="both", expand=True, padx=14, pady=4)
        left = ttk.LabelFrame(cols, text="🎨 Look & downloads", padding=(12, 8))
        left.pack(side="left", fill="both", expand=True, padx=(0, 6))
        self.theme_choice_var = tk.StringVar(value=self.settings.get("theme", "auto"))
        ttk.Label(left, text="Theme", background="#131b2e", font=("Arial", 10, "bold")).pack(anchor="w")
        for val, title in (("auto", "Auto — follow my computer's setting"), ("dark", "Dark"), ("light", "Light")):
            ttk.Radiobutton(left, text=title, value=val, variable=self.theme_choice_var,
                            command=lambda: self.set_theme_choice(self.theme_choice_var.get())).pack(anchor="w", pady=1)
        form = ttk.Frame(left, style="Card.TFrame")
        form.pack(fill="x", pady=(10, 4))
        ttk.Label(form, text="Maximum quality:", background="#131b2e").grid(row=0, column=0, sticky="w", pady=3)
        self.quality_var = tk.StringVar(value={"best": "Best available", "1080": "1080p", "720": "720p", "480": "480p",
                                               "smallest": "Smallest file"}[self.settings.get("max_quality", "best")])
        qcb = ttk.Combobox(form, textvariable=self.quality_var, values=["Best available", "1080p", "720p", "480p", "Smallest file"], state="readonly", width=18)
        qcb.grid(row=0, column=1, sticky="w", padx=6)
        qcb.bind("<<ComboboxSelected>>", lambda e: self._save_download_prefs())
        ttk.Label(form, text="Speed limit:", background="#131b2e").grid(row=1, column=0, sticky="w", pady=3)
        self.speed_var = tk.StringVar(value=self.settings.get("speed_limit") or "Unlimited")
        scb = ttk.Combobox(form, textvariable=self.speed_var, values=["Unlimited", "500K", "1M", "2M", "5M", "10M", "20M"], width=18)
        scb.grid(row=1, column=1, sticky="w", padx=6)
        scb.bind("<<ComboboxSelected>>", lambda e: self._save_download_prefs())
        scb.bind("<FocusOut>", lambda e: self._save_download_prefs())
        ttk.Label(form, text="(bytes per second, e.g. 5M = 5 MB/s)", background="#131b2e", foreground="#94a3b8").grid(row=1, column=2, sticky="w")
        self.notify_var = tk.BooleanVar(value=bool(self.settings.get("notify", True)))
        ttk.Checkbutton(left, text="🔔 Notify me when downloads finish", variable=self.notify_var, style="Card.TCheckbutton",
                        command=lambda: (self.settings.__setitem__("notify", bool(self.notify_var.get())), self.save_settings())).pack(anchor="w", pady=4)
        out_row = ttk.Frame(left, style="Card.TFrame")
        out_row.pack(fill="x", pady=(8, 2))
        ttk.Label(out_row, text="Save videos to:", background="#131b2e").pack(side="left")
        self.out_dir_lbl = tk.Label(out_row, text=self.output_base, bg="#131b2e", fg="#38bdf8", font=("Arial", 9))
        self.out_dir_lbl.pack(side="left", padx=6)
        ttk.Button(left, text="📁 Change Folder…", command=self._change_output_dir).pack(anchor="w", pady=2)
        tk.Label(left, text="Cookie files (optional, put next to this app):\n• shortmax_cookies.txt   • tiktok_cookies.txt\n"
                            "Export them with a browser extension such as 'Get cookies.txt LOCALLY'.",
                 justify="left", bg="#131b2e", fg="#94a3b8", font=("Arial", 9)).pack(anchor="w", pady=(12, 0))

        right = ttk.LabelFrame(cols, text="🩺 Engines & updates", padding=(12, 8))
        right.pack(side="left", fill="both", expand=True, padx=(6, 0))
        self.health_tree = ttk.Treeview(right, columns=("v",), show="tree headings", height=7)
        self.health_tree.heading("#0", text="Engine")
        self.health_tree.heading("v", text="Version / status")
        self.health_tree.column("#0", width=190)
        self.health_tree.column("v", width=360)
        self.health_tree.pack(fill="x")
        hb = ttk.Frame(right, style="Card.TFrame")
        hb.pack(fill="x", pady=6)
        ttk.Button(hb, text="🔄 Check Again", command=self.refresh_health).pack(side="left", padx=2)
        self.update_btn = ttk.Button(hb, text="⬆️ Update yt-dlp (+ impersonation)", style="Accent.TButton", command=self.update_ytdlp)
        self.update_btn.pack(side="left", padx=2)
        tk.Label(right, text="Sites change often; most 'it stopped working' problems are fixed by updating yt-dlp.",
                 bg="#131b2e", fg="#94a3b8", font=("Arial", 9), wraplength=520, justify="left").pack(anchor="w")
        self.update_log = tk.Text(right, height=9, bg="#0f172a", fg="#cbd5e1", insertbackground="#ffffff", font=("Courier", 9),
                                  relief="flat", highlightthickness=1, highlightbackground="#1e293b")
        self.update_log.pack(fill="both", expand=True, pady=(6, 0))


    # =========================================================================
    # 🔍 FIND BY IMAGE (v1.9.3): upload / paste a picture → read its title → search the sites
    # → show IMAGE matches (poster looks the same) and NAME matches, each with its direct link
    # =========================================================================
    FIND_THUMB = (120, 170)

    # ---------------------------------------------------------------- reading the title (OCR)
    def ocr_image_text(self, path):
        """Text in the picture: rapidocr (if installed) → Windows built-in OCR → '' (you can type the name)."""
        try:
            from rapidocr_onnxruntime import RapidOCR
            if not hasattr(self, "_rapidocr"):
                self._rapidocr = RapidOCR()
            res, _ = self._rapidocr(path)
            lines = [r[1] for r in (res or []) if r[2] > 0.5]
            if lines:
                return lines
        except Exception:
            pass
        if sys.platform == "win32":
            png = os.path.join(self.base_dir, ".find_cache", "_ocr_input.png")
            os.makedirs(os.path.dirname(png), exist_ok=True)
            self.run_ffmpeg(["ffmpeg", "-y", "-i", path, "-vf", "scale='min(1600,iw)':-2", "-frames:v", "1", png])
            ps = r'''
$ErrorActionPreference = 'Stop'
Add-Type -AssemblyName System.Runtime.WindowsRuntime
$null = [Windows.Storage.StorageFile, Windows.Storage, ContentType = WindowsRuntime]
$null = [Windows.Media.Ocr.OcrEngine, Windows.Foundation, ContentType = WindowsRuntime]
$null = [Windows.Graphics.Imaging.BitmapDecoder, Windows.Graphics, ContentType = WindowsRuntime]
$asTask = ([System.WindowsRuntimeSystemExtensions].GetMethods() | ? { $_.Name -eq 'AsTask' -and $_.GetParameters().Count -eq 1 -and $_.GetParameters()[0].ParameterType.Name -eq 'IAsyncOperation`1' })[0]
function Await($op, $type) { $t = $asTask.MakeGenericMethod($type).Invoke($null, @($op)); $t.Wait(-1) | Out-Null; $t.Result }
$file = Await ([Windows.Storage.StorageFile]::GetFileFromPathAsync($env:ANK_OCR_FILE)) ([Windows.Storage.StorageFile])
$stream = Await ($file.OpenAsync([Windows.Storage.FileAccessMode]::Read)) ([Windows.Storage.Streams.IRandomAccessStream])
$decoder = Await ([Windows.Graphics.Imaging.BitmapDecoder]::CreateAsync($stream)) ([Windows.Graphics.Imaging.BitmapDecoder])
$bmp = Await ($decoder.GetSoftwareBitmapAsync()) ([Windows.Graphics.Imaging.SoftwareBitmap])
$engine = [Windows.Media.Ocr.OcrEngine]::TryCreateFromUserProfileLanguages()
$res = Await ($engine.RecognizeAsync($bmp)) ([Windows.Media.Ocr.OcrResult])
$res.Lines | ForEach-Object { $_.Text }
'''
            try:
                env = dict(os.environ, ANK_OCR_FILE=os.path.abspath(png if os.path.exists(png) else path))
                r = subprocess.run(["powershell", "-NoProfile", "-ExecutionPolicy", "Bypass", "-Command", ps], capture_output=True,
                                   text=True, encoding="utf-8", errors="ignore", timeout=60, env=env, creationflags=0x08000000)
                lines = [ln.strip() for ln in (r.stdout or "").splitlines() if ln.strip()]
                if lines:
                    return lines
            except Exception:
                pass
        return []

    @staticmethod
    def title_from_ocr(lines):
        """Keeps the words that look like a title (drops clock, battery, EP numbers, likes…)."""
        junk = re.compile(r"^(lte|5g|4g|wifi|ep ?\d*|ep0+\w*|\d+[:.]?\d*|[0-9.,k]+|follow|share|like|more|for you|following)$", re.IGNORECASE)
        words = []
        for ln in lines:
            t = re.sub(r"[^\w'’&\- ]+", " ", ln).strip()
            if not t or junk.match(t) or len(re.sub(r"[^A-Za-z؀-ۿ]", "", t)) < 2:
                continue
            words.append(t)
        title = " ".join(words)
        title = re.sub(r"\s+", " ", title).strip()
        return title[:90]

    # ------------------------------------------------------------------- image fingerprints
    def _img_pixels(self, path, crop_expr, w, h):
        """RGB pixels (list of (r,g,b)) of a crop of the picture, resized to w×h, via FFmpeg."""
        kwargs = {"creationflags": 0x08000000} if sys.platform == "win32" else {}
        vf = (crop_expr + "," if crop_expr else "") + f"scale={w}:{h}:flags=area"
        r = subprocess.run(["ffmpeg", "-v", "error", "-i", path, "-vf", vf, "-frames:v", "1", "-f", "rawvideo", "-pix_fmt", "rgb24", "-"],
                           capture_output=True, **kwargs)
        b = r.stdout
        if len(b) < w * h * 3:
            return None
        return [(b[i], b[i + 1], b[i + 2]) for i in range(0, w * h * 3, 3)]

    @staticmethod
    def _fingerprint(px):
        gray = [0.299 * r + 0.587 * g + 0.114 * b for r, g, b in px]
        m = sum(gray) / len(gray)
        v = [x - m for x in gray]
        n = math.sqrt(sum(x * x for x in v)) or 1.0
        hist = [0] * 64
        for r, g, b in px:
            hist[(r >> 6) * 16 + (g >> 6) * 4 + (b >> 6)] += 1
        tot = float(len(px))
        return [x / n for x in v], [x / tot for x in hist]

    FIND_W, FIND_H = 18, 27   # 2:3 poster shape

    def _crops_for(self, path, query=False):
        """Poster-shaped crops: several for your picture (it may be a phone screenshot with buttons), fewer for posters."""
        crops = []
        if query:
            # a 2:3 window at several sizes and heights over the picture
            for scale in (1.0, 0.85, 0.7, 0.55):
                for ypos in (0.0, 0.25, 0.5, 0.75, 1.0):
                    crops.append(f"crop='min(iw,ih*2/3)*{scale}':'min(iw,ih*2/3)*{scale}*3/2':"
                                 f"'(iw-min(iw,ih*2/3)*{scale})/2':'(ih-min(iw,ih*2/3)*{scale}*3/2)*{ypos}'")
        else:
            crops.append("crop='min(iw,ih*2/3)':'min(iw,ih*2/3)*3/2'")
            crops.append("crop='min(iw,ih*2/3)*0.85':'min(iw,ih*2/3)*0.85*3/2'")
        out = []
        for c in crops:
            px = self._img_pixels(path, c, self.FIND_W, self.FIND_H)
            if px:
                out.append(self._fingerprint(px))
        return out

    @staticmethod
    def _similarity(a, b):
        corr = sum(x * y for x, y in zip(a[0], b[0]))                  # shapes / layout (-1..1)
        hist = sum(min(x, y) for x, y in zip(a[1], b[1]))              # colours (0..1)
        return max(0.0, 0.7 * max(0.0, corr) + 0.3 * hist)

    def image_match_score(self, query_prints, poster_path):
        cands = self._crops_for(poster_path)
        if not cands or not query_prints:
            return 0.0
        return max(self._similarity(q, c) for q in query_prints for c in cands)

    @staticmethod
    def name_score(query, title):
        import difflib
        nq = re.sub(r"[^a-z0-9؀-ۿ ]", "", (query or "").lower().replace("’", "'"))
        nt = re.sub(r"[^a-z0-9؀-ۿ ]", "", (title or "").lower().replace("’", "'"))
        if not nq or not nt:
            return 0.0
        qs, ts = set(nq.split()), set(nt.split())
        overlap = len(qs & ts) / max(1, len(qs))
        return 0.55 * overlap + 0.45 * difflib.SequenceMatcher(None, nq, nt).ratio()

    # ------------------------------------------------------------------------ site searches
    def _search_narto(self, q):
        out = []
        for host in ("narto-drama.com",):
            html = self.curl_fetch(f"https://{host}/search?lang=en-US&q={urllib.parse.quote_plus(q)}")
            if not html or self.is_browser_check_page(html):
                continue
            for m in re.finditer(r'<a\b[^>]*href=["\']([^"\']*(?:/detail/|/watch/|/movie/|/series/)[^"\']*)["\'][^>]*>(.*?)</a>', html, re.S | re.I):
                href, inner = m.group(1), m.group(2)
                img = re.search(r'<img\b[^>]*?(?:data-src|data-original|src)=["\']([^"\']+)["\'][^>]*>', inner, re.I)
                if not img:
                    continue
                alt = re.search(r'alt=(["\'])(.*?)\1', img.group(0), re.I | re.S)
                txt = re.sub(r"<[^>]+>", " ", inner)
                txt = re.sub(r"\s+", " ", txt).strip()
                title = (alt.group(2) if alt and len(alt.group(2)) > 3 else "") or txt[:90]
                prov = re.search(r'(PineDrama|ReelShort|FlareFlow|FreeReels|Melolo|Narto Drama|ShortMax|DramaBox|GoodShort|OhMyTV|NetShort)', inner, re.I)
                out.append({"site": "Narto", "title": re.sub(r"&#0?39;|&apos;", "'", title).replace("&amp;", "&"),
                            "link": urllib.parse.urljoin(f"https://{host}/", href),
                            "thumb": urllib.parse.urljoin(f"https://{host}/", img.group(1).replace("&amp;", "&")),
                            "info": prov.group(1) if prov else "narto-drama.com"})
        seen, uniq = set(), []
        for r in out:
            if r["link"] not in seen:
                seen.add(r["link"])
                uniq.append(r)
        return uniq[:40]

    def _search_dailymotion(self, q):
        url = ("https://api.dailymotion.com/videos?" + urllib.parse.urlencode(
            {"search": q, "fields": "id,title,thumbnail_360_url,url,duration,owner.screenname", "limit": 30}))
        data = json.loads(urllib.request.urlopen(urllib.request.Request(url, headers={"User-Agent": "Mozilla/5.0"}), timeout=20).read())
        return [{"site": "Dailymotion", "title": v.get("title", ""), "link": v.get("url", ""), "thumb": v.get("thumbnail_360_url", ""),
                 "info": f"{v.get('owner.screenname', '')} • {int(v.get('duration') or 0) // 60} min"} for v in data.get("list", [])]

    def _search_youtube(self, q):
        yt = self.get_yt_dlp_path()
        if not yt or not os.path.exists(yt):
            return []
        kwargs = {"creationflags": 0x08000000} if sys.platform == "win32" else {}
        r = subprocess.run([yt, "--flat-playlist", "-J", "--no-warnings", f"ytsearch20:{q}"], capture_output=True, text=True,
                           encoding="utf-8", errors="ignore", timeout=60, **kwargs)
        out = []
        for e in (json.loads(r.stdout or "{}").get("entries") or []):
            thumbs = e.get("thumbnails") or []
            th = thumbs[-1]["url"] if thumbs else f"https://i.ytimg.com/vi/{e.get('id')}/hqdefault.jpg"
            out.append({"site": "YouTube", "title": e.get("title", ""), "link": e.get("url") or f"https://www.youtube.com/watch?v={e.get('id')}",
                        "thumb": th, "info": f"{e.get('channel') or ''} • {int(e.get('duration') or 0) // 60} min"})
        return out

    # ----------------------------------------------------------------------------- the page
    def build_find_page(self):
        page = ttk.Frame(self.page_container)
        self.pages["find"] = page
        self.find_cache = os.path.join(self.base_dir, ".find_cache")
        os.makedirs(self.find_cache, exist_ok=True)
        left = tk.Frame(page, bg="#111a2c", width=300, highlightthickness=1, highlightbackground="#24324d")
        left.pack(side="left", fill="y", padx=(12, 6), pady=10)
        left.pack_propagate(False)
        tk.Label(left, text="🔍 Find by Image", font=("Arial", 14, "bold"), bg="#111a2c", fg="#f8fafc").pack(anchor="w", padx=12, pady=(12, 0))
        tk.Label(left, text="Upload or paste a picture (a poster, a TikTok screenshot…). The app reads its name, searches the sites "
                            "and shows the posters that look the same.", bg="#111a2c", fg="#94a3b8", font=("Arial", 9),
                 wraplength=270, justify="left").pack(anchor="w", padx=12, pady=(2, 8))
        row = tk.Frame(left, bg="#111a2c")
        row.pack(fill="x", padx=12)
        ttk.Button(row, text="🖼️ Choose Image…", style="Accent.TButton", command=self.find_choose_image).pack(side="left")
        ttk.Button(row, text="📋 Paste Image", command=self.find_paste_image).pack(side="left", padx=4)
        self.find_preview = tk.Label(left, bg="#0b0f19", width=220, height=300, text="No picture yet", fg="#475569")
        self.find_preview.pack(padx=12, pady=8)
        tk.Label(left, text="Name found in the picture (you can edit it):", bg="#111a2c", fg="#cbd5e1", font=("Arial", 9, "bold")).pack(anchor="w", padx=12)
        self.find_title = ttk.Entry(left)
        self.find_title.pack(fill="x", padx=12, pady=(2, 6))
        self.find_title.bind("<Return>", lambda e: self.find_start())
        self.find_sites = {}
        for key, label in (("Narto", "Narto-Drama (all providers)"), ("Dailymotion", "Dailymotion"), ("YouTube", "YouTube")):
            v = tk.BooleanVar(value=True)
            ttk.Checkbutton(left, text=label, variable=v, style="Panel.TCheckbutton").pack(anchor="w", padx=12)
            self.find_sites[key] = v
        self.find_btn = ttk.Button(left, text="🔎 Search Everywhere", style="Success.TButton", command=self.find_start)
        self.find_btn.pack(fill="x", padx=12, pady=(10, 4))
        tk.Label(left, text="Open the same search on:", bg="#111a2c", fg="#94a3b8", font=("Arial", 9)).pack(anchor="w", padx=12, pady=(8, 2))
        r2 = tk.Frame(left, bg="#111a2c")
        r2.pack(fill="x", padx=12)
        for txt, url in (("TikTok", "https://www.tiktok.com/search?q={q}"), ("Shortmax", "https://www.google.com/search?q=site%3Ashorttw.live+{q}"),
                         ("Google", "https://www.google.com/search?tbm=isch&q={q}")):
            ttk.Button(r2, text=txt, width=8, command=lambda u=url: webbrowser.open(u.format(q=urllib.parse.quote_plus(self.find_title.get().strip())))).pack(side="left", padx=1)
        self.find_status = tk.Label(left, text="", bg="#111a2c", fg="#fbbf24", font=("Arial", 9), wraplength=270, justify="left")
        self.find_status.pack(anchor="w", padx=12, pady=8)

        right = tk.Frame(page, bg="#0b0f19")
        right.pack(side="left", fill="both", expand=True, padx=(0, 8), pady=10)
        self.find_canvas = tk.Canvas(right, bg="#0b0f19", highlightthickness=0)
        vs = ttk.Scrollbar(right, orient="vertical", command=self.find_canvas.yview)
        self.find_canvas.configure(yscrollcommand=vs.set)
        vs.pack(side="right", fill="y")
        self.find_canvas.pack(side="left", fill="both", expand=True)
        self.find_inner = tk.Frame(self.find_canvas, bg="#0b0f19")
        self._find_win = self.find_canvas.create_window(0, 0, window=self.find_inner, anchor="nw")
        self.find_inner.bind("<Configure>", lambda e: self.find_canvas.configure(scrollregion=self.find_canvas.bbox("all")))
        self.find_canvas.bind("<Configure>", lambda e: (self.find_canvas.itemconfigure(self._find_win, width=e.width), self._find_relayout(e.width)))
        for w in (self.find_canvas, self.find_inner):
            w.bind("<MouseWheel>", lambda e: self.find_canvas.yview_scroll(int(-e.delta / 120) or (-1 if e.delta > 0 else 1), "units"))
            w.bind("<Button-4>", lambda e: self.find_canvas.yview_scroll(-3, "units"))
            w.bind("<Button-5>", lambda e: self.find_canvas.yview_scroll(3, "units"))
        self.find_image_path = ""
        self._find_imgs = []
        self._find_results = None
        self._find_cols = 0
        tk.Label(self.find_inner, text="Results appear here:\n🖼️ Image matches — posters that look like your picture\n"
                                       "🔤 Name matches — titles like the name in your picture\n\nClick any result to open its play page in your browser.",
                 bg="#0b0f19", fg="#64748b", font=("Arial", 11), justify="left").pack(anchor="w", padx=20, pady=40)

    def find_choose_image(self):
        p = filedialog.askopenfilename(title="Choose a picture", filetypes=[("Images", "*.png *.jpg *.jpeg *.webp *.bmp *.gif"), ("All", "*.*")])
        if p:
            self.find_set_image(p)

    def find_paste_image(self):
        out = os.path.join(self.find_cache, f"pasted_{int(time.time())}.png")
        try:
            if sys.platform == "win32":
                ps = ("Add-Type -AssemblyName System.Windows.Forms; $i=[System.Windows.Forms.Clipboard]::GetImage(); "
                      f"if($i){{$i.Save('{out}',[System.Drawing.Imaging.ImageFormat]::Png)}}")
                subprocess.run(["powershell", "-NoProfile", "-STA", "-Command", ps], timeout=20, creationflags=0x08000000)
            elif sys.platform == "darwin":
                subprocess.run(["osascript", "-e", f'set f to open for access POSIX file "{out}" with write permission',
                                "-e", "write (the clipboard as «class PNGf») to f", "-e", "close access f"], timeout=20)
            else:
                with open(out, "wb") as f:
                    subprocess.run(["xclip", "-selection", "clipboard", "-t", "image/png", "-o"], stdout=f, timeout=20)
        except Exception:
            pass
        if os.path.exists(out) and os.path.getsize(out) > 100:
            self.find_set_image(out)
        else:
            messagebox.showinfo("Paste image", "There is no picture in the clipboard. Copy an image (or take a screenshot) first.")

    def find_set_image(self, path):
        self.find_image_path = path
        prev = os.path.join(self.find_cache, "_preview.png")
        self.run_ffmpeg(["ffmpeg", "-y", "-i", path, "-vf", "scale=220:300:force_original_aspect_ratio=decrease", "-frames:v", "1", prev])
        try:
            self._find_prev_img = tk.PhotoImage(file=prev)
            self.find_preview.config(image=self._find_prev_img, text="", width=220, height=300)
        except Exception:
            pass
        self.find_status.config(text="Reading the name in the picture…")
        self.find_title.delete(0, tk.END)

        def work():
            lines = self.ocr_image_text(path)
            title = self.title_from_ocr(lines)

            def done():
                self.find_title.delete(0, tk.END)
                self.find_title.insert(0, title)
                if title:
                    self.find_status.config(text=f"Found the name: “{title}”. Fix it if needed, then press Search.")
                    self.find_start()
                else:
                    self.find_status.config(text="Couldn't read a name in the picture. Type the name (even part of it) and press Search — "
                                                 "the picture is still used to rank the posters.")
            self.root.after(0, done)
        threading.Thread(target=work, daemon=True).start()

    def find_start(self):
        q = self.find_title.get().strip()
        if not q:
            messagebox.showinfo("Find", "Type the name (or part of it) first.")
            return
        self.find_btn.config(state="disabled")
        self.find_status.config(text="Searching the sites…")
        threading.Thread(target=self._find_worker, args=(q,), daemon=True).start()

    def _find_worker(self, q):
        say = lambda t: self.root.after(0, lambda: self.find_status.config(text=t))
        results, errors = [], []
        queries = [q]
        words = q.split()
        if len(words) > 4:
            queries.append(" ".join(words[:4]))
        for site, fn in (("Narto", self._search_narto), ("Dailymotion", self._search_dailymotion), ("YouTube", self._search_youtube)):
            if not self.find_sites[site].get():
                continue
            for qq in queries:
                say(f"Searching {site} for “{qq}”…")
                try:
                    results += fn(qq)
                except Exception as e:
                    errors.append(f"{site}: {e}")
        seen, uniq = set(), []
        for r in results:
            if r["link"] and r["link"] not in seen:
                seen.add(r["link"])
                uniq.append(r)
        query_prints = self._crops_for(self.find_image_path, query=True) if self.find_image_path else []
        import hashlib
        for k, r in enumerate(uniq, 1):
            say(f"Comparing posters with your picture… {k}/{len(uniq)}")
            r["name_score"] = self.name_score(q, r["title"])
            r["img_score"] = 0.0
            r["thumb_png"] = ""
            if not r.get("thumb"):
                continue
            raw = os.path.join(self.find_cache, hashlib.md5(r["thumb"].encode()).hexdigest()[:16])
            png = raw + ".png"
            try:
                if not os.path.exists(raw):
                    req = urllib.request.Request(r["thumb"], headers={"User-Agent": self.NARTO_UA, "Referer": r["link"]})
                    with open(raw, "wb") as f:
                        f.write(urllib.request.urlopen(req, timeout=15).read(6 * 1024 * 1024))
                if not os.path.exists(png):
                    self.run_ffmpeg(["ffmpeg", "-y", "-i", raw, "-vf", f"scale={self.FIND_THUMB[0]}:{self.FIND_THUMB[1]}:force_original_aspect_ratio=increase,"
                                     f"crop={self.FIND_THUMB[0]}:{self.FIND_THUMB[1]}", "-frames:v", "1", png])
                r["thumb_png"] = png if os.path.exists(png) else ""
                if query_prints:
                    r["img_score"] = self.image_match_score(query_prints, raw)
            except Exception:
                pass
        self._find_results = (q, uniq, bool(query_prints))
        msg = f"{len(uniq)} results." + (f"  (Not searched: {'; '.join(errors)[:160]})" if errors else "")
        if not any(r["site"] == "Narto" for r in uniq) and self.find_sites["Narto"].get():
            msg += "  Narto gave no results — if it shows a browser check, open narto-drama.com once in Edge/Firefox."
        self.root.after(0, lambda: (self.find_status.config(text=msg), self.find_btn.config(state="normal"), self._find_render()))

    def _find_relayout(self, width):
        cols = max(1, (width - 20) // 236)
        if cols != self._find_cols:
            self._find_cols = cols
            if self._find_results:
                self._find_render()

    def _find_render(self):
        for w in self.find_inner.winfo_children():
            w.destroy()
        self._find_imgs = []
        q, res, has_img = self._find_results
        cols = max(1, self._find_cols or 5)
        img_hits = sorted([r for r in res if r["img_score"] >= 0.65], key=lambda r: -r["img_score"])[:12] if has_img else []
        name_hits = sorted([r for r in res if r["name_score"] >= 0.35], key=lambda r: -r["name_score"])[:30]
        sections = []
        if has_img:
            sections.append(("🖼️ Image matches — posters that look like your picture", img_hits, "img_score",
                             "No poster looks like your picture yet — check the name matches below."))
        sections.append((f"🔤 Name matches — “{q}”", name_hits, "name_score", "No titles like this name were found."))
        for title, items, key, empty in sections:
            tk.Label(self.find_inner, text=title, bg="#0b0f19", fg="#38bdf8", font=("Arial", 12, "bold")).pack(anchor="w", padx=10, pady=(12, 4))
            grid = tk.Frame(self.find_inner, bg="#0b0f19")
            grid.pack(fill="x", padx=6)
            if not items:
                tk.Label(grid, text=empty, bg="#0b0f19", fg="#64748b", font=("Arial", 10)).grid(row=0, column=0, padx=10, sticky="w")
            for k, r in enumerate(items):
                self._find_card(grid, r, key).grid(row=k // cols, column=k % cols, padx=6, pady=6, sticky="n")
        if getattr(self, "_theme_now", "dark") == "light":
            self._remap_tree(self.find_inner, True)
        self.find_canvas.yview_moveto(0)

    def _find_card(self, parent, r, key):
        site_col = {"Narto": "#a855f7", "Dailymotion": "#38bdf8", "YouTube": "#f43f5e"}.get(r["site"], "#10b981")
        card = tk.Frame(parent, bg="#131b2e", highlightthickness=2 if key == "img_score" else 1,
                        highlightbackground=site_col if key == "img_score" else "#24324d", cursor="hand2")
        img = None
        if r.get("thumb_png"):
            try:
                img = tk.PhotoImage(file=r["thumb_png"])
            except Exception:
                img = None
        self._find_imgs.append(img)
        pic = tk.Label(card, image=img, bg="#0b0f19", width=self.FIND_THUMB[0], height=self.FIND_THUMB[1]) if img else \
            tk.Label(card, text="(no picture)", bg="#0b0f19", fg="#475569", width=16, height=10)
        pic.pack(padx=5, pady=(5, 2))
        tk.Label(card, text=f" {r['site']} ", bg=site_col, fg="#ffffff", font=("Arial", 8, "bold")).pack(anchor="w", padx=6)
        tk.Label(card, text=r["title"][:70], bg="#131b2e", fg="#f8fafc", font=("Arial", 9, "bold"), wraplength=self.FIND_THUMB[0] + 6,
                 justify="left").pack(anchor="w", padx=6)
        pct = int(round(r[key] * 100))
        extra = f"🖼️ looks {pct}% alike" if key == "img_score" else f"🔤 name {pct}% match"
        tk.Label(card, text=f"{extra}\n{r.get('info', '')[:40]}", bg="#131b2e", fg="#94a3b8", font=("Arial", 8), justify="left").pack(anchor="w", padx=6)
        link = tk.Label(card, text=r["link"].replace("https://", "")[:34] + "…", bg="#131b2e", fg="#60a5fa", font=("Arial", 8, "underline"), cursor="hand2")
        link.pack(anchor="w", padx=6)
        row = tk.Frame(card, bg="#131b2e")
        row.pack(fill="x", padx=4, pady=(2, 6))
        ttk.Button(row, text="▶ Open", style="Accent.TButton", width=7, command=lambda: webbrowser.open(r["link"])).pack(side="left")
        ttk.Button(row, text="⬇️", width=3, command=lambda: self._find_download(r)).pack(side="left", padx=2)
        ttk.Button(row, text="📋", width=3, command=lambda: (self.root.clipboard_clear(), self.root.clipboard_append(r["link"]),
                                                          self.find_status.config(text="Link copied."))).pack(side="left")
        for w in (card, pic, link):
            w.bind("<Button-1>", lambda e: webbrowser.open(r["link"]))
        for w in [card] + list(card.winfo_children()):
            w.bind("<MouseWheel>", lambda e: self.find_canvas.yview_scroll(int(-e.delta / 120) or (-1 if e.delta > 0 else 1), "units"), add="+")
            w.bind("<Button-4>", lambda e: self.find_canvas.yview_scroll(-3, "units"), add="+")
            w.bind("<Button-5>", lambda e: self.find_canvas.yview_scroll(3, "units"), add="+")
        pic._help = ("Open this result", f"{r['title']}\n{r['site']} — {r.get('info', '')}\n{r['link']}\n\nClick to open the play page in your browser.")
        return card

    def _find_download(self, r):
        target = {"Narto": ("url_entry7", 2), "Dailymotion": ("url_entry5", 3), "YouTube": ("url_entry3", 5)}.get(r["site"], ("url_entry3", 5))
        entry = getattr(self, target[0])
        entry.delete(0, tk.END)
        entry.insert(0, r["link"])
        self.show_page("home")
        try: self.home_tabs.select(target[1])
        except Exception: pass
        self.update_status(f"Link ready in the {r['site']} tab — press its Download button (or ➕ Add to Queue).", "green")

    def _save_download_prefs(self):
        self.settings["max_quality"] = {"Best available": "best", "1080p": "1080", "720p": "720", "480p": "480",
                                        "Smallest file": "smallest"}.get(self.quality_var.get(), "best")
        sp = self.speed_var.get().strip()
        self.settings["speed_limit"] = "" if sp.lower().startswith("unlim") or not sp else sp.upper().replace(" ", "")
        self.save_settings()

    def _change_output_dir(self):
        d = filedialog.askdirectory(initialdir=self.output_base, title="Where should finished videos go?")
        if d:
            os.makedirs(d, exist_ok=True)
            self.output_base = d
            self.last_output_folder = d
            self.settings["output_dir"] = d
            self.save_settings()
            self.out_dir_lbl.config(text=d)

    def refresh_health(self):
        self.health_tree.delete(*self.health_tree.get_children())
        self.health_tree.insert("", "end", text="Checking…", values=("",))

        def work():
            rows = self.engine_versions()

            def show():
                self.health_tree.delete(*self.health_tree.get_children())
                for name, val in rows:
                    ok = not any(w in val for w in ("not found", "not working", "missing"))
                    self.health_tree.insert("", "end", text=f"{'✅' if ok else '⚠️'}  {name}", values=(val,))
            self.root.after(0, show)
        threading.Thread(target=work, daemon=True).start()

    def update_ytdlp(self):
        cmd = self.ytdlp_update_command()
        self.update_btn.config(state="disabled")
        self.update_log.delete("1.0", tk.END)
        self.update_log.insert(tk.END, "$ " + " ".join(cmd) + "\n")

        def work():
            kwargs = {"creationflags": 0x08000000} if sys.platform == "win32" else {}
            try:
                proc = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, encoding="utf-8",
                                        errors="ignore", bufsize=1, **kwargs)
                for line in proc.stdout:
                    self.root.after(0, lambda l=line: (self.update_log.insert(tk.END, l), self.update_log.see(tk.END)))
                rc = proc.wait()
            except Exception as e:
                rc = -1
                self.root.after(0, lambda: self.update_log.insert(tk.END, f"\n{e}\n"))
            self.root.after(0, lambda: (self.update_log.insert(tk.END, "\n✅ Up to date.\n" if rc == 0 else f"\n⚠️ Update failed (code {rc}).\n"),
                                        self.update_btn.config(state="normal"), self.refresh_health()))
        threading.Thread(target=work, daemon=True).start()

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
        yt_dlp_cmd = self.with_global_args(yt_dlp_cmd)
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
        self._current_dl_url = ""
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
            # Stable folder (not dated) so a stopped or crashed bulk run resumes where it left off
            temp_dir = os.path.join(self.output_base, "_resume", re.sub(r'[\\/:*?"<>|]+', "_", series_folder_name))
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
                if self.is_valid_video_file(file_name):
                    downloaded_files.append(file_name)
                    last_saved_ep = episode
                    self.log_message(f"Resume: Link {episode} already downloaded, skipping.")
                    episode += 1
                    continue

                max_retries = 2
                success = False
                err = ""

                for attempt in range(max_retries):
                    if self.stop_flag:
                        break

                    succ, stderr = self.download_tiktok_one(yt_dlp_path, url, file_name, accel_args)

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

            ok, msg = self.merge_clips_uniform(downloaded_files, final_output, "TikTok merge")

            if not ok:
                self.log_message(f"TikTok MERGE ERROR:\n{msg}")
                self.update_status("Merge failed — the downloaded clips are kept for a retry. Check log.", "#f43f5e")
                self.reset_buttons()
                return
            for file in downloaded_files:
                try: os.remove(file)
                except: pass
            try: os.rmdir(temp_dir)
            except: pass

            self.update_status(f"Success! Bulk Merged up to Ep {last_saved_ep}. {msg}.", "#10b981")
            self.log_message(f"COMPLETED: Saved to {final_output} ({msg})")

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

        if self.redirect_wrong_tab(raw_url, source):
            return
        url = self.sanitize_url(raw_url)
        if not self.confirm_not_duplicate(url):
            return
        self._current_dl_url = url
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

    # v1.9.2: a link pasted into the wrong site tab is offered to the right tab instead of failing
    LINK_SITES = [("shortmax", 1, 0, "Shortmax"), ("narto", 2, 1, "Narto (Original)"), ("tiktok.com", 4, 4, "TikTok"),
                  ("dailymotion.com", 5, 3, "Dailymotion"), ("dai.ly", 5, 3, "Dailymotion")]
    SOURCE_ENTRY = {1: "url_entry1", 2: "url_entry2", 7: "url_entry7", 5: "url_entry5", 4: "url_entry4", 3: "url_entry3"}

    def redirect_wrong_tab(self, raw_url, source):
        """Returns True when the link belongs to another tab (the download is then started there, or cancelled)."""
        host = urllib.parse.urlparse(raw_url.strip()).netloc.lower()
        for key, target, tab_index, name in self.LINK_SITES:
            if key in host:
                if target == source or (target == 2 and source == 7):
                    return False
                if not messagebox.askyesno("Wrong tab", f"This is a {name} link, but you pressed the button of another site.\n\n"
                                                        f"Download it in the {name} tab instead?"):
                    return True
                entry = getattr(self, self.SOURCE_ENTRY[target])
                entry.delete(0, tk.END)
                entry.insert(0, raw_url.strip())
                try: self.home_tabs.select(tab_index)
                except Exception: pass
                self.start_thread(target)
                return True
        return False

    def start_narto_claude_thread(self):
        self.stop_flag = False

        if self.current_run_log:
            self.previous_runs_log = self.current_run_log + "\n\n" + self.previous_runs_log
            self.current_run_log = ""

        raw_url = self.url_entry7.get().strip()
        if not raw_url:
            messagebox.showerror("Error", "Please enter a narto-drama.com watch URL")
            return

        if self.redirect_wrong_tab(raw_url, 7):
            return
        url = self.sanitize_url(raw_url)
        if not self.confirm_not_duplicate(url):
            return
        self._current_dl_url = url
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
        cmd = self.with_global_args(cmd)
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
                done_file = os.path.join(temp_dir, f"ep_{ep:03d}.mp4")
                if self.is_valid_video_file(done_file):
                    self.log_message(f"Narto Claude: Resume — Episode {ep} was already downloaded, skipped.")
                    return "ok"
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
        if self.settings.get("speed_limit"):
            cmd.append(f"--max-overall-download-limit={self.settings['speed_limit']}")
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
        c = self.theme_fg(color_map.get(color, color))
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
        body = res.stdout if res.returncode == 0 else ""
        # v1.9.2: narto-drama.com now shows a "Checking your browser..." page to programs. Use YOUR browser's
        # session (the cookies your browser gets after it passes the check), then ask again once.
        if self.is_browser_check_page(body) and not getattr(self, "_in_gate_retry", False):
            self._in_gate_retry = True
            try:
                if self.prepare_site_cookies(target_url):
                    res = subprocess.run(cmd, capture_output=True, text=True, encoding="utf-8", errors="ignore", **kwargs)
                    body = res.stdout if res.returncode == 0 else ""
                if self.is_browser_check_page(body):
                    self.report_browser_check(target_url)
            finally:
                self._in_gate_retry = False
        return body

    # ------------------------------------------------------------------ v1.9.2: site browser checks
    @staticmethod
    def is_browser_check_page(body):
        if not body or len(body) > 20000:
            return False
        low = body.lower()
        return ("checking your browser" in low or "challenge-platform" in low or "just a moment" in low) and \
               ("location.reload" in low or "cf-chl" in low or "challenge-platform" in low)

    def _merge_netscape_cookies(self, src_text, domain_key):
        """Adds the site's cookies from a cookies.txt export into the app's cookie jar (replacing older ones)."""
        new = {}
        for ln in src_text.splitlines():
            parts = ln.split("\t")
            if len(parts) >= 7 and domain_key in parts[0].lower():
                new[(parts[0].replace("#HttpOnly_", "").lower(), parts[5])] = ln.strip()
        if not new:
            return 0
        kept = []
        try:
            for ln in open(self.cookie_jar_file, encoding="utf-8", errors="ignore"):
                parts = ln.rstrip("\n").split("\t")
                if len(parts) >= 7 and (parts[0].replace("#HttpOnly_", "").lower(), parts[5]) in new:
                    continue
                kept.append(ln.rstrip("\n"))
        except OSError:
            kept = ["# Netscape HTTP Cookie File"]
        if not kept or not kept[0].startswith("# Netscape"):
            kept.insert(0, "# Netscape HTTP Cookie File")
        with open(self.cookie_jar_file, "w", encoding="utf-8") as f:
            f.write("\n".join(kept + list(new.values())) + "\n")
        return len(new)

    def prepare_site_cookies(self, url):
        """Loads your browser's cookies for this site: from an exported file next to the app, or straight from
        your browser through yt-dlp (Edge / Firefox / Chrome / Brave / Safari). Returns True if any were found."""
        host = urllib.parse.urlparse(url).netloc.lower().split(":")[0]
        key = host[4:] if host.startswith("www.") else host
        short = key.split(".")[0]
        for name in (f"{short}_cookies_browser.txt", f"{key}_cookies.txt", f"{short}_browser_cookies.txt", "cookies.txt"):
            p = os.path.join(self.base_dir, name)
            if os.path.exists(p):
                n = self._merge_netscape_cookies(open(p, encoding="utf-8", errors="ignore").read(), short)
                if n:
                    self.log_message(f"{key}: using {n} cookie(s) from {name}")
                    return True
        yt = self.get_yt_dlp_path()
        if not yt or not os.path.exists(yt):
            return False
        browsers = ["edge", "firefox", "chrome", "brave", "opera"]
        if sys.platform == "darwin":
            browsers.insert(0, "safari")
        kwargs = {"creationflags": 0x08000000} if sys.platform == "win32" else {}
        tmp = os.path.join(self.base_dir, f".{short}_cookie_export.txt")
        for b in browsers:
            self.update_status(f"{key} shows a browser check — borrowing your {b.title()} session…", "orange")
            try:
                if os.path.exists(tmp):
                    os.remove(tmp)
                subprocess.run([yt, "--cookies-from-browser", b, "--cookies", tmp, "--skip-download", "--no-warnings",
                                "--ignore-errors", "--no-playlist", f"https://{host}/"], capture_output=True, text=True,
                               encoding="utf-8", errors="ignore", timeout=60, **kwargs)
                if os.path.exists(tmp):
                    n = self._merge_netscape_cookies(open(tmp, encoding="utf-8", errors="ignore").read(), short)
                    if n:
                        self.log_message(f"{key}: using {n} cookie(s) from your {b.title()} browser")
                        return True
            except Exception:
                pass
            finally:
                try: os.remove(tmp)
                except OSError: pass
        return False

    def report_browser_check(self, url):
        host = urllib.parse.urlparse(url).netloc
        if time.time() - getattr(self, "_gate_reported", 0) < 60:
            return
        self._gate_reported = time.time()
        short = host.replace("www.", "").split(".")[0]
        msg = (f"{host} is showing a 'Checking your browser…' page, so the app can't read the episode list.\n\n"
               f"Fix (1 minute):\n"
               f"1. Open {host} in Edge or Firefox and play any episode, so your browser passes the check.\n"
               f"2. Close that browser completely, then press Start again — the app borrows your browser's session.\n\n"
               f"If it still fails: with the free browser extension 'Get cookies.txt LOCALLY', export the cookies of {host} "
               f"and save the file next to Downloader.py as:\n    {short}_cookies_browser.txt")
        self.log_message(f"BROWSER CHECK on {host}: " + msg.replace("\n", " "))
        self.update_status(f"{host}: browser check — see the message / log to fix it in 1 minute.", "red")
        try:
            self.root.after(0, lambda: (messagebox.showwarning("Browser check", msg), webbrowser.open(f"https://{host}/")))
        except Exception:
            pass

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

                succ, err = self.download_tiktok_one(yt_dlp_path, url, file_name, accel_args)

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
                if source == 1 and self.is_valid_video_file(file_name):
                    cumulative_duration_sec += self.get_media_duration(file_name)
                    downloaded_files.append(file_name)
                    last_saved_ep = episode
                    self.log_message(f"Resume: Episode {episode} was already downloaded — skipped.")
                    episode += 1
                    continue
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
                            if source == 1 and ("cloudflare" in err.lower() or self.is_http_403(err)):
                                self.log_message(
                                    "Shortmax: blocked by the site's bot check (HTTP 403) — every cookie source was tried, retrying will not help.\n"
                                    "Fix: 1) ⚙️ Settings → 'Update yt-dlp (+ impersonation)'. 2) Open the series in Chrome/Edge, play an episode, "
                                    "then export the site's cookies with the 'Get cookies.txt LOCALLY' extension and save them next to Downloader.py "
                                    "as shortmax_cookies.txt. 3) Start again."
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
                        if source == 1 and ("cloudflare" in err.lower() or self.is_http_403(err)):
                            self.update_status("Shortmax blocked by its bot check (403): add shortmax_cookies.txt — see log / ℹ️.", "red")
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