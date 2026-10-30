import http.cookiejar
import importlib.util
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import threading
import time
import urllib.error
import urllib.request
import zipfile
from collections import defaultdict, deque
from urllib.parse import urlparse

import yt_dlp
from yt_dlp.utils import match_filter_func
from werkzeug.middleware.proxy_fix import ProxyFix
from flask import (Flask, after_this_request, jsonify, request, send_file,
                   send_from_directory)

app = Flask(__name__)
app.wsgi_app = ProxyFix(app.wsgi_app, x_for=1)  # baca IP asli di balik proxy
# URL website Vercel Anda, contoh: https://mediaflow.vercel.app
ORIGIN = os.environ.get("ALLOWED_ORIGIN", "").rstrip("/")
BASE = os.path.dirname(os.path.abspath(__file__))
COOKIES = os.path.join(BASE, "cookies.txt")  # opsional, format Netscape
ALLOWED = ("facebook.com", "fb.watch", "instagram.com", "tiktok.com")
IMG_EXT = ("jpg", "jpeg", "png", "webp")
SLIDE_SEC = 3       # lama tiap foto di video slideshow
VF = ("scale=1080:1920:force_original_aspect_ratio=decrease,"
      "pad=1080:1920:(ow-iw)/2:(oh-ih)/2:black,setsar=1,format=yuv420p")
MAX_MB = 150        # batas ukuran file
MAX_SEC = 600       # batas durasi media (detik)
MAX_TIME = 120      # batas waktu proses download (detik)
MAX_PHOTOS = 20     # batas jumlah foto per postingan
RATE = 40           # maks permintaan per IP per menit
MAX_JOBS = 3        # maks download berjalan bersamaan
HITS = defaultdict(deque)
JOBS = threading.BoundedSemaphore(MAX_JOBS)
VERSION = "foto-v4"
# Opsional: proxy residensial (TikTok/Instagram sering memblokir IP hosting). Contoh: http://user:pass@host:port
PROXY = os.environ.get("PROXY_URL", "")
# Set DEBUG_ERRORS=1 di host untuk menampilkan detail penyebab error di website.
DEBUG = os.environ.get("DEBUG_ERRORS") == "1"
LAST = threading.local()


def err(code, status=400, detail=None):
    if DEBUG and detail:
        return jsonify(code=code, detail=detail), status
    return jsonify(code=code), status


def clean(x, n=200):
    """Teks singkat tanpa URL, aman ditampilkan."""
    return re.sub(r"https?://\S+", "<url>", str(x)).replace("\n", " ").strip()[:n]


def classify(e, default):
    m = str(e).lower()
    if any(k in m for k in ("private", "login", "log in", "sign in", "cookies",
                            "restricted", "not available", "removed")):
        return "private"
    if any(k in m for k in ("http error 5", "unable to download webpage",
                            "timed out", "connection")):
        return "platform"
    return default


def limited():
    q, now = HITS[request.remote_addr], time.time()
    while q and now - q[0] > 60:
        q.popleft()
    if len(q) >= RATE:
        return True
    q.append(now)
    return False


def allowed_host(url):
    p = urlparse(url)
    host = (p.hostname or "").lower()
    return p.scheme in ("http", "https") and any(
        host == d or host.endswith("." + d) for d in ALLOWED)


def valid(url):
    return len(url) <= 500 and allowed_host(url)


def body():
    return request.get_json(silent=True) or {}


def ytdl_base():
    o = {"quiet": True, "noplaylist": True, "socket_timeout": 15}
    if PROXY:
        o["proxy"] = PROXY
    if os.path.exists(COOKIES):
        o["cookiefile"] = COOKIES
    return o


# ---------- foto lewat gallery-dl ----------
def gdl(*args, timeout):
    cmd = [sys.executable, "-m", "gallery_dl"]
    if PROXY:
        cmd += ["--proxy", PROXY]
    if os.path.exists(COOKIES):
        cmd += ["--cookies", COOKIES]
    return subprocess.run(cmd + list(args), capture_output=True, text=True,
                          timeout=timeout)


def text(x):
    return x if isinstance(x, str) else ""


def gdl_reason(r):
    e = (r.stderr or "").lower()
    if "no module named" in e:
        return "no_gdl"          # gallery-dl belum terpasang di server
    if any(k in e for k in ("login", "401", "403", "auth", "cookie",
                            "checkpoint", "challenge")):
        return "login"           # butuh login / cookies
    return "none"


def gdl_info(url):
    """Mengembalikan (info, alasan). info None jika tidak ada foto / gagal."""
    LAST.gdl = "timeout / gagal dijalankan"
    try:
        r = gdl("-j", "--range", f"1-{MAX_PHOTOS}", url, timeout=45)
    except Exception:
        return None, "none"
    lines = (r.stderr or "").strip().splitlines()
    LAST.gdl = clean(lines[-1]) if lines else "tidak ada foto di hasil"
    try:
        data = json.loads(r.stdout or "[]")
    except ValueError:
        data = []
    files = [e for e in data if isinstance(e, list) and len(e) >= 3
             and e[0] == 3 and isinstance(e[2], dict)]
    # i = nomor urut file di postingan (dipakai sebagai --range saat download)
    imgs = [(i + 1, e) for i, e in enumerate(files)
            if text(e[2].get("extension")).lower() in IMG_EXT]
    if not imgs:
        return None, gdl_reason(r)
    m = imgs[0][1][2]
    owner = m.get("owner") if isinstance(m.get("owner"), dict) else {}
    return {
        "title": (text(m.get("description")) or text(m.get("title"))
                  or text(m.get("caption")) or "Foto")[:120],
        "uploader": (text(m.get("username")) or text(owner.get("username"))
                     or text(m.get("uploader")) or text(m.get("author"))),
        "thumbnail": imgs[0][1][1],
        "count": len(imgs),
        "photos": [{"i": i, "u": e[1]} for i, e in imgs],
    }, ""


# ---------- foto TikTok (slideshow) dibaca langsung dari halaman ----------
UA = ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
      "(KHTML, like Gecko) Chrome/124.0 Safari/537.36")
IMG_HOSTS = (".tiktokcdn.com", ".tiktokcdn-us.com", ".tiktokcdn-eu.com",
             ".ibyteimg.com", ".byteimg.com", ".tiktokv.com", ".tiktok.com",
             ".muscdn.com")
MAX_IMG = 25 * 1024 * 1024


def is_tiktok(url):
    host = (urlparse(url).hostname or "").lower()
    return host == "tiktok.com" or host.endswith(".tiktok.com")


def ok_img(u):
    p = urlparse(u)
    host = (p.hostname or "").lower()
    return p.scheme == "https" and host.endswith(IMG_HOSTS)


class SafeRedirect(urllib.request.HTTPRedirectHandler):
    def redirect_request(self, req, fp, code, msg, headers, newurl):
        if not (allowed_host(newurl) or ok_img(newurl)):
            raise urllib.error.URLError("redirect diblokir")
        return super().redirect_request(req, fp, code, msg, headers, newurl)


def opener():
    hs = [SafeRedirect, urllib.request.HTTPCookieProcessor(http.cookiejar.CookieJar())]
    if PROXY:
        hs.append(urllib.request.ProxyHandler({"http": PROXY, "https": PROXY}))
    return urllib.request.build_opener(*hs)


def find_key(o, key):
    """Cari dict pertama yang memuat key (struktur halaman TikTok bisa berubah)."""
    if isinstance(o, dict):
        if key in o:
            return o
        for v in o.values():
            r = find_key(v, key)
            if r:
                return r
    elif isinstance(o, list):
        for v in o:
            r = find_key(v, key)
            if r:
                return r
    return None


def tiktok_photos(url):
    """Info foto dari halaman TikTok. None jika bukan slideshow / gagal."""
    LAST.tt = ""
    op = opener()

    def get(u):
        req = urllib.request.Request(u, headers={
            "User-Agent": UA, "Accept-Language": "en-US,en;q=0.9"})
        with op.open(req, timeout=15) as r:
            return r.read(3_000_000).decode("utf-8", "ignore"), r.geturl()

    try:
        html, final = get(url)
        # Slideshow: datanya ada di bentuk /video/<id>, bukan /photo/<id>.
        if "/photo/" in final:
            try:
                html, final = get(final.replace("/photo/", "/video/", 1))
            except Exception:
                pass
    except Exception as e:
        LAST.tt = "halaman gagal dibuka: " + clean(e, 80)
        return None
    m = re.search(r'<script id="(?:__UNIVERSAL_DATA_FOR_REHYDRATION__|SIGI_STATE)"[^>]*>(.*?)</script>',
                  html, re.S)
    if not m:
        LAST.tt = "data halaman tidak ada (IP server kemungkinan diblokir/captcha)"
        return None
    try:
        data = json.loads(m.group(1))
    except ValueError:
        LAST.tt = "data halaman rusak"
        return None
    item = find_key(data, "imagePost")
    if not item or not isinstance(item.get("imagePost"), dict):
        LAST.tt = "bukan postingan foto"
        return None
    photos = []
    for n, im in enumerate(item["imagePost"].get("images") or [], 1):
        urls = ((im or {}).get("imageURL") or {}).get("urlList") or []
        u = next((x for x in urls if isinstance(x, str) and ok_img(x)), None)
        if u and n <= MAX_PHOTOS:
            photos.append({"i": n, "u": u})
    if not photos:
        LAST.tt = "URL foto tidak dikenali"
        return None
    author = item.get("author") if isinstance(item.get("author"), dict) else {}
    music = item.get("music") if isinstance(item.get("music"), dict) else {}
    audio = text(music.get("playUrl"))
    return {"audio": audio if ok_img(audio) else "", "title": text(item.get("desc"))[:120] or "Foto",
            "uploader": text(author.get("uniqueId")) or text(item.get("author")),
            "thumbnail": photos[0]["u"], "count": len(photos), "photos": photos}


def fetch_one(u, base, start, default_ext="jpg"):
    """Unduh satu file dari CDN TikTok ke base.<ext>. None jika gagal."""
    if time.time() - start > MAX_TIME:
        return None
    try:
        req = urllib.request.Request(u, headers={
            "User-Agent": UA, "Referer": "https://www.tiktok.com/"})
        with opener().open(req, timeout=20) as r:
            data = r.read(MAX_IMG + 1)
    except Exception:
        return None
    if not data or len(data) > MAX_IMG:
        return None
    if data[:4] == b"\x89PNG":
        ext = "png"
    elif data[8:12] == b"WEBP":
        ext = "webp"
    elif data[:3] == b"\xff\xd8\xff":
        ext = "jpg"
    elif data[:3] == b"ID3" or data[:2] in (b"\xff\xfb", b"\xff\xf3"):
        ext = "mp3"
    else:
        ext = default_ext
    path = f"{base}.{ext}"
    with open(path, "wb") as f:
        f.write(data)
    return path


def fetch_images(photos, pick, tmp, start):
    out = []
    for p in photos:
        if pick and p["i"] not in pick:
            continue
        f = fetch_one(p["u"], os.path.join(tmp, f"foto-{p['i']}"), start)
        if f:
            out.append(f)
    return out


def ffmpeg(*args):
    r = subprocess.run(["ffmpeg", "-y", "-v", "error", *args],
                       capture_output=True, timeout=MAX_TIME)
    if r.returncode:
        raise Exception("ffmpeg gagal")


def make_slideshow(url, tmp, start):
    """Video MP4 dari semua foto (+ musik jika ada)."""
    g = tiktok_photos(url) if is_tiktok(url) else None
    files = fetch_images(g["photos"], [], tmp, start) if g else []
    if not files:
        files = gdl_photos(url, tmp)
    if not files:
        raise Exception("tidak ada foto")
    lst = os.path.join(tmp, "list.txt")
    with open(lst, "w") as f:
        for p in files:
            f.write(f"file '{p}'\nduration {SLIDE_SEC}\n")
        f.write(f"file '{files[-1]}'\n")
    cmd = ["-f", "concat", "-safe", "0", "-i", lst]
    music = (fetch_one(g["audio"], os.path.join(tmp, "music"), start, "m4a")
             if g and g.get("audio") else None)
    if music:
        cmd += ["-i", music]
    cmd += ["-vf", VF, "-r", "30", "-c:v", "libx264", "-pix_fmt", "yuv420p",
            "-t", str(SLIDE_SEC * len(files))]
    if music:
        cmd += ["-c:a", "aac", "-af", "apad"]
    out = os.path.join(tmp, "mediaflow-slideshow.mp4")
    ffmpeg(*cmd, "-movflags", "+faststart", out)
    return out


def photo_json(g):
    return jsonify(title=g["title"], uploader=g["uploader"],
                   thumbnail=g["thumbnail"], heights=[], duration=None,
                   size=None, direct_url=None, photo_only=True,
                   count=g["count"], photos=g["photos"],
                   has_audio=bool(g.get("audio")))


def gdl_photos(url, tmp, pick=None):
    rng = ",".join(map(str, pick)) if pick else f"1-{MAX_PHOTOS}"
    try:
        gdl("-D", tmp, "--range", rng, "--filesize-max",
            f"{MAX_MB}M", "--no-mtime", url, timeout=MAX_TIME)
    except Exception:
        return []
    return sorted((os.path.join(tmp, f) for f in os.listdir(tmp)
                   if f.lower().endswith(IMG_EXT)),
                  key=lambda x: [int(c) if c.isdigit() else c
                                 for c in re.split(r"(\d+)", x)])


@app.get("/")
def home():
    if os.path.exists(os.path.join(BASE, "index.html")):
        return send_from_directory(BASE, "index.html")
    return jsonify(ok=True, name="mediaflow-api")


@app.get("/api/ping")
def ping():
    return jsonify(ok=True, v=VERSION,
                   gallery_dl=importlib.util.find_spec("gallery_dl") is not None,
                   cookies=os.path.exists(COOKIES))


@app.post("/api/info")
def info():
    if limited():
        return err("rate", 429)
    url = (body().get("url") or "").strip()
    if not valid(url):
        return err("bad_link")
    LAST.tt = LAST.gdl = "-"
    if is_tiktok(url) and "/photo/" in url:
        g = tiktok_photos(url)
        if g:
            return photo_json(g)
    try:
        with yt_dlp.YoutubeDL({**ytdl_base(), "skip_download": True}) as y:
            d = y.extract_info(url, download=False)
    except Exception as e:
        # Postingan foto biasanya gagal di yt-dlp: coba TikTok langsung, lalu gallery-dl.
        g = tiktok_photos(url) if is_tiktok(url) else None
        reason = ""
        if not g:
            g, reason = gdl_info(url)
        if g:
            return photo_json(g)
        detail = (f"yt-dlp: {clean(e, 120)} | tiktok: {LAST.tt} | "
                  f"gallery-dl: {LAST.gdl}")
        if reason == "no_gdl":
            return err("no_gdl", 500, detail)
        if reason == "login" and classify(e, "") != "private":
            return err("login", 400, detail)
        return err(classify(e, "read_fail"), 400, detail)
    if (d.get("duration") or 0) > MAX_SEC:
        return err("too_long")
    fm = d.get("formats") or []
    vids = [f for f in fm if f.get("vcodec") not in (None, "none")]
    heights = sorted({f["height"] for f in vids if f.get("height")})
    muxed = [f for f in vids if f.get("url") and f.get("acodec") not in (None, "none")]
    best = muxed[-1] if muxed else None
    direct = best["url"] if best else d.get("url")
    size = None
    if best:
        size = best.get("filesize") or best.get("filesize_approx")
    size = size or d.get("filesize") or d.get("filesize_approx")
    return jsonify(title=d.get("title"), thumbnail=d.get("thumbnail"),
                   uploader=d.get("uploader"), heights=heights,
                   duration=d.get("duration"), size=size, direct_url=direct)


@app.post("/api/download")
def download():
    if limited():
        return err("rate", 429)
    b = body()
    url = (b.get("url") or "").strip()
    kind = b.get("kind", "video")
    try:
        h = int(b.get("height") or 0)
    except (TypeError, ValueError):
        h = 0
    if not valid(url) or kind not in ("video", "audio", "photo", "slideshow"):
        return err("bad_link")
    raw = b.get("pick") if isinstance(b.get("pick"), list) else []
    pick = sorted({int(x) for x in raw
                   if str(x).isdigit() and 1 <= int(x) <= MAX_PHOTOS})
    if not JOBS.acquire(blocking=False):
        return err("busy", 503)

    start = time.time()

    def hook(_):
        if time.time() - start > MAX_TIME:
            raise Exception("timeout")

    tmp = tempfile.mkdtemp()
    opts = {**ytdl_base(), "retries": 1,
            "max_filesize": MAX_MB * 1024 * 1024,
            "match_filter": match_filter_func(f"duration <= {MAX_SEC}"),
            "progress_hooks": [hook],
            "outtmpl": os.path.join(tmp, "%(id)s.%(ext)s")}
    if kind == "audio":
        opts.update(format="bestaudio/best", postprocessors=[
            {"key": "FFmpegExtractAudio", "preferredcodec": "mp3",
             "preferredquality": "192"}])
    elif kind == "video":
        opts.update(format=(f"best[height<={h}][ext=mp4]/best[height<={h}]/best"
                            if h else "best[ext=mp4]/best"))

    try:
        if kind == "slideshow":
            path = make_slideshow(url, tmp, start)
        elif kind == "photo":
            files = []
            if is_tiktok(url):
                g = tiktok_photos(url)
                if g:
                    files = fetch_images(g["photos"], pick, tmp, start)
            if not files:
                files = gdl_photos(url, tmp, pick)
            if not files:  # cadangan: gambar sampul lewat yt-dlp
                opts.update(skip_download=True, writethumbnail=True)
                with yt_dlp.YoutubeDL(opts) as y:
                    y.extract_info(url, download=True)
                files = sorted(os.path.join(tmp, f) for f in os.listdir(tmp))
            if len(files) > 1:
                path = os.path.join(tmp, "mediaflow-foto.zip")
                with zipfile.ZipFile(path, "w", zipfile.ZIP_STORED) as z:
                    for f in files:
                        z.write(f, os.path.basename(f))
            else:
                path = files[0]
        else:
            try:
                with yt_dlp.YoutubeDL(opts) as y:
                    y.extract_info(url, download=True)
                path = os.path.join(tmp, os.listdir(tmp)[0])
            except Exception:
                path = None
                if kind == "audio" and is_tiktok(url):  # musik dari slideshow foto
                    g = tiktok_photos(url)
                    if g and g.get("audio"):
                        path = fetch_one(g["audio"], os.path.join(tmp, "audio"),
                                         start, "m4a")
                        if path and not path.endswith(".mp3"):
                            try:  # samakan formatnya jadi MP3
                                mp3 = os.path.join(tmp, "mediaflow-audio.mp3")
                                ffmpeg("-i", path, "-vn", "-c:a", "libmp3lame",
                                       "-q:a", "2", mp3)
                                path = mp3
                            except Exception:
                                pass
                if not path:
                    raise
        if os.path.getsize(path) > MAX_MB * 1024 * 1024:
            raise Exception("too big")
    except Exception as e:
        shutil.rmtree(tmp, ignore_errors=True)
        return err(classify(e, "dl_fail"))
    finally:
        JOBS.release()

    @after_this_request
    def cleanup(resp):
        shutil.rmtree(tmp, ignore_errors=True)
        return resp

    return send_file(path, as_attachment=True)


FB_HITS = defaultdict(deque)


def fb_limited():
    """Maks 5 pesan per jam per IP agar form tidak jadi spam."""
    q, now = FB_HITS[request.remote_addr], time.time()
    while q and now - q[0] > 3600:
        q.popleft()
    if len(q) >= 5:
        return True
    q.append(now)
    return False


def post_json(url, data):
    try:
        req = urllib.request.Request(
            url, data=json.dumps(data).encode(),
            headers={"Content-Type": "application/json", "User-Agent": "mediaflow"})
        with urllib.request.urlopen(req, timeout=10) as r:
            return 200 <= r.status < 300
    except Exception:
        return False


def notify(msg):
    """Kirim ke Discord dan/atau Telegram jika variabel lingkungannya diisi."""
    sent = False
    hook = os.environ.get("DISCORD_WEBHOOK_URL", "")
    if hook.startswith(("https://discord.com/api/webhooks/",
                        "https://discordapp.com/api/webhooks/")):
        sent |= post_json(hook, {"content": msg[:1900],
                                 "allowed_mentions": {"parse": []}})
    tok = os.environ.get("TELEGRAM_BOT_TOKEN", "")
    chat = os.environ.get("TELEGRAM_CHAT_ID", "")
    if tok and chat:
        sent |= post_json(f"https://api.telegram.org/bot{tok}/sendMessage",
                          {"chat_id": chat, "text": msg[:3500]})
    return sent


@app.post("/api/feedback")
def feedback():
    if limited() or fb_limited():
        return err("rate", 429)
    b = body()
    msg = (b.get("message") or "").strip()[:1000]
    contact = (b.get("contact") or "").strip()[:100]
    if len(msg) < 5:
        return err("short")
    # Hanya pesan & kontak opsional. URL pengguna tidak ikut disimpan.
    notify(f"MEDIAFLOW feedback\nKontak: {contact or '-'}\n\n{msg}")
    line = (f"{time.strftime('%Y-%m-%d %H:%M')} | {contact} | "
            f"{msg.replace(chr(10), ' ')}")
    print("FEEDBACK:", line, flush=True)  # terlihat di log host
    try:
        with open(os.path.join(BASE, "feedback.txt"), "a", encoding="utf-8") as f:
            f.write(line + "\n")
    except OSError:
        pass
    return jsonify(ok=True)


if __name__ == "__main__":
    app.run(host="0.0.0.0", port=int(os.environ.get("PORT", 5000)))
