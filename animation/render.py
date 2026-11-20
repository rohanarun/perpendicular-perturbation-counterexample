import math as m, json, subprocess
from PIL import Image, ImageDraw, ImageFont
from functools import lru_cache
from pathlib import Path

W, H = 1280, 720
FPS = 24
bg = "#102C30"
ink = "#F7EFE1"
muted = "#B4C5BF"
grid = "#375153"
gold = "#FFC76F"
teal = "#66E1D0"
coral = "#FF9783"
fontdir = Path("/System/Library/Fonts/Supplemental")


@lru_cache(None)
def font(n, style="sans"):
    names = {
        "sans": ("Arial.ttf", "DejaVuSans.ttf"),
        "bold": ("Arial Bold.ttf", "DejaVuSans-Bold.ttf"),
        "serif": ("Georgia.ttf", "DejaVuSerif.ttf"),
        "ital": ("Georgia Italic.ttf", "DejaVuSerif-Italic.ttf"),
    }
    original, fallback = names[style]
    return ImageFont.truetype(
        str(fontdir / original) if (fontdir / original).is_file() else fallback, n
    )


def txt(x, y, s, n=24, c=ink, style="sans", anchor="la"):
    d.text((x, y), s, font=font(n, style), fill=c, anchor=anchor, stroke_width=0)


def line(pts, c=grid, w=2):
    d.line(pts, fill=c, width=w, joint="curve")


def dot(pt, r=7, c=ink):
    x, y = pt
    d.ellipse((x - r, y - r, x + r, y + r), fill=c)


def clamp(x):
    return max(0, min(1, x))


def ease(x):
    x = clamp(x)
    return x * x * (3 - 2 * x)


def blend(a, b, u):
    return tuple(x + (y - x) * u for x, y in zip(a, b))


def path(fun, N=180):
    return [fun(i / N) for i in range(N + 1)]


def boundary(x, y, r, shape):
    pts = []
    for i in range(361):
        a = i * m.pi / 180
        u, v = m.cos(a), m.sin(a)
        read = [1, (0.8 * u * u + 1.2 * v * v) ** 0.5, 0.8 * abs(u + v)]
        s = max(read) if shape == "norm" else read[{"disk": 0, "ellipse": 1}[shape]]
        pts.append((x + r * u / s, y - r * v / s))
    return pts


def arcrow(u):
    return [
        blend(
            (123 + 82 * i, 405),
            (
                369 + 305 * m.sin((i - 3) * 0.25),
                460 - 305 * (1 - m.cos((i - 3) * 0.25)),
            ),
            u,
        )
        for i in range(7)
    ]


def rows(x, y, lines):
    for i, (s, c) in enumerate(lines):
        txt(x, y + 47 * i, s, 26, c)


def key(x, y, c, s):
    line([(x, y + 11), (x + 27, y + 11)], c, 4)
    txt(x + 37, y, s, 19, muted)


def circle(x, y, r, c):
    d.ellipse((x - r, y - r, x + r, y + r), outline=c, width=2)


chapters = json.loads(Path(__file__).with_name("chapters.json").read_text())
times = [(c["start"], c["end"]) for c in chapters]
duration = times[-1][1]
titles = [
    "Can these dots be straightened?",
    "A ruler and an arc can agree",
    "A different rule for distance",
    "Which circle counts?",
    "What parallel slides preserve",
    "One norm. Every size from four.",
]
subs = [
    "The perpendicular perturbation conjecture",
    "Equal distances depend on the gap between marks.",
    "The unit ball is the overlap of three regions.",
    "Three points determine the relevant norm circle.",
    "Project onto a line perpendicular to the slides.",
    "A counterexample to Fish et al., Conjecture 6.5",
]
out = subprocess.Popen(
    [
        "ffmpeg",
        "-v",
        "error",
        "-y",
        "-f",
        "rawvideo",
        "-pix_fmt",
        "rgb24",
        "-s",
        f"{W}x{H}",
        "-r",
        str(FPS),
        "-i",
        "-",
        "-i",
        "voice.wav",
        "-f",
        "ffmetadata",
        "-i",
        "chapters.ffmeta",
        "-map",
        "0:v:0",
        "-map",
        "1:a:0",
        "-map_metadata",
        "2",
        "-map_chapters",
        "2",
        "-c:v",
        "libx264",
        "-preset",
        "fast",
        "-crf",
        "19",
        "-pix_fmt",
        "yuv420p",
        "-c:a",
        "aac",
        "-b:a",
        "160k",
        "-af",
        "loudnorm=I=-16:TP=-1.5:LRA=9",
        "-movflags",
        "+faststart",
        "conjecture65-explained.mp4",
    ],
    stdin=subprocess.PIPE,
)
for frame in range(m.ceil(duration * FPS)):
    now = frame / FPS
    i = next((i for i, (_, end) in enumerate(times) if now < end), 5)
    start, end = times[i]
    u = clamp((now - start) / (end - start))
    im = Image.new("RGB", (W, H), bg)
    d = ImageDraw.Draw(im)
    txt(64, 45, titles[i], 55, ink, "serif")
    txt(66, 125, subs[i], 28, muted)
    line([(65, 186), (1215, 186)], grid)
    line([(65, 620), (1215, 620)], grid)
    txt(65, 655, "Rohan Arun  /  Super Powers AI", 22, muted)
    txt(1215, 655, "Conjecture 6.5  ·  Fish et al.", 21, muted, anchor="ra")
    line([(65, 704), (65 + 1150 * now / duration, 704)], teal, 3)
    if i == 0:
        pts = arcrow(ease((u - 0.08) / 0.48))
        line(pts, grid, 2)
        for j, p in enumerate(pts):
            dot(p, 8, gold)
        txt(123, 520, "Seven points, shown schematically", 20, muted)
        rows(
            760,
            257,
            [
                ("The conjecture assumes", ink),
                ("a flat side on the unit ball,", teal),
                ("no three dots on a line,", ink),
                ("and no four on a norm circle.", ink),
            ],
        )
        txt(760, 490, "Must parallel slides suffice?", 27, gold, "serif")
    elif i == 1:
        pts = arcrow(ease((u - 0.34) / 0.34))
        gap = 1 if u < 0.24 or 0.68 < u < 0.82 else 2
        line(pts, grid, 2)
        for j in range(len(pts) - gap):
            line([pts[j], pts[j + gap]], teal if j % 2 == 0 else gold, 4)
        j = min(6 - gap, int((u * 12) % (7 - gap)))
        line([pts[j], pts[j + gap]], coral, 7)
        for k, p in enumerate(pts):
            dot(p, 8)
            txt(p[0], p[1] + 22, str(k + 1), 18, muted, anchor="ma")
        txt(760, 272, f"Index gap = {gap}", 37, teal, "serif")
        rows(
            760,
            350,
            [
                ("One step: all six pairs match.", ink),
                ("Two steps: all five pairs match.", ink),
            ],
        )
        txt(760, 477, "The arc is enlarged for visibility.", 20, muted)
    elif i == 2:
        cx, cy, r = 368, 407, 155
        line(boundary(cx, cy, r, "disk"), muted, 2)
        line(boundary(cx, cy, r, "ellipse"), gold, 3)
        for sign in (-1, 1):
            a, b = (0.18, 1.07) if sign == 1 else (-1.07, -0.18)
            line([(cx + r * x, cy - r * (1.25 * sign - x)) for x in (a, b)], coral, 3)
        line(boundary(cx, cy, r, "norm"), teal, 5)
        angle = 0.07 + 0.7 * (1 + m.cos(2 * m.pi * u)) * 0.5
        ex, ey = m.cos(angle), m.sin(angle)
        s = max(1, (0.8 * ex * ex + 1.2 * ey * ey) ** 0.5, 0.8 * abs(ex + ey))
        line([(cx, cy), (cx + r * ex / s, cy - r * ey / s)], ink, 3)
        dot((cx + r * ex / s, cy - r * ey / s), 7)
        for j, (c, l) in enumerate(
            [
                (muted, "Euclidean disk"),
                (gold, "Ellipse"),
                (coral, "Diagonal strip"),
                (teal, "Boundary of the actual unit ball"),
            ]
        ):
            key(716, 258 + j * 55, c, l)
        txt(716, 503, "Flat edge supplied by the strip", 24, coral)
    elif i == 3:
        cx, cy, r = 340, 418, 152
        circle(cx, cy, r, muted)
        # Exact auxiliary ellipse through three exaggerated sample angles.
        ds = [0.10, 0.26, 0.42]
        angs = [m.pi / 2 + x for x in ds] + [m.pi / 2 - sum(ds)]
        a, b = 0.8, 1.2
        sx = sum(m.cos(t) for t in angs)
        sy = sum(m.sin(t) for t in angs)
        vx = (a - b) * sx / (4 * a)
        vy = -(a - b) * sy / (4 * b)
        R = (a * (m.cos(angs[0]) - vx) ** 2 + b * (m.sin(angs[0]) - vy) ** 2) ** 0.5
        line(
            path(
                lambda z: (
                    cx + r * (vx + R * m.cos(2 * m.pi * z) / a**0.5),
                    cy - r * (vy + R * m.sin(2 * m.pi * z) / b**0.5),
                )
            ),
            gold,
            3,
        )
        for k, t in enumerate(angs):
            if k < 3 or u > 0.45:
                pt = (cx + r * m.cos(t), cy - r * m.sin(t))
                dot(pt, 7, teal if k < 3 else coral)
                if k == 3:
                    line([pt, (pt[0] + 38, pt[1] + 14)], coral)
                    txt(pt[0] + 43, pt[1] + 5, "fourth", 18, coral)
        rows(
            696,
            250,
            [
                ("Three selected dots lie on both curves.", ink),
                ("The fourth intersection is outside", coral),
                ("the selected arc.", coral),
            ],
        )
        key(696, 439, muted, "Euclidean circle")
        key(696, 477, gold, "Ellipse controlling the triple")
        txt(695, 541, "Angles enlarged to show the intersections.", 19, muted)
    elif i == 4:
        # Parallel vertical motion preserves all horizontal coordinates.
        pts = [(126 + 80 * k, 305 + 48 * m.sin(k * 1.45)) for k in range(6)]
        t = ease((u - 0.02) / 0.35)
        for x, y in pts:
            line([(x, y), (x, 475)], grid)
            dot((x, y + (475 - y) * t), 8, gold)
        line([(89, 475), (564, 475)], muted)
        txt(96, 510, "Parallel slides preserve projected positions.", 21, muted)
        txt(655, 245, "For ruler marks", 31, ink, "serif")
        txt(655, 300, "Ratios of differences are rational.", 23, muted)
        txt(655, 375, "For four consecutive arc points", 30, ink, "serif")
        txt(655, 430, "(y₄ − y₁) / (y₃ − y₂) = 1 + 2 cos h", 29, teal)
        txt(655, 495, "The chosen angle makes this irrational.", 23, coral)
    else:
        pts = arcrow(1)
        for j, p in enumerate(pts):
            dot(p, 9, teal if j % 2 else gold)
        txt(125, 506, "Line-like distances. No parallel straightening.", 24, ink)
        txt(735, 256, "Read the proof", 40, ink, "serif")
        txt(735, 333, "Rohan Arun", 30, ink)
        txt(735, 381, "Super Powers AI", 24, muted)
        txt(735, 472, "doi.org/10.5281/zenodo.24384224", 23, teal)
    out.stdin.write(im.tobytes())
out.stdin.close()
if out.wait():
    raise SystemExit("Video encoder failed")
