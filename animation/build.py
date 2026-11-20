"""Build the six-chapter video from the manuscript narration and vector scenes."""

import hashlib
import json
import os
import subprocess
import sys
import urllib.request
from pathlib import Path

import numpy as np
import soundfile as sf
from kokoro_onnx import Kokoro

source = Path(__file__).resolve().parent
build = source / "build"
build.mkdir(exist_ok=True)
os.chdir(build)
models = {
    "kokoro-v1.0.onnx": "7d5df8ecf7d4b1878015a32686053fd0eebe2bc377234608764cc0ef3636a6c5",
    "voices-v1.0.bin": "bca610b8308e8d99f32e6fe4197e7ec01679264efed0cac9140fe9c29f1fbf7d",
}
release = (
    "https://github.com/thewh1teagle/kokoro-onnx/releases/download/model-files-v1.0/"
)
for name, digest in models.items():
    model = Path(name)
    if not model.exists():
        temporary = model.with_suffix(".download")
        urllib.request.urlretrieve(release + name, temporary)
        with temporary.open("rb") as data:
            downloaded_digest = hashlib.file_digest(data, "sha256").hexdigest()
        if downloaded_digest != digest:
            raise ValueError(f"Download checksum mismatch for {name}")
        temporary.replace(model)
    with model.open("rb") as data:
        if hashlib.file_digest(data, "sha256").hexdigest() != digest:
            raise ValueError(f"Checksum mismatch for {name}")

chapters = json.loads((source / "chapters.json").read_text())
engine = Kokoro("kokoro-v1.0.onnx", "voices-v1.0.bin")
rate = 24000
track = np.zeros(round(chapters[-1]["end"] * rate), dtype=np.float32)
metadata = [
    ";FFMETADATA1",
    "title=A counterexample to the perpendicular perturbation conjecture",
    "artist=Rohan Arun, Super Powers AI",
]
for chapter in chapters:
    start, end = chapter["start"], chapter["end"]
    audio, sample_rate = engine.create(
        chapter["narration"], voice="af_heart", speed=1.04, lang="en-us"
    )
    if sample_rate != rate or not np.isfinite(audio).all():
        raise ValueError(f"Invalid narration for {chapter['title']}")
    sf.write("dry.wav", audio, rate)
    tempo = len(audio) / rate / (end - start - 0.72)
    subprocess.run(
        [
            "ffmpeg",
            "-v",
            "error",
            "-y",
            "-i",
            "dry.wav",
            "-af",
            f"atempo={tempo:.6f}",
            "fit.wav",
        ],
        check=True,
    )
    fitted, _ = sf.read("fit.wav", dtype="float32")
    first = round((start + 0.28) * rate)
    if first + len(fitted) > round(end * rate):
        raise ValueError(f"Narration exceeds chapter length for {chapter['title']}")
    track[first : first + len(fitted)] = fitted
    metadata.extend(
        [
            "[CHAPTER]",
            "TIMEBASE=1/1000",
            f"START={round(start * 1000)}",
            f"END={round(end * 1000)}",
            f"title={chapter['title']}",
        ]
    )
sf.write("voice.wav", track, rate)
Path("chapters.ffmeta").write_text("\n".join(metadata) + "\n")
subprocess.run([sys.executable, str(source / "render.py")], check=True)
print(build / "conjecture65-explained.mp4")
