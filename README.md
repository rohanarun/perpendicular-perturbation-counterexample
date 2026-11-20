# A counterexample to the perpendicular perturbation conjecture for normed planes

**Rohan Arun**  
Super Powers AI

This AI-assisted research note gives an explicit counterexample to Conjecture 6.5 of Fish, King, Miller, Palsson and Wahlenmayer. For every n ≥ 4, one fixed non-strictly convex norm admits a line-like crescent configuration that cannot be taken to equally spaced collinear points by parallel displacements.

[Read the proof](conjecture65.pdf) · [LaTeX source](conjecture65.tex) · [Prior-art search](conjecture65-prior-art.txt) · [Original conjecture, page 37](https://math.colgate.edu/~integers/u96/u96.pdf#page=37)

[Watch or download the narrated explanation (1:53)](https://raw.githubusercontent.com/rohanarun/perpendicular-perturbation-counterexample/main/conjecture65-explained.mp4) · [Zenodo preprint](https://doi.org/10.5281/zenodo.24384125)

The note is a preprint for independent review. The prior-art search found no earlier disproof. Corrections and references are welcome in the issue tracker.

## Generate the example

Run `python3 examples/arc.py 7` to print the seven point coordinates and compare measured distances for each index gap with the exact chord formula. Replace 7 with any integer at least four. Small differences in the printed values come from floating-point rounding. [Construction script](examples/arc.py)

## Reproduce the Lean proof

Lean 4.32.0 checks the quantified counterexample in [Counterexample.lean](Counterexample.lean). The theorem `CrescentCounterexample.all_sizes` gives the construction for every size from four upward. The final theorem `CrescentCounterexample.counterexample` rules out any threshold in the original conjecture. Its axiom audit lists `propext`, `Classical.choice`, and `Quot.sound`.

With Lean's Elan toolchain manager installed, run these commands from this directory. The manifest pins the mathlib revision.

```sh
lake exe cache get
lake build Counterexample
lake env leanchecker Arc Projection Circumcenter Ellipse Homothets ArcEllipse NormPlane FourPoints Configuration Counterexample
```

The formal proof excludes a second circle through the four points by direct inequalities. The PDF uses a published result about intersections of convex curves for this step.

The animation uses the Heart voice from [Kokoro-82M](https://huggingface.co/hexgrad/Kokoro-82M).

## Rebuild the narrated animation

Use Python 3.11 and FFmpeg with the libx264 and AAC encoders. On Linux, install the DejaVu fonts. The renderer uses Arial and Georgia when available on macOS.

From the repository root, run

```sh
python3.11 -m venv animation/.venv
animation/.venv/bin/python -m pip install -r animation/requirements.txt
animation/.venv/bin/python animation/build.py
```

The first run downloads and checksum-verifies the Kokoro v1.0 weights and voices. Subsequent runs use the local files. The script synthesizes each passage with the Heart voice, fits it to its chapter, renders the diagrams, and exports `animation/build/conjecture65-explained.mp4`. No API key is required. Font availability and encoder versions can affect the rendered pixels and file hash.

[Chapter timings and narration](animation/chapters.json) · [Narration and build script](animation/build.py) · [Diagram renderer](animation/render.py)
