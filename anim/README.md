# Tiling animations

The animations use whole seven-cube crosses, a fixed camera, and seeded random
translations. The explosion displacement decreases to zero to assemble the
exact tiling, then returns to the exploded view.

HTML players, SVGs, MP4s, and `media-exports*.json` manifests are generated
locally and ignored by Git. The commands below recreate them from the Python
scripts and included JavaScript renderer. MP4 export also uses
Playwright/Chromium and FFmpeg; no manual video editing is required.
The file links below refer to local outputs after generation.

| Patch | MP4 | Browser player | Animated SVG | Static SVG |
|---|---|---|---|---|
| 421 tiles | [assembly-tall.mp4](assembly-tall.mp4) | [animation-tall.html](animation-tall.html) | [assembly-tall.svg](assembly-tall.svg) | [assembly-tall-frame.svg](assembly-tall-frame.svg) |
| 625 tiles | [assembly-taller.mp4](assembly-taller.mp4) | [animation-taller.html](animation-taller.html) | [assembly-taller.svg](assembly-taller.svg) | [assembly-taller-frame.svg](assembly-taller-frame.svg) |

Both MP4s contain a 12-second loop at 25 fps, with H.264 video, a white
background, and no player controls. Their resolutions are 1400 × 640 and
1400 × 800, respectively. The original 243-tile browser player and SVG are
also retained as `animation.html` and `assembly.svg`.

Black-background MP4s are available as [assembly-tall-black.mp4](assembly-tall-black.mp4)
and [assembly-taller-black.mp4](assembly-taller-black.mp4), at the same resolution
and with the same timing. These are rendered against black, including the
translucent tile faces.

Run these commands from the repository root with Python 3:

```sh
# Generate the three browser players and animated SVGs (standard library only).
python anim/generate_translation_tiling_animation.py
python anim/generate_translation_tiling_animation.py -v 1
python anim/generate_translation_tiling_animation.py -v 2

# Save static frames: -p 0 is assembled; -p 1 is exploded.
python anim/generate_translation_tiling_animation.py -n 243 -j extra -p 0
python anim/generate_translation_tiling_animation.py -v 1 -n 421 -j extra -p 1
python anim/generate_translation_tiling_animation.py -v 2 -n 625 -j extra -p 1

# Export both MP4s at the default resolution, frame rate, and duration.
python anim/export_translation_tiling_media.py

# Render black-background copies, preserving the white-background videos.
python anim/export_translation_tiling_media.py --background black
```

The media exporter needs `playwright`, `Pillow`, an installed Chromium browser,
and FFmpeg with the `libx264` encoder. It tries installed Chrome before
Playwright's Chromium. Pass `--browser` or `--ffmpeg` to select executables.
Use `--variants tall` or `--variants taller` to export only one patch, and
`--width`, `--fps`, or `--seconds` to change the output. GIF export is available
with `--gif`; it is off by default.

Animation-specific code:

- `generate_translation_tiling_animation.py`: SVG and browser-player generation.
- `translation_tiling_animation.js`: fixed-view animation and SVG frame export.
- `export_translation_tiling_media.py`: frame capture and video encoding.

The exporter writes `media-exports.json` and `media-exports-black.json` with
video dimensions, sizes, source hashes, and regeneration commands.

Shared infrastructure stays under `figures/`: [generate_translation_tiling.py](../figures/generate_translation_tiling.py)
provides the lattice, colors, camera, and SVG renderer;
[translation_tiling_layout.py](../figures/translation_tiling_layout.py) provides
whole-tile patch selection, spacing, and perturbations. The animation generator
imports these directly. The paper's figure-generation command is unchanged.
