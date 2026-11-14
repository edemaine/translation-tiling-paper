"""Export existing fixed-view animation players to H.264 MP4 (optionally GIF).

Run: python anim/export_translation_tiling_media.py
Requires Playwright, an installed Chromium browser, and FFmpeg with libx264.
Only the SVG figure is captured; the player controls are omitted.
"""

import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile

from PIL import Image
from playwright.sync_api import sync_playwright


ROOT = Path(__file__).resolve().parent.parent
OUT = Path(__file__).resolve().parent


def find_ffmpeg(explicit):
    if explicit:
        return explicit
    # Prefer a native Windows build over Cygwin's build without libx264.
    candidates = []
    if os.name == 'nt':
        packages = Path(os.environ.get('LOCALAPPDATA', '')) / 'Microsoft/WinGet/Packages'
        candidates.extend(packages.glob('*FFmpeg*/*/bin/ffmpeg.exe'))
    found = shutil.which('ffmpeg')
    if found:
        candidates.append(Path(found))
    for candidate in candidates:
        encoders = subprocess.check_output([str(candidate), '-hide_banner', '-encoders'],
                                          stderr=subprocess.DEVNULL, text=True)
        if 'libx264 ' in encoders:
            return str(candidate)
    raise RuntimeError('Pass --ffmpeg pointing to an FFmpeg build with libx264')


def phase_at(q):
    def smooth(x):
        return x*x*(3-2*x)
    if q < .10:
        return 1
    if q < .45:
        return 1-smooth((q-.10)/.35)
    if q < .60:
        return 0
    if q < .95:
        return smooth((q-.60)/.35)
    return 1


def encode(ffmpeg, frames, target, fps, command, gif=False, background='white'):
    common = [ffmpeg, '-hide_banner', '-loglevel', 'error', '-y']
    source = ['-framerate', str(fps), '-i', str(frames/'%04d.png')]
    subprocess.run(common+source+['-an', '-c:v', 'libx264', '-preset', 'slow',
                   '-crf', '18', '-pix_fmt', 'yuv420p', '-movflags', '+faststart',
                   '-metadata', 'comment=Regenerate: '+command, str(target.with_suffix('.mp4'))],
                   check=True)
    if not gif:
        return
    palette = frames/'palette.png'
    subprocess.run(common+source+['-vf', 'palettegen=reserve_transparent=0',
                   '-frames:v', '1', '-update', '1', str(palette)], check=True)
    # Preserve the exact background endpoint through palette quantization.
    with Image.open(palette) as image:
        image = image.convert('RGBA')
        colors = list(image.getdata())
        choose = max if background == 'white' else min
        endpoint = 255 if background == 'white' else 0
        colors[choose(range(len(colors)), key=lambda i: sum(colors[i][:3]))] = (endpoint,endpoint,endpoint,255)
        image.putdata(colors)
        image.save(palette)
    subprocess.run(common+source+['-i', str(palette), '-lavfi',
                   'paletteuse=dither=bayer:bayer_scale=3:diff_mode=rectangle',
                   '-loop', '0', str(target.with_suffix('.gif'))], check=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--variants', nargs='+', choices=('tall', 'taller'),
                        default=['tall', 'taller'])
    parser.add_argument('--width', type=int, default=1400)
    parser.add_argument('--fps', type=int, choices=(10, 20, 25, 50), default=25,
                        help='Rates with exact centisecond GIF frame durations')
    parser.add_argument('--seconds', type=int, default=12)
    parser.add_argument('--background', choices=('white', 'black'), default='white',
                        help='Figure background; black outputs use a -black suffix')
    parser.add_argument('--gif', action='store_true', help='Also export GIF; the default is MP4 only')
    parser.add_argument('--ffmpeg')
    parser.add_argument('--browser', help='Chromium executable; otherwise try Chrome, then Playwright')
    args = parser.parse_args()
    if args.width <= 0 or args.width % 2 or args.seconds <= 0:
        parser.error('--width must be positive and even; --seconds must be positive')
    ffmpeg = find_ffmpeg(args.ffmpeg)
    command = ('python anim/export_translation_tiling_media.py --variants '
               +' '.join(args.variants)+f' --width {args.width} --fps {args.fps} --seconds {args.seconds}')
    if args.gif:
        command += ' --gif'
    if args.background != 'white':
        command += ' --background '+args.background
    background_suffix = '' if args.background == 'white' else '-'+args.background
    results = []
    with sync_playwright() as playwright:
        if args.browser:
            browser = playwright.chromium.launch(executable_path=args.browser, headless=True)
        else:
            try:
                browser = playwright.chromium.launch(channel='chrome', headless=True)
            except Exception:
                browser = playwright.chromium.launch(headless=True)
        try:
            for variant in args.variants:
                source = OUT/f'animation-{variant}.html'
                canvas_height = 480 if variant == 'tall' else 600
                height = 2*round(args.width*canvas_height/1050/2)
                page = browser.new_page(viewport={'width': args.width, 'height': height},
                                        device_scale_factor=1, color_scheme='light')
                errors = []
                page.on('pageerror', lambda error: errors.append(str(error)))
                page.goto(source.as_uri())
                page.evaluate('''(background) => {
                    tilingPlayer.pause();
                    document.body.style.margin='0';
                    for(const child of document.body.children)
                        if(child.tagName.toLowerCase()!=='svg') child.style.display='none';
                    const svg=document.getElementById('tiling-animation');
                    svg.style.width='100vw';svg.style.height='100vh';
                    svg.style.background=background;
                    document.body.style.background=background;
                }''', args.background)
                box = page.locator('svg').get_attribute('viewBox')
                frames_count = args.seconds*args.fps
                with tempfile.TemporaryDirectory(prefix='tiling-frames-') as temporary:
                    frames = Path(temporary)
                    cached = {}
                    for index in range(frames_count):
                        phase = round(phase_at(index/frames_count), 12)
                        frame = frames/f'{index:04d}.png'
                        if phase in cached:
                            os.link(cached[phase], frame)
                        else:
                            page.evaluate('(phase)=>tilingPlayer.setPhase(phase)', phase)
                            assert page.locator('svg').get_attribute('viewBox') == box
                            page.screenshot(path=str(frame), animations='disabled')
                            cached[phase] = frame
                        if index % args.fps == 0:
                            print(variant, f'{index}/{frames_count} frames', flush=True)
                    assert not errors, errors
                    target = OUT/f'assembly-{variant}{background_suffix}'
                    encode(ffmpeg, frames, target, args.fps, command, args.gif, args.background)
                    record = dict(variant=variant, width=args.width, height=height,
                                  fps=args.fps, seconds=args.seconds, background=args.background,
                                  source=source.name, sourceSHA256=hashlib.sha256(source.read_bytes()).hexdigest(),
                                  command=command)
                    for suffix in (('.mp4', '.gif') if args.gif else ('.mp4',)):
                        path = target.with_suffix(suffix)
                        record[suffix[1:]] = dict(file=path.name, bytes=path.stat().st_size)
                    results.append(record)
                    print(json.dumps(record), flush=True)
                page.close()
        finally:
            browser.close()
    (OUT/f'media-exports{background_suffix}.json').write_text(json.dumps(results, indent=2)+'\n', encoding='utf-8')


if __name__ == '__main__':
    main()
