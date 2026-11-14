"""Generate a self-contained SVG/HTML animation of the translational tiling.

Run: python anim/generate_translation_tiling_animation.py
The exact lattice tiling is the assembled endpoint; no display gap remains.
The camera and framing stay fixed at the exploded view. Only the existing
explosion displacement (including seeded perturbations) is scaled down/up.
"""

import argparse
import json
from pathlib import Path
import sys
import xml.etree.ElementTree as ET

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / 'figures'))
import generate_translation_tiling as base
import translation_tiling_layout as layout


OUT = Path(__file__).resolve().parent
ASPECT = 1050/360


def pose(centers, exploded, phase):
    """Scale the existing explosion displacement; keep world coordinates fixed."""
    return {c: tuple(c[i]+phase*(exploded[c][i]-c[i]) for i in range(3))
            for c in centers}


def fit_bounds(bounds, scale, aspect=ASPECT):
    left, top, right, bottom = bounds
    left -= .6*scale
    top -= .6*scale
    right += .6*scale
    bottom += .6*scale
    width, height = right-left, bottom-top
    cx, cy = (left+right)/2, (top+bottom)/2
    if width/height < aspect:
        width = height*aspect
    else:
        height = width/aspect
    return [cx-width/2, cy-height/2, width, height]


def fixed_bounds(centers, exploded, scale, extents, aspect=ASPECT):
    # Every coordinate between the endpoint poses stays inside their bounds.
    points = list(centers)+list(exploded.values())
    projected = [base.project(p) for p in points]
    bounds = [scale*(min(p[i] for p in projected)+extents[i]) for i in range(2)]
    bounds += [scale*(max(p[i] for p in projected)+extents[i+2]) for i in range(2)]
    return fit_bounds(bounds, scale, aspect)


def make_data(count=None, key=None, vertical_radius=0):
    baseline = base.surfaces(base.DENT_FREE_CENTERS, base.GAP, base.OPACITY,
                             tile_colors=base.DENT_FREE_COLORS)
    ys = [v[1] for face in baseline for v in face['vertices']]
    scale = 340/(max(ys)-min(ys))
    local = base.surfaces([(0, 0, 0)], 0, 1)
    points = [v for face in local for v in face['vertices']]
    extents = [min(v[0] for v in points), min(v[1] for v in points),
               max(v[0] for v in points), max(v[1] for v in points)]
    box = (scale*extents[0], scale*extents[1],
           scale*(extents[2]-extents[0]), scale*(extents[3]-extents[1]))
    root = ET.fromstring('<svg>'+base.draw(local, box, 'assembly', scale=scale)+'</svg>')
    polygons = [ET.tostring(g.find('polygon'), encoding='unicode') for g in root.find('g')]
    shades = {normal: shade for normal, _, shade in base.FACES}
    styles = []
    for color in base.PALETTE:
        row = []
        for face in local:
            fill = base.color(color, shades[face['normal']])
            row.append([fill, base.color(fill, .66)])
        styles.append(row)
    height = 360+120*vertical_radius
    data = dict(verticalRadius=vertical_radius, canvasHeight=height, pixelScale=scale, right=base.RIGHT, up=base.UP, eye=base.EYE,
                opacity=base.OPACITY, polygons=polygons, extents=extents,
                localDepths=[f['depth'] for f in local], styles=styles, cases={})
    patches = {}
    for radius in (0, 1, 2):
        patch = layout.make_patch(radius, vertical_radius)
        if count is not None and patch.count != count:
            continue
        patches[patch.count] = patch
        model = dict(centers=patch.centers, colors=[patch.colors[c] for c in patch.centers], states={})
        for study in (layout.BASE_STUDY, *layout.JITTER_STUDIES):
            study_key = study.key.rsplit('-', 1)[-1] if study.jitter_strength else 'none'
            if key is not None and study_key != key:
                continue
            exploded = layout.positions_for(study, patch)
            layout.check(exploded, patch)
            model['states'][study_key] = dict(positions=[exploded[c] for c in patch.centers],
                                       label=study.label,
                                       fixedViewBox=fixed_bounds(patch.centers, exploded, scale, extents, 1050/height))
            print(patch.count, study_key, 'fixed-view explosion', flush=True)
        data['cases'][str(patch.count)] = model
    return data, patches


def render_svg(data, patch, key, phase=1):
    state = data['cases'][str(patch.count)]['states'][key]
    exploded = dict(zip(patch.centers, state['positions']))
    positions = pose(patch.centers, exploded, phase)
    faces = layout.faces_for(positions, patch)
    points = [v for face in faces for v in face['vertices']]
    scale = data['pixelScale']
    bounds = [min(v[0] for v in points), min(v[1] for v in points),
              max(v[0] for v in points), max(v[1] for v in points)]
    box = state['fixedViewBox']
    drawing_box = (scale*bounds[0], scale*bounds[1],
                   scale*(bounds[2]-bounds[0]), scale*(bounds[3]-bounds[1]))
    scene = base.draw(faces, drawing_box, 'assembly', scale=scale)
    return f'''<svg xmlns="http://www.w3.org/2000/svg" id="tiling-animation" width="1050" height="{data['canvasHeight']}" viewBox="{' '.join(f'{x:.6f}' for x in box)}" role="img" aria-labelledby="assembly-title assembly-desc">
<title id="assembly-title">{patch.count} translated crosses: assembly animation</title>
<desc id="assembly-desc">Complete unrotated crosses move between an exploded view and an exact lattice tiling at scale 1. Seed 17; uniform opacity.</desc>
{scene}
</svg>'''


def standalone(svg, data, engine, count, key):
    command = f'python anim/generate_translation_tiling_animation.py -n {count} -j {key}'
    if data['verticalRadius']:
        command += f" -v {data['verticalRadius']}"
    comment = f'<!-- Regenerate from the repository root:\n     {command}\n-->\n'
    svg = svg.replace('<title ', comment+'<title ', 1)
    code = ('(()=>{\n'+engine+'\nconst assemblyData='+json.dumps(data, separators=(',', ':'))+';\n'
            +'const assemblyRoot=document.currentScript.ownerSVGElement||document.documentElement;\n'
            +f'const assemblyPlayer=createTilingAnimation(assemblyRoot,assemblyData,{{count:{count},key:"{key}"}});\n'
            +'assemblyRoot.addEventListener("click",()=>{if(assemblyPlayer.getState().playing)assemblyPlayer.pause();else assemblyPlayer.play()});\n'
            +'assemblyPlayer.play();\n})();')
    return svg.replace('</svg>', '<script><![CDATA[\n'+code+'\n]]></script>\n</svg>')


def player_html(svg, data, engine, count, key):
    keys = ('none', 'mild', 'medium', 'strong', 'extra', 'extreme')
    labels = ('None', 'Mild', 'Medium', 'Strong', 'Extra (2x)', 'Extreme (3x)')
    sizes = ''.join(f'<option value="{n}"'+(' selected' if n == count else '')+f'>{n}</option>' for n in sorted(map(int, data['cases'])))
    strengths = ''.join(f'<option value="{k}"'+(' selected' if k == key else '')+f'>{label}</option>' for k,label in zip(keys,labels))
    return '''<!doctype html><html><head><meta charset="utf-8"><title>Translation tiling assembly</title>
<style>
body{margin:0;font-family:var(--font-sans,system-ui,sans-serif);color:var(--foreground,#26323c)}
p{font-size:13px;color:var(--muted-foreground,#68737d);margin:0 0 10px}
.controls{display:flex;align-items:center;flex-wrap:wrap;gap:10px;margin:10px 0;font-size:13px}
button,select,input[type=number]{font:inherit;color:var(--foreground,#26323c);background:var(--card,#fff);border:1px solid var(--border,#ccd2d7);border-radius:4px;padding:4px 7px}
button{cursor:pointer}label{display:flex;align-items:center;gap:5px}
#spread{flex:1;min-width:150px;max-width:420px}#status{font-size:13px;min-width:145px}
#cycle{width:50px}svg{display:block;width:100%;height:auto;background:white}
</style></head><body>
<p>Fixed view: the explosion parameter decreases to scale 1, then returns to the previous exploded diagram.</p>
<div class="controls"><button id="play">Pause</button><button id="assembled">Assemble</button><button id="exploded">Explode</button>
<label>Tiles <select id="count">''' + sizes + '''</select></label><label>Perturbation <select id="strength">''' + strengths + '''</select></label></div>
''' + svg + '''
<div class="controls"><label for="spread">Spread</label><input id="spread" type="range" min="0" max="1" step="0.001" value="1"><output id="status">Exploded</output></div>
<div class="controls"><label>Cycle <input id="cycle" type="number" min="6" max="30" value="12"> seconds</label>
<button id="save-animation">Animated SVG</button><button id="save-frame">Save SVG frame</button></div>
<script>''' + engine + '\nconst ANIMATION_DATA=' + json.dumps(data, separators=(',', ':')) + ';\n' + '''
const tilingPlayer=createTilingAnimation(document.getElementById('tiling-animation'),ANIMATION_DATA,{count:''' + str(count) + ''',key:"''' + key + r'''"});
window.tilingPlayer=tilingPlayer;
const playButton=document.getElementById('play'), spread=document.getElementById('spread');
tilingPlayer.onUpdate(s=>{
  playButton.textContent=s.playing?'Pause':'Play';spread.value=s.phase;
  document.getElementById('status').textContent=s.phase<.0005?'Assembled - scale 1':s.phase>.9995?'Exploded':Math.round(100*s.phase)+'% exploded';
});
playButton.onclick=()=>{if(tilingPlayer.getState().playing)tilingPlayer.pause();else tilingPlayer.play()};
document.getElementById('assembled').onclick=()=>{tilingPlayer.pause();tilingPlayer.setPhase(0)};
document.getElementById('exploded').onclick=()=>{tilingPlayer.pause();tilingPlayer.setPhase(1)};
spread.oninput=()=>{const value=Number(spread.value);tilingPlayer.pause();tilingPlayer.setPhase(value)};
for(const id of ['count','strength']) document.getElementById(id).onchange=()=>tilingPlayer.setCase(Number(document.getElementById('count').value),document.getElementById('strength').value);
document.getElementById('cycle').onchange=e=>{if(Number(e.target.value)>=6)tilingPlayer.setPeriod(Number(e.target.value))};
function download(filename,text){
  const url=URL.createObjectURL(new Blob([text],{type:'image/svg+xml'}));
  const a=document.createElement('a');a.href=url;a.download=filename;a.click();setTimeout(()=>URL.revokeObjectURL(url),1000);
}
function exportSVG(animated){
  const s=tilingPlayer.getState(), copy=document.getElementById('tiling-animation').cloneNode(true);
  let command='python anim/generate_translation_tiling_animation.py -n '+s.count+' -j '+s.key;
  if(ANIMATION_DATA.verticalRadius) command+=' -v '+ANIMATION_DATA.verticalRadius;
  if(!animated) command+=' -p '+s.phase.toPrecision(12);
  copy.insertBefore(document.createComment(' Regenerate from the repository root:\n     '+command+'\n'),copy.firstChild);
  let text=new XMLSerializer().serializeToString(copy);
  if(animated){
    const code='(()=>{\n'+createTilingAnimation.toString()+'\nconst data='+JSON.stringify(ANIMATION_DATA)+';\nconst root=document.currentScript.ownerSVGElement||document.documentElement;const player=createTilingAnimation(root,data,'+JSON.stringify({count:s.count,key:s.key})+');root.addEventListener("click",()=>{if(player.getState().playing)player.pause();else player.play()});player.play();\n})();';
    text=text.replace('</svg>','<script><![CDATA[\n'+code+'\n]]><'+'/script></svg>');
  }
  download('tiling-'+s.count+'-'+s.key+(animated?'-animation':'-frame')+'.svg',text);
}
document.getElementById('save-animation').onclick=()=>exportSVG(true);
document.getElementById('save-frame').onclick=()=>exportSVG(false);
tilingPlayer.play();
</script></body></html>'''


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('-n', type=int, help='Tile count; defaults to the longest patch at the selected height')
    parser.add_argument('-v', type=int, choices=(0,1,2), default=0, help='Extra vertical lattice layers; 0 preserves the original animation')
    parser.add_argument('-j', choices=('none','mild','medium','strong','extra','extreme'), default='extra')
    parser.add_argument('-p', type=float, help='Save a static frame at spread 0..1 instead of the animation')
    args = parser.parse_args()
    if args.p is not None and not 0 <= args.p <= 1:
        parser.error('-p must be between 0 and 1')
    available = [layout.make_patch(r, args.v).count for r in (0,1,2)]
    if args.n is None:
        args.n = max(available)
    if args.n not in available:
        parser.error('-n must be one of '+', '.join(map(str, available)))
    data, patches = make_data(args.n, args.j, args.v) if args.p is not None else make_data(vertical_radius=args.v)
    suffix = ('', '-tall', '-taller')[args.v]
    OUT.mkdir(exist_ok=True)
    patch = patches[args.n]
    svg = render_svg(data, patch, args.j, args.p if args.p is not None else 1)
    if args.p is not None:
        command = f'python anim/generate_translation_tiling_animation.py -n {args.n} -j {args.j} -p {args.p}'
        if args.v:
            command += f' -v {args.v}'
        svg = svg.replace('<title ', f'<!-- Regenerate: {command} -->\n<title ', 1)
        (OUT/f'assembly{suffix}-frame.svg').write_text(svg+'\n', encoding='utf-8')
        print(OUT/f'assembly{suffix}-frame.svg')
        return
    engine = (Path(__file__).parent/'translation_tiling_animation.js').read_text(encoding='utf-8')
    (OUT/f'assembly{suffix}.svg').write_text(standalone(svg, data, engine, args.n, args.j)+'\n', encoding='utf-8')
    (OUT/f'animation{suffix}.html').write_text(player_html(svg, data, engine, args.n, args.j), encoding='utf-8')
    print(f'Wrote assembly{suffix}.svg and animation{suffix}.html in', OUT)


if __name__ == '__main__':
    main()
