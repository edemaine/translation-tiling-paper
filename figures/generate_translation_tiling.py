"""Generate the paper's separate seven-cube cross and tiling-patch SVGs.

Run from any directory with Python 3 (standard library only). Use make figures
to also export the panels to PDF with Inkscape.

The cross consists of 0 and the six signed coordinate unit vectors. Its
residues under x+2y+3z modulo 7 are exactly 0,...,6, so translations by the
kernel of that map partition Z^3. Displayed tiles are complete, unrotated
copies from that lattice. Exploding the picture moves tile centers only.
"""

from html import escape
from collections import Counter
from itertools import product
from math import cos, isqrt, radians, sin
from pathlib import Path


OUT = Path(__file__).resolve().parent
CROSS = ((0, 0, 0), (1, 0, 0), (-1, 0, 0), (0, 1, 0),
         (0, -1, 0), (0, 0, 1), (0, 0, -1))
def patch(radius2):
    extent = isqrt(radius2)
    return sorted(p for p in product(range(-extent, extent+1), repeat=3)
                  if sum(v*v for v in p) <= radius2 and (p[0]+2*p[1]+3*p[2]) % 7 == 0)


CENTERS = patch(10)
LARGER_PATCHES = (patch(20), patch(26))
ALL_CENTERS = LARGER_PATCHES[-1]
GAP = .08
OPACITY = .88
PALETTE = ('#438bad', '#dc9860', '#77a995', '#a293bc', '#c9ad63', '#c47888')
# Shared camera for the input and tiling. Previously elevation 36.87 degrees,
# azimuth -53.13 degrees; the small azimuth change separates projected edges.
ELEVATION, AZIMUTH = radians(30), radians(-58)
RIGHT = (-sin(AZIMUTH), cos(AZIMUTH), 0)
UP = (-sin(ELEVATION)*cos(AZIMUTH), -sin(ELEVATION)*sin(AZIMUTH), cos(ELEVATION))
EYE = (cos(ELEVATION)*cos(AZIMUTH), cos(ELEVATION)*sin(AZIMUTH), sin(ELEVATION))
# Outward, camera-facing surface squares. Per-tile visibility masks below hide
# each tile's own rear surfaces while allowing other tiles to show through.
FACES = (
    ((1, 0, 0), ((.5,-.5,-.5),(.5,.5,-.5),(.5,.5,.5),(.5,-.5,.5)), .80),
    ((0,-1, 0), ((-.5,-.5,-.5),(.5,-.5,-.5),(.5,-.5,.5),(-.5,-.5,.5)), .67),
    ((0, 0, 1), ((-.5,-.5,.5),(.5,-.5,.5),(.5,.5,.5),(-.5,.5,.5)), 1.0),
)


def add(a, b):
    return tuple(x+y for x, y in zip(a, b))


def tile_owner(p):
    """The unique center in the infinite lattice tiling covering cell p."""
    return next(tuple(p[i]-cube[i] for i in range(3)) for cube in CROSS
                if sum(w*(p[i]-cube[i]) for i, w in enumerate((1, 2, 3))) % 7 == 0)


def dent_cells(centers):
    """Empty unit cells with at least five occupied face-neighbors, before gaps."""
    cubes = {add(c, p) for c in centers for p in CROSS}
    adjacent = Counter(add(p, direction) for p in cubes for direction in CROSS[1:])
    return {p: count for p, count in adjacent.items() if p not in cubes and count >= 5}


def fill_dents(centers):
    """Add complete covering tiles until no five- or six-neighbor dent remains."""
    centers = set(centers)
    rounds = []
    while dents := dent_cells(centers):
        additions = {tile_owner(p) for p in dents}
        assert not (additions & centers)
        rounds.append((dents, additions))
        centers |= additions
    return sorted(centers), rounds


def dot(a, b):
    return sum(x*y for x, y in zip(a, b))


def project(p):
    return dot(p, RIGHT), -dot(p, UP)


def tile_contacts(centers):
    """Adjacency includes contact along a face, edge, or vertex before spacing."""
    cubes = {c: [add(c, p) for p in CROSS] for c in centers}
    contacts = {c: set() for c in centers}
    for i, c in enumerate(centers):
        for d in centers[i+1:]:
            if any(max(abs(p[k]-q[k]) for k in range(3)) <= 1
                   for p in cubes[c] for q in cubes[d]):
                contacts[c].add(d)
                contacts[d].add(c)
    return contacts


CONTACTS = tile_contacts(ALL_CENTERS)
DENT_FREE_CENTERS, DENT_REPAIRS = fill_dents(LARGER_PATCHES[0])
DENT_FREE_CONTACTS = tile_contacts(DENT_FREE_CENTERS)


def assign_colors(centers, contacts, preferred=None, fixed=None):
    """Properly color contacts, preferring distant repeats in the projection."""
    assigned = dict(fixed) if fixed is not None else {(0, 0, 0): 0}
    preferred = preferred or {}
    positions = {c: project(c) for c in centers}
    def complete():
        if len(assigned) == len(centers):
            return True
        c = max((c for c in centers if c not in assigned),
                key=lambda c: (len({assigned[d] for d in contacts[c] if d in assigned}),
                               len(contacts[c]), -dot(c, c), c))
        used = {assigned[d] for d in contacts[c] if d in assigned}

        def reuse_cost(index):
            return sum(1 / (.1 + sum((positions[c][i]-positions[d][i])**2
                                     for i in range(2)))
                       for d, color_index in assigned.items() if color_index == index)

        available = [i for i in range(len(PALETTE)) if i not in used]
        for index in sorted(available, key=lambda i: (c in preferred and i != preferred[c],
                                                     reuse_cost(i), i)):
            assigned[c] = index
            if complete():
                return True
            del assigned[c]
        return False

    assert complete(), 'Palette too small for the contact graph'
    return assigned


# Prefer the accepted colors when extending the patch; recolor where needed to
# keep all additional face, edge, and vertex contacts properly colored.
ORIGINAL_COLORS = assign_colors(CENTERS, tile_contacts(CENTERS))
TILE_COLORS = assign_colors(ALL_CENTERS, CONTACTS, ORIGINAL_COLORS)
DENT_FREE_COLORS = assign_colors(DENT_FREE_CENTERS, DENT_FREE_CONTACTS,
                                fixed={c: TILE_COLORS[c] for c in LARGER_PATCHES[0]})


def color(hexcolor, shade):
    channels = [int(hexcolor[i:i+2], 16) for i in (1, 3, 5)]
    return '#' + ''.join(f'{round(c*shade):02x}' for c in channels)


def surfaces(centers, gap, opacity, radial=False, focus=False, tile_colors=None):
    result = []
    occupied = set(CROSS)
    for center in centers:
        radius2 = dot(center, center)
        spread = 1 + gap + (.065*radius2 if radial else 0)
        offset = tuple(spread*c for c in center)
        base = PALETTE[(tile_colors or TILE_COLORS)[center]]
        alpha = opacity
        if focus:
            base = '#297fa9' if radius2 == 0 else base
            alpha = .97 if radius2 == 0 else opacity * (.88 - .025*radius2)
        for cube in CROSS:
            for normal, corners, shade in FACES:
                if add(cube, normal) in occupied:
                    continue
                vertices = [add(add(cube, corner), offset) for corner in corners]
                midpoint = tuple(sum(p[i] for p in vertices)/4 for i in range(3))
                result.append(dict(depth=dot(midpoint, EYE),
                                   vertices=[project(p) for p in vertices],
                                   fill=color(base, shade), alpha=alpha,
                                   center=center, cube=cube, normal=normal,
                                   local=[project(add(cube, corner)) for corner in corners],
                                   offset=project(offset)))
    return sorted(result, key=lambda f: f['depth'])


def draw(faces, box, prefix, *, scale=None):
    x, y, width, height = box
    vertices = [p for face in faces for p in face['vertices']]
    xmin, xmax = min(p[0] for p in vertices), max(p[0] for p in vertices)
    ymin, ymax = min(p[1] for p in vertices), max(p[1] for p in vertices)
    scale = scale or min(width/(xmax-xmin), height/(ymax-ymin))
    tx, ty = x+width/2-scale*(xmin+xmax)/2, y+height/2-scale*(ymin+ymax)/2
    # Reuse a front-surface visibility mask for each face of the prototile.
    # A translucent tile hides its own rear faces, while other tiles remain
    # visible through it. This avoids an unreadable X-ray of every cube edge.
    local_faces = surfaces([(0, 0, 0)], 0, 1)
    parts = ['<defs>']
    mask_ids = {}
    for i, local_face in enumerate(local_faces):
        mask_id = f'{prefix}-visible-{i}'
        mask_ids[(local_face['cube'], local_face['normal'])] = mask_id
        parts.append(f'<mask id="{mask_id}" maskUnits="userSpaceOnUse" x="-4" y="-4" width="8" height="8">'
                     '<rect x="-4" y="-4" width="8" height="8" fill="white"/>')
        for near in local_faces[i+1:]:
            pts = ' '.join(f'{u:.6f},{v:.6f}' for u,v in near['vertices'])
            parts.append(f'<polygon points="{pts}" fill="black"/>')
        parts.append('</mask>')
    parts.extend(['</defs>', f'<g id="{prefix}" stroke-linejoin="round" stroke-width="{.8/scale:.5f}">'])
    for face in faces:
        pts = ' '.join(f'{u:.6f},{v:.6f}' for u,v in face['local'])
        ox, oy = face['offset']
        transform = f'translate({tx+scale*ox:.3f} {ty+scale*oy:.3f}) scale({scale:.6f})'
        mask_id = mask_ids[(face['cube'], face['normal'])]
        c = ','.join(str(v) for v in face['center'])
        parts.append(f'<g transform="{transform}"><polygon points="{pts}" fill="{face["fill"]}" '
                     f'fill-opacity="{face["alpha"]:.3f}" '
                     f'stroke="{color(face["fill"], .66)}" '
                     f'stroke-opacity="{face.get("stroke_alpha", min(1,face["alpha"]+.13)):.3f}" '
                     f'mask="url(#{mask_id})" data-center="{c}"/></g>')
    parts.append('</g>')
    return '\n'.join(parts)


def panel_svg(faces, height, tag, title, description, *,
              generator='figures/generate_translation_tiling.py', filename=None):
    """A tightly cropped artwork-only panel for independent LaTeX placement."""
    points = [p for face in faces for p in face['vertices']]
    width = height * (max(p[0] for p in points)-min(p[0] for p in points)) / (
        max(p[1] for p in points)-min(p[1] for p in points))
    # One unit of padding protects the half-unit outline from clipping.
    filename = filename or tag
    return f'''<svg xmlns="http://www.w3.org/2000/svg" width="{width+2:.3f}" height="{height+2:.3f}" viewBox="0 0 {width+2:.3f} {height+2:.3f}" role="img" aria-labelledby="{tag}-title {tag}-desc">
<!-- Regenerate from the repository root:
     python {generator}
     No command-line flags are required; figure parameters are defined in the script.
     Export this panel for LaTeX:
     inkscape figures/{filename}.svg -o figures/{filename}.pdf
-->
<title id="{tag}-title">{escape(title)}</title>
<desc id="{tag}-desc">{escape(description)}</desc>
{draw(faces, (1, 1, width, height), tag)}
</svg>'''


def verify():
    assert {(p[0]+2*p[1]+3*p[2]) % 7 for p in CROSS} == set(range(7))
    # Check unique coverage in a box of lattice cells independently of the patch.
    for p in product(range(-8, 9), repeat=3):
        owners = [tuple(p[i]-cube[i] for i in range(3)) for cube in CROSS
                  if sum(w*(p[i]-cube[i]) for i,w in enumerate((1,2,3))) % 7 == 0]
        assert len(owners) == 1
    assert len(DENT_FREE_CENTERS) == 65
    assert len(DENT_REPAIRS) == 1
    assert len(DENT_REPAIRS[0][0]) == len(DENT_REPAIRS[0][1]) == 6
    assert all(count == 5 for count in DENT_REPAIRS[0][0].values())
    assert not dent_cells(DENT_FREE_CENTERS)
    assert all(DENT_FREE_COLORS[c] == TILE_COLORS[c] for c in LARGER_PATCHES[0])
    assert len({add(c, p) for c in DENT_FREE_CENTERS for p in CROSS}) == 7*65
    assert all((c[0]+2*c[1]+3*c[2]) % 7 == 0 for c in DENT_FREE_CENTERS)
    assert all(DENT_FREE_COLORS[c] != DENT_FREE_COLORS[d]
               for c, neighbors in DENT_FREE_CONTACTS.items() for d in neighbors)
    cubes = [(c, tuple((1+GAP)*c[i]+cube[i] for i in range(3)))
             for c in DENT_FREE_CENTERS for cube in CROSS]
    for i, (owner, p) in enumerate(cubes):
        for other, q in cubes[i+1:]:
            if owner != other:
                assert any(abs(p[j]-q[j]) >= 1-1e-8 for j in range(3))


def main():
    verify()
    prototile = surfaces([(0, 0, 0)], 0, .98)
    for face in prototile:
        shade = next(s for n, _, s in FACES if n == face['normal'])
        face['fill'] = color('#297fa9', shade)
    for key, faces, height, title, note in (
        ('prototile', prototile, 215, 'A seven-cube cross',
         'A central cube and its six face-neighbors.'),
        ('patch', surfaces(DENT_FREE_CENTERS, GAP, OPACITY, tile_colors=DENT_FREE_COLORS),
         340, 'A patch of a translational tiling of three-dimensional space',
         '65 complete translated crosses from the lattice x+2y+3z = 0 modulo 7. '
         'Display gaps separate the tiles; no empty cell has five or six occupied '
         'face-neighbors before adding gaps.'),
    ):
        tag = f'translation-tiling-{key}'
        image = panel_svg(faces, height, tag, title, note)
        (OUT / f'{tag}.svg').write_text(image+'\n', encoding='utf-8')
    print("Checked: 65 disjoint whole tiles, distinct colors at contacts, and no five- or six-neighbor dents.")
    print("Wrote translation-tiling-prototile.svg and translation-tiling-patch.svg.")


if __name__ == '__main__':
    main()
