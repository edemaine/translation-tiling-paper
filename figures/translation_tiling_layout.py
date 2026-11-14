"""Whole-tile patch selection, spacing, and seeded animation perturbations.

This shared library supplies the animation generator. It does not write files.
"""

from dataclasses import dataclass
from collections import defaultdict
from itertools import product
from math import floor, sqrt
import random

if __package__:
    from . import generate_translation_tiling as base
else:
    import generate_translation_tiling as base


CENTERS = base.DENT_FREE_CENTERS
BASE_HORIZONTAL = {c: base.dot(c, base.RIGHT) for c in CENTERS}
BASE_SPAN = max(BASE_HORIZONTAL.values())-min(BASE_HORIZONTAL.values())
LEFT_HORIZONTAL_GAP = 12.0
RIGHT_GAP = base.GAP
HORIZONTAL_SHIFT = (LEFT_HORIZONTAL_GAP-RIGHT_GAP)*(.8*BASE_SPAN)/2
CLEARANCE = .015
NEIGHBORS = tuple(product((-1, 0, 1), repeat=3))


@dataclass(frozen=True)
class Study:
    key: str
    label: str
    note: str
    left_transverse_gap: float = RIGHT_GAP
    jitter_strength: float = 0
    seed: int = 17


BASE_STUDY = Study(
    'spacing-all-wide', 'Horizontal, vertical, and depth spacing',
    'The left also opens vertically and in depth. All three spacings settle to the current spacing on the right.',
    left_transverse_gap=3.0,
)


JITTER_STUDIES = tuple(
    Study('spacing-all-jitter-'+name, name.capitalize()+' random perturbation',
          'The three-direction layout with random translations proportional to local extra spacing. '
          'The packed end is unchanged; opacity stays uniform.',
          left_transverse_gap=3.0, jitter_strength=strength)
    for name, strength in (('mild', .25), ('medium', .5), ('strong', 1.0),
                           ('extra', 2.0), ('extreme', 3.0))
)


@dataclass
class Patch:
    centers: list
    colors: dict

    def __post_init__(self):
        self.horizontal = {c: base.dot(c, base.RIGHT) for c in self.centers}
        self.left = min(self.horizontal.values())
        self.span = max(self.horizontal.values())-self.left
        self.transition = .8*self.span

    @property
    def count(self):
        return len(self.centers)


def make_patch(radius, vertical_radius=0):
    if radius == 0 and vertical_radius == 0:
        return Patch(CENTERS, base.DENT_FREE_COLORS)
    # (3,2,0) belongs to the tiling lattice and projects almost horizontally:
    # about 3.60 units across, 0.05 vertically, and 0.09 in depth.
    centers = {tuple(c[i]+k*(3, 2, 0)[i]+j*(-1, 1, 2)[i] for i in range(3))
               for c in CENTERS for k in range(-radius, radius+1)
               for j in range(-vertical_radius, vertical_radius+1)}
    # (-1,1,2) is another lattice vector, projecting nearly vertically:
    # -0.32 across, 2.42 upward, and -0.19 in depth per added layer.
    centers, _ = base.fill_dents(centers)
    # x+y-z modulo 5 properly colors all face/edge/vertex contacts in this
    # lattice. Split one independent color class to use the sixth palette hue.
    colors = {}
    for c in centers:
        index = (c[0]+c[1]-c[2]) % 5
        colors[c] = 5 if index == 0 and sum(c) % 2 else index
    return Patch(centers, colors)


def forbidden_intervals(fixed, placed):
    """Horizontal center positions that would overlap an already placed cube.

    The moving tile's center is u*RIGHT + fixed. Its seven cubes are rigid;
    each pair of unit cubes excludes an interval of values of u. This lets us
    correct a few collisions without rotating, deforming, or overlapping tiles.
    """
    intervals = []
    for other in placed:
        if abs(fixed[2]-other[2]) >= 3:
            continue  # Horizontal motion cannot bridge the vertical gap.
        for a in base.CROSS:
            for b in base.CROSS:
                low, high = -float('inf'), float('inf')
                for i, coefficient in enumerate(base.RIGHT):
                    constant = fixed[i]+a[i]-other[i]-b[i]
                    if abs(coefficient) < 1e-12:
                        if abs(constant) >= 1-1e-10:
                            low, high = 1, 0
                            break
                    else:
                        first_bound = (-1-constant)/coefficient
                        second_bound = (1-constant)/coefficient
                        low = max(low, min(first_bound, second_bound))
                        high = min(high, max(first_bound, second_bound))
                if low < high:
                    intervals.append((low-CLEARANCE, high+CLEARANCE))
    merged = []
    for low, high in sorted(intervals):
        if merged and low <= merged[-1][1]:
            merged[-1] = (merged[-1][0], max(high, merged[-1][1]))
        else:
            merged.append((low, high))
    return merged


def extra_spacing(center, study, patch):
    t = max(0, min(1, (patch.horizontal[center]-patch.left)/patch.transition))
    horizontal = 2*HORIZONTAL_SHIFT/patch.transition*(1-t)
    transverse = (study.left_transverse_gap-RIGHT_GAP)*(1-t)**3
    return sqrt((horizontal*horizontal+2*transverse*transverse)/3)


def insert_tile(buckets, center, position):
    for cube in base.CROSS:
        point = base.add(position, cube)
        bucket = tuple(floor(v/(1+2e-8)) for v in point)
        buckets[bucket].append((center, point))


def intersects(center, position, buckets):
    for cube in base.CROSS:
        point = base.add(position, cube)
        bucket = tuple(floor(v/(1+2e-8)) for v in point)
        for delta in NEIGHBORS:
            for other, q in buckets.get(base.add(bucket, delta), ()):
                if other != center and all(abs(point[i]-q[i]) < 1-1e-8 for i in range(3)):
                    return True
    return False


def perturb_positions(original, study, patch):
    # Reserve all original poses as well as the accepted perturbed poses.
    # This guarantees that shortening an offset to zero always leaves room.
    reserved, accepted = defaultdict(list), defaultdict(list)
    for center, position in original.items():
        insert_tile(reserved, center, position)
    result = {}
    for center in sorted(patch.centers, key=lambda c: (-patch.horizontal[c], c)):
        amplitude = study.jitter_strength*extra_spacing(center, study, patch)
        if amplitude == 0:
            position = original[center]
        else:
            rng = random.Random(f'{study.seed}:{center[0]},{center[1]},{center[2]}')
            while True:
                direction = tuple(rng.uniform(-1, 1) for _ in range(3))
                if base.dot(direction, direction) <= 1:
                    break  # Uniform sample in the unit ball; bounded displacement.
            for fraction in (1, .75, .5, .25, 0):
                position = tuple(original[center][i]+amplitude*fraction*direction[i]
                                 for i in range(3))
                if not intersects(center, position, reserved) and not intersects(center, position, accepted):
                    break
            else:
                raise AssertionError(('No collision-free perturbation', center))
        result[center] = position
        insert_tile(accepted, center, position)
    return result


def positions_for(study, patch):
    """Spread centers in all three camera directions; keep closure horizontal."""
    if study.jitter_strength:
        original = getattr(patch, 'all_positions', None)
        if original is None:
            original = positions_for(BASE_STUDY, patch)
        return perturb_positions(original, study, patch)
    placed = {}
    previous_u = float('inf')
    for center in sorted(patch.centers, key=lambda c: (-patch.horizontal[c], c)):
        t = max(0, min(1, (patch.horizontal[center]-patch.left)/patch.transition))
        # Integrating the horizontal gap makes the positions quadratic. The
        # final fifth exactly matches the accepted layout.
        target_u = ((1+RIGHT_GAP)*patch.horizontal[center]
                    - HORIZONTAL_SHIFT*(1-t)**2)
        transverse = 1+RIGHT_GAP+(study.left_transverse_gap-RIGHT_GAP)*(1-t)**3
        v = transverse*base.dot(center, base.UP)
        depth = transverse*base.dot(center, base.EYE)
        fixed = tuple(v*base.UP[i]+depth*base.EYE[i] for i in range(3))
        u = min(target_u, previous_u)
        intervals = forbidden_intervals(fixed, placed.values())
        for low, high in reversed(intervals):
            if low < u < high:
                u = low
        previous_u = u
        placed[center] = tuple(u*base.RIGHT[i]+fixed[i] for i in range(3))
    if study.key == BASE_STUDY.key:
        patch.all_positions = placed
    return placed



def faces_for(positions, patch):
    faces = base.surfaces(patch.centers, 0, base.OPACITY, tile_colors=patch.colors)
    for face in faces:
        center = face['center']
        target = positions[center]
        delta = tuple(target[i]-center[i] for i in range(3))
        face['depth'] += base.dot(delta, base.EYE)
        face['offset'] = offset = base.project(target)
        face['vertices'] = [(x+offset[0], y+offset[1]) for x, y in face['local']]
    return sorted(faces, key=lambda f: f['depth'])


def check(positions, patch):
    original = {base.add(c, p): c for c in patch.centers for p in base.CROSS}
    assert len(original) == 7*patch.count
    assert not base.dent_cells(patch.centers)
    assert all((c[0]+2*c[1]+3*c[2]) % 7 == 0 for c in patch.centers)
    for p, owner in original.items():
        for delta in NEIGHBORS:
            other = original.get(base.add(p, delta))
            if other is not None and other != owner:
                assert patch.colors[owner] != patch.colors[other]
    cubes = [(c, tuple(positions[c][i]+p[i] for i in range(3)))
             for c in patch.centers for p in base.CROSS]
    contacts = set()
    buckets = defaultdict(list)
    for owner, p in cubes:
        bucket = tuple(floor(v/(1+2e-8)) for v in p)
        for delta in NEIGHBORS:
            for other, q in buckets.get(base.add(bucket, delta), ()):
                if owner != other:
                    distances = [abs(p[j]-q[j]) for j in range(3)]
                    assert any(d >= 1-1e-8 for d in distances), (owner, other)
                    if all(d <= 1+1e-8 for d in distances):
                        contacts.add(tuple(sorted((owner, other))))
        buckets[bucket].append((owner, p))
    assert all(patch.colors[a] != patch.colors[b] for a, b in contacts)
    for center in patch.centers:
        if patch.horizontal[center] >= patch.left+patch.transition:
            assert all(abs(positions[center][i]-(1+base.GAP)*center[i]) < 1e-8
                       for i in range(3)), 'The packed end must match the current figure'
