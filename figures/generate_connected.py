"""Render the exact small Kim example as vector PDFs using only Python's stdlib.

Run from the repository root: python3 figures/generate_connected.py
The PDFs are checked-in figure assets. Geometry follows paper.texlish, Section 6.3,
and Kim, arXiv:2508.11725v2, Section 2. No cubes, bumps, or dents are omitted.
"""

from itertools import product
from math import sqrt
from pathlib import Path


BLUE = (0.16, 0.43, 0.65)
ORANGE = (0.85, 0.42, 0.15)
PALETTE = (
    BLUE, ORANGE, (0.24, 0.62, 0.48), (0.59, 0.42, 0.69),
    (0.72, 0.61, 0.24), (0.20, 0.63, 0.70), (0.72, 0.36, 0.46),
    (0.48, 0.51, 0.56),
)
AXES = ((1, 0, 0), (0, 1, 0), (0, 0, 1))


def add(p, q):
    return tuple(a + b for a, b in zip(p, q))


def neighbors(p):
    for axis in AXES:
        yield add(p, axis)
        yield add(p, tuple(-v for v in axis))


def connected(points):
    unseen = set(points)
    pending = [unseen.pop()]
    while pending:
        for q in neighbors(pending.pop()):
            if q in unseen:
                unseen.remove(q)
                pending.append(q)
    return not unseen


def label(m, x, y, z):
    if x <= m and 1 <= y <= m and z == 0:
        return y
    if 1 <= x <= m and y <= m and z == m + 1:
        return x
    if x == 0 and 1 <= y <= m and 1 <= z <= m:
        return y
    if 1 <= x <= m and y == 0 and 1 <= z <= m:
        return x
    if 1 <= x <= m + 1 and 1 <= y <= m + 1 and 1 <= z <= m:
        return z
    return 1


def shell(l):
    m = l**3 - (l - 2)**3
    s = 3*m + 6
    pieces = [set() for _ in range(m)]
    for p in product(range(m + 2), repeat=3):
        i = label(m, *p) - 1
        for delta in product(range(3), repeat=3):
            pieces[i].add(tuple(3*p[j] + delta[j] for j in range(3)))
    dents = {(s-1, 1, 1), (1, s-1, 1), (1, 1, s-1)}
    assert dents <= pieces[0]
    pieces[0] -= dents
    pieces[0] |= {(-1, 1, 1), (1, -1, 1), (1, 1, -1)}
    assert all(connected(q) for q in pieces)
    boundary = [p for p in product(range(l), repeat=3)
                if any(v in (0, l-1) for v in p)]
    result = {}
    for i, (x, piece) in enumerate(zip(boundary, pieces)):
        for p in piece:
            target = tuple(s*x[j] + p[j] for j in range(3))
            assert target not in result
            result[target] = PALETTE[i]
    assert len(result) == s**3
    assert len({tuple(v % s for v in p) for p in result}) == s**3
    assert connected(result)
    return s, result


def project(p):
    # Orthographic camera at (1,-2,2); the diagonal (1,1,1) is visible.
    x, y, z = p
    return ((2*x + y)/sqrt(5), (-2*x + 4*y + 5*z)/sqrt(45))


def write_pdf(path, content, width, height):
    # A minimal vector-only PDF; labels are typeset by the surrounding LaTeX.
    objects = [
        b"<< /Type /Catalog /Pages 2 0 R >>",
        b"<< /Type /Pages /Kids [3 0 R] /Count 1 >>",
        (f"<< /Type /Page /Parent 2 0 R /MediaBox [0 0 {width} {height}] "
         "/Resources << >> /Contents 4 0 R >>").encode(),
        f"<< /Length {len(content)} >>\nstream\n".encode() + content + b"\nendstream",
    ]
    result = bytearray(b"%PDF-1.4\n%\xe2\xe3\xcf\xd3\n")
    offsets = [0]
    for i, obj in enumerate(objects, 1):
        offsets.append(len(result))
        result.extend(f"{i} 0 obj\n".encode() + obj + b"\nendobj\n")
    xref = len(result)
    result.extend(f"xref\n0 {len(objects)+1}\n0000000000 65535 f \n".encode())
    for offset in offsets[1:]:
        result.extend(f"{offset:010d} 00000 n \n".encode())
    result.extend((f"trailer\n<< /Size {len(objects)+1} /Root 1 0 R >>\n"
                   f"startxref\n{xref}\n%%EOF\n").encode())
    path.write_bytes(result)


def render(path, voxels, width=300, height=280):
    # Exposed, camera-facing unit squares, sorted from back to front.
    # Unit faces keep the visibility ordering independent of mesh simplification.
    face_specs = (
        ((1, 0, 0), ((1,0,0), (1,1,0), (1,1,1), (1,0,1)), .77),
        ((0,-1, 0), ((0,0,0), (1,0,0), (1,0,1), (0,0,1)), .62),
        ((0, 0, 1), ((0,0,1), (1,0,1), (1,1,1), (0,1,1)), 1.0),
    )
    faces = []
    for p, color in sorted(voxels.items()):
        for normal, corners, shade in face_specs:
            if add(p, normal) in voxels:
                continue
            points = [add(p, corner) for corner in corners]
            center = tuple(sum(q[j] for q in points)/4 for j in range(3))
            depth = center[0] - 2*center[1] + 2*center[2]
            faces.append((depth, [project(q) for q in points],
                          tuple(shade*c for c in color)))
    faces.sort(key=lambda f: f[0])
    all_points = [q for _, points, _ in faces for q in points]
    xmin, xmax = min(p[0] for p in all_points), max(p[0] for p in all_points)
    ymin, ymax = min(p[1] for p in all_points), max(p[1] for p in all_points)
    scale = min((width-12)/(xmax-xmin), (height-12)/(ymax-ymin))
    tx = width/2 - scale*(xmin+xmax)/2
    ty = height/2 - scale*(ymin+ymax)/2
    commands = ["0.1 w 1 j"]
    previous = None
    for _, points, color in faces:
        if color != previous:
            rgb = " ".join(f"{v:.3f}" for v in color)
            commands.append(f"{rgb} rg {rgb} RG")
            previous = color
        coordinates = [(scale*x+tx, scale*y+ty) for x, y in points]
        commands.append(" ".join(f"{x:.3f} {y:.3f} {'m' if i == 0 else 'l'}"
                                 for i, (x, y) in enumerate(coordinates)) + " h B")
    write_pdf(path, "\n".join(commands).encode(), width, height)
    print(f"{path}: {len(voxels):,} cubes, {len(faces):,} exposed front faces")


def main():
    output = Path(__file__).resolve().parent
    original = {(0,0,0): BLUE, (1,1,1): ORANGE}
    s, assembly = shell(2)
    replacement = {}
    copies = []
    for e, color in original.items():
        copy = {tuple(s*e[j] + p[j] for j in range(3)) for p in assembly}
        assert not (copy & replacement.keys())
        copies.append(copy)
        replacement.update(dict.fromkeys(copy, color))
    assert len(assembly) == 27000
    assert len(replacement) == 54000 and connected(replacement)
    contacts = sum(q in copies[1] for p in copies[0] for q in neighbors(p))
    assert contacts > 0
    print(f"Two disjoint copies of S_2 have {contacts:,} shared unit faces.")
    render(output / "kim-input.pdf", original)
    render(output / "kim-shell.pdf", assembly)
    render(output / "kim-connected.pdf", replacement)


if __name__ == "__main__":
    main()
