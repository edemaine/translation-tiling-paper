#!/usr/bin/env python3
"""Exhaustive small-instance checks of the forward activation maps.

These are checks of the algebra, not a proof of the infinite reduction.
No inverse formula from the paper is used to establish bijectivity here.
The ordinary test has two CRT digits and exercises both active labels.
The seed test uses 19 residue labels with regions of sizes 3, 4, and 12.
Only the cardinality and the label permutations of S enter this test;
this small S is not the huge two-prime residue group in the paper.

Run with Python 3.9 or later; no third-party packages are needed.
"""

from itertools import product
from math import gcd, lcm


def crt(residues, moduli):
    value, modulus = 0, 1
    for residue, next_modulus in zip(residues, moduli):
        assert gcd(modulus, next_modulus) == 1
        value += modulus * ((residue - value) * pow(modulus, -1, next_modulus) % next_modulus)
        modulus *= next_modulus
    return value % modulus


def shift_list(a, b):
    entries = []
    for alpha, xi in product(range(a), range(b)):
        multiplicity = 1 + ((alpha, xi) in [(0, 0), (1, 1)]) - ((alpha, xi) in [(1, 0), (0, 1)])
        entries.extend([(alpha, xi)] * multiplicity)
    rho_a, rho_b = [0] * len(entries), [0] * len(entries)
    for xi in range(b):
        indices = [d for d, entry in enumerate(entries) if entry[1] == xi]
        assert len(indices) == a
        for assigned, d in enumerate(indices):
            rho_a[d] = (assigned - entries[d][0]) % a
    for alpha in range(a):
        indices = [d for d, entry in enumerate(entries) if entry[0] == alpha]
        assert len(indices) == b
        for assigned, d in enumerate(indices):
            rho_b[d] = (assigned - entries[d][1]) % b
    return entries, rho_a, rho_b


def digit_blocks(r, a, b):
    # Require both block sizes, to test both branches of the construction.
    for count_b in range(1, r // b + 1):
        if (r - count_b * b) % a == 0 and r - count_b * b > 0:
            sizes = [a] * ((r - count_b * b) // a) + [b] * count_b
            break
    else:
        raise AssertionError('No mixed block partition')
    blocks, start = [], 0
    for size in sizes:
        blocks.append(tuple(range(start, start + size)))
        start += size
    assert start == r
    return blocks


def block_outputs(blocks, a, b, r):
    colors = [None] * r
    rotations = [[None] * r for _ in range(lcm(a, b))]
    for block in blocks:
        for label, point in enumerate(block):
            colors[point] = (label, 0) if len(block) == a else (0, label)
            for t, rotation in enumerate(rotations):
                rotation[point] = block[(label + t) % len(block)]
    assert all(color is not None for color in colors)
    assert all(len(set(rotation)) == r for rotation in rotations)
    return colors, rotations


def check_ordinary():
    a, b = 5, 7
    digits = (17, 19)
    r = digits[0] * digits[1]
    entries, rho_a, rho_b = shift_list(a, b)
    offsets = [crt((ra, rb), (a, b)) for ra, rb in zip(rho_a, rho_b)]
    checked = 0
    for active in range(2):
        blocks = []
        for other in range(digits[1 - active]):
            for digit_block in digit_blocks(digits[active], a, b):
                blocks.append(tuple(crt((d, other) if active == 0 else (other, d), digits)
                                    for d in digit_block))
        colors, rotations = block_outputs(blocks, a, b, r)
        for t in range(lcm(a, b)):
            images = set()
            for d, (ea, eb) in enumerate(entries):
                rotation = rotations[(t - offsets[d]) % len(rotations)]
                for source in range(r):
                    ca, cb = colors[source]
                    image = ((ca + ea) % a, (cb + eb) % b, rotation[source])
                    assert image not in images, ('ordinary collision', active, t, image)
                    images.add(image)
            assert len(images) == r * a * b
            checked += len(images)
    print(f'ordinary block maps: {checked:,} forward images checked', flush=True)


def seed_label_spaces():
    # (region, copy, label for eta_1 or None, label for eta_2 or None)
    labels = [(1, 0, None, y2) for y2 in range(3)]
    labels += [(2, copy, y1, None) for copy in range(2) for y1 in range(2)]
    labels += [(0, copy, y1, y2) for copy in range(2)
               for y1 in range(2) for y2 in range(3)]
    assert len(labels) == 19
    index = {label: i for i, label in enumerate(labels)}
    rotations = []
    for t in range(6):
        rotations.append([index[(region, copy,
                                 None if y1 is None else (y1 + t) % 2,
                                 None if y2 is None else (y2 + t) % 3)]
                          for region, copy, y1, y2 in labels])
    return labels, rotations


def check_seeds():
    labels, residue_rotations = seed_label_spaces()
    total = 0
    for seed, a, b, r, other_a in [(1, 2, 23, 31, 3), (2, 3, 29, 41, 2)]:
        assert b > len(labels) and len(labels) % a != 0
        entries, rho_a, rho_b = shift_list(a, b)
        period = lcm(a, b, other_a)
        offsets = [crt((ra, rb, 0), (a, b, other_a)) for ra, rb in zip(rho_a, rho_b)]
        colors, rotations = block_outputs(digit_blocks(r, a, b), a, b, r)
        expected = len(labels) * r * a * b
        for t in range(period):
            images = set()
            for d, (ea, eb) in enumerate(entries):
                source_t = t - offsets[d]
                block_rotation = rotations[source_t % len(rotations)]
                residue_rotation = residue_rotations[source_t % 6]
                for s, label in enumerate(labels):
                    z = residue_rotation[s]
                    if label[0] == seed:
                        for source in range(r):
                            ca, cb = colors[source]
                            image = ((ca + ea) % a, (cb + eb) % b, block_rotation[source], z)
                            assert image not in images, ('active seed collision', seed, t, image)
                            images.add(image)
                    else:
                        ca = label[seed + 1]
                        assert ca is not None
                        for source in range(r):
                            image = ((ca + ea) % a, eb, source, z)
                            assert image not in images, ('inactive seed collision', seed, t, image)
                            images.add(image)
            assert len(images) == expected
            total += len(images)
        print(f'seed {seed}: all {period} horizontal residues checked', flush=True)
    print(f'shared-output seed maps: {total:,} forward images checked', flush=True)


def check_shear():
    count = 0
    for r in (31, 41, 323):
        for x, k, h, beta in product((-100, -1, 0, 1, 100),
                                      (0, 1, r - 1), (-2 * r - 3, -1, 0, 1, 2 * r + 5),
                                      (0, 1, r - 1)):
            source_x, source_k = x - h, (k - h) % r
            source_v = (source_x + (source_k - source_x) % r + r * beta) % (r * r)
            target_v = (x + (k - x) % r + r * beta) % (r * r)
            assert (source_v + h) % (r * r) == target_v
            count += 1
    print(f'sheared cyclic coordinate: {count:,} signed cases checked', flush=True)


if __name__ == '__main__':
    check_ordinary()
    check_seeds()
    check_shear()
    print('All finite activation checks passed.', flush=True)
