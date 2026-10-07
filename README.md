# Translational monotiling in dimension three

Working draft of a reduction from Wang tiling to tiling all of `Z^3`
with translations of a single finite, possibly disconnected tile.
The draft also proves co-RE completeness, explains dimension optimality,
and gives the corresponding result for integer unit-cube unions with
arbitrary real translations.

## Files and build

- [paper.texlish](paper.texlish): authoritative source, in Texlish 0.2.0 syntax.
- [paper.tex](paper.tex): generated LaTeX.
- [paper.pdf](paper.pdf): compiled draft.
- [paper.bib](paper.bib): bibliography with version-specific source links.
- [verification/check_activation.py](verification/check_activation.py): finite algebra checks.

Build with Texlish, LaTeX, BibTeX, and latexmk installed:

```sh
make
```

Equivalently:

```sh
texlish paper.texlish
latexmk -pdf -interaction=nonstopmode -halt-on-error paper.tex
```

Edit `paper.texlish`, not `paper.tex`.

## Argument and dependencies

The paper supplies the graph, dependence, cycle, activation, common-solution,
and stacking arguments. The change from the one-prime construction is to
use decorated two-prime symbols and let seed `t` restrict both arithmetic
components to `t`, leaving the Wang label free. Residues are indexed by
`S = (Z/(pq)^2 Z)^2`; only the cyclic coordinate of order `|S|` enters the
ambient finite group.

The external mathematical inputs are:

1. Berger's domino undecidability/completeness theorem.
2. Greenfeld–Tao, arXiv:2309.09504v2, Definition 5.1 and Proposition 5.2:
   the decorated Sudoku rule, its soundness, and its canonical model.
3. Meyerovitch–Sanadhya–Solomon, arXiv:2211.07140v1, Theorem 1.1:
   the effective quotient reduction preserving arbitrary tilings and the
   number of prototiles.
4. Bhattacharya, arXiv:1602.05738v1: planar periodicity and decidability.

The cyclic gadgets are adapted and reproved from Sections 3–6 of OpenAI's
*A translational tile with no fully periodic tiling in dimension three*,
dated September 23, 2026. The bibliography pins repository commit
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`, inspected October 7, 2026.
The draft uses MSS for arbitrary-tiling descent; it does not substitute
the periodic-only descent in Section 7 of the OpenAI preprint.

This is a draft mathematical argument, not a formal verification.
In particular, the finite checks below do not prove the infinite reduction
or independently verify the imported theorems.

## Finite verification

With Python 3.9 or later:

```sh
python verification/check_activation.py
```

The checker enumerates forward maps and detects collisions directly,
without using the inverse formulas as an oracle. It checks:

- Both active digits of a two-digit ordinary channel, including both
  block sizes, for every relevant horizontal residue.
- Both seed tests with the same auxiliary output permutation, all three
  active/inactive regions, both block sizes, and every relevant horizontal
  residue. The small abstract residue set has size 19; this tests the
  label-space algebra, not the enormous two-prime Sudoku instance.
- Signed shifts and boundary residues in the sheared cyclic coordinate.

The run on October 7, 2026 passed 791,350 ordinary-map images,
15,531,474 seed-map images, and 675 shear cases.
Low-coordinate targets merely reindex the enumerated source inputs;
residue targets similarly reindex the source residues. These reindexings
are why the checker need not rerun each target separately.

The PDF was compiled, checked for unresolved references and overfull boxes,
and rendered for visual inspection. Rendering intermediates are in the
ignored `build/` directory.
