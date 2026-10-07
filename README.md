# Translational monotiling in dimension three

Working draft of a reduction from Wang tiling to tiling all of `Z^3`
with translations of a single finite face-connected tile (a polycube).
The draft also proves co-RE completeness, explains dimension optimality,
and gives the corresponding result for connected integer unit-cube unions with
arbitrary real translations.

## Files and build

- [paper.texlish](paper.texlish): human-written abstract and introduction.
- [slop.texlish](slop.texlish): LLM-written technical overview, with definitions,
  theorem statements, constructions, and proofs; no abstract or introduction.
- `paper.tex`, `slop.tex`: generated LaTeX; both sources use Texlish 0.2.0 syntax.
- `paper.pdf`, `slop.pdf`: compiled documents.
- [paper.bib](paper.bib): bibliography with version-specific source links.
- [verification/check_activation.py](verification/check_activation.py): finite algebra checks.
- [figures/generate_connected.py](figures/generate_connected.py): exact connectedness-example renderer.
- [figures/](figures/): checked-in PDF figures needed to build the paper.

Build with Texlish, LaTeX (including TikZ and subcaption), BibTeX, latexmk,
and Make installed:

```sh
make
```

Equivalently:

```sh
texlish paper.texlish
texlish slop.texlish
latexmk -pdf -interaction=nonstopmode -halt-on-error slop.tex
latexmk -pdf -interaction=nonstopmode -halt-on-error paper.tex
```

Edit the `.texlish` sources, not the generated `.tex` files. Keep prose edits
to `paper.texlish` human-written; LLM-authored material belongs in `slop.texlish`.
The technical overview repeats the definitions and main theorem so it can be
read independently. Both documents use `paper.bib` and build independently.
Keep numbered references within each document.
TikZ diagrams are inline in the Texlish sources; panel captions use `subcaption`.

The introduction includes a reduction overview. The technical overview includes
a two-Wang-tile Sudoku example, cycle and activation diagrams, and an exact
54,000-cube connectedness example. The Sudoku figure uses toy primes 3 and 5
to show the arithmetic;
the soundness theorem requires primes greater than 200. The connectedness
figure shows the final construction step on a small disconnected input,
rather than the output of the full reduction.

The three figure PDFs in `figures/` are checked in, so building the paper
does not require Python. With Python 3 installed, `make figures` regenerates
these assets; include any updated PDFs when committing changes to the renderer.
The renderer uses only the Python standard library and
checks the cube counts, distinct residues, connectedness, and contact
between the two replacement pieces before writing vector PDFs.

## Argument and dependencies

The technical overview defines the decorated Sudoku word rule and canonical
solution,
supplies the graph, dependence, cycle, activation, common-solution,
and stacking arguments, explicitly builds a lattice tile from rigid
component shapes, and then applies an explicit connectedness construction.
The change from the one-prime construction is to
use decorated two-prime symbols and let seed `t` restrict both arithmetic
components to `t`, leaving the Wang label free. Residues are indexed by
`S = (Z/(pq)^2 Z)^2`; only the cyclic coordinate of order `|S|` enters the
ambient finite group.

The external mathematical inputs are:

1. Berger's domino undecidability/completeness theorem.
2. Greenfeld–Tao, arXiv:2309.09504v2, Definition 5.1 and Proposition 5.2:
   soundness of the explicitly stated decorated Sudoku rule. The draft
   verifies the canonical solution directly.
3. Meyerovitch–Sanadhya–Solomon, arXiv:2211.07140v1, Lemma 2.1:
   rigidity of the explicitly defined component shapes. The draft supplies
   their assembly and the arbitrary-tiling correspondence of Theorem 1.1.
4. Bhattacharya, arXiv:1602.05738v1: planar periodicity and decidability.
5. Kim, arXiv:2508.11725v2, Section 2 and Theorem 2.5: a reduction
   making tiles face-connected while preserving dimension and tile count.
   The draft defines its partition and assembly explicitly and supplies
   the one-tile equivalence using the rigidity statement of Lemma 2.4.

The cyclic gadgets are adapted and reproved from Sections 3–6 of OpenAI's
*A translational tile with no fully periodic tiling in dimension three*,
dated September 23, 2026. The bibliography pins repository commit
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`, inspected October 7, 2026.
The draft uses MSS for arbitrary-tiling descent; it does not substitute
the periodic-only descent in Section 7 of the OpenAI preprint.

The Lean formalization is in progress; the main reduction is not yet formally
proved. The finite checks below do not prove the infinite reduction or
independently verify the imported theorems.

## Lean formalization

[lean/TranslationTiling/Statements.lean](lean/TranslationTiling/Statements.lean) collects
the short formal statements. Proved theorems and outstanding `Claims` are
distinguished explicitly. Proofs are in `lean/TranslationTiling/Proofs/`; the external
mathematical hypotheses are explicit propositions in `lean/TranslationTiling/External/`.

The project pins the GitHub Wang formalization, rather than a local checkout.
Build from `lean/` with `lake update`, `lake exe cache get`, and `lake build`.
See [lean/README.md](lean/README.md) for checked results, remaining proof
obligations, and existing online formalizations. An axiom audit rejects
unfinished proofs and assumptions beyond Lean's three standard axioms.

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
