# Tiling 3D by Translates of a Single Polycube is Undecidable

[Website](https://edemaine.github.io/translation-tiling-paper/) ·
[Paper (PDF)](https://edemaine.github.io/translation-tiling-paper/paper.pdf) ·
[Technical overview (PDF)](https://edemaine.github.io/translation-tiling-paper/slop.pdf)

Given a single polycube, can copies of it tile three-dimensional space using
only translations? We prove that this problem is undecidable, even when the
polycube is connected through faces. More precisely, the problem is co-RE
complete. Dimension three is optimal: the corresponding problem in two
dimensions is decidable.

## Files and build

- [paper.texlish](paper.texlish): human-written overview of the results,
  proof ideas, and Lean formalization.
- [slop.texlish](slop.texlish): LLM-written technical overview, with definitions,
  theorem statements, constructions, and proofs; no abstract or introduction.
- `paper.tex`, `slop.tex`: generated LaTeX.
- `paper.pdf`, `slop.pdf`: compiled documents.
- [paper.bib](paper.bib): bibliography with version-specific source links.
- [verification/check_activation.py](verification/check_activation.py): finite algebra checks.
- [figures/generate_connected.py](figures/generate_connected.py): exact connectedness-example renderer.
- [figures/](figures/): checked-in PDF figures needed to build the paper.

Build with [Texlish](https://texlish.org/),
LaTeX (including TikZ, subcaption, and tcolorbox), BibTeX, latexmk,
Python 3, and Make installed:

```sh
make
```

Alternatively, compile directly using the checked-in figures and Lean snippets,
without Python, Make, or latexmk:

```sh
texlish --pdf paper.texlish
texlish --pdf slop.texlish
```

Edit the `.texlish` sources, not the generated `.tex` files. Keep prose edits
to `paper.texlish` human-written; LLM-authored material belongs in `slop.texlish`.
The technical overview repeats the definitions and main theorem so it can be
read independently. Both documents use `paper.bib` and build independently.
Keep numbered references within each document.
TikZ diagrams are inline in the Texlish sources; panel captions use `subcaption`.

The paper includes a reduction overview. The technical overview includes
a two-Wang-tile Sudoku example, cycle and activation diagrams, and an exact
54,000-cube connectedness example. The Sudoku figure uses toy primes 3 and 5
to show the arithmetic;
the soundness theorem requires primes greater than 200. The connectedness
figure shows the final construction step on a small disconnected input,
rather than the output of the full reduction.

The three figure PDFs in `figures/` are checked in. `make figures` regenerates
these assets; include any updated PDFs when committing changes to the renderer.
The renderer uses only the Python standard library and
checks the cube counts, distinct residues, connectedness, and contact
between the two replacement pieces before writing vector PDFs.

## Website and GitHub Pages

With Pandoc also installed, run `make website` to build both PDFs and the
landing page from [website/index.md](website/index.md), styled by
[website/style.css](website/style.css). The published files are generated in
`build/site/`. To preview locally, run:

```sh
python3 -m http.server 8000 --directory build/site
```

Then open <http://localhost:8000/>.

[The Pages workflow](.github/workflows/pages.yml) builds the site on pull
requests and publishes it on pushes to `main` or manual runs on `main`.
In the repository's **Settings → Pages**, set **Source** to **GitHub Actions**.
The PDFs are built in CI and are not committed to the repository.

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

The mathematical ingredients from prior work are:

1. Berger's domino undecidability/completeness theorem.
2. Greenfeld–Tao, arXiv:2309.09504v2, Definition 5.1 and Proposition 5.2:
   soundness of the explicitly stated decorated Sudoku rule. The paper
   verifies the canonical solution directly.
3. Meyerovitch–Sanadhya–Solomon, arXiv:2211.07140v1, Lemma 2.1:
   rigidity of the explicitly defined component shapes. The paper supplies
   their assembly and the arbitrary-tiling correspondence of Theorem 1.1.
4. Bhattacharya, arXiv:1602.05738v1: planar periodicity and decidability.
5. Kim, arXiv:2508.11725v2, Section 2 and Theorem 2.5: a reduction
   making tiles face-connected while preserving dimension and tile count.
   The paper defines its partition and assembly explicitly and supplies
   the one-tile equivalence using the rigidity statement of Lemma 2.4.

The cyclic gadgets are adapted and reproved from Sections 3–6 of OpenAI's
*A translational tile with no fully periodic tiling in dimension three*,
dated September 23, 2026. The bibliography pins repository commit
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`, inspected October 7, 2026.
The paper uses MSS for arbitrary-tiling descent; it does not substitute
the periodic-only descent in Section 7 of the OpenAI preprint.

The Lean formalization proves the infinite reduction and all mathematical
inputs. The Python checks below provide additional checks of the finite
gadget algebra.

## Lean formalization

Start with [Abstract.lean](lean/TranslationTiling/Abstract.lean), the
human-readable definitions and main theorem statements typeset in the paper.
It defines finite prototiles as lists of points `Fin 3 → ℤ`, face-connectivity,
lattice tiling by unique covering translates, and real tiling by almost-everywhere
unique coverage by translates of the union of closed unit cubes. It states
co-RE completeness and undecidability for connected prototiles in both
`Z^3` and `R^3`.

[AbstractBridge.lean](lean/TranslationTiling/AbstractBridge.lean) proves these
results using the rest of the formalization, which uses the same model `Fin 3 → ℤ`
of `ℤ³`. It proves that connectivity and both tiling predicates agree with the
project's definitions, and derives the complexity results. Readers can check what
is claimed in `Abstract.lean`; Lean verifies the bridge and the underlying proofs.

[Statements.lean](lean/TranslationTiling/Statements.lean) collects the broader
public interface, including compiler effectivity and dimension optimality.
The complete computable Wang-to-tile reduction,
connected and Euclidean co-RE completeness, and dimension optimality are proved
without imported mathematical hypotheses. All mathematical inputs are proved
in the project or its pinned dependencies. Proofs are in `lean/TranslationTiling/`.

The project pins the GitHub Wang formalization, rather than a local checkout.
Build from `lean/` with `lake update`, `lake exe cache get`, and `lake build`.
See [lean/README.md](lean/README.md) for checked proofs, build instructions,
and existing online formalizations. An axiom audit rejects
unfinished proofs and assumptions beyond Lean's three standard axioms.

## Finite verification

These Python checks predate the completed Lean formalization. The Lean proofs
now establish the gadget properties for all required parameters, superseding
these finite checks as justification for the results. The scripts are retained
as an extra sanity check of small finite instances.

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
