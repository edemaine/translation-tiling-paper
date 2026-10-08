# Lean formalization

The complete computable Wang-to-tile reduction and co-r.e.-completeness in
dimension three are proved unconditionally. Its output is a nonempty,
face-connected tile, tileable exactly when the input Wang tiles tile the plane.

Start with [Abstract.lean](TranslationTiling/Abstract.lean) for the
human-readable definitions and main theorem statements used in the paper.
Its prototiles are lists of integer triples; connectivity is defined by paths
of adjacent points, lattice tiling by unique decompositions, and real tiling
by almost-everywhere unique coverage by translates of the solid body. The
statements give co-r.e.-completeness for connected prototiles in both `ℤ³`
and `ℝ³`, and undecidability in `ℤ³`.

[AbstractBridge.lean](TranslationTiling/AbstractBridge.lean) proves these
statements from the rest of the development. It identifies integer triples
with `Fin 3 → ℤ` by computable inverse maps, proves equivalence of the
connectivity and lattice/real tiling predicates, and transfers co-r.e.-completeness
and undecidability. The definitions and theorem statements in `Abstract.lean`
make the claims inspectable; Lean checks the bridge and the underlying proofs.

Read [Statements.lean](TranslationTiling/Statements.lean) for the broader public
interface, including the compiler and dimension-optimality results.
`compiler_effectivity` and `compiler_correct`
prove uniform computability and connected correctness. Every public theorem,
including `reduction`, `connected_completeness`, `real_completeness`, and
`dimension_optimality`, has no imported mathematical hypothesis. The former
inputs appear as proved theorems: `sudoku_soundness`, `mss_rigidity`,
`kim_coset_rigidity`, and `planar_periodicity`. There is no assumed compiler
certificate or outstanding `Claims` namespace.

## Build

The project uses Lean 4.31.0 and the GitHub dependency
[`edemaine/lean-wang`](https://github.com/edemaine/lean-wang/tree/6c4711c2329b444bc3096e883912e00773dcce50),
pinned to `6c4711c2329b444bc3096e883912e00773dcce50`. There is no local-path
dependency. `lake-manifest.json` also pins mathlib and its transitive dependencies.

From the paper repository's root:

```sh
cd lean
lake update
lake exe cache get
lake build
```

The first build includes the Wang repository's completed Kari–Hooper development.
Build artifacts from the same dependency commit and toolchain may be reused.
The full `lake build` passes, including the examples and axiom audit.
`TranslationTiling/AxiomAudit.lean` rejects every axiom beyond `propext`,
`Classical.choice`, and `Quot.sound` in the public theorems and selected main lemmas.
Generic auxiliary lemmas use explicit theorem parameters; the public results
have no unproved mathematical input. No unfinished proof is accepted.

## Definitions and proved inputs

`Tile d` is a list of points of `Fin d → ℤ`, with the canonical primitive-recursive
encoding. List membership interprets it as a finite set: order and duplicate
entries have no effect on tilability. `ExactTiling A F` says that addition from
`A × F` to the entire ambient group is bijective. Translation sets are arbitrary
sets, with no periodicity or finite-support assumption.

`RealTiles F` allows arbitrary real translations of the closed unit-cube union
associated with `F`. Coverage and uniqueness hold almost everywhere for Lebesgue
measure, so shared cube boundaries do not count as overlapping interiors.
`FaceConnected` uses paths of signed coordinate unit steps within the tile.

[ExternalInputs.lean](TranslationTiling/ExternalInputs.lean) imports the proved
inputs used by the compiler. The former `ReductionInputs` hypothesis is removed.

| Proved input | Formal meaning |
| --- | --- |
| Greenfeld–Tao | Decorated Sudoku soundness (`Sudoku.soundness`). |
| Meyerovitch–Sanadhya–Solomon | Arbitrary mixed-tiling rigidity of the two scale-201 component shapes (`MSS.rigidity`). |
| Kim | Arbitrary-tiling coset rigidity and all geometric shell properties (`Kim.cosetRigidity`, `Kim.rigidity`). |
| Bhattacharya | Existence of a fully periodic planar tiling complement (`planarPeriodicity_proved`). |

Meyerovitch–Sanadhya–Solomon rigidity is proved in
`MSS/GridAssembly.lean`. The proof uses singleton isolation to force a forward
ray of centers, coverage to close that ray backwards, and packing to separate
the transverse rows. The main cubes cover the transverse plane. Whole-frame
matching then forces the other coordinate steps and the full cubic grid.
The special frames force both color periods. Reassembly of the marked cells
proves the converse mixed tiling.

Kim's arbitrary-tiling coset rigidity is proved in `Proofs/KimRigidity.lean`.
The shell before its unit modifications consists of aligned 3-blocks. Two
distinct missing points cannot be in one such block. The occupied transverse
rim of a dent therefore excludes coverage by an ordinary block of another
copy. A bump must fill the dent, and the occupied corner block forces its
orientation. This forces all three positive grid steps. Coverage and the
shell's fundamental-domain property then force a complete grid coset.

Bhattacharya's planar periodicity theorem is now proved in
`Proofs/PlanarPeriodicity.lean` using the ported proof chain in `Planar/`.
The theorem supplies a complement with a finite-index subgroup of periods.
It is included in the axiom audit.

Greenfeld–Tao's decorated Sudoku soundness is proved in
`SudokuArithmetic/Soundness.lean`. The proof projects the decorated rule to
each arithmetic component, establishes affine structure on the whole board,
proves compatibility under prime rescaling, and iterates to arbitrary finite
valuation depth. A simultaneous CRT shear makes both components canonical
at the required depths. Constant rows and the tested columns `1`, `p`, and `q`
then provide Wang adjacencies on every finite rectangle; the pinned Wang
dependency supplies compactness. This discharges the Sudoku input without
p-adic compactness or additional hypotheses.

The input statements are defined in `TranslationTiling/External/` and proved
by the modules above. Berger's undecidability and completeness theorems are
proved by the pinned Wang dependency, using its independent Kari–Hooper certificate.

## Checked proofs

| Part | Proof files |
| --- | --- |
| Exact coverage, duplicate/order invariance, additive transport | `Proofs/Basic.lean` |
| Compactness and finite obstruction characterization | `Proofs/Compactness.lean` |
| Primitive-recursive finite satisfiability test; co-r.e. membership in every fixed dimension | `Proofs/FiniteSearch.lean` |
| Primitive-recursive finite cut test, computable face-connectivity, and connected co-r.e. membership in every fixed dimension | `Proofs/FiniteConnectivity.lean` |
| Total computable witness search, computable prime search, and decidability from positive certificates | `Proofs/ComputableSearch.lean`, `Proofs/Decidability.lean` |
| Quadrant/plane Wang equivalence; extraction of Wang tilings from an activated label system and Sudoku soundness | `Proofs/Wang.lean`, `Proofs/SudokuSoundness.lean` |
| Last-nonzero-digit arithmetic, two-prime CRT, canonical Sudoku solutions, and unconditional Sudoku–Wang equivalence | `Proofs/Arithmetic.lean`, `Proofs/Canonical.lean`, `Proofs/WordResidues.lean`, `Proofs/CanonicalLineRule.lean` |
| Initial and finite-depth arithmetic structure, rescaling compatibility, decorated rectangle extraction, and Sudoku soundness | `SudokuArithmetic/*.lean` |
| Bounded coefficient equivalence, executable finite word-rule search, and exact enumeration of allowed words | `Proofs/FiniteWordRule.lean` |
| Graph equation and arbitrary-tiling stacking equivalence | `Proofs/Graph.lean`, `Proofs/Stacking*.lean` |
| Existence of fresh prime full-difference partitions and cyclic consolidation | `Proofs/FullDifferencePartition.lean` and its counting lemmas, `Proofs/CyclicStacking.lean` |
| Histogram separability and mass divisibility obstruction | `Proofs/Histogram.lean` |
| Computable dimensional embedding and tiling equivalence | `Proofs/Dimension.lean` |
| Translating a tile preserves tilability | `Proofs/Translation.lean` |
| Integer/real tiling equivalence, including countability of arbitrary real translation sets and a good sampling grid | `Proofs/Euclidean.lean` |
| Unconditional planar periodicity, using finite periodic decomposition and periodic region replacement | `Planar/*.lean`, `Proofs/PlanarPeriodicity.lean` |
| Rectangular periods from a finite-index period subgroup | `Proofs/PeriodicGrid.lean` |
| Primitive-recursive torus certificates, their equivalence with periodic tilings, and planar decidability from periodicity | `Proofs/IntegerResidues.lean`, `Proofs/PeriodicCertificates.lean` |
| Kim's finite color bounds, nonempty pieces, exact block partition, disjoint colors, internal and external piece contacts, and nonempty shells | `Proofs/KimGeometry.lean` |
| Kim's residue representatives, shell fundamental-domain coverage, volume `s³`, disjoint grid translates, and contacts between whole shells | `Proofs/KimResidues.lean`, `Proofs/KimShellGeometry.lean` |
| Kim's coarse color classes, dented pieces, cube boundary, and shell are face connected | `Proofs/FacePaths.lean`, `Proofs/Kim*Connectivity.lean` |
| Unconditional arbitrary-tiling Kim shell coset rigidity | `Proofs/KimBlocks.lean`, `Proofs/KimDefectGeometry.lean`, `Proofs/KimDentForcing.lean`, `Proofs/KimRigidity.lean` |
| Generic shell-assembly equivalence from fundamental-domain coverage and coset rigidity | `Proofs/ShellAssembly.lean` |
| MSS frame geometry and a counterexample to the one-point local forcing argument (not to global rigidity) | `MSS/FrameGeometry.lean`, `MSS/LocalForcingCheck.lean` |
| MSS frame connectivity and separation, neighbors in frames, and uniqueness of the singleton in the punctured body | `MSS/FrameConnectivity.lean`, `MSS/FrameSeparation.lean`, `MSS/FrameIsolation.lean`, `MSS/BodyIsolation.lean` |
| Unconditional arbitrary mixed-tiling MSS rigidity, including both directions | `MSS/FirstBump.lean`, `MSS/FirstPeriod.lean`, `MSS/RayPacking.lean`, `MSS/TransverseCoverage.lean`, `MSS/FrameMatching.lean`, `MSS/CommonForcing.lean`, `MSS/GridCenters.lean`, `MSS/ColorPeriods.lean`, `MSS/GridAssembly.lean` |
| Completeness, undecidability, higher dimensions, connected completeness, and dimension optimality | `Proofs/Complexity.lean`, `Compiler/Main.lean` |

`Examples.lean` checks small finite searches, repeated tile entries,
face-connectivity, and torus certificates, including rejection of folded
overlaps and modulus zero. It also derives real tilability of a single cube.
It uses kernel evaluation.

## Main compiler

`Compiler/Completeness.lean` proves equivalence of the graph, dependence, cycle,
ordinary activation, and paired-seed constraints with Wang tilability. It uses
one common auxiliary solution for completeness and the proved decorated Sudoku
soundness theorem. `Consolidation.lean` stacks the finite family into a cyclic tile.
`LatticeCompiler.lean` proves arbitrary-tiling descent and completeness using the
explicit MSS components. `ConnectedCompiler.lean` applies Kim's shells and proves
face-connectivity. These semantic constructions have corresponding uniform
numerical algorithms, assembled in `Compiler/Main.lean`.

The numerical alphabet and decorated word-rule enumeration are primitive
recursive (`EffectiveWordRule*.lean`, `EffectiveAlphabet.lean`). Prime and block
coefficient searches are total computable (`EffectiveChoices.lean`,
`EffectiveParameters.lean`). Full-difference colorings are found by a total
computable certificate search (`EffectivePartition.lean`). Numerical cyclic
stacking, its tiling equivalence, positivity, and nonemptiness are checked in
`EffectiveStacking.lean`. Lattice assembly and
connected-shell conversion are primitive recursive (`EffectiveLattice.lean`,
`EffectiveConnected.lean`). Activation fibre orderings and batch indices now use
explicit numerical ranks instead of input-dependent arbitrary enumerations.

`EffectiveDependence.lean`, `EffectiveConstraintFamilies.lean`, and
`EffectiveActivationFamily.lean` serialize every dependence, bad-word,
seed-constraint, and activation gadget. `EffectiveCycleCorrect.lean` proves that
the numerical cycle tables represent **every** required finite function and
produce exactly the semantic cycle family. `EffectiveSystem.lean` proves that
the complete serialized family equals the checked finite system, and transports
its common complement through the cyclic CRT equivalence.

`Main.lean` composes this family with the searched full-difference partition,
cyclic stacking, MSS lattice assembly, and Kim shell conversion. It constructs
`wangReduction` and `connectedWangReduction`, proving effectivity, nonemptiness,
arbitrary-tiling soundness and completeness, and face-connectivity. The algorithm
does not depend on proofs of the mathematical inputs.

The `Computable` proofs establish total recursion on the canonical encodings.
Some definitions use `noncomputable` to express fixed finite tables or searched
witnesses; their uniform effectivity is separately proved. The exhaustive
enumerations are enormous and are intended for the reduction proof.

All mathematical inputs are proved. The public compiler correctness, connected
completeness, Euclidean completeness, and dimension-optimality theorems are
unconditional. No periodicity assumption is imposed on a tiling complement.

The local forcing sentence in MSS Lemma 2.1 does not by itself establish
rigidity. `MSS.unintended_neighbor` gives two disjoint copies of `baseShape`:
one at zero and one translated by `(-214, -1, 200)`. The latter covers
`201 e₂` through its first detached frame, although its translation is not
`201 e₂`. These two copies are not claimed to extend to a tiling. The full rigidity
proof in `MSS/GridAssembly.lean` uses further coverage constraints.

## Online formalizations inspected (October 7, 2026)

The most relevant source is
[`openai/math`, commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`](https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/PeriodicTiling),
already cited by the paper. It uses Lean 4.34.1, so direct imports into this
4.31.0 project require a port.

- [PlanarPeriodicity.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/PeriodicTiling/PlanarPeriodicity.lean)
  contains `plane_tile_has_fullyPeriodic_complement`, the required form of planar
  periodicity. Its 28-module proof closure has been ported, built, and audited
  against this project's pinned dependencies. The lattice bridge discharges
  the Bhattacharya hypothesis.
- [Stacking.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/PeriodicTiling/Stacking.lean)
  and [Activation.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/PeriodicTiling/Activation.lean)
  provide generic stacking and histogram arguments. Selected parts have been
  ported and checked in this project; see the license/provenance record below.
- [WordRule.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/PeriodicTiling/WordRule.lean)
  treats the one-prime arithmetic rule. Its initial affine structure and
  vertical-period obstruction proof closure have been ported. The additional
  finite-depth, two-prime, and decoration arguments in this project prove
  the required decorated soundness theorem.
- [MarkedTileDescent.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/PeriodicTiling/MarkedTileDescent.lean)
  descends fully periodic tilings. That restriction does not provide the
  arbitrary-tiling MSS equivalence required by this reduction.

Targeted web and GitHub searches by authors, paper IDs, and Lean terminology
found no preexisting exact formalization of the decorated two-prime soundness,
the stated MSS rigid-component input, or Kim's coset rigidity input. This is a search result,
not a proof of their absence.

See [third_party/README.md](third_party/README.md) for copied-source provenance.
