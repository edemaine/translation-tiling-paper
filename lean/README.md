# Lean formalization

The complete computable Wang-to-tile reduction is proved, conditional on the
named mathematical inputs. Its output is a nonempty, face-connected tile in
dimension three, tileable exactly when the input Wang tiles tile the plane.

Read [TranslationTiling/Statements.lean](TranslationTiling/Statements.lean) for
the short public statements. `compiler_effectivity` and `compiler_correct`
prove uniform computability and correctness. `reduction`, `completeness`,
`connected_completeness`, and `real_completeness` take only `ReductionInputs`;
`dimension_optimality` additionally uses planar periodicity. There is no assumed
compiler certificate or outstanding `Claims` namespace.

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
Mathematical hypotheses are theorem parameters. No unfinished proof is accepted.

## Definitions and hypotheses

`Tile d` is a list of points of `Fin d → ℤ`, with the canonical primitive-recursive
encoding. List membership interprets it as a finite set: order and duplicate
entries have no effect on tilability. `ExactTiling A F` says that addition from
`A × F` to the entire ambient group is bijective. Translation sets are arbitrary
sets, with no periodicity or finite-support assumption.

`RealTiles F` allows arbitrary real translations of the closed unit-cube union
associated with `F`. Coverage and uniqueness hold almost everywhere for Lebesgue
measure, so shared cube boundaries do not count as overlapping interiors.
`FaceConnected` uses paths of signed coordinate unit steps within the tile.

[ExternalInputs.lean](TranslationTiling/ExternalInputs.lean) packages four explicit
propositions matching the current draft. `ReductionInputs` contains the three
inputs used by the connected compiler; `ExternalInputs` additionally includes
planar periodicity for dimension optimality:

| Input | Formal meaning |
| --- | --- |
| Greenfeld–Tao | Soundness of the explicit decorated two-prime Sudoku rule, with fixed primes 211 and 223; both arithmetic components are nonconstant in each column. |
| Meyerovitch–Sanadhya–Solomon | Arbitrary-tiling rigidity of the paper's explicitly defined two component shapes, with scale 201. |
| Bhattacharya | Every tileable planar tile has a complement with a finite-index subgroup of periods. |
| Kim | Connectivity, contacts, fundamental-domain coverage, and arbitrary-tiling rigidity of the explicit shell in the updated draft. |

The actual definitions are in `TranslationTiling/External/`. These are parameters,
not global `axiom` declarations. The main computable reduction is not included
among the external hypotheses. Berger's undecidability/completeness input is
proved by the pinned Wang dependency, using its independent Kari–Hooper certificate.

## Checked proofs

| Part | Proof files |
| --- | --- |
| Exact coverage, duplicate/order invariance, additive transport | `Proofs/Basic.lean` |
| Compactness and finite obstruction characterization | `Proofs/Compactness.lean` |
| Primitive-recursive finite satisfiability test; co-r.e. membership in every fixed dimension | `Proofs/FiniteSearch.lean` |
| Primitive-recursive finite cut test, computable face-connectivity, and connected co-r.e. membership in every fixed dimension | `Proofs/FiniteConnectivity.lean` |
| Total computable witness search, computable prime search, and decidability from positive certificates | `Proofs/ComputableSearch.lean`, `Proofs/Decidability.lean` |
| Quadrant/plane Wang equivalence; soundness from an activated label system and the raw Sudoku hypothesis | `Proofs/Wang.lean`, `Proofs/SudokuSoundness.lean` |
| Last-nonzero-digit arithmetic, two-prime CRT, and the canonical Sudoku solution; Sudoku–Wang equivalence conditional on soundness | `Proofs/Arithmetic.lean`, `Proofs/Canonical.lean`, `Proofs/WordResidues.lean`, `Proofs/CanonicalLineRule.lean` |
| Bounded coefficient equivalence, executable finite word-rule search, and exact enumeration of allowed words | `Proofs/FiniteWordRule.lean` |
| Graph equation and arbitrary-tiling stacking equivalence | `Proofs/Graph.lean`, `Proofs/Stacking*.lean` |
| Existence of fresh prime full-difference partitions and cyclic consolidation | `Proofs/FullDifferencePartition.lean` and its counting lemmas, `Proofs/CyclicStacking.lean` |
| Histogram separability and mass divisibility obstruction | `Proofs/Histogram.lean` |
| Computable dimensional embedding and tiling equivalence | `Proofs/Dimension.lean` |
| Translating a tile preserves tilability | `Proofs/Translation.lean` |
| Integer/real tiling equivalence, including countability of arbitrary real translation sets and a good sampling grid | `Proofs/Euclidean.lean` |
| Rectangular periods from the finite-index periodicity input | `Proofs/PeriodicGrid.lean` |
| Primitive-recursive torus certificates, their equivalence with periodic tilings, and planar decidability from periodicity | `Proofs/IntegerResidues.lean`, `Proofs/PeriodicCertificates.lean` |
| Shell assembly preserves tilability under a fundamental-domain and coset-rigidity hypothesis | `Proofs/ShellAssembly.lean` |
| Completeness, undecidability, higher dimensions, connected completeness, and dimension optimality | `Proofs/Complexity.lean`, `Compiler/Main.lean` |

`Examples.lean` checks small finite searches, repeated tile entries,
face-connectivity, and torus certificates, including rejection of folded
overlaps and modulus zero. It also derives real tilability of a single cube.
It uses kernel evaluation.

## Main compiler

`Compiler/Completeness.lean` proves equivalence of the graph, dependence, cycle,
ordinary activation, and paired-seed constraints with Wang tilability. It uses
one common auxiliary solution for completeness and the decorated Sudoku input
for soundness. `Consolidation.lean` stacks the finite family into a cyclic tile.
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

The remaining work is to discharge the named mathematical inputs themselves.
They can be formalized independently without changing the compiler.

## Online formalizations inspected (October 7, 2026)

The most relevant source is
[`openai/math`, commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`](https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/PeriodicTiling),
already cited by the draft. It uses Lean 4.34.1, so direct imports into this
4.31.0 project require a port.

- [PlanarPeriodicity.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/PeriodicTiling/PlanarPeriodicity.lean)
  contains `plane_tile_has_fullyPeriodic_complement`, the required form of planar
  periodicity. Its transitive source closure was inspected, but has not been
  independently built here. It is a promising starting point for discharging
  the Bhattacharya hypothesis.
- [Stacking.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/PeriodicTiling/Stacking.lean)
  and [Activation.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/PeriodicTiling/Activation.lean)
  provide generic stacking and histogram arguments. Selected parts have been
  ported and checked in this project; see the license/provenance record below.
- [WordRule.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/PeriodicTiling/WordRule.lean)
  treats the one-prime arithmetic rule. It does not discharge the decorated
  two-prime Wang soundness hypothesis used here.
- [MarkedTileDescent.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/PeriodicTiling/MarkedTileDescent.lean)
  descends fully periodic tilings. That restriction does not provide the
  arbitrary-tiling MSS equivalence required by this reduction.

Targeted web and GitHub searches by authors, paper IDs, and Lean terminology
found no exact formalization of the decorated two-prime soundness, the stated
MSS rigid-component input, or Kim's connectedness input. This is a search result,
not a proof of their absence.

See [third_party/README.md](third_party/README.md) for copied-source provenance.
