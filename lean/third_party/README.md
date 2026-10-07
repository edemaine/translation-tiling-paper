# Source provenance

Selected proofs were adapted from the Apache-2.0 repository
[`openai/math`](https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/PeriodicTiling),
commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
The complete upstream license is [openai-math.LICENSE](openai-math.LICENSE).

| Local file | Upstream source |
| --- | --- |
| `TranslationTiling/Proofs/FiniteTiling.lean` | `TilingBasic.lean`, unique-tile characterization |
| `TranslationTiling/Proofs/StackingContributions.lean` | `Stacking.lean`, stacking and contribution lemmas |
| `TranslationTiling/Proofs/Stacking.lean` | `Stacking.lean`, with a new forward lift and existential equivalence |
| `TranslationTiling/Proofs/Histogram.lean` | `Activation.lean`, mixed-difference and histogram lemmas |
| `TranslationTiling/Proofs/Arithmetic.lean` | `LastDigit.lean`, prime-free quotient and last-nonzero-digit lemmas |
| `TranslationTiling/Proofs/FinitePairCounting.lean`, `PrimeDifferencePairs.lean`, `FullDifferenceBound.lean`, `FullDifferencePartition.lean` | Corresponding files, proving existence of a fresh prime full-difference partition |
| `TranslationTiling/Proofs/Euclidean.lean` | Arguments from `AETilingCountable.lean` and `LatticeThickening.lean`, extended to prove the sampling/rounding equivalence |

Compiler ports (local and upstream basenames agree):

`Activation.lean`, `ActivationOffsets.lean`, `ActivationTiles.lean`, `BlockActivationInverse.lean`, `ChannelDigitBlocks.lean`, `CommonModel.lean`, `CommonSeedOutputs.lean`, `CommonSolution.lean`, `ConstraintCycles.lean`, `CycleTests.lean`, `CyclicCRT.lean`, `CyclicCoordinates.lean`, `CyclicFactorCRT.lean`, `CyclicQuotient.lean`, `CyclicShear.lean`, `CyclicTypes.lean`, `Dependence.lean`, `EncodedSystem.lean`, `EncodingParameters.lean`, `EncodingPrimeSelection.lean`, `GraphTests.lean`, `LabeledDigitBlocks.lean`, `OrdinaryActivation.lean`, `OrdinaryModel.lean`, `QuotientTiling.lean`, `SharedSeedInactive.lean`, `SharedSeedInverse.lean`, `SharedSeedLabelEquiv.lean`, `SharedSeedLabels.lean`, `SharedSeedRegions.lean`, `SharedSeedSizeTransport.lean`, `ShiftMultiplicity.lean`.

These ports adapt the auxiliary finite-group construction to the decorated
two-prime alphabet. They retain the upstream notices. Numerical activation
rankings and index encodings have been replaced with explicit formulas; the
integer descent, connected assembly, and computability bridges are developed
locally.

The ports change namespaces and imports for Lean 4.31.0, replace the upstream
finite tiling predicate with `TranslationTiling.Stacking.Covers`, and add bridges
to this project's set-based exact-coverage definition. All local copied/adapted
proofs are checked against this project's pinned dependencies.

The pinned `lean-wang` dependency is also Apache-2.0 and retains its own license
and author notices in `.lake/packages/lean_wang/` after `lake update`.
