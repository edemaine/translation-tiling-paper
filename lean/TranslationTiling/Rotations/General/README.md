# Dimension-Generic Key Gadget

This development proves a computable, dimension-preserving rotation-resistant
replacement for every dimension `d ≥ 3`, including arbitrary Euclidean rotations
and reflections. It treats the input translation tile as a black box.

The main entry points are:

- `General.Real.protection d hd` in [Real/Protect.lean](Real/Protect.lean): one
  computable replacement preserves tilability for every allowed set of Euclidean
  rotations containing the identity. Connected inputs have connected outputs.
- `General.Real.rigidity hd` in [Real/GlobalRigidity.lean](Real/GlobalRigidity.lean):
  every Euclidean tiling by the gadget has a common orientation and period lattice.
- `General.Real.dimension_hardness d hd` in [Real/Hardness.lean](Real/Hardness.lean):
  tilability of one connected polycube is co-RE-hard and undecidable in every
  dimension `d ≥ 3`, both for proper Euclidean rotations and for rotations with
  reflections.
- `General.Real.rotationCompile_length_bound` in that file: the optimized Wang
  compiler keeps its previous bound, multiplied by a dimension-dependent constant.

Here `hd : 3 ≤ d`, and `General` abbreviates
`TranslationTiling.Rotations.General`. Import `General.Main` for the complete
development. The existing three-dimensional construction remains available with
its smaller constant overhead.

## Construction

The `2*d` face labels are `Fin (2*d)`. Set `K = 8*d+8`. The rectangular chamber
for label `f` has side lengths that are powers of two, with exponents

- `f+1` in coordinate 0;
- `K-(f+1)` in coordinate 1;
- `K+j` in coordinates `j ≥ 2`.

All chambers have equal volume. Their shortest sides identify their face labels,
and their distinct side lengths identify the coordinate axes. A thin stem meets
a corner of each chamber and eliminates the remaining reflections. This replaces
the three-dimensional numerical moment calculation.

The neck has length `8*d+8`. The face gates have transverse coordinates
`3*A` on negative faces and `3*A+1` on positive faces, where
`A = 8*d+18+2^(9*d+10)`. Remove each recess from a cube of side

```
L(d) = 100*(d+1)*(8*d+18+2^(9*d+10))
```

and attach its translate by one period in the inward-normal direction.
`General.gadget_decomposition` proves that this geometric description agrees
with the effective construction.

The exact replacement overhead is `L(d)^d` voxels. The simpler bound is
`2^(10*(d+1)^2)` voxels per input voxel. Both cardinality and output-list length
are bounded in [ProtectedSize.lean](ProtectedSize.lean), including disconnected
inputs. No optimization of this constant is claimed.

## Proof Ingredients

[KeyShapes.lean](KeyShapes.lean) proves that complete keys cannot be confused or
moved by a nonidentity grid motion, including reflections. A thick rectangular
box cannot enter a one-voxel-wide stem. Equal volumes therefore identify the
rectangular parts, whose side lengths identify the label and axes. The
corner-mounted stem fixes the remaining signs and translation. This argument
works already in dimension two.

[BodyConnectivity.lean](BodyConnectivity.lean) proves that the body stays
connected after deleting any voxel. Intact coordinate planes provide a common
skeleton. Every body voxel reaches that skeleton along a clear coordinate line;
two blocked transverse lines would imply that the voxel belongs to a recess.
The use of a third coordinate is where `d ≥ 3` enters.

[KeyedGadget.lean](KeyedGadget.lean), [LocalForcing.lean](LocalForcing.lean), and
[GlobalRigidity.lean](GlobalRigidity.lean) prove component recognition, forced
neighbors, and grid rigidity. The shared `../Chambers.lean` and
`../KeyRecognition.lean` lemmas now accept an arbitrary dimension.

The [Real](Real) modules extend the proof to arbitrary Euclidean motions. A cube
meeting the middle of a long neck is confined transversely, forcing a signed
coordinate-permutation orientation. Its transverse coordinates become integral.
A blocking copy monopolizes the capped chamber; contact with the closed end
then fixes the axial phase. Each voxel of the remaining neck prefix is the sole
exit of its chamber suffix, so the same copy fills the complete chamber.
Component recognition forces the neighbor, and forced neighbors propagate to a
common frame throughout space.

Finally, [Padding.lean](Padding.lean) preserves translation tilability and
connectivity when appending zero coordinates. Applying the new replacement
after padding the existing optimized three-dimensional compiler gives the
higher-dimensional hardness results without inspecting that compiler.

## Verification

[AxiomAudit.lean](AxiomAudit.lean) checks every declaration in this namespace and
all its axiom dependencies. Only Lean's standard `propext`, `Classical.choice`,
and `Quot.sound` are permitted. The audit is included in the repository's full
`lake build TranslationTiling` target. There are no proof placeholders or
additional mathematical axioms.
