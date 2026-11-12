import Mathlib.Computability.Halting
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Euclidean.Projection
import Mathlib.LinearAlgebra.Determinant
import LeanWang.CoRE
import LeanWang.Basic
import TranslationTiling.AbstractBridge

/-!
# Tiling in 3D+

For fixed dimension `d ≥ 3`, a *prototile* is a finite list of points in `ℤ^d`.
A prototile `P` *tiles space* if `ℤ^d` can be partitioned into
translates of `P`: there is a set `T` of translation vectors such
that every point of `ℤ^d` lies in exactly one translate `t + P` with `t ∈ T`.

We show that deciding whether a *connected* prototile tiles is co-RE-complete,
both for `ℤ^d` and for the solid body in `ℝ^d` (union of unit cubes).
For the latter, we allow arbitrary real translations and optionally allow
arbitrary real rotations and/or reflections.
We also give quasipolynomial bounds on the numbers of lattice points / cubes
in our reduction from Wang tiling.

The definitions and theorem statements in this file are self-contained,
with imports only to Mathlib and the co-RE and Wang-tiling definitions
from `lean-wang`.
The proofs invoke `TranslationTiling.AbstractBridge`, which connects
the statements to the rest of the project.
-/

namespace TranslationTiling.Abstract

/-- A point of `ℤ^d`. -/
abbrev Point (d : ℕ) := Fin d → ℤ

/-- A prototile: a finite set of points of `ℤ^d`, given as a list for
algorithmic processing. Duplicates do not change connectivity or tilability. -/
abbrev Prototile (d : ℕ) := List (Point d)

/-- Two points are adjacent when their `ℓ¹` distance is one. -/
def Adjacent {d : ℕ} (a b : Point d) : Prop :=
  ∑ i, |a i - b i| = 1

/-- `P` is (facet-)connected: any two of its points are joined by a path of
adjacent points inside `P`. -/
def Connected {d : ℕ} (P : Prototile d) : Prop :=
  ∀ p ∈ P, ∀ q ∈ P, Relation.ReflTransGen (fun a b => a ∈ P ∧ b ∈ P ∧ Adjacent a b) p q

/-! ### Tiling `ℤ^d` by translation -/

/-- `P` tiles `ℤ^d`: for some set `T` of translations, every point `x` lies in
exactly one translate `t + P` with `t ∈ T`, i.e., for exactly one `t ∈ T`
we have `x - t ∈ P`. -/
def Tiles {d : ℕ} (P : Prototile d) : Prop :=
  ∃ T : Set (Point d), ∀ x : Point d, ∃! t ∈ T, x - t ∈ P

/-- **Main theorem.** For each fixed `d ≥ 3`, deciding whether a connected
prototile in `ℤ^d` tiles space is co-RE-complete: the non-tilers are recursively
enumerable, and every co-RE problem many-one reduces (computably) to it. -/
theorem tiling_coRE_complete (d : ℕ) (hd : 3 ≤ d) :
  LeanWang.CoREComplete fun P : Prototile d => Connected P ∧ Tiles P :=
  AbstractBridge.connected_coRE_complete d hd

/-- **Corollary.** For each fixed `d ≥ 3`, no algorithm decides whether a
connected prototile in `ℤ^d` tiles space.
(Relies only on Mathlib's computable predicate, no LeanWang.) -/
theorem tiling_undecidable (d : ℕ) (hd : 3 ≤ d) :
  ¬ ComputablePred fun P : Prototile d => Connected P ∧ Tiles P :=
  AbstractBridge.connected_undecidable d hd

/-- **Theorem.** For each fixed `d ≥ 3`, a computable reduction maps Wang tiling
to translational tiling by a nonempty connected polycube with the stated cube
bound.  List lengths count the input tiles and output cubes; `Real.logb 2` is
the base-two logarithm. Thus the bound is `(n + 4)^(10^61 * lg lg (n + 4))`. -/
theorem tiling_reduction (d : ℕ) (hd : 3 ≤ d) :
  ∃ f : LeanWang.TileSet → Prototile d, Computable f ∧
    ∀ T, f T ≠ [] ∧ Connected (f T) ∧ (LeanWang.TilesPlane T ↔ Tiles (f T)) ∧
      ((f T).length : ℝ) ≤ ((T.length : ℝ) + 4) ^
        (10 ^ 61 * Real.logb 2 (Real.logb 2 ((T.length : ℝ) + 4))) :=
  AbstractBridge.tiling_reduction d hd

/-! ### Tiling `ℝ^d` by Euclidean motions -/

/-- A point of Euclidean `ℝ^d`: `d` real coordinates with the usual Euclidean
norm. A coordinate is written `x i` for `i : Fin d`, like our `Point` above. -/
abbrev RealPoint (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- The solid body of a prototile: the union of the unit cubes `p + [0, 1]^d`, `p ∈ P`. -/
def Solid {d : ℕ} (P : Prototile d) : Set (RealPoint d) :=
  {x | ∃ p ∈ P, ∀ i, p i ≤ x i ∧ x i ≤ p i + 1}

/-- A Euclidean motion: an affine isometry of `ℝ^d`, including arbitrary real
rotations and translations and optionally a reflection. The notation
`RealPoint d ≃ᵃⁱ[ℝ] RealPoint d` means Mathlib's `AffineIsometryEquiv` over the
scalar field `ℝ`: `≃` denotes a bijection, `ᵃ` means affine, and `ⁱ` means
isometric (distance-preserving). -/
abbrev Motion (d : ℕ) := RealPoint d ≃ᵃⁱ[ℝ] RealPoint d

/-- All Euclidean motions, allowing translations, rotations, and reflections.
`Set.univ` gives the whole set of Euclidean motions. -/
def allMotions {d : ℕ} : Set (Motion d) := Set.univ

/-- Translations: the Euclidean motions whose linear part is the identity.
`f.linear` extracts the invertible linear part, ignoring the translation;
`1` denotes the identity linear map. -/
def translations {d : ℕ} : Set (Motion d) := {f | f.linear = 1}

/-- Translations and arbitrary real rotations: the linear part has determinant
`1`. `f.linear.det` computes the determinant of the invertible linear part. -/
def translationsAndRotations {d : ℕ} : Set (Motion d) := {f | f.linear.det = 1}

/-- Translations optionally composed with reflection through a hyperplane.
Mathlib's `AffineSubspace.perpBisector p q` is the set of points equidistant
from `p` and `q`; for distinct points, this is their perpendicular-bisector
hyperplane. `EuclideanGeometry.reflection` reflects in that affine subspace,
returning a Euclidean motion. Multiplication `t * r` applies `r` then `t`.
For `p = q`, the bisector is the whole space and its reflection is the identity,
so translations alone are included too. -/
def translationsAndReflections {d : ℕ} : Set (Motion d) :=
  {f | ∃ t ∈ translations, ∃ p q : RealPoint d,
    f = t * EuclideanGeometry.reflection (AffineSubspace.perpBisector p q)}

/-- The solid body of `P` tiles `ℝ^d` using motions from the given set, with
almost-everywhere unique coverage. `T ⊆ motions` requires every placed copy
to use a permitted motion; `∃! f ∈ T` means exactly one motion in `T` covers `x`.
The image notation `f '' Solid P` means `{f x | x ∈ Solid P}`,
the solid after applying `f`. -/
def RealTiles {d : ℕ} (P : Prototile d) (motions : Set (Motion d)) : Prop :=
  ∃ T ⊆ motions, ∀ᵐ x ∂MeasureTheory.volume,
    ∃! f ∈ T, x ∈ f '' Solid P

/-- **Theorem.** For each fixed `d ≥ 3`, it is co-RE-hard to decide whether
a connected prototile tiles `ℝ^d` for any set of Euclidean motions
containing all translations. -/
theorem real_tiling_coRE_hard (d : ℕ) (hd : 3 ≤ d)
  (motions : Set (Motion d)) (hm : translations ⊆ motions) :
    LeanWang.CoREHard fun P : Prototile d => Connected P ∧ RealTiles P motions :=
  AbstractBridge.connected_set_motion_coRE_hard d hd motions hm

/-- **Corollary.** For each fixed `d ≥ 3`, no algorithm decides tilability of
a connected prototile in `ℝ^d` for any set of Euclidean motions
containing all translations. -/
theorem real_tiling_undecidable (d : ℕ) (hd : 3 ≤ d)
  (motions : Set (Motion d)) (hm : translations ⊆ motions) :
    ¬ ComputablePred fun P : Prototile d => Connected P ∧ RealTiles P motions :=
  AbstractBridge.connected_set_motion_undecidable d hd motions hm

/-- **Theorem.** For each fixed `d ≥ 3`, the tiling problem is co-RE-complete
for translations, and optionally rotations and optionally reflections,
of a single connected prototile. -/
theorem real_tiling_coRE_complete (d : ℕ) (hd : 3 ≤ d)
  (motions : Set (Motion d))
  (hm : motions ∈ ({allMotions, translations, translationsAndRotations,
                    translationsAndReflections} : Set _)) :
    LeanWang.CoREComplete fun P : Prototile d => Connected P ∧ RealTiles P motions :=
  AbstractBridge.connected_set_motion_coRE_complete d hd motions hm

/-- **Theorem.** For each fixed `d ≥ 3`, a computable reduction with the same
cube bound as the ℤ^d case (tiling_reduction) works for arbitrary real
translations of the output polycube. The same output tiles `ℤ^d` exactly when
the solid tiles `ℝ^d` by translations. For `n` input Wang tiles, the cube bound
is `(n + 4)^(10^61 * lg lg (n + 4))`. -/
theorem real_tiling_reduction (d : ℕ) (hd : 3 ≤ d) :
  ∃ f : LeanWang.TileSet → Prototile d, Computable f ∧
    ∀ T, f T ≠ [] ∧ Connected (f T) ∧
      (LeanWang.TilesPlane T ↔ Tiles (f T)) ∧
      (Tiles (f T) ↔ RealTiles (f T) translations) ∧
      ((f T).length : ℝ) ≤ ((T.length : ℝ) + 4) ^
        (10 ^ 61 * Real.logb 2 (Real.logb 2 ((T.length : ℝ) + 4))) :=
  AbstractBridge.set_real_tiling_reduction d hd

/-- **Theorem.** For each fixed `d ≥ 3`, a computable reduction from Wang tiling
produces a nonempty connected polycube with equivalent tilability under lattice
translations and any set of Euclidean motions containing all translations.
Its cube bound is `2^(10 * (d + 1)^2) * (n + 4)^(10^61 * lg lg (n + 4))`. -/
theorem rigid_tiling_reduction (d : ℕ) (hd : 3 ≤ d) :
  ∃ f : LeanWang.TileSet → Prototile d, Computable f ∧
    ∀ T, f T ≠ [] ∧ Connected (f T) ∧
      (LeanWang.TilesPlane T ↔ Tiles (f T)) ∧
      (∀ motions : Set (Motion d), translations ⊆ motions →
        (Tiles (f T) ↔ RealTiles (f T) motions)) ∧
      ((f T).length : ℝ) ≤ (2 : ℝ) ^ (10 * (d + 1) ^ 2) * (((T.length : ℝ) + 4) ^
        (10 ^ 61 * Real.logb 2 (Real.logb 2 ((T.length : ℝ) + 4)))) :=
  AbstractBridge.set_motion_tiling_reduction d hd

/-- **Corollary.** In 3D, the same equivalences hold with the sharper
cube bound `64000 * (n + 4)^(10^61 * lg lg (n + 4))`. -/
theorem rigid_tiling_reduction_three :
  ∃ f : LeanWang.TileSet → Prototile 3, Computable f ∧
    ∀ T, f T ≠ [] ∧ Connected (f T) ∧
      (LeanWang.TilesPlane T ↔ Tiles (f T)) ∧
      (∀ motions : Set (Motion 3), translations ⊆ motions →
        (Tiles (f T) ↔ RealTiles (f T) motions)) ∧
      ((f T).length : ℝ) ≤ 64000 * (((T.length : ℝ) + 4) ^
        (10 ^ 61 * Real.logb 2 (Real.logb 2 ((T.length : ℝ) + 4)))) :=
  AbstractBridge.set_motion_tiling_reduction_three

end TranslationTiling.Abstract
