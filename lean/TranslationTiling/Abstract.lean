import Mathlib.Computability.Halting
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import LeanWang.CoRE
import TranslationTiling.AbstractBridge

/-!
# The 3D tiling problem

A *prototile* is a finite list of points of `ℤ³`. It *tiles space* if `ℤ³` can be
partitioned into translates of it: there is a set `A` of translation vectors such
that every point of `ℤ³` is written in exactly one way as `a + p`, with `a ∈ A`
and `p` in the prototile.

We show that deciding whether a *connected* prototile tiles is co-r.e.-complete,
both for `ℤ³` and for the solid body in `ℝ³` (union of unit cubes, arbitrary real
translations). The proofs invoke `TranslationTiling.AbstractBridge`, which connects
the statements to the rest of the project.
-/

namespace TranslationTiling.Abstract

/-- A point of `ℤ³`. -/
abbrev Point := Fin 3 → ℤ

/-- A prototile: a finite set of points of `ℤ³`, given as a list. -/
abbrev Prototile := List Point

/-- Two points are adjacent when their `ℓ¹` distance is one. -/
def Adjacent (a b : Point) : Prop :=
  ∑ i, |a i - b i| = 1

/-- `P` is (face-)connected: any two of its points are joined by a path of
adjacent points inside `P`. -/
def Connected (P : Prototile) : Prop :=
  ∀ p ∈ P, ∀ q ∈ P, Relation.ReflTransGen (fun a b => a ∈ P ∧ b ∈ P ∧ Adjacent a b) p q

/-! ### Tiling `ℤ³` -/

/-- `P` tiles `ℤ³`: for some set `T` of translations, every point `x` lies in exactly
one translate `t + P` with `t ∈ T`, i.e., for exactly one `t ∈ T` we have `x - t ∈ P`. -/
def Tiles (P : Prototile) : Prop :=
  ∃ T : Set Point, ∀ x : Point, ∃! t : Point, t ∈ T ∧ x - t ∈ P

/-- **Main theorem.** Deciding whether a connected prototile in `ℤ³` tiles space is
co-r.e.-complete: the non-tilers are recursively enumerable, and every co-r.e.
problem many-one reduces (computably) to it. -/
theorem tiling_coRE_complete : LeanWang.CoREComplete fun P => Connected P ∧ Tiles P :=
  AbstractBridge.connected_coRE_complete

/-- **Corollary.** No algorithm decides whether a connected prototile in `ℤ³`
tiles space. (Mathlib notions only.) -/
theorem tiling_undecidable : ¬ ComputablePred fun P => Connected P ∧ Tiles P :=
  AbstractBridge.connected_undecidable

/-! ### Tiling `ℝ³` -/

/-- A point of `ℝ³`. -/
abbrev RealPoint := Fin 3 → ℝ

/-- The solid body of a prototile: the union of the unit cubes `p + [0, 1]³`, `p ∈ P`. -/
def Solid (P : Prototile) : Set RealPoint :=
  {x | ∃ p ∈ P, ∀ i, p i ≤ x i ∧ x i ≤ p i + 1}

/-- The solid body of `P` tiles `ℝ³` by translations: for some set `T ⊆ ℝ³` of
(arbitrary real) translations, almost every point `x` of `ℝ³` lies in exactly one
translate `t + Solid P` with `t ∈ T`. -/
def RealTiles (P : Prototile) : Prop :=
  ∃ T : Set RealPoint, ∀ᵐ x ∂MeasureTheory.volume, ∃! t : RealPoint, t ∈ T ∧ x - t ∈ Solid P

/-- The same holds for the solid body in `ℝ³` with arbitrary real translations. -/
theorem real_tiling_coRE_complete : LeanWang.CoREComplete fun P => Connected P ∧ RealTiles P :=
  AbstractBridge.connected_real_coRE_complete

/-- No algorithm decides whether a connected prototile tiles `ℝ³` by arbitrary
real translations. (Mathlib notions only.) -/
theorem real_tiling_undecidable : ¬ ComputablePred fun P => Connected P ∧ RealTiles P :=
  AbstractBridge.connected_real_undecidable

end TranslationTiling.Abstract
