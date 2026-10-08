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
abbrev Point := ℤ × ℤ × ℤ

/-- A prototile: a finite set of points of `ℤ³`, given as a list. -/
abbrev Prototile := List Point

/-- Two points are adjacent when their `ℓ¹` distance is one. -/
def Adjacent (a b : Point) : Prop :=
  |a.1 - b.1| + |a.2.1 - b.2.1| + |a.2.2 - b.2.2| = 1

/-- `P` is (face-)connected: any two of its points are joined by a path of
adjacent points inside `P`. -/
def Connected (P : Prototile) : Prop :=
  ∀ p ∈ P, ∀ q ∈ P, Relation.ReflTransGen (fun a b => a ∈ P ∧ b ∈ P ∧ Adjacent a b) p q

/-! ### Tiling `ℤ³` -/

/-- `P` tiles `ℤ³`: for some set `A` of translations, every point `x` equals `a + p`
for exactly one pair with `a ∈ A` and `p ∈ P`. -/
def Tiles (P : Prototile) : Prop :=
  ∃ A : Set Point, ∀ x : Point, ∃! t : Point × Point, t.1 ∈ A ∧ t.2 ∈ P ∧ t.1 + t.2 = x

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

/-- The solid body of a prototile: the union of its unit cubes, the cube of `p ∈ P`
being the translate of the unit cube `[0, 1]³` by `p`. -/
def Solid (P : Prototile) : Set (Fin 3 → ℝ) :=
  {x | ∃ p ∈ P, x - ![(p.1 : ℝ), p.2.1, p.2.2] ∈ Set.Icc 0 1}

/-- The solid body of `P` tiles `ℝ³` by translations: for some set `A ⊆ ℝ³` of
(arbitrary real) translations, almost every point of `ℝ³` lies in exactly one
translate `a + Solid P`. -/
def RealTiles (P : Prototile) : Prop :=
  ∃ A : Set (Fin 3 → ℝ), ∀ᵐ x ∂MeasureTheory.volume, ∃! a : A, x - a.val ∈ Solid P

/-- The same holds for the solid body in `ℝ³` with arbitrary real translations. -/
theorem real_tiling_coRE_complete : LeanWang.CoREComplete fun P => Connected P ∧ RealTiles P :=
  AbstractBridge.connected_real_coRE_complete

end TranslationTiling.Abstract
