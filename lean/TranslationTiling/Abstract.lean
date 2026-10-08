import Mathlib.Computability.Halting
import Mathlib.Computability.Primrec.List
import LeanWang.CoRE
import TranslationTiling.AbstractBridge

/-!
# The 3D tiling problem

A *prototile* is a finite list of points of `ℤ³`. It *tiles space* if `ℤ³` can be
partitioned into translates of it: there is a set `A` of translation vectors such
that every point of `ℤ³` is written in exactly one way as `a + p`, with `a ∈ A`
and `p` in the prototile.

The unconditional statements below use the co-r.e. notions of `LeanWang.CoRE`.
Their one-line proofs invoke
`TranslationTiling.AbstractBridge`, which connects them to the rest of the project.
-/

namespace TranslationTiling.Abstract

/-- A point of `ℤ³`. -/
abbrev Point := ℤ × ℤ × ℤ

/-- A prototile: a finite set of points of `ℤ³`, given as a list. -/
abbrev Prototile := List Point

/-- `P` tiles space: for some set `A` of translations, every point `x` of `ℤ³`
equals `a + p` for exactly one pair with `a ∈ A` and `p ∈ P`. -/
def Tiles (P : Prototile) : Prop :=
  ∃ A : Set Point, ∀ x : Point, ∃! t : Point × Point, t.1 ∈ A ∧ t.2 ∈ P ∧ t.1 + t.2 = x

/-- **Main theorem.** Deciding whether a single prototile in `ℤ³` tiles space is
co-r.e.-complete: the non-tilers are recursively enumerable, and every co-r.e.
problem many-one reduces (computably) to tilability. -/
theorem tiling_coRE_complete : LeanWang.CoREComplete Tiles :=
  AbstractBridge.coRE_complete

/-- **Corollary.** No algorithm decides whether a prototile in `ℤ³` tiles space. -/
theorem tiling_undecidable : ¬ ComputablePred Tiles :=
  AbstractBridge.undecidable

end TranslationTiling.Abstract
