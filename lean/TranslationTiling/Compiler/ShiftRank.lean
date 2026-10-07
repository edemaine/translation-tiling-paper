import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.SplitIfs
import Lean.Elab.Tactic.Omega

namespace TranslationTiling.Compiler

/-- The modified rectangular multiplicity, in numerical coordinates. -/
def numericalMultiplicity (α ξ : ℕ) : ℕ :=
  if ξ = 0 then if α = 0 then 2 else if α = 1 then 0 else 1
  else if ξ = 1 then if α = 0 then 0 else if α = 1 then 2 else 1
  else 1

/-- Rank in a row of the modified rectangle. The two copies at 0 or 1
occupy ranks 0 and 1; the deleted position leaves no gap. -/
def numericalRank (α ξ k : ℕ) : ℕ :=
  if ξ = 0 then if α = 0 then k else α
  else if ξ = 1 then if α = 1 then k else α
  else α

theorem numericalRank_lt {a α ξ k : ℕ} (ha : 2 ≤ a) (hα : α < a)
    (hk : k < numericalMultiplicity α ξ) : numericalRank α ξ k < a := by
  unfold numericalRank numericalMultiplicity at *
  split_ifs at * <;> omega

theorem numericalRank_injective {α β ξ k l : ℕ}
    (hk : k < numericalMultiplicity α ξ) (hl : l < numericalMultiplicity β ξ)
    (h : numericalRank α ξ k = numericalRank β ξ l) : α = β ∧ k = l := by
  unfold numericalRank numericalMultiplicity at *
  split_ifs at * <;> omega

theorem numericalMultiplicity_symm (α ξ : ℕ) :
    numericalMultiplicity α ξ = numericalMultiplicity ξ α := by
  unfold numericalMultiplicity
  split_ifs <;> omega

end TranslationTiling.Compiler
