import TranslationTiling.SudokuArithmetic.NinePatchFormula
import Mathlib.Tactic

namespace TranslationTiling.Sudoku.NinePatch
open Mathlib.Tactic

/-- The local line tests, before excluding all affine explanations. -/
def hypotheses (p : Nat) : Sat.Fmla :=
  cellChoices p ++ normalization p ++ lineClauses p

private theorem satisfies_iff (v : Sat.Valuation) (c : List Sat.Literal) :
    v.satisfies c ↔ ∃ l ∈ c, ¬ v.neg l := by
  classical
  induction c with
  | nil => simp [Sat.Valuation.satisfies]
  | cons l c ih =>
    simp only [Sat.Valuation.satisfies, ih, List.mem_cons]
    by_cases h : v.neg l <;> simp_all

/-- Semantic content of the finite contradiction certificate: one nonzero
coefficient triple agrees with every nonzero prediction on the patch. -/
theorem classify_of_unsat {p : Nat} (hu : Sat.Fmla.proof (formula p) [])
    (v : Sat.Valuation) (hv : v.satisfies_fmla (hypotheses p)) :
    ∃ abc ∈ triples p, ∀ n < 9, ∀ y < 7, affineValue p abc n y ≠ 0 →
      v (cell p n y (affineValue p abc n y)) := by
  classical
  by_contra hn
  apply hu v
  constructor
  intro c hc
  change c ∈ hypotheses p ++ exclusions p at hc
  rcases List.mem_append.mp hc with hc | hc
  · exact hv.prop c hc
  · obtain ⟨abc,habc,rfl⟩ := List.mem_map.mp hc
    have hf : ¬ (∀ n < 9, ∀ y < 7, affineValue p abc n y ≠ 0 →
        v (cell p n y (affineValue p abc n y))) := by
      intro h
      exact hn ⟨abc, habc, h⟩
    push Not at hf
    obtain ⟨n,hn,y,hy,hval,hbad⟩ := hf
    apply (satisfies_iff _ _).mpr
    refine ⟨.neg (cell p n y (affineValue p abc n y)), ?_, ?_⟩
    · apply List.mem_flatMap.mpr
      refine ⟨n, List.mem_range.mpr hn, ?_⟩
      apply List.mem_map.mpr
      exact ⟨y, by simp [hy,hval], rfl⟩
    · exact hbad

/-- A patch read from the cell atoms has an affine approximation. -/
theorem classify_patch {p : Nat} (hu : Sat.Fmla.proof (formula p) [])
    (W : Nat → Nat → Nat) (v : Sat.Valuation)
    (hv : v.satisfies_fmla (hypotheses p))
    (hc : ∀ n < 9, ∀ y < 7, ∀ z < p, v (cell p n y z) ↔ W n y = z)
    (hp : 0 < p) :
    ∃ abc ∈ triples p, ∀ n < 9, ∀ y < 7, affineValue p abc n y ≠ 0 →
      W n y = affineValue p abc n y := by
  obtain ⟨abc,habc,h⟩ := classify_of_unsat hu v hv
  refine ⟨abc,habc,fun n hn y hy hz => ?_⟩
  exact (hc n hn y hy _ (Nat.mod_lt _ hp)).mp (h n hn y hy hz)

end TranslationTiling.Sudoku.NinePatch
