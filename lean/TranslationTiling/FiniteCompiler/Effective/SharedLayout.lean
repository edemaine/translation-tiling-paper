import TranslationTiling.FiniteCompiler.Effective.SharedParameterData
import TranslationTiling.FiniteCompiler.SharedCoordinates

namespace TranslationTiling.FiniteCompiler.Packed

open Effective
open scoped BigOperators

private abbrev positiveRow (row : ℕ × ℕ × List ℕ) : Prop :=
  0 < row.2.2.prod ∧ 0 < row.1 ∧ 0 < row.2.1

private theorem primeProduct_positive (ds : List ℕ) (hp : ∀ d ∈ ds, d.Prime) :
    0 < ds.prod := by
  induction ds with
  | nil => decide
  | cons d ds ih =>
    exact Nat.mul_pos (hp d (by simp)).pos (ih (fun p h => hp p (by simp [h])))

theorem sharedRows_moduli_positive {k i : ℕ} (hi : i < (sharedRows k).length) :
    0 < rowR (sharedRows k) i ∧ 0 < sharedObservedA (sharedRows k) i ∧
      0 < rowB (sharedRows k) i := by
  unfold rowR rowDigits sharedObservedA rowB rowA
  by_cases h₀ : i < 18
  · rw [if_neg (fun h => (not_le_of_gt h₀) h.1),sharedRows_fixed_at h₀]
    exact (by decide +kernel : ∀ j : Fin 18, positiveRow (sharedArithmeticRow j)) ⟨i,h₀⟩
  · by_cases h : i < 18+2*k
    · let j := i-18
      have hj : j < 2*k := by dsimp [j]; omega
      have he : i = 18+j := by dsimp [j]; omega
      have hobs : 18 ≤ i ∧ i < (sharedRows k).length-2 := by
        rw [sharedRows_length]
        omega
      rw [if_pos hobs,he,sharedRows_wang_at hj]
      obtain ⟨_,hb,_,_,_,hd⟩ := sharedWangRow_facts hj
      exact ⟨primeProduct_positive _ (fun d hd' => (hd d hd').1),by decide,hb.pos⟩
    · let t := i-(18+2*k)
      have ht : t < 2 := by rw [sharedRows_length] at hi; dsimp [t]; omega
      have he : i = 18+2*k+t := by dsimp [t]; omega
      have hobs : ¬ (18 ≤ i ∧ i < (sharedRows k).length-2) := by
        rw [sharedRows_length]
        omega
      rw [if_neg hobs,he,sharedRows_seed_at]
      exact (by decide +kernel : ∀ j : Fin 2, positiveRow (sharedSeedRows.getD j (0,0,[]))) ⟨t,ht⟩

def sharedLayout (k : ℕ) : SharedCoordinates.Layout (Fin (sharedRows k).length) where
  lowSize i := rowR (sharedRows k) i
  firstSize i := sharedObservedA (sharedRows k) i
  secondSize i := rowB (sharedRows k) i
  lowSize_pos i := (sharedRows_moduli_positive i.isLt).1

instance (k : ℕ) (i : Fin (sharedRows k).length) :
    NeZero ((sharedLayout k).firstSize i) := ⟨(sharedRows_moduli_positive i.isLt).2.1.ne'⟩

instance (k : ℕ) (i : Fin (sharedRows k).length) :
    NeZero ((sharedLayout k).secondSize i) := ⟨(sharedRows_moduli_positive i.isLt).2.2.ne'⟩

open SharedCoordinates in
theorem sharedLayout_order (k : ℕ) : order (sharedLayout k) = sharedOrder (sharedRows k) := by
  unfold order sharedOrder
  rw [← Fin.prod_ofFn]
  apply congrArg (fun n => 1225*199*163*n)
  apply congrArg List.prod
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn,rowModulus,sharedLayout]

theorem sharedInputOrder_eq (k : ℕ) :
    (guardedModuli (sharedRows k)).prod = ∏ i, (sharedLayout k).lowSize i := by
  rw [← Fin.prod_ofFn]
  apply congrArg List.prod
  unfold guardedModuli
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn,sharedLayout]

theorem sharedInputOrder_pos (k : ℕ) : 0 < (guardedModuli (sharedRows k)).prod := by
  rw [sharedInputOrder_eq]
  exact Finset.prod_pos fun i _ => (sharedLayout k).lowSize_pos i

theorem sharedOrder_pos (k : ℕ) : 0 < sharedOrder (sharedRows k) := by
  rw [← sharedLayout_order]
  unfold SharedCoordinates.order
  apply Nat.mul_pos (by decide)
  apply Finset.prod_pos
  intro i _
  obtain ⟨hr,ha,hb⟩ := sharedRows_moduli_positive i.isLt
  exact Nat.mul_pos (Nat.mul_pos (pow_pos hr _) ha) hb

instance (k : ℕ) : NeZero (sharedOrder (sharedRows k)) := ⟨(sharedOrder_pos k).ne'⟩

end TranslationTiling.FiniteCompiler.Packed
