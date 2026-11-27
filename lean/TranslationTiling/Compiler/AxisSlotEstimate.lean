import TranslationTiling.FiniteCompiler.Effective.AxisSlotPrimes
import TranslationTiling.FiniteCompiler.Effective.AxisSlotCRT
import TranslationTiling.Compiler.AxisRadixBound
import TranslationTiling.FiniteCompiler.Effective.AxisSlotWordBridge

namespace TranslationTiling.Compiler.Size

open FiniteCompiler FiniteCompiler.Effective FiniteCompiler.Packed
open FiniteCompiler.SharedCoordinates FiniteCompiler.Packed.AxisParameters
open scoped BigOperators

set_option maxRecDepth 10000
attribute [local irreducible] slotPrimeAt slotSearchCap


theorem rankedAxisPrime_caps (k m : ℕ) :
    (∀ i, (rankedAxisParameters k m).fallback i ≤ axisFallbackCap m) ∧
    (∀ i, (rankedAxisParameters k m).prime i ≤ axisPrimeCap m (2*k*m)) := by
  have h : AxisParameters.axisFallbackCap m ≤ (AxisParameters.axisFallbackCap m)^2 := by
    have hm : 1 ≤ axisFallbackCap m :=
      (by decide : 1 ≤ SlotParameters.slotBasePrimeCap).trans (threshold_le_slotSearchCap ..)
    simpa [pow_two] using Nat.mul_le_mul_right (axisFallbackCap m) hm
  have hQ : (axisFallbackCap m)^2 ≤ axisPrimeCap m (2*k*m) := by
    unfold axisPrimeCap slotWindowCap
    apply le_trans (le_max_left ..)
    exact Nat.le_mul_of_pos_left _ (by decide : 0 < 8)
  have hfb (i : AxisFallback m) : (rankedAxisParameters k m).fallback i ≤ axisFallbackCap m :=
    (slotPrimeAt_spec (axisFallbackRank m i).isLt).2.2
  exact ⟨hfb,fun i => by
    rcases i with ⟨i,j⟩ | i
    · exact (axisGroupPrime_spec i (axisLabelIndex_lt j)).2.2
    · exact (hfb i).trans (h.trans hQ)⟩

/-- A Wang slot contributes four low factors and three marker factors.
Each position and slope contributes four shared fallback factors. -/
theorem axis_order_le {k m A P : ℕ} (s : AxisParameters k m)
    (hA : ∀ i, s.fallback i ≤ A) (hP : ∀ i, s.prime i ≤ P) :
    order s.layout ≤ order (fourValueLayout 0) * (P^(7*(2*k*m))*A^(8*m)) := by
  rw [s.order_split,Fintype.prod_sum_type]
  have hw (i : WangSlot k m) : rowModulus s.layout (.inr (.inl i)) ≤ P^7 := by
    change s.low i^2*1*(∏ j, s.marker i j) ≤ _
    have hlo : s.low i ≤ P^2 := by
      rw [pow_two]
      exact Nat.mul_le_mul (hP _) (hP _)
    have hmark : (∏ j, s.marker i j) ≤ P^3 := by
      have h := (Finset.prod_le_prod (s := Finset.univ) (f := s.marker i)
        (g := fun _ : Fin 3 => P) (fun j _ => hP (.inl (i,.inr j))))
      simpa only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] using h
    simpa only [mul_one,← pow_mul,← pow_add] using
      Nat.mul_le_mul (Nat.pow_le_pow_left hlo 2) hmark
  have hfb (i : AxisFallback m) : rowModulus s.layout (.inr (.inr i)) ≤ A := by
    simpa [rowModulus,layout] using hA i
  apply Nat.mul_le_mul_left
  apply Nat.mul_le_mul
  · have h := Finset.prod_le_prod (s := Finset.univ) (g := fun _ : WangSlot k m => P^7)
      (fun i _ => hw i)
    simpa only [← pow_mul,Finset.prod_const,Finset.card_univ,Fintype.card_congr (axisSlotRank k m),
      Fintype.card_fin] using h
  · have h := Finset.prod_le_prod (s := Finset.univ) (g := fun _ : AxisFallback m => A)
      (fun i _ => hfb i)
    simpa only [Finset.prod_const,Finset.card_univ,Fintype.card_congr (axisFallbackRank m),
      Fintype.card_fin] using h

theorem axis_digit_log_bound {n t : ℕ} (hn : 0 < n) (ht : 0 < t) :
    (((axisPackedDigits n t)-1 : ℕ) : ℝ) *
      (7*(t : ℝ)*Real.logb 2 7 - Real.logb 2 (7*(t : ℝ)+1)) ≤ Real.logb 2 (n : ℝ) := by
  let D := axisRadix (7*t) (6*t)
  let d := axisPackedDigits n t-1
  have hD : 1 < D := axisRadix_one_lt ht
  have hd : d = Nat.clog D n-1 := by unfold d axisPackedDigits D; omega
  have hp : D^d ≤ n := by
    by_cases h : 1 < n
    · rw [hd]
      exact (Nat.pow_pred_clog_lt_self hD h).le
    · have he : n = 1 := by omega
      rw [hd,he,Nat.clog_one_right]
      simp
  have hpos : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  have hl := lg_mono (pow_pos hpos d) (show (D : ℝ)^d ≤ n by exact_mod_cast hp)
  rw [Real.logb_pow] at hl
  have hradix : 7*(t : ℝ)*Real.logb 2 7 - Real.logb 2 (7*(t : ℝ)+1) ≤ Real.logb 2 (D : ℝ) := by
    simpa only [D,axisRadix,SlotWords.card_word] using axis_radix_log_lower t
  exact (mul_le_mul_of_nonneg_left hradix (Nat.cast_nonneg d)).trans hl

end TranslationTiling.Compiler.Size
