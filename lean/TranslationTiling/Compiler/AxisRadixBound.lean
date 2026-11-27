import TranslationTiling.Compiler.GuardedLogBound
import TranslationTiling.FiniteCompiler.SlotWords
import Mathlib.Analysis.Complex.ExponentialBounds

namespace TranslationTiling.FiniteCompiler.SlotWords

/-- Six active labels and one inactive label give a seven-letter alphabet.
The layer with six sevenths of the slots active is a largest layer. -/
theorem seven_pow_le_weighted (t : ℕ) :
    7^(7*t) ≤ (7*t+1) * Fintype.card (Word (7*t) (6*t) 6) := by
  rw [card_word]
  let f (j : ℕ) := (7*t).choose j * 6^j
  change 7^(7*t) ≤ (7*t+1) * f (6*t)
  have hstep (j : ℕ) : f (j+1) * (j+1) = f j * (6*(7*t-j)) := by
    unfold f
    rw [pow_succ]
    calc
      _ = ((7*t).choose (j+1)*(j+1))*6^j*6 := by ring
      _ = _ := by rw [Nat.choose_succ_right_eq]; ring
  have hup (j : ℕ) (hj : j < 6*t) : f j ≤ f (j+1) := by
    refine Nat.le_of_mul_le_mul_right ?_ (by omega : 0 < j+1)
    rw [hstep]
    exact Nat.mul_le_mul_left _ (by omega)
  have hdown (j : ℕ) (hj : 6*t ≤ j) : f (j+1) ≤ f j := by
    refine Nat.le_of_mul_le_mul_right ?_ (by omega : 0 < j+1)
    rw [hstep]
    exact Nat.mul_le_mul_left _ (by omega)
  have hbelow (j : ℕ) : ∀ i ≤ j, j ≤ 6*t → f i ≤ f j := by
    induction j with
    | zero =>
      intro i hi _
      simpa only [Nat.le_zero.mp hi] using (le_rfl : f 0 ≤ f 0)
    | succ j ih =>
      intro i hi hj
      by_cases h : i = j+1
      · simp [h]
      · exact (ih i (by omega) (by omega)).trans (hup j (by omega))
  have habove (j : ℕ) : f (6*t+j) ≤ f (6*t) := by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [Nat.add_succ]
      exact (hdown (6*t+j) (by omega)).trans ih
  have hpeak (j : ℕ) : f j ≤ f (6*t) := by
    by_cases h : j ≤ 6*t
    · exact hbelow _ _ h le_rfl
    · have hh := habove (j-6*t)
      rwa [Nat.add_sub_of_le (by omega : 6*t ≤ j)] at hh
  calc
    7^(7*t) = ∑ j ∈ Finset.range (7*t+1), f j := by
      simpa [f,mul_comm] using (add_pow (6:ℕ) 1 (7*t))
    _ ≤ (7*t+1) * f (6*t) := by
      simpa using (Finset.sum_le_sum (s := Finset.range (7*t+1))
        (f := f) (g := fun _ => f (6*t)) (fun j _ => hpeak j))

end TranslationTiling.FiniteCompiler.SlotWords

namespace TranslationTiling.Compiler.Size

open FiniteCompiler.SlotWords

/-- A weighted two-axis digit loses at most the logarithm of the number of layers. -/
theorem axis_radix_log_lower (t : ℕ) :
    7*(t : ℝ)*Real.logb 2 7 - Real.logb 2 (7*(t : ℝ)+1) ≤
      Real.logb 2 (Fintype.card (Word (7*t) (6*t) 6)) := by
  let R := Fintype.card (Word (7*t) (6*t) 6)
  have h := seven_pow_le_weighted t
  change 7^(7*t) ≤ (7*t+1)*R at h
  have hR : 0 < R := by
    by_contra! hzero
    have hpos : 0 < 7^(7*t) := by positivity
    simp [Nat.eq_zero_of_le_zero hzero] at h
  have hlog := lg_mono (show 0 < (7 : ℝ)^(7*t) by positivity)
    (show (7 : ℝ)^(7*t) ≤ (7*(t : ℝ)+1)*(R : ℝ) by exact_mod_cast h)
  rw [Real.logb_pow,Real.logb_mul (by positivity) (by exact_mod_cast hR.ne')] at hlog
  push_cast at hlog
  change _ ≤ Real.logb 2 (R : ℝ)
  linarith

/-- The decimal coefficient rounds (14/log_2 7) upward. -/
theorem axis_coefficient_le_decimal : 14 / Real.logb 2 7 ≤ (4.986901 : ℝ) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := 1/8) (by norm_num) 10
  norm_num [Finset.sum_range_succ] at h
  have hlow := (abs_le.mp h).1
  have h7 : Real.log 7 = 3 * Real.log 2 + Real.log (7/8) := by
    rw [show (7:ℝ) = 2^3*(7/8) by norm_num,Real.log_mul (by norm_num) (by norm_num),
      Real.log_pow]
    norm_num
  rw [Real.logb,div_div_eq_mul_div,mul_comm,div_le_iff₀ (Real.log_pos (by norm_num)),h7]
  linarith [Real.log_two_gt_d9]

end TranslationTiling.Compiler.Size
