import TranslationTiling.Compiler.GuardedLogBound
import TranslationTiling.FiniteCompiler.SlotWords
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Stirling

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

private theorem log_factorial_eq (n : ℕ) (hn : 0 < n) :
    Real.log (n.factorial:ℝ) = Real.log (Stirling.stirlingSeq n) +
      Real.log (2*(n:ℝ))/2 + n*(Real.log n-1) := by
  have h := Stirling.log_stirlingSeq_formula n
  rw [Real.log_div (by exact_mod_cast hn.ne') (by positivity),Real.log_exp] at h
  linarith only [h]

/-- The largest weighted layer loses at most one bit plus half the logarithm
of the number of positions, by explicit bounds for the Stirling sequence. -/
theorem axis_radix_log_lower_sharp {t : ℕ} (ht : 0 < t) :
    7*(t:ℝ)*Real.logb 2 7 - (1 + Real.logb 2 (7*(t:ℝ))/2) ≤
      Real.logb 2 (Fintype.card (Word (7*t) (6*t) 6)) := by
  rw [card_word]
  have hchoose : 0 < (7*t).choose (6*t) := Nat.choose_pos (by omega)
  have hf : ((7*t).choose (6*t):ℝ)*((6*t).factorial:ℝ)*(t.factorial:ℝ) =
      ((7*t).factorial:ℝ) := by
    exact_mod_cast (show (7*t).choose (6*t)*(6*t).factorial*t.factorial = (7*t).factorial by
      have h := Nat.choose_mul_factorial_mul_factorial (n:=7*t) (k:=6*t) (by omega)
      rw [show 7*t-6*t = t by omega] at h
      exact h)
  have hlog := congrArg Real.log hf
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by exact_mod_cast hchoose.ne') (by positivity),
    log_factorial_eq t ht, log_factorial_eq (6*t) (by omega),
    log_factorial_eq (7*t) (by omega)] at hlog
  have lo (n : ℕ) (hn : 0 < n) :
      1-1/12-Real.log 2/2 ≤ Real.log (Stirling.stirlingSeq n) := by
    cases n with
    | zero => omega
    | succ n => simpa only [one_div] using Stirling.log_stirlingSeq_bounded_by_constant n
  have hi (n : ℕ) (hn : 0 < n) :
      Real.log (Stirling.stirlingSeq n) ≤ 1-Real.log 2/2 := by
    cases n with
    | zero => omega
    | succ n =>
      have h := Stirling.log_stirlingSeq'_antitone (show 0 ≤ n by omega)
      change _ ≤ Real.log (Stirling.stirlingSeq 1) at h
      rwa [Stirling.stirlingSeq_one, Real.log_div (by positivity) (by positivity),
        Real.log_exp,Real.log_sqrt (by norm_num)] at h
  have htR : 0 < (t:ℝ) := by exact_mod_cast ht
  have hgeom : 2*Real.log 2 ≤ Real.log 7*2-(Real.log 2+Real.log 6) := by
    have h := Real.log_le_log (show (0:ℝ)<4*12 by norm_num) (show (4*12:ℝ) ≤ 7^2 by norm_num)
    rw [Real.log_mul (x := 4) (by norm_num) (by norm_num),Real.log_pow,
      show (4:ℝ) = 2^2 by norm_num,Real.log_pow,
      show (12:ℝ) = 2*6 by norm_num,Real.log_mul (x := 2) (by norm_num) (by norm_num)] at h
    norm_num at h
    linarith only [h]
  rw [Real.logb,Real.logb,Real.logb]
  have h2 := Real.log_pos (show (1:ℝ)<2 by norm_num)
  apply (le_div_iff₀ h2).mpr
  have hcleared : (7*(t:ℝ)*(Real.log 7/Real.log 2) -
      (1+Real.log (7*(t:ℝ))/Real.log 2/2))*Real.log 2 =
      7*(t:ℝ)*Real.log 7 - Real.log 2 - Real.log (7*(t:ℝ))/2 := by
    field_simp
    <;> ring
  rw [hcleared]
  push_cast at hlog ⊢
  rw [Real.log_mul (x := ((7*t).choose (6*t):ℝ)) (by exact_mod_cast hchoose.ne') (by positivity),
    Real.log_pow]
  repeat rw [Real.log_mul (x := 2) (by norm_num) (by positivity)] at hlog
  rw [Real.log_mul (x := 7) (by norm_num) htR.ne'] at hlog ⊢
  rw [Real.log_mul (x := 6) (by norm_num) htR.ne'] at hlog
  norm_num at hlog ⊢
  nlinarith only [hlog,hgeom,lo (7*t) (by omega),hi (6*t) (by omega),hi t ht,Real.log_two_gt_d9]

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
