import TranslationTiling.Compiler.SlotRadixBound
import TranslationTiling.FiniteCompiler.Effective.SlotWordBridge

namespace TranslationTiling.Compiler.Size

open FiniteCompiler.SlotWords FiniteCompiler.Packed

/-- The capacity of all but the last digit bounds the leading slot
count. Writing `m = 4*t`, the parenthesized term is
`2*m - lg(m+1)`. -/
theorem slot_digit_log_bound {n t : ℕ} (hn : 0 < n) (ht : 0 < t) :
    (((slotPackedDigits n t)-1 : ℕ) : ℝ) *
      (8*(t : ℝ) - Real.logb 2 (4*(t : ℝ)+1)) ≤ Real.logb 2 (n : ℝ) := by
  let D := slotRadix (4*t) (3*t)
  let d := slotPackedDigits n t-1
  have hD : 1 < D := slotRadix_one_lt ht
  have hd : d = Nat.clog D n-1 := by unfold d slotPackedDigits D; omega
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
  have hradix : 8*(t : ℝ) - Real.logb 2 (4*(t : ℝ)+1) ≤ Real.logb 2 (D : ℝ) := by
    simpa only [D,slotRadix,card_word] using slot_radix_log_lower t
  exact (mul_le_mul_of_nonneg_left hradix (Nat.cast_nonneg d)).trans hl

/-- The number of slot prime factors is five times the input bit count,
up to the capacity loss from the fixed weight and the last digit. -/
theorem slot_factor_count {n t : ℕ} (hn : 0 < n) (ht : 0 < t) :
    10*(slotPackedDigits n t : ℝ)*(4*(t : ℝ)) ≤
      5*Real.logb 2 (n : ℝ)*(1 + Real.logb 2 (4*(t : ℝ)+1)/(4*(t : ℝ))) + 40*(t : ℝ) := by
  let m : ℝ := 4*(t : ℝ)
  let v := Real.logb 2 (m+1)
  let u := Real.logb 2 (n : ℝ)
  let j : ℝ := ((slotPackedDigits n t-1 : ℕ) : ℝ)
  have hm : 0 < m := by dsimp [m]; positivity
  have hv : 0 ≤ v := Real.logb_nonneg (by norm_num) (show 1 ≤ m+1 by linarith)
  have hnat (m : ℕ) : m+1 ≤ 2^m := by
    induction m with
    | zero => decide
    | succ b ih =>
      rw [pow_succ]
      omega
  have hvm : v ≤ m := by
    have hl := lg_mono (x := 4*(t : ℝ)+1) (y := (2 : ℝ)^(4*t)) (by positivity)
      (by exact_mod_cast hnat (4*t))
    rw [lg_two_pow] at hl
    simpa [v,m] using hl
  have hc : j*(2*m-v) ≤ u := by
    convert slot_digit_log_bound hn ht using 1
    dsimp [m,v,u,j]
    ring
  have ha : 2*m*m ≤ (2*m-v)*(m+v) := by nlinarith [mul_nonneg hv (sub_nonneg.mpr hvm)]
  have hma := mul_le_mul_of_nonneg_left ha (show 0 ≤ 5*j by dsimp [j]; positivity)
  have hmb := mul_le_mul_of_nonneg_right hc (show 0 ≤ 5*(m+v) by positivity)
  have hmul : (10*j*m)* m ≤ 5*u*(m+v) := by
    calc
      _ = 5*j*(2*m*m) := by ring
      _ ≤ 5*j*((2*m-v)*(m+v)) := hma
      _ = (j*(2*m-v))*(5*(m+v)) := by ring
      _ ≤ u*(5*(m+v)) := hmb
      _ = _ := by ring
  have hdiv := (le_div_iff₀ hm).mpr hmul
  have hk : (slotPackedDigits n t : ℝ) = j+1 := by
    have hh : 1 ≤ slotPackedDigits n t := le_max_left ..
    have he : slotPackedDigits n t = (slotPackedDigits n t-1)+1 := by omega
    change (slotPackedDigits n t : ℝ) = ((slotPackedDigits n t-1 : ℕ) : ℝ)+1
    simpa only [Nat.cast_add,Nat.cast_one] using congrArg (fun i : ℕ => (i : ℝ)) he
  change 10*(slotPackedDigits n t : ℝ)*m ≤ 5*u*(1+v/m)+40*(t : ℝ)
  calc
    _ = 10*j*m+10*m := by rw [hk]; ring
    _ ≤ 5*u*(m+v)/m+10*m := add_le_add hdiv le_rfl
    _ = _ := by field_simp; dsimp [m]; ring

end TranslationTiling.Compiler.Size
