import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Complex.ExponentialBounds

namespace TranslationTiling.Compiler.Size

noncomputable section

/-- The uniform size bound for the guarded Sudoku reduction. -/
def guardedBound (n : ℕ) : ℝ :=
  max (((n : ℝ) + 4) ^ ((88331 / 5000 : ℝ) * Real.logb 2 (Real.logb 2 ((n : ℝ) + 4)) + 561))
    ((2 : ℝ) ^ (2392 : ℕ))

theorem lg_mono {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    Real.logb 2 x ≤ Real.logb 2 y :=
  Real.logb_le_logb_of_le (by norm_num) hx hxy

theorem lg_two_pow (a : ℕ) : Real.logb 2 ((2 : ℝ) ^ a) = a := by
  rw [Real.logb_pow]
  norm_num [Real.logb_self_eq_one]

theorem lg_lower {a b : ℕ} {x : ℝ} (hb : 0 < b) (h : (2 : ℝ)^a ≤ x^b) (_hx : 0 < x) :
    (a : ℝ) / b ≤ Real.logb 2 x := by
  have hl := lg_mono (by positivity) h
  rw [lg_two_pow, Real.logb_pow] at hl
  exact (div_le_iff₀ (by exact_mod_cast hb)).mpr (by simpa only [mul_comm] using hl)

theorem guarded_bound_log {n N : ℕ} (hN : 0 < N)
    (h : Real.logb 2 N ≤
      Real.logb 2 ((n : ℝ) + 4) *
        ((88331 / 5000 : ℝ) * Real.logb 2 (Real.logb 2 ((n : ℝ) + 4)) + 561)) :
    (N : ℝ) ≤ guardedBound n := by
  apply le_trans _ (le_max_left _ _)
  apply (Real.logb_le_logb (by norm_num : (1 : ℝ) < 2)
    (by exact_mod_cast hN) (by positivity)).mp
  rwa [Real.logb_rpow_eq_mul_logb_of_pos (by positivity), mul_comm]

theorem guarded_bound_dyadic {n e a b c d : ℕ} (hb : 0 < b) (hd : 0 < d)
    (ht : (2 : ℝ)^a ≤ ((n : ℝ) + 4)^b)
    (hg : (2 : ℝ)^c ≤ ((a : ℝ) / b)^d) (ha : 0 < a)
    (he : (e : ℝ) ≤ ((a : ℝ) / b) * ((88331 / 5000 : ℝ) * ((c : ℝ) / d) + 561)) :
    ((2^e : ℕ) : ℝ) ≤ guardedBound n := by
  have ht' := lg_lower hb ht (by positivity)
  have hg' := (lg_lower hd hg (by positivity)).trans (lg_mono (by positivity) ht')
  apply guarded_bound_log (by positivity)
  rw [Nat.cast_pow, Nat.cast_ofNat, lg_two_pow]
  exact he.trans (mul_le_mul ht' (by linarith) (by positivity) (le_trans (by positivity) ht'))

private theorem log_two_lower : (1 / 2 : ℝ) ≤ Real.log 2 := by
  linarith [Real.log_two_gt_d9]

theorem lg_le_twice_sub_one {x : ℝ} (hx : 1 ≤ x) :
    Real.logb 2 x ≤ 2 * (x - 1) := by
  rw [Real.logb, div_le_iff₀ (by linarith [log_two_lower] : 0 < Real.log 2)]
  have h := Real.log_le_sub_one_of_pos (show 0 < x by linarith)
  nlinarith only [h, mul_nonneg (show 0 ≤ x - 1 by linarith)
    (show 0 ≤ 2 * Real.log 2 - 1 by linarith [log_two_lower])]

theorem lg_ratio {t : ℝ} {b : ℕ} (hb : 2 ≤ b) (ht : (2 : ℝ)^b ≤ t) :
    Real.logb 2 t ≤ (b : ℝ) * (t / (2 : ℝ)^b) := by
  have hs : 1 ≤ t / (2 : ℝ)^b := (le_div_iff₀ (by positivity)).mpr (by simpa using ht)
  have h := lg_le_twice_sub_one hs
  have ht0 : 0 < t := lt_of_lt_of_le (by positivity) ht
  rw [Real.logb_div ht0.ne' (by positivity : (2 : ℝ)^b ≠ 0), lg_two_pow] at h
  have hb' : (2 : ℝ) ≤ b := by exact_mod_cast hb
  nlinarith only [h, mul_nonneg (show 0 ≤ (b : ℝ) - 2 by linarith)
    (show 0 ≤ t / (2 : ℝ)^b - 1 by linarith)]

private theorem lg_tangent {g : ℝ} (hg : 0 < g) :
    Real.logb 2 g ≤ 123 / 7 + 2 * g / (2 : ℝ)^19 := by
  have h := Real.log_le_sub_one_of_pos (show 0 < g / (2 : ℝ)^19 by positivity)
  rw [Real.log_div hg.ne' (by positivity), Real.log_pow] at h
  norm_num only [Nat.cast_ofNat] at h
  have hu : Real.log 2 ≤ 7 / 10 := by linarith [Real.log_two_lt_d9]
  have hlog : 0 < Real.log 2 := by linarith [log_two_lower]
  have hi : 10 / 7 ≤ (Real.log 2)⁻¹ := by
    rw [← one_div, le_div_iff₀ hlog]
    linarith
  have hj : (Real.log 2)⁻¹ ≤ 2 := by
    rw [← one_div, div_le_iff₀ hlog]
    linarith [log_two_lower]
  have hm := mul_le_mul_of_nonneg_right h
    (inv_nonneg.mpr (by linarith [log_two_lower] : 0 ≤ Real.log 2))
  have he : Real.log 2 * (Real.log 2)⁻¹ = 1 := by
    field_simp [show Real.log 2 ≠ 0 by linarith [log_two_lower]]
  have hs := mul_le_mul_of_nonneg_right hj
    (show 0 ≤ g / (2 : ℝ)^19 by positivity)
  rw [Real.logb, div_eq_mul_inv]
  nlinarith only [hm, he, hi, hs]

/-- The normalized logarithmic volume estimate in the two prime-budget ranges. -/
theorem guarded_volume_log {t v : ℝ} (ht : 32 ≤ t)
    (hlo : Real.logb 2 t < 17 →
      v ≤ (28 * Real.logb 2 t + 40 * Real.logb 2 (Real.logb 2 t) + 240) *
        ((359 / 569 : ℝ) * t + 1) +
        425 * Real.logb 2 t + 616 * Real.logb 2 (Real.logb 2 t) + 3908 + 4*t)
    (hhi : 17 ≤ Real.logb 2 t →
      v ≤ (28 * Real.logb 2 t + 40 * Real.logb 2 (Real.logb 2 t) + 172) *
        ((359 / 569 : ℝ) * t + 1) +
        425 * Real.logb 2 t + 616 * Real.logb 2 (Real.logb 2 t) + 2868 + 4*t) :
    v ≤ t * ((88331 / 5000 : ℝ) * Real.logb 2 t + 561) := by
  let g := Real.logb 2 t
  let l := Real.logb 2 g
  have hg : 5 ≤ g := by
    have h := lg_mono (by positivity : 0 < (2 : ℝ)^5) (show (2 : ℝ)^5 ≤ t by norm_num; exact ht)
    simpa only [lg_two_pow, Nat.cast_ofNat] using h
  have hlg : l ≤ g / 2 := by
    have h := lg_ratio (t := g) (b := 2) (by decide) (by norm_num; linarith)
    norm_num at h
    change Real.logb 2 g ≤ g / 2
    linarith
  by_cases h : g < 17
  · have hlow := hlo h
    change v ≤ (28*g + 40*l + 240)*((359/569 : ℝ)*t + 1) + 425*g + 616*l + 3908 + 4*t at hlow
    have hl₅ : l ≤ 5 := by
      exact (lg_mono (by linarith : 0 < g) (show g ≤ (2 : ℝ)^5 by norm_num; linarith)).trans_eq
        (by rw [lg_two_pow]; norm_num)
    have hg' : g ≤ 5*(t/32) := by
      simpa only [g, Nat.cast_ofNat, show (2 : ℝ)^5 = 32 by norm_num] using
        (lg_ratio (t := t) (b := 5) (by decide) (by norm_num; exact ht))
    have hrest : 453*g + 656*l + 4148 ≤ 252*t := by linarith
    have hlt := mul_le_mul_of_nonneg_right hl₅ (show 0 ≤ t by linarith)
    have hgt : 0 ≤ g*t := mul_nonneg (by linarith) (by linarith)
    change v ≤ t * ((88331/5000 : ℝ)*g + 561)
    nlinarith only [hlow, hrest, hlt, hgt, ht]
  · have hg₁₇ : 17 ≤ g := le_of_not_gt h
    have hbig := hhi hg₁₇
    change v ≤ (28*g + 40*l + 172)*((359/569 : ℝ)*t + 1) + 425*g + 616*l + 2868 + 4*t at hbig
    have ht' : (2 : ℝ)^17 ≤ t := by
      have hh := (Real.le_logb_iff_rpow_le (by norm_num : (1 : ℝ) < 2)
        (by linarith : 0 < t)).mp hg₁₇
      simpa only [← Real.rpow_natCast, Nat.cast_ofNat] using hh
    have ht₁₇ : 131072 ≤ t := by norm_num at ht'; exact ht'
    have hg' : g ≤ 17*(t/131072) := by
      simpa only [g, Nat.cast_ofNat, show (2 : ℝ)^17 = 131072 by norm_num] using
        (lg_ratio (t := t) (b := 17) (by decide) ht')
    have hrest : 453*g + 656*l + 3040 ≤ t := by linarith
    have hl' : l ≤ 123/7 + g/262144 := by
      have htan := lg_tangent (by linarith : 0 < g)
      norm_num at htan
      linarith
    have hlt := mul_le_mul_of_nonneg_right hl' (show 0 ≤ t by linarith)
    have hgt : 0 ≤ g*t := mul_nonneg (by linarith) (by linarith)
    change v ≤ t * ((88331/5000 : ℝ)*g + 561)
    nlinarith only [hbig, hrest, hlt, hgt, ht]

end
end TranslationTiling.Compiler.Size
