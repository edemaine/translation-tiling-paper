import TranslationTiling.Compiler.GuardedPrimeCounting

namespace TranslationTiling.Compiler.Size

noncomputable section

set_option exponentiation.threshold 2000

def guardedTrits (n : ℕ) : ℕ := Nat.log 3 (n-1) + 1

def guardedPairRanks (k : ℕ) : ℕ := 4*k+44

def guardedPairCap (k : ℕ) : ℕ := guardedPrimeCap (guardedPairRanks k)

def guardedDigitStart (k : ℕ) : ℕ := guardedPairCap k ^ 2 + 2*guardedPairCap k

def guardedDigitRanks (k : ℕ) : ℕ := guardedDigitStart k + 6*k + 100

def guardedDigitCap (k : ℕ) : ℕ := guardedPrimeCap (guardedDigitRanks k)

def guardedTests (n : ℕ) : ℕ := 1024 * (n+4)^2

theorem guardedTrits_capacity (n : ℕ) : n ≤ 3^guardedTrits n := by
  have h := Nat.lt_pow_succ_log_self (by decide : 1 < 3) (n-1)
  unfold guardedTrits
  omega

theorem guardedTrits_capacity_le {n : ℕ} (hn : 1 < n) :
    3^guardedTrits n ≤ 3*n := by
  unfold guardedTrits
  rw [pow_succ]
  calc
    _ ≤ (n-1)*3 := Nat.mul_le_mul_right 3 (Nat.pow_log_le_self 3 (by omega : n-1 ≠ 0))
    _ ≤ _ := by omega

theorem guardedTrits_ge {n : ℕ} (hn : 3^21 < n) : 20 ≤ guardedTrits n := by
  have h := (Nat.le_log_iff_pow_le (by decide : 1 < 3) (by omega : n-1 ≠ 0)).mpr
    (show 3^20 ≤ n-1 from (by decide : 3^20 ≤ 3^21).trans (by omega))
  unfold guardedTrits
  omega

theorem guarded_t_lower {n : ℕ} (hn : 3^21 < n) : 32 ≤ Real.logb 2 ((n : ℝ)+4) := by
  have hu : (2 : ℝ)^32 ≤ (n : ℝ)+4 := by
    exact_mod_cast (show 2^32 ≤ n+4 from (by decide : 2^32 ≤ 3^21).trans (by omega))
  have h := lg_mono (by positivity) hu
  simpa only [lg_two_pow, Nat.cast_ofNat] using h

theorem guardedTrits_log {n : ℕ} (hn : 1 < n) :
    (guardedTrits n : ℝ) ≤ (359/569 : ℝ)*Real.logb 2 ((n : ℝ)+4)+1 := by
  have h3 : (569 : ℝ) / 359 ≤ Real.logb 2 3 := by
    apply lg_lower (a := 569) (b := 359) (by decide) _ (by norm_num)
    exact_mod_cast (by decide : (2:ℕ)^569 ≤ 3^359)
  have hn' : 3^Nat.log 3 (n-1) ≤ n-1 := Nat.pow_log_le_self 3 (by omega)
  have hpow : (3 : ℝ)^Nat.log 3 (n-1) ≤ (n : ℝ)+4 := by
    exact_mod_cast (show 3^Nat.log 3 (n-1) ≤ n+4 from hn'.trans (by omega))
  have h := lg_mono (by positivity) hpow
  rw [Real.logb_pow] at h
  have hh := mul_le_mul_of_nonneg_left h3
    (show 0 ≤ (Nat.log 3 (n-1) : ℝ) by positivity)
  unfold guardedTrits
  push_cast
  nlinarith only [h,hh]

theorem guardedPairCaps_ge {k : ℕ} (hk : 20 ≤ k) :
    16 ≤ guardedPairCap k ∧ guardedPairRanks k ≤ guardedPairCap k := by
  have h : guardedPairRanks k ≤ guardedPairCap k := by
    unfold guardedPairCap guardedPrimeCap
    exact (show guardedPairRanks k ≤ 4*guardedPairRanks k by omega).trans
      (Nat.le_mul_of_pos_right _ (by omega))
  exact ⟨(show 16 ≤ guardedPairRanks k by unfold guardedPairRanks; omega).trans h, h⟩

theorem guardedDigitRanks_le {k : ℕ} (hk : 20 ≤ k) :
    guardedDigitRanks k ≤ 2*(guardedPairCap k)^2 := by
  obtain ⟨hmin, hcap⟩ := guardedPairCaps_ge hk
  have hcount : 6*k+100 ≤ 2*guardedPairCap k := by unfold guardedPairRanks at hcap; omega
  unfold guardedDigitRanks guardedDigitStart
  nlinarith only [hmin, hcount, Nat.zero_le ((guardedPairCap k-4)^2),
    Nat.sub_add_cancel (show 4 ≤ guardedPairCap k by omega),
    Nat.mul_le_mul_right (guardedPairCap k) (show 4 ≤ guardedPairCap k by omega)]

theorem guardedDigitCap_gt {k : ℕ} (hk : 20 ≤ k) :
    guardedDigitStart k < guardedDigitCap k := by
  unfold guardedDigitCap guardedPrimeCap
  have h : guardedDigitStart k < guardedDigitRanks k := by unfold guardedDigitRanks; omega
  exact h.trans_le (by
    have := Nat.mul_le_mul_left (4*guardedDigitRanks k)
      (show 1 ≤ Nat.log 2 (guardedDigitRanks k)+1 by omega)
    omega)

theorem guarded_g_lower {t : ℝ} (ht : 32 ≤ t) : 5 ≤ Real.logb 2 t := by
  have h := lg_mono (by positivity : 0 < (2 : ℝ)^5) (show (2 : ℝ)^5 ≤ t by norm_num; exact ht)
  simpa only [lg_two_pow, Nat.cast_ofNat] using h

theorem guarded_prime_logs {n : ℕ} (hn : 3^21 < n) :
    let k := guardedTrits n
    let t := Real.logb 2 ((n : ℝ)+4)
    let g := Real.logb 2 t
    let l := Real.logb 2 g
    (Real.logb 2 (guardedPairCap k) ≤ g+l+6 ∧
      Real.logb 2 (guardedDigitCap k) ≤ 2*g+3*l+18) ∧
    (17 ≤ g → Real.logb 2 (guardedPairCap k) ≤ g+l+4 ∧
      Real.logb 2 (guardedDigitCap k) ≤ 2*g+3*l+13) := by
  let k := guardedTrits n
  let t := Real.logb 2 ((n : ℝ)+4)
  let g := Real.logb 2 t
  let l := Real.logb 2 g
  let x := guardedPairCap k
  let y := guardedDigitCap k
  let m := guardedPairRanks k
  let M := guardedDigitRanks k
  change (Real.logb 2 x ≤ g+l+6 ∧ Real.logb 2 y ≤ 2*g+3*l+18) ∧
    (17 ≤ g → Real.logb 2 x ≤ g+l+4 ∧ Real.logb 2 y ≤ 2*g+3*l+13)
  have hn' : 1 < n := (by decide : 1 < 3^21).trans hn
  have hk : 20 ≤ k := guardedTrits_ge hn
  have ht : 32 ≤ t := guarded_t_lower hn
  have hg : 5 ≤ g := guarded_g_lower ht
  have hl : l ≤ g/2 := by
    have h := lg_ratio (t := g) (b := 2) (by decide) (by norm_num; linarith)
    change Real.logb 2 g ≤ g/2
    norm_num at h
    linarith
  have hkr : (k : ℝ) ≤ (359/569 : ℝ)*t+1 := guardedTrits_log hn'
  have hm : 0 < m := by unfold m guardedPairRanks; omega
  have hx : 0 < x := lt_of_lt_of_le (by decide) (guardedPairCaps_ge hk).1
  have hM : 0 < M := by unfold M guardedDigitRanks; omega
  have hx' : (x : ℝ) = 4*(m : ℝ)*((Nat.log 2 m : ℝ)+1) := by
    simp only [x, m, guardedPairCap, guardedPrimeCap, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]
  have hy' : (y : ℝ) = 4*(M : ℝ)*((Nat.log 2 M : ℝ)+1) := by
    simp only [y, M, guardedDigitCap, guardedPrimeCap, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]
  have hM' : (M : ℝ) ≤ 2*(x : ℝ)^2 := by exact_mod_cast (guardedDigitRanks_le hk)
  have hlogM := lg_mono (by exact_mod_cast hM : 0 < (M : ℝ)) hM'
  rw [Real.logb_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity), Real.logb_pow,
    Real.logb_self_eq_one (by norm_num), Nat.cast_ofNat] at hlogM
  have hx0 : 0 < (x : ℝ) := by exact_mod_cast hx
  have hy0 : 0 < (y : ℝ) := by rw [hy']; positivity
  have ht0 : 0 < t := by linarith
  have hg0 : 0 < g := by linarith
  have hlgM := lg_natLog_le hM
  have log_prod (b : ℕ) (hb : b ≠ 0) (u : ℝ) (hu : 0 < u) :
      Real.logb 2 ((2 : ℝ)^b * u) = (b : ℝ) + Real.logb 2 u := by
    rw [Real.logb_mul (by positivity) hu.ne', lg_two_pow]
  have xlog {c a : ℕ} (hc : 0 < c) (hm₁ : (m : ℝ) ≤ c*t)
      (hlg : Real.logb 2 (c : ℝ) + 1 ≤ a)
      {b : ℕ} (hb : 0 < b)
      (hscale : 4*(c : ℝ)*(g+a) ≤ (2 : ℝ)^b*g) :
      Real.logb 2 x ≤ g+l+b := by
    have hmlg := lg_mono (by exact_mod_cast hm : 0 < (m : ℝ)) hm₁
    rw [Real.logb_mul (by exact_mod_cast hc.ne') ht0.ne'] at hmlg
    have hlog := lg_natLog_le hm
    have hh := mul_le_mul hm₁ (show (Nat.log 2 m : ℝ)+1 ≤ g+a by linarith)
      (by positivity) (by positivity)
    have hxle : (x : ℝ) ≤ (2 : ℝ)^b*(t*g) := by
      rw [hx']
      have hh' := mul_le_mul_of_nonneg_right hscale ht0.le
      nlinarith only [hh, hh']
    have hlx := lg_mono hx0 hxle
    rw [log_prod b hb.ne' (t*g) (mul_pos ht0 hg0), Real.logb_mul ht0.ne' hg0.ne'] at hlx
    linarith
  have ylog {a b c : ℕ} (ha : Real.logb 2 x ≤ g+l+a)
      (hb : 0 < b) (hxlog : Real.logb 2 x + 1 ≤ (c : ℝ)*g)
      (hbc : (16 : ℝ)*c ≤ (2 : ℝ)^b) :
      Real.logb 2 y ≤ 2*g+3*l+2*a+b := by
    have hmul := mul_le_mul hM' (show (Nat.log 2 M : ℝ)+1 ≤ 2*(c : ℝ)*g by linarith)
      (by positivity) (by positivity)
    have hy : (y : ℝ) ≤ (2 : ℝ)^b*((x : ℝ)^2*g) := by
      rw [hy']
      have hh := mul_le_mul_of_nonneg_right hbc
        (show 0 ≤ (x : ℝ)^2*g by positivity)
      nlinarith only [hmul, hh]
    have hlog := lg_mono hy0 hy
    rw [log_prod b hb.ne' ((x : ℝ)^2*g) (by positivity), Real.logb_mul (by positivity) hg0.ne',
      Real.logb_pow, Nat.cast_ofNat] at hlog
    linarith
  have hm₅ : (m : ℝ) ≤ 5*t := by
    change (↑(4*k+44 : ℕ) : ℝ) ≤ 5*t
    push_cast
    linarith
  have hx₆ : Real.logb 2 x ≤ g+l+6 := by
    have h := lg_mono (by norm_num : 0 < (5 : ℝ)) (show (5 : ℝ) ≤ 2^3 by norm_num)
    rw [lg_two_pow] at h
    norm_num at h
    refine xlog (c := 5) (a := 4) (b := 6) (by decide) hm₅ ?_ (by decide) ?_
    · norm_num
      linarith
    · norm_num
      linarith
  have hy₁₈ : Real.logb 2 y ≤ 2*g+3*l+18 := by
    have hxlog : Real.logb 2 x + 1 ≤ (3 : ℝ)*g := by linarith
    have h := ylog (a := 6) (b := 6) (c := 3) hx₆ (by decide) hxlog (by norm_num)
    norm_num at h
    linarith
  refine ⟨⟨hx₆, hy₁₈⟩, fun hg₁₇ => ?_⟩
  have ht₁₇ : 131072 ≤ t := by
    have hh := (Real.le_logb_iff_rpow_le (by norm_num : (1 : ℝ) < 2) ht0).mp hg₁₇
    rw [show (17 : ℝ) = ((17 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at hh
    norm_num at hh
    exact hh
  have hm₃ : (m : ℝ) ≤ 3*t := by
    change (↑(4*k+44 : ℕ) : ℝ) ≤ 3*t
    push_cast
    linarith
  have hx₄ : Real.logb 2 x ≤ g+l+4 := by
    have h := lg_mono (by norm_num : 0 < (3 : ℝ)) (show (3 : ℝ) ≤ 2^2 by norm_num)
    rw [lg_two_pow] at h
    norm_num at h
    refine xlog (c := 3) (a := 3) (b := 4) (by decide) hm₃ ?_ (by decide) ?_
    · norm_num
      linarith
    · norm_num
      linarith
  have hy₁₃ : Real.logb 2 y ≤ 2*g+3*l+13 := by
    have hxlog : Real.logb 2 x + 1 ≤ (2 : ℝ)*g := by linarith
    have h := ylog (a := 4) (b := 5) (c := 2) hx₄ (by decide) hxlog (by norm_num)
    norm_num at h
    linarith
  exact ⟨hx₄, hy₁₃⟩

end
end TranslationTiling.Compiler.Size
