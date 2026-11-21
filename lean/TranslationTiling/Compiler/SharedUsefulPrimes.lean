import TranslationTiling.Compiler.GuardedPrimeCounting

namespace TranslationTiling.Compiler.Size

noncomputable section

set_option maxRecDepth 10000

private theorem prime_count_lower (M : ℕ) (hM : 2 ≤ M) :
    (M : ℝ) / Real.logb 2 M - 2 ≤ Nat.primeCounting M := by
  have h2 : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have hlog : 0 < Real.logb 2 M := Real.logb_pos (by norm_num) (by linarith)
  have hplus := lg_mono (show 0 < (M : ℝ)+1 by positivity)
    (show (M : ℝ)+1 ≤ (M : ℝ)^2 by nlinarith)
  rw [Real.logb_pow, Nat.cast_ofNat] at hplus
  have hc := (div_le_iff₀ (Real.log_pos (show (1 : ℝ) < M by linarith))).mp
    (Chebyshev.pi_ge M)
  have hs : (M : ℝ) ≤ (Nat.primeCounting M : ℝ)*Real.logb 2 M +
      Real.logb 2 ((M : ℝ)+1) := by
    unfold Real.logb
    rw [← mul_div_assoc, ← add_div, le_div_iff₀ (Real.log_pos (by norm_num : (1:ℝ)<2))]
    linarith only [hc]
  have he : (M : ℝ) ≤ ((Nat.primeCounting M : ℝ) + 2)*Real.logb 2 M := by
    linarith only [hs,hplus]
  linarith only [(div_le_iff₀ hlog).mpr he]

private theorem prime_count_upper (M : ℕ) (hM : 2 ≤ M) :
    (Nat.primeCounting M : ℝ) ≤ 4*(M : ℝ) / Real.logb 2 M + Real.sqrt M := by
  have h2 : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have hlog : 0 < Real.log (M : ℝ) := Real.log_pos (by linarith)
  have hc := Chebyshev.pi_le_log4_mul_div (show (1:ℝ) < M by linarith)
  have h4 : Real.log 4 = 2*Real.log 2 := by
    rw [show (4:ℝ)=2^2 by norm_num,Real.log_pow]
    norm_num
  rw [Nat.floor_natCast,h4,Real.log_sqrt (by positivity)] at hc
  have he : 2 * Real.log 2 * (M : ℝ) / (Real.log M / 2) =
      4 * (M : ℝ) / Real.logb 2 M := by
    unfold Real.logb
    field_simp [(Real.log_pos (by norm_num : (1:ℝ)<2)).ne',hlog.ne']
    ring
  rwa [he] at hc

/-- An explicit large interval supplies the private digit primes. -/
theorem shared_prime_interval {M : ℕ} (hM : 512 ≤ M) :
    (M : ℝ)/Real.logb 2 M - 2 ≤
      (Nat.primeCounting (8*M) : ℝ) - Nat.primeCounting M := by
  let y := Real.logb 2 M
  have hMr : (512 : ℝ) ≤ M := by exact_mod_cast hM
  have hy := lg_lower (x := (M : ℝ)) (a := 9) (b := 1) (by decide)
    (by rw [pow_one,show (2:ℝ)^9=512 by norm_num]; exact hMr)
    (show (0 : ℝ) < M by linarith)
  have hy' : 9 ≤ y := by simpa [y] using hy
  have hm : 0 < (M : ℝ) := by linarith
  have ht : 16 ≤ Real.sqrt (M : ℝ) := (Real.le_sqrt (by norm_num) hm.le).mpr (by linarith)
  have hg := lg_ratio (t := Real.sqrt (M : ℝ)) (b := 4) (by decide) (by norm_num; exact ht)
  have he : (2 : ℝ)*Real.logb 2 (Real.sqrt (M : ℝ)) = y := by
    conv_rhs => rw [show y = Real.logb 2 (Real.sqrt (M : ℝ)^2) by rw [Real.sq_sqrt hm.le]]
    rw [Real.logb_pow,Nat.cast_ofNat]
  norm_num at hg
  have hs : Real.sqrt (M : ℝ) ≤ (M : ℝ)/y := by
    apply (le_div_iff₀ (by linarith : 0 < y)).mpr
    have hle : y ≤ Real.sqrt (M : ℝ) := by linarith only [he,hg,ht]
    calc
      _ ≤ Real.sqrt (M : ℝ)*Real.sqrt (M : ℝ) :=
        mul_le_mul_of_nonneg_left hle (Real.sqrt_nonneg _)
      _ = _ := by rw [← pow_two,Real.sq_sqrt hm.le]
  have hhi := prime_count_upper M (by omega)
  have hlo := prime_count_lower (8*M) (by omega)
  push_cast at hlo
  rw [Real.logb_mul (by norm_num) hm.ne',
    show Real.logb 2 8 = 3 by
      rw [show (8:ℝ)=2^3 by norm_num,lg_two_pow]; norm_num] at hlo
  change 8*(M : ℝ)/(3+y) - 2 ≤ _ at hlo
  change _ ≤ 4*(M : ℝ)/y + _ at hhi
  change (M : ℝ)/y - 2 ≤ _
  have hd : 6*((M : ℝ)/y) ≤ 8*(M : ℝ)/(3+y) := by
    apply (le_div_iff₀ (by linarith : 0 < 3+y)).mpr
    have hmul := (div_mul_cancel₀ (M : ℝ) (by linarith : y ≠ 0))
    have hc := mul_le_mul_of_nonneg_right hy' (show 0 ≤ (M : ℝ)/y by positivity)
    nlinarith only [hmul,hc]
  rw [mul_div_assoc] at hhi
  linarith only [hd,hhi,hlo,hs]

set_option maxHeartbeats 1500000 in
/-- The interval used in the compiler contains six digit primes per trit. -/
theorem shared_digit_count (k : ℕ) :
    6*k + Nat.primeCounting (200*guardedPrimeCap (2*k+136)) ≤
      Nat.primeCounting (1600*guardedPrimeCap (2*k+136)) := by
  let m := 2*k+136
  let s := Nat.log 2 m+1
  let M := 200*guardedPrimeCap m
  have hs : 8 ≤ s := by
    have h := (Nat.le_log_iff_pow_le (by decide : 1 < 2) (by dsimp [m]; omega : m ≠ 0)).mpr
      (by dsimp [m]; omega : 2^7 ≤ m)
    dsimp [s]
    omega
  have hm : m ≤ 2^s := (Nat.lt_pow_succ_log_self (by decide) m).le
  have hpow (j : ℕ) (hj : 4 ≤ j) : 4*j ≤ 2^j := by
    induction j, hj using Nat.le_induction with
    | base => decide
    | succ j hj ih =>
      rw [pow_succ]
      omega
  have hM : M = 200*m*(4*s) := by
    unfold M guardedPrimeCap s
    ring
  have hMle : M ≤ 2^(8+2*s) := by
    calc
      M = 200*m*(4*s) := hM
      _ ≤ (2^8*2^s)*2^s :=
        Nat.mul_le_mul (Nat.mul_le_mul (by decide : 200 ≤ 2^8) hm) (hpow s (by omega))
      _ = 2^(8+2*s) := by
        rw [Nat.mul_assoc, ← pow_add 2 s s, ← pow_add 2 8]
        congr 1
        omega
  have hlarge : 512 ≤ M := by
    rw [hM]
    have hm' : 136 ≤ m := by dsimp [m]; omega
    exact (by decide : 512 ≤ 200*136*(4*8)).trans
      (Nat.mul_le_mul (Nat.mul_le_mul_left 200 hm') (Nat.mul_le_mul_left 4 hs))
  have hlg := lg_mono (show (0:ℝ) < M by exact_mod_cast (show 0 < M by omega))
    (show (M:ℝ) ≤ 2^(8+2*s : ℕ) by exact_mod_cast hMle)
  rw [lg_two_pow] at hlg
  push_cast at hlg
  have hs' : (8 : ℝ) ≤ s := by exact_mod_cast hs
  have hbound : 200*(m : ℝ) ≤ (M : ℝ)/Real.logb 2 M := by
    apply (le_div_iff₀ (Real.logb_pos (by norm_num) (by exact_mod_cast (show 1 < M by omega)))).mpr
    have he : (M : ℝ) = 800*(m : ℝ)*s := by
      rw [hM]
      push_cast
      ring
    have h := mul_le_mul_of_nonneg_left (show Real.logb 2 M ≤ 4*(s : ℝ) by linarith)
      (show 0 ≤ 200*(m : ℝ) by positivity)
    linarith only [he,h]
  have h := shared_prime_interval hlarge
  have hm' : (m : ℝ) = 2*(k : ℝ)+136 := by simp [m]
  have hcost : 6*(k : ℝ) ≤ 200*(m : ℝ)-2 := by
    nlinarith only [hm',show (0:ℝ) ≤ (k:ℝ) from Nat.cast_nonneg k]
  have hc := hcost.trans (sub_le_sub_right hbound 2)
  have hr : 6*(k : ℝ) + Nat.primeCounting M ≤ Nat.primeCounting (8*M) := by
    exact le_sub_iff_add_le.mp (hc.trans h)
  have ht : 6*k + Nat.primeCounting M ≤ Nat.primeCounting (8*M) := by exact_mod_cast hr
  have he : 8*M = 1600*guardedPrimeCap (2*k+136) :=
    (Nat.mul_assoc 8 200 (guardedPrimeCap m)).symm
  rwa [he] at ht

end

end TranslationTiling.Compiler.Size
