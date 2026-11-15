import TranslationTiling.Compiler.SharpPrimeCounting
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas

namespace TranslationTiling.Compiler.Size
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

/-- Integer caps keep the certificate verifier purely arithmetic. -/
def tightUsefulCap (C : ℕ) : ℕ := Nat.nthRoot 3 (C^4)
def tightDigitThreshold (C : ℕ) : ℕ :=
  tightUsefulCap C ^ 2 + 2*tightUsefulCap C + Sudoku.p + Sudoku.q + 3

private theorem log_root_bound {k : ℕ} (hk : 84≤k) :
    Real.log ((k:ℝ)+1) ≤ ((k:ℝ)-2)/18 := by
  have h85 : Real.log (85:ℝ) ≤ 91/20 := by
    have h := Real.log_le_log (by norm_num : (0:ℝ)<85^2)
      (by norm_num : (85:ℝ)^2 ≤ 2^13)
    rw [Real.log_pow,Real.log_pow] at h
    have h2 := Real.log_two_lt_d9
    norm_num at h
    linarith
  have hp : (0:ℝ)<((k:ℝ)+1)/85 := by positivity
  have h := Real.log_le_sub_one_of_pos hp
  have he : (k:ℝ)+1 = 85*(((k:ℝ)+1)/85) := by ring
  have hh : Real.log ((k:ℝ)+1) ≤ 91/20+(((k:ℝ)+1)/85-1) := by
    calc
      _ = Real.log 85 + Real.log (((k:ℝ)+1)/85) := by
        conv_lhs => rw [he]
        rw [Real.log_mul (by norm_num) (ne_of_gt hp)]
      _ ≤ _ := add_le_add h85 h
  have hkr : (84:ℝ)≤k := by exact_mod_cast hk
  linarith

private theorem primeCounting_log_bound {n : ℕ} (hn : 2≤n) :
    (n:ℝ) ≤ ((Nat.primeCounting n:ℝ)+2)*(2*Real.log (n:ℝ)) := by
  have hnR : (2:ℝ)≤n := by exact_mod_cast hn
  have hlog : 0<Real.log (n:ℝ) := Real.log_pos (by linarith)
  have hp := (div_le_iff₀ hlog).mp (Chebyshev.pi_ge n)
  have htwo : (1/2:ℝ)≤Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at h ⊢
    exact h
  have htail : Real.log ((n:ℝ)+1) ≤ 2*Real.log (n:ℝ) := by
    have h := Real.log_le_log (by linarith : (0:ℝ)<(n:ℝ)+1)
      (show (n:ℝ)+1≤(n:ℝ)^2 by nlinarith)
    simpa only [Real.log_pow,Nat.cast_ofNat] using h
  push_cast at hp
  nlinarith only [hp,htail,mul_le_mul_of_nonneg_left htwo (show (0:ℝ)≤n by positivity)]

theorem tight_caps (C : ℕ) (hC : 596750≤C) :
    let U := tightUsefulCap C
    U^3≤C^4 ∧ 84*C≤U ∧ U≤C^2 ∧
      2*C+7≤Nat.primeCounting U ∧
      tightDigitThreshold C+3*C+1≤Nat.primeCounting (C^3) := by
  let k := Nat.nthRoot 3 C
  let U := tightUsefulCap C
  have hk : 84≤k := (Nat.le_nthRoot_iff (by decide : 3≠0)).mpr (by norm_num; omega)
  have hklo : k^3≤C := Nat.pow_nthRoot_le (Or.inl (by decide))
  have hkhi : C<(k+1)^3 := Nat.lt_pow_nthRoot_add_one (by decide) C
  have hU3 : U^3≤C^4 := Nat.pow_nthRoot_le (Or.inl (by decide))
  have hUlo : C*k≤U := (Nat.le_nthRoot_iff (by decide : 3≠0)).mpr (by
    calc
      _ = C^3*k^3 := by ring
      _ ≤ C^3*C := Nat.mul_le_mul_left _ hklo
      _ = _ := by ring)
  have hUhi : U≤C*(k+1) := by
    apply (Nat.pow_le_pow_iff_left (by decide : 3≠0)).mp
    calc
      _ ≤ C^4 := hU3
      _ = C^3*C := by ring
      _ ≤ C^3*(k+1)^3 := Nat.mul_le_mul_left _ hkhi.le
      _ = _ := by ring
  have hUC : C≤U := (by nlinarith : C≤C*k).trans hUlo
  have hUsq : U≤C^2 := by
    apply (Nat.pow_le_pow_iff_left (by decide : 3≠0)).mp
    apply hU3.trans
    rw [← pow_mul]
    exact Nat.pow_le_pow_right (by omega) (by decide)
  have hkr : (84:ℝ)≤k := by exact_mod_cast hk
  have hCr : (596750:ℝ)≤C := by exact_mod_cast hC
  have hlo : (k:ℝ)^3≤C := by exact_mod_cast hklo
  have hhi : (C:ℝ)≤((k:ℝ)+1)^3 := by exact_mod_cast hkhi.le
  have hlogk := log_root_bound hk
  have hlogC : 6*Real.log (C:ℝ) ≤ (k:ℝ)-2 := by
    have h := Real.log_le_log (by positivity : (0:ℝ)<C) hhi
    rw [Real.log_pow] at h
    norm_num at h
    linarith
  have hlogU : 9*Real.log (U:ℝ) ≤ 2*((k:ℝ)-2) := by
    have hh : (U:ℝ)≤(C:ℝ)*((k:ℝ)+1) := by exact_mod_cast hUhi
    have h := Real.log_le_log (by exact_mod_cast (by omega : 0<U)) hh
    rw [Real.log_mul (by positivity) (by positivity)] at h
    linarith
  have hpu : 2*C+7≤Nat.primeCounting U := by
    have hp := primeCounting_log_bound (show 2≤U by omega)
    have hmul := mul_le_mul_of_nonneg_left hlogU
      (show (0:ℝ)≤2*((Nat.primeCounting U:ℝ)+2) by positivity)
    have hu : (C:ℝ)*k≤U := by exact_mod_cast hUlo
    by_contra hn
    have hnR : (Nat.primeCounting U:ℝ)≤2*(C:ℝ)+6 := by exact_mod_cast (by omega : Nat.primeCounting U≤2*C+6)
    have hb := mul_le_mul_of_nonneg_right hnR (show (0:ℝ)≤4*((k:ℝ)-2) by linarith)
    have hCK : (40:ℝ)*k≤(C:ℝ)*k := mul_le_mul_of_nonneg_right (by linarith : (40:ℝ)≤C) (by positivity)
    nlinarith only [hp,hmul,hu,hb,hCK,hCr]
  have hpq : tightDigitThreshold C+3*C+1≤Nat.primeCounting (C^3) := by
    let A := tightDigitThreshold C+3*C+3
    have hA : (A:ℝ) ≤ (C:ℝ)^2*((k:ℝ)+1)^2+6*(C:ℝ)*((k:ℝ)+1) := by
      have hu : (U:ℝ)≤(C:ℝ)*((k:ℝ)+1) := by exact_mod_cast hUhi
      have hu2 := pow_le_pow_left₀ (by positivity : (0:ℝ)≤U) hu 2
      change (((U^2+2*U+Sudoku.p+Sudoku.q+3+3*C+3:ℕ):ℝ))≤_
      push_cast
      norm_num only [Sudoku.p,Sudoku.q]
      nlinarith only [hu2,hu,hCr,hkr,mul_nonneg (show (0:ℝ)≤C by positivity) (show (0:ℝ)≤k by positivity)]
    have htwo : 2*((k:ℝ)+1)≤C := by nlinarith only [hlo,hkr,sq_nonneg ((k:ℝ)-2),mul_nonneg (show (0:ℝ)≤(k:ℝ)-84 by linarith) (show (0:ℝ)≤(k:ℝ)^2 by positivity)]
    have hpoly : ((C:ℝ)^2*((k:ℝ)+1)^2+6*(C:ℝ)*((k:ℝ)+1))*((k:ℝ)-2) ≤ (C:ℝ)^3 := by
      have h1 := mul_le_mul_of_nonneg_left hlo (show (0:ℝ)≤(C:ℝ)^2 by positivity)
      have h2 := mul_le_mul_of_nonneg_left htwo (show (0:ℝ)≤(C:ℝ)*(3*(k:ℝ)+2) by positivity)
      nlinarith only [h1,h2,mul_nonneg (show (0:ℝ)≤C by positivity) (show (0:ℝ)≤16*(k:ℝ)+16 by positivity)]
    have hAc := (mul_le_mul_of_nonneg_right hA (show (0:ℝ)≤(k:ℝ)-2 by linarith)).trans hpoly
    have hp := primeCounting_log_bound (show 2≤C^3 by nlinarith)
    have hm := mul_le_mul_of_nonneg_left hlogC (show (0:ℝ)≤(Nat.primeCounting (C^3):ℝ)+2 by positivity)
    rw [Nat.cast_pow,Real.log_pow] at hp
    norm_num at hp
    have hr : (A:ℝ)≤(Nat.primeCounting (C^3):ℝ)+2 := by nlinarith only [hAc,hp,hm,hkr]
    have hh : A≤Nat.primeCounting (C^3)+2 := by exact_mod_cast hr
    dsimp [A] at hh
    omega
  exact ⟨hU3,by nlinarith,hUsq,hpu,hpq⟩

end
end TranslationTiling.Compiler.Size
