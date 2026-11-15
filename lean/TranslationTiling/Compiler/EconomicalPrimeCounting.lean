import TranslationTiling.Compiler.TightPrimeCounting

namespace TranslationTiling.Compiler.Size
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def economicalUsefulCap (C : ℕ) : ℕ := C * Nat.nthRoot 2 C

def economicalDigitThreshold (C : ℕ) : ℕ :=
  max (C^3+2*economicalUsefulCap C) (16*Sudoku.SeedModulus^2+3) +
    Sudoku.p+Sudoku.q+5

private theorem log_two_lower : (1/2:ℝ) ≤ Real.log 2 := by
  have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
  norm_num at h ⊢
  exact h

private theorem economical_log_root {k : ℕ} (hk : 31≤k) :
    Real.log ((k:ℝ)+1) ≤ ((k:ℝ)-1)/6 * Real.log 2 := by
  have hkr : (31:ℝ)≤k := by exact_mod_cast hk
  have hp : (0:ℝ)<((k:ℝ)+1)/32 := by positivity
  have hh := Real.log_le_sub_one_of_pos hp
  have he : (k:ℝ)+1 = 32*(((k:ℝ)+1)/32) := by ring
  have hlog32 : Real.log (32:ℝ) = 5*Real.log 2 := by
    rw [show (32:ℝ)=2^5 by norm_num,Real.log_pow]; norm_num
  have hh' : Real.log ((k:ℝ)+1) ≤ 5*Real.log 2+(((k:ℝ)+1)/32-1) := by
    calc
      _ = Real.log 32 + Real.log (((k:ℝ)+1)/32) := by
        conv_lhs => rw [he]
        rw [Real.log_mul (by norm_num) (ne_of_gt hp)]
      _ ≤ _ := by rw [hlog32]; linarith
  nlinarith only [hh',hkr,mul_nonneg (show (0:ℝ)≤(k:ℝ)-31 by linarith)
    (show (0:ℝ)≤Real.log 2-1/2 by linarith [log_two_lower])]

theorem primeCounting_quartic_economical {C : ℕ} (hC : 962≤C) :
    6*C^3 ≤ Nat.primeCounting (C^4) := by
  have hc : (962:ℝ)≤C := by exact_mod_cast hC
  have hlog := log_le_div_sixtyfour (by omega : 768≤C)
  have htail : Real.log ((C^4+1:ℕ):ℝ) ≤ 1+4*Real.log (C:ℝ) := by
    have hp : (1:ℝ)≤(C:ℝ)^4 := one_le_pow₀ (by linarith)
    have hh : ((C^4+1:ℕ):ℝ)≤2*(C:ℝ)^4 := by push_cast; linarith
    have hl := Real.log_le_log (by positivity : (0:ℝ)<((C^4+1:ℕ):ℝ)) hh
    rw [Real.log_mul (by norm_num) (by positivity),Real.log_pow] at hl
    have h2 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at *
    linarith
  have hpos : 0<Real.log ((C^4:ℕ):ℝ) := Real.log_pos (by push_cast; nlinarith [one_le_pow₀ (by linarith : (1:ℝ)≤C) (n:=3)])
  have hp := (div_le_iff₀ hpos).mp (Chebyshev.pi_ge (C^4))
  have hm := mul_le_mul_of_nonneg_left hlog (show (0:ℝ)≤(C:ℝ)^3 by positivity)
  have ht := mul_le_mul_of_nonneg_left log_two_lower (show (0:ℝ)≤(C:ℝ)^4 by positivity)
  have hc4 : (C:ℝ)^2≤(C:ℝ)^4 := pow_le_pow_right₀ (by linarith) (by decide)
  have hden : ((6*C^3:ℕ):ℝ)*Real.log ((C^4:ℕ):ℝ) ≤
      ((C^4:ℕ):ℝ)*Real.log 2-Real.log ((C^4+1:ℕ):ℝ) := by
    push_cast at *
    rw [Real.log_pow]
    norm_num only [Nat.cast_ofNat] at *
    nlinarith only [hc,hlog,htail,hm,ht,hc4]
  norm_num only [Nat.cast_add,Nat.cast_one] at hden
  exact_mod_cast (mul_le_mul_iff_left₀ hpos).mp (hden.trans hp)

theorem economical_caps {C : ℕ} (hC : 962≤C) :
    let U := economicalUsefulCap C
    U^2≤C^3 ∧ U≤C^2 ∧ 2*C+7≤Nat.primeCounting U ∧
      economicalDigitThreshold C+3*C+1≤Nat.primeCounting (C^4) := by
  let k := Nat.nthRoot 2 C
  let U := economicalUsefulCap C
  have hk : 31≤k := (Nat.le_nthRoot_iff (by decide : 2≠0)).mpr (by norm_num; omega)
  have hklo : k^2≤C := Nat.pow_nthRoot_le (Or.inl (by decide))
  have hkhi : C<(k+1)^2 := Nat.lt_pow_nthRoot_add_one (by decide) C
  have hUeq : U=C*k := rfl
  have hUsq : U^2≤C^3 := by rw [hUeq,mul_pow]; nlinarith [Nat.mul_le_mul_left (C^2) hklo]
  have hUhi : U≤C^2 := by
    rw [hUeq,pow_two]
    exact Nat.mul_le_mul_left _ (by nlinarith : k≤C)
  have hkr : (31:ℝ)≤k := by exact_mod_cast hk
  have hcr : (962:ℝ)≤C := by exact_mod_cast hC
  have hlogU : Real.log (U:ℝ) ≤ ((k:ℝ)-1)/2*Real.log 2 := by
    have hu : (U:ℝ)≤((k:ℝ)+1)^3 := by
      have hh : U≤(k+1)^3 := by rw [hUeq]; nlinarith
      exact_mod_cast hh
    have hl := Real.log_le_log (by exact_mod_cast (by rw [hUeq]; positivity : 0<U)) hu
    rw [Real.log_pow] at hl
    norm_num at hl
    linarith [economical_log_root hk]
  have hpu : 2*C+7≤Nat.primeCounting U := by
    have hu : (2:ℝ)≤U := by exact_mod_cast (by rw [hUeq]; nlinarith : 2≤U)
    have hpos : 0<Real.log (U:ℝ) := Real.log_pos (by linarith)
    have hp := (div_le_iff₀ hpos).mp (Chebyshev.pi_ge U)
    have htail : Real.log ((U:ℝ)+1)≤2*Real.log (U:ℝ) := by
      have hh := Real.log_le_log (by positivity : (0:ℝ)<(U:ℝ)+1)
        (show (U:ℝ)+1≤(U:ℝ)^2 by nlinarith)
      simpa only [Real.log_pow,Nat.cast_ofNat] using hh
    push_cast at hp
    have hpi : (U:ℝ)*Real.log 2≤((Nat.primeCounting U:ℝ)+2)*Real.log (U:ℝ) := by linarith
    have hm := mul_le_mul_of_nonneg_left hlogU (show (0:ℝ)≤(Nat.primeCounting U:ℝ)+2 by positivity)
    have htwo : 0<Real.log (2:ℝ) := Real.log_pos (by norm_num)
    have hbound : 2*(U:ℝ)≤((Nat.primeCounting U:ℝ)+2)*((k:ℝ)-1) := by nlinarith only [hpi,hm,htwo]
    by_contra hn
    have hnR : (Nat.primeCounting U:ℝ)≤2*(C:ℝ)+6 := by exact_mod_cast (by omega : Nat.primeCounting U≤2*C+6)
    have hb := mul_le_mul_of_nonneg_right hnR (show (0:ℝ)≤(k:ℝ)-1 by linarith)
    have he : (U:ℝ)=(C:ℝ)*k := by exact_mod_cast hUeq
    have hlo : (k:ℝ)^2≤C := by exact_mod_cast hklo
    nlinarith only [hbound,hb,he,hlo,hkr,sq_nonneg ((k:ℝ)-4)]
  have hL : economicalDigitThreshold C+3*C+1≤6*C^3 := by
    have hseed : 16*Sudoku.SeedModulus^2+3+Sudoku.p+Sudoku.q+6≤5*962^3 := by
      norm_num [Sudoku.SeedModulus,Sudoku.p,Sudoku.q]
    have hc3 : 962^3≤C^3 := Nat.pow_le_pow_left hC 3
    have hc4 : 4*C≤C^3 := by nlinarith [Nat.mul_le_mul_left C (show 4≤C^2 by nlinarith)]
    have hc2 : C^2≤C^3 := Nat.pow_le_pow_right (by omega) (by decide)
    unfold economicalDigitThreshold
    rcases le_total (C^3+2*U) (16*Sudoku.SeedModulus^2+3) with hh | hh
    · rw [max_eq_right hh]
      norm_num only [Sudoku.p,Sudoku.q]
      norm_num only [Sudoku.p,Sudoku.q] at hseed
      nlinarith
    · rw [max_eq_left hh]
      norm_num only [Sudoku.p,Sudoku.q]
      nlinarith
  exact ⟨hUsq,hUhi,hpu,hL.trans (primeCounting_quartic_economical hC)⟩

end
end TranslationTiling.Compiler.Size
