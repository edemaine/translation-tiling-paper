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


/-- Two explicit primes just above the compulsory seed threshold. -/
def seedPrime0 : ℕ := 244453241
def seedPrime1 : ℕ := 244453243

theorem seedPrime0_prime : seedPrime0.Prime := by norm_num [seedPrime0]
theorem seedPrime1_prime : seedPrime1.Prime := by norm_num [seedPrime1]

def refinedDigitThreshold (C : ℕ) : ℕ :=
  max (C^3+2*economicalUsefulCap C) (4*seedPrime1+3)+Sudoku.p+Sudoku.q+5

def refinedDigitCap (C : ℕ) : ℕ := 4*C^3*Nat.nthRoot 2 C/3

/-- The twentieth-power certificate avoids fractional exponents in the compiler. -/
theorem refined_digit_caps {C : ℕ} (hC : 962≤C) :
    refinedDigitCap C^20≤C^71 ∧ refinedDigitCap C≤C^4 ∧
      refinedDigitThreshold C+3*C+1≤Nat.primeCounting (refinedDigitCap C) := by
  let k := Nat.nthRoot 2 C
  let Q := refinedDigitCap C
  have hk : 31≤k := (Nat.le_nthRoot_iff (by decide : 2≠0)).mpr (by norm_num; omega)
  have hklo : k^2≤C := Nat.pow_nthRoot_le (Or.inl (by decide))
  have hkhi : C<(k+1)^2 := Nat.lt_pow_nthRoot_add_one (by decide) C
  have hdiv : 3*Q≤4*C^3*k ∧ 8*C^3*k-4≤6*Q := by
    have hm := Nat.mod_lt (4*C^3*k) (by decide : 0<3)
    have he := Nat.mod_add_div (4*C^3*k) 3
    change 4*C^3*k%3+3*Q=4*C^3*k at he
    rw [show 8*C^3*k=2*(4*C^3*k) by ring]
    omega
  have hC3 : C≤C^3 := Nat.le_self_pow (by decide) C
  have hC1 : 1≤C := by omega
  have hQ2 : 2≤Q := by
    have hh : 31*C≤C^3*k := by
      calc
        _ = C*31 := by ring
        _ ≤ _ := Nat.mul_le_mul hC3 hk
    have hl : 8*C^3*k≤6*Q+4 := by omega
    nlinarith only [hh,hl,hC]
  have h9 : 9*Q^2≤16*C^7 := by
    have hh := Nat.pow_le_pow_left hdiv.1 2
    have hh' := Nat.mul_le_mul_left (16*C^6) hklo
    nlinarith only [hh,hh']
  have hpow : Q^20≤C^71 := by
    have hh := Nat.pow_le_pow_left h9 10
    have he : (9*Q^2)^10=3^20*Q^20 := by ring
    have he' : (16*C^7)^10=4^20*C^70 := by ring
    rw [he,he'] at hh
    have hn : 4^20≤3^20*C := by
      apply (by norm_num : 4^20≤3^20*962).trans
      exact Nat.mul_le_mul_left _ hC
    have hmul : 3^20*Q^20≤3^20*C^71 := by
      calc
        _ ≤ 4^20*C^70 := hh
        _ ≤ (3^20*C)*C^70 := Nat.mul_le_mul_right _ hn
        _ = _ := by ring
    exact (Nat.mul_le_mul_left_iff (by decide : 0<3^20)).mp hmul
  have hQ4 : Q≤C^4 := by
    apply (Nat.pow_le_pow_iff_left (by decide : 20≠0)).mp
    apply hpow.trans
    rw [← pow_mul]
    exact Nat.pow_le_pow_right hC1 (by decide)
  have hL : 7*(refinedDigitThreshold C+3*C+3)≤8*C^3 := by
    have hU := (economical_caps hC).2.1
    have hgap : 7*(2*C^2+3*C+120)≤C^3 := by
      have hh := Nat.mul_le_mul_right (C^2) hC
      have he : C*C^2=C^3 := by ring
      rw [he] at hh
      nlinarith
    have hseed : 8*(4*seedPrime1+3)≤9*C^3 := by
      apply (by norm_num [seedPrime1] : 8*(4*seedPrime1+3)≤9*962^3).trans
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hC 3)
    have htail : 56*(3*C+120)≤C^3 := by
      have hh := Nat.mul_le_mul_left C (Nat.pow_le_pow_left hC 2)
      have he : C*C^2=C^3 := by ring
      rw [he] at hh
      nlinarith
    unfold refinedDigitThreshold
    rcases le_total (C^3+2*economicalUsefulCap C) (4*seedPrime1+3) with hh | hh
    · rw [max_eq_right hh]
      norm_num only [Sudoku.p,Sudoku.q]
      nlinarith only [hseed,htail]
    · rw [max_eq_left hh]
      norm_num only [Sudoku.p,Sudoku.q]
      nlinarith only [hgap,hU]
  have hlog : Real.log (Q:ℝ)≤((7*(k:ℝ)-4)/6)*Real.log 2 := by
    have hn : 3*Q≤4*(k+1)^7 := by
      apply hdiv.1.trans
      have hc := Nat.pow_le_pow_left hkhi.le 3
      have he : ((k+1)^2)^3=(k+1)^6 := by ring
      rw [he] at hc
      calc
        _ ≤ 4*(k+1)^6*(k+1) := Nat.mul_le_mul (Nat.mul_le_mul_left _ hc) (Nat.le_succ k)
        _ = _ := by ring
    have hr : (Q:ℝ)≤(4/3:ℝ)*((k:ℝ)+1)^7 := by
      have hh : (3:ℝ)*Q≤4*((k:ℝ)+1)^7 := by exact_mod_cast hn
      linarith
    have hh := Real.log_le_log (by exact_mod_cast (by omega : 0<Q)) hr
    rw [Real.log_mul (by norm_num) (by positivity),Real.log_pow] at hh
    have h43 : Real.log (4/3:ℝ)≤(1/2:ℝ)*Real.log 2 := by
      have he := Real.log_le_log (by norm_num : (0:ℝ)<(4/3:ℝ)^2) (by norm_num : (4/3:ℝ)^2≤2)
      rw [Real.log_pow] at he
      norm_num at he
      linarith
    have hklog := economical_log_root hk
    norm_num only [Nat.cast_ofNat] at hh
    linarith
  have hpi : 8*C^3<7*(Nat.primeCounting Q+2) := by
    have hpos : 0<Real.log (Q:ℝ) := Real.log_pos (by exact_mod_cast hQ2 : (1:ℝ)<Q)
    have hp := (div_le_iff₀ hpos).mp (Chebyshev.pi_ge Q)
    have htail : Real.log ((Q:ℝ)+1)≤2*Real.log (Q:ℝ) := by
      have hqr : (2:ℝ)≤Q := by exact_mod_cast hQ2
      have hh := Real.log_le_log (by positivity : (0:ℝ)<(Q:ℝ)+1)
        (show (Q:ℝ)+1≤(Q:ℝ)^2 by nlinarith)
      simpa only [Real.log_pow,Nat.cast_ofNat] using hh
    have hp' : (Q:ℝ)*Real.log 2≤((Nat.primeCounting Q:ℝ)+2)*Real.log (Q:ℝ) := by
      push_cast at hp
      linarith
    have hm := mul_le_mul_of_nonneg_left hlog (show (0:ℝ)≤(Nat.primeCounting Q:ℝ)+2 by positivity)
    have htwo : 0<Real.log (2:ℝ) := Real.log_pos (by norm_num)
    have hb : 6*(Q:ℝ)≤((Nat.primeCounting Q:ℝ)+2)*(7*(k:ℝ)-4) := by nlinarith only [hp',hm,htwo]
    by_contra hh
    have hn : 7*(Nat.primeCounting Q+2)≤8*C^3 := by omega
    have hnr : 7*((Nat.primeCounting Q:ℝ)+2)≤8*(C:ℝ)^3 := by exact_mod_cast hn
    have hkr : (31:ℝ)≤k := by exact_mod_cast hk
    have hm' := mul_le_mul_of_nonneg_right hnr (show (0:ℝ)≤7*(k:ℝ)-4 by linarith)
    have hlo : 8*(C:ℝ)^3*k-4≤6*(Q:ℝ) := by
      have he := Nat.mod_add_div (4*C^3*k) 3
      have hh := Nat.mod_lt (4*C^3*k) (by decide : 0<3)
      have hn' : 8*C^3*k≤6*Q+4 := by change _+3*Q=_ at he; omega
      have hr : (8:ℝ)*(C:ℝ)^3*k≤6*(Q:ℝ)+4 := by exact_mod_cast hn'
      linarith
    have hc : (1:ℝ)≤(C:ℝ)^3 := by exact_mod_cast (hC1.trans hC3)
    nlinarith only [hb,hm',hlo,hc]
  exact ⟨hpow,hQ4,by change _≤Nat.primeCounting Q; omega⟩

end
end TranslationTiling.Compiler.Size
