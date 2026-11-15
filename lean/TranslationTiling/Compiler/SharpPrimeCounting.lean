import TranslationTiling.Compiler.PolynomialPrimes

namespace TranslationTiling.Compiler.Size
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

/-- A very weak logarithm estimate suffices at the compiler's actual sizes. -/
theorem log_le_div_sixtyfour {C : ℕ} (hC : 768 ≤ C) : Real.log (C:ℝ) ≤ C / 64 := by
  have hc : (768:ℝ) ≤ C := by exact_mod_cast hC
  have hp : (0:ℝ) < C / 256 := by positivity
  have he : (C:ℝ) = 256 * (C/256) := by ring
  have hlog256 : Real.log (256:ℝ) ≤ 8 := by
    have h2 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    have he : (256:ℝ) = 2^8 := by norm_num
    rw [he,Real.log_pow]
    norm_num at *
    linarith
  have h := Real.log_le_sub_one_of_pos hp
  calc
    Real.log (C:ℝ) = Real.log 256 + Real.log (C/256) := by
      conv_lhs => rw [he]
      rw [Real.log_mul (by norm_num) (ne_of_gt hp)]
    _ ≤ 8 + (C/256-1) := add_le_add hlog256 h
    _ ≤ _ := by linarith

private theorem log_pow_add_one_le {C k : ℕ} (hC : 1024 ≤ C) (hk : 0 < k) :
    Real.log ((C^k+1:ℕ):ℝ) ≤ 1 + k * Real.log (C:ℝ) := by
  have hc : (1:ℝ) ≤ C := by exact_mod_cast (by omega : 1 ≤ C)
  have hp : (1:ℝ) ≤ (C:ℝ)^k := one_le_pow₀ hc
  have h : (((C^k+1:ℕ):ℝ)) ≤ 2*(C:ℝ)^k := by push_cast; linarith
  have hl := Real.log_le_log (by positivity : (0:ℝ)<((C^k+1:ℕ):ℝ)) h
  rw [Real.log_mul (by norm_num) (by positivity),Real.log_pow] at hl
  have h2 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
  linarith

theorem primeCounting_square_medium {C : ℕ} (hC : 1024 ≤ C) :
    8*C ≤ Nat.primeCounting (C^2) := by
  have hc : (1024:ℝ) ≤ C := by exact_mod_cast (by omega : 1024 ≤ C)
  have hlog := log_le_div_sixtyfour (by omega : 768 ≤ C)
  have htail := log_pow_add_one_le (C:=C) (k:=2) (by omega) (by decide)
  have htwo : (1/2:ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at h ⊢
    exact h
  have hpos : 0 < Real.log (((C^2:ℕ):ℝ)) := Real.log_pos (by push_cast; nlinarith)
  have hp := (div_le_iff₀ hpos).mp (Chebyshev.pi_ge (C^2))
  have hden : (8*C:ℝ) * Real.log (((C^2:ℕ):ℝ)) ≤
      (((C^2:ℕ):ℝ))*Real.log 2 - Real.log (((C^2+1:ℕ):ℝ)) := by
    rw [Nat.cast_pow,Real.log_pow]
    norm_num only [Nat.cast_pow,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat] at *
    have hcr : (1024:ℝ) ≤ C := by exact_mod_cast (by omega : 1024 ≤ C)
    nlinarith only [hcr,htail,hlog,mul_le_mul_of_nonneg_left hlog (by positivity : (0:ℝ) ≤ C),
      mul_le_mul_of_nonneg_left htwo (by positivity : (0:ℝ) ≤ (C:ℝ)^2)]
  have hp' := hp
  norm_num only [Nat.cast_add,Nat.cast_one] at hden
  have hresult := (mul_le_mul_iff_left₀ hpos).mp (hden.trans hp')
  exact_mod_cast hresult

theorem primeCounting_fifth_medium {C : ℕ} (hC : 1024 ≤ C) :
    3*C^4 ≤ Nat.primeCounting (C^5) := by
  have hc : (1024:ℝ) ≤ C := by exact_mod_cast (by omega : 1024 ≤ C)
  have hlog := log_le_div_sixtyfour (by omega : 768 ≤ C)
  have htail := log_pow_add_one_le (C:=C) (k:=5) (by omega) (by decide)
  have htwo : (1/2:ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at h ⊢
    exact h
  have hpos : 0 < Real.log (((C^5:ℕ):ℝ)) := Real.log_pos (by push_cast; nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℝ)≤2) (by linarith : (2:ℝ)≤C) 5])
  have hp := (div_le_iff₀ hpos).mp (Chebyshev.pi_ge (C^5))
  have hden : ((3*C^4:ℕ):ℝ) * Real.log (((C^5:ℕ):ℝ)) ≤
      (((C^5:ℕ):ℝ))*Real.log 2 - Real.log (((C^5+1:ℕ):ℝ)) := by
    push_cast
    rw [Real.log_pow]
    have hc4 : (1:ℝ) ≤ (C:ℝ)^4 := one_le_pow₀ (by linarith)
    have hc5 : (C:ℝ)^2 ≤ (C:ℝ)^5 := pow_le_pow_right₀ (by linarith) (by decide)
    have hm := mul_le_mul_of_nonneg_left hlog (show (0:ℝ) ≤ (C:ℝ)^4 by positivity)
    have ht := mul_le_mul_of_nonneg_left htwo (show (0:ℝ) ≤ (C:ℝ)^5 by positivity)
    push_cast at htail
    norm_num only [Nat.cast_ofNat] at *
    nlinarith only [hc,hlog,htail,hc5,hm,ht]
  have hp' := hp
  norm_num only [Nat.cast_add,Nat.cast_one] at hden
  have hresult := (mul_le_mul_iff_left₀ hpos).mp (hden.trans hp')
  exact_mod_cast hresult

theorem primeCounting_square_large {C : ℕ} (hC : 596750≤C) :
    8*C≤Nat.primeCounting (C^2) := primeCounting_square_medium (by omega)

theorem primeCounting_fifth_large {C : ℕ} (hC : 596750≤C) :
    3*C^4≤Nat.primeCounting (C^5) := primeCounting_fifth_medium (by omega)

end
end TranslationTiling.Compiler.Size
