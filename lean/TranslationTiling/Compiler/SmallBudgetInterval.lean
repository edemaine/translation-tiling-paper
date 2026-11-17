import TranslationTiling.Compiler.IntervalPrimeCounting

namespace TranslationTiling.Compiler.Size
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

theorem small_budget_log_bound {C : ℕ} (hC : 256≤C) :
    Real.log (C:ℝ)≤(C:ℝ)/40 := by
  have hc : (256:ℝ)≤C := by exact_mod_cast hC
  have ht := Real.log_le_sub_one_of_pos (by positivity : (0:ℝ)<(C:ℝ)/256)
  have he : (C:ℝ)=256*((C:ℝ)/256) := by ring
  have hh : Real.log (C:ℝ)≤8*Real.log 2+((C:ℝ)/256-1) := by
    calc
      _ = Real.log 256+Real.log ((C:ℝ)/256) := by
        conv_lhs => rw [he]
        rw [Real.log_mul (by norm_num) (by positivity)]
      _ ≤ _ := by
        rw [show (256:ℝ)=2^8 by norm_num,Real.log_pow]
        norm_num at *
        linarith
  have htwo := Real.log_two_lt_d9
  linarith

theorem small_ordinary_threshold_bound {C : ℕ} (hC : 256≤C) :
    40*ordinaryDigitThreshold C≤19*C^3 := by
  have hu : 2*economicalUsefulCap C≤C^2 := by
    unfold economicalUsefulCap
    have hr := Nat.pow_nthRoot_le (n:=2) (a:=C) (Or.inl (by decide))
    have hc : 256≤C := hC
    have hh : 2*Nat.nthRoot 2 C≤C := by nlinarith
    nlinarith
  have hd : 32*(15*C^3/32)≤15*C^3 := Nat.mul_div_le _ _
  have hpoly : 160*(C^2+117)≤C^3 := by
    have hm := Nat.mul_le_mul_right (C^2) hC
    nlinarith
  unfold ordinaryDigitThreshold
  omega

/-- There are enough primes above the value threshold, rather than its index. -/
theorem small_ordinary_interval_count {C : ℕ} (hC : 256≤C) :
    Nat.primeCounting (ordinaryDigitThreshold C)+3*C+1≤Nat.primeCounting (C^3) := by
  let L := ordinaryDigitThreshold C
  let Q := C^3
  have hc : (256:ℝ)≤C := by exact_mod_cast hC
  have hpos : (0:ℝ)<C := by linarith
  have hQ : (Q:ℝ)=(C:ℝ)^3 := by simp [Q]
  have hL : 40*(L:ℝ)≤19*(C:ℝ)^3 := by exact_mod_cast small_ordinary_threshold_bound hC
  have hLQ : L≤Q := by exact_mod_cast (by nlinarith : (L:ℝ)≤(Q:ℝ))
  have hlog := small_budget_log_bound hC
  have h2 : (1/2:ℝ)≤Real.log 2 := by
    have ht := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at ht ⊢
    exact ht
  have hsqrt : Real.sqrt (Q:ℝ)≤(C:ℝ)^2/16 := by
    apply (Real.sqrt_le_iff).mpr
    constructor
    · positivity
    · rw [hQ]
      have hh := mul_nonneg (show (0:ℝ)≤(C:ℝ)-256 by linarith) (show (0:ℝ)≤(C:ℝ)^3 by positivity)
      nlinarith only [hh]
  have hlogQ : Real.log (Q:ℝ)=3*Real.log (C:ℝ) := by rw [hQ,Real.log_pow]; norm_num
  have htail : Real.log ((Q:ℝ)+1)≤1+3*Real.log (C:ℝ) := by
    have ht := Real.log_le_log (by positivity : (0:ℝ)<(Q:ℝ)+1)
      (show (Q:ℝ)+1≤2*(Q:ℝ) by rw [hQ]; nlinarith [one_le_pow₀ (by linarith : (1:ℝ)≤C) (n:=3)])
    rw [Real.log_mul (by norm_num) (by positivity),hlogQ] at ht
    have htwo := Real.log_two_lt_d9
    linarith
  have hlo := Chebyshev.theta_ge Q
  have hhi := Chebyshev.theta_le_log4_mul_x (show (0:ℝ)≤L by positivity)
  have hdiff : Chebyshev.theta (Q:ℝ)-Chebyshev.theta (L:ℝ)≤
      ((Nat.primeCounting Q-Nat.primeCounting L:ℕ):ℝ)*Real.log (Q:ℝ) := by
    rw [Chebyshev.theta_eq_sum_primesLE_log,Chebyshev.theta_eq_sum_primesLE_log]
    have hsub : Nat.primesLE L⊆Nat.primesLE Q := by intro p hp; exact Nat.mem_primesLE.mpr ⟨(Nat.mem_primesLE.mp hp).1.trans hLQ,(Nat.mem_primesLE.mp hp).2⟩
    rw [← Finset.sum_sdiff hsub,add_sub_cancel_right]
    calc
      _ ≤ ∑ _p ∈ Nat.primesLE Q \ Nat.primesLE L, Real.log (Q:ℝ) := Finset.sum_le_sum (fun p hp =>
        Real.log_le_log (by exact_mod_cast (Nat.mem_primesLE.mp (Finset.mem_sdiff.mp hp).1).2.pos)
          (by exact_mod_cast (Nat.mem_primesLE.mp (Finset.mem_sdiff.mp hp).1).1))
      _ = _ := by simp [Finset.card_sdiff_of_subset hsub,Nat.primesLE_card_eq_primeCounting]
  have hlog4 : Real.log (4:ℝ)=2*Real.log 2 := by rw [show (4:ℝ)=2^2 by norm_num,Real.log_pow]; norm_num
  have hmain : (C:ℝ)^3/80≤Chebyshev.theta (Q:ℝ)-Chebyshev.theta (L:ℝ) := by
    have hmL := mul_le_mul_of_nonneg_right hL (show (0:ℝ)≤Real.log 2 by positivity)
    have hm2 := mul_le_mul_of_nonneg_left h2 (show (0:ℝ)≤(C:ℝ)^3 by positivity)
    have hml := mul_le_mul_of_nonneg_left hlog (show (0:ℝ)≤(C:ℝ)^2/16 by positivity)
    have hms := mul_le_mul_of_nonneg_right hsqrt (show (0:ℝ)≤Real.log (Q:ℝ) by rw [hlogQ]; positivity)
    have hp : 320+24*(C:ℝ)≤(C:ℝ)^3 := by
      have hm := mul_le_mul_of_nonneg_right hc (show (0:ℝ)≤(C:ℝ)^2 by positivity)
      nlinarith [sq_nonneg ((C:ℝ)-16)]
    push_cast at hlo
    rw [hlogQ] at hlo
    have hQmul : (Q:ℝ)*Real.log 2=(C:ℝ)^3*Real.log 2 := by rw [hQ]
    rw [hlogQ] at hms
    rw [hlog4] at hhi
    nlinarith only [hlo,hhi,hQmul,htail,hmL,hm2,hml,hms,hlog,hp,hc]
  have hmon := Nat.monotone_primeCounting hLQ
  by_contra hn
  change ¬ Nat.primeCounting L+3*C+1≤Nat.primeCounting Q at hn
  have hn' : (Nat.primeCounting Q-Nat.primeCounting L:ℕ)≤3*C := by omega
  have hh := mul_le_mul_of_nonneg_right (show ((Nat.primeCounting Q-Nat.primeCounting L:ℕ):ℝ)≤3*(C:ℝ) by exact_mod_cast hn')
    (show (0:ℝ)≤Real.log (Q:ℝ) by rw [hlogQ]; positivity)
  have hm := mul_le_mul_of_nonneg_left hlog (show (0:ℝ)≤9*(C:ℝ) by positivity)
  have hp := mul_nonneg (show (0:ℝ)≤(C:ℝ)-256 by linarith) (show (0:ℝ)≤(C:ℝ)^2 by positivity)
  rw [hlogQ] at hdiff hh
  nlinarith only [hmain,hdiff,hh,hm,hp,hc]

end
end TranslationTiling.Compiler.Size
