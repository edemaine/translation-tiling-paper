import TranslationTiling.Compiler.EconomicalPrimeCounting

namespace TranslationTiling.Compiler.Size
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def asymmetricUsefulCap (C : ℕ) : ℕ := 15*economicalUsefulCap C/32
def ordinaryDigitThreshold (C : ℕ) : ℕ := 15*C^3/32+2*economicalUsefulCap C+117

/-- A smaller pool suffices for one useful prime in each ordinary pair. -/
theorem asymmetric_useful_count {C : ℕ} (hC : 962≤C) :
    C+7≤Nat.primeCounting (asymmetricUsefulCap C) := by
  let h := Nat.nthRoot 2 C
  let S := asymmetricUsefulCap C
  have hh : 31≤h := (Nat.le_nthRoot_iff (by decide : 2≠0)).mpr (by norm_num; omega)
  have hlo : h^2≤C := Nat.pow_nthRoot_le (Or.inl (by decide))
  have hhi : C<(h+1)^2 := Nat.lt_pow_nthRoot_add_one (by decide) C
  have hS : 32*S≤15*C*h ∧ 15*C*h<32*S+32 := by
    have hd := Nat.mod_add_div (15*(C*h)) 32
    have hm := Nat.mod_lt (15*(C*h)) (by decide : 0<32)
    change 15*(C*h)%32+32*S=15*(C*h) at hd
    simp only [← Nat.mul_assoc] at hd hm
    omega
  have hS2 : 2≤S := by nlinarith [Nat.mul_le_mul hC hh]
  have h2 : (1/2:ℝ)≤Real.log 2 := by
    have ht := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at ht ⊢
    exact ht
  have hhr : (31:ℝ)≤h := by exact_mod_cast hh
  have hcr : (962:ℝ)≤C := by exact_mod_cast hC
  have hspos : (0:ℝ)<S := by exact_mod_cast (by omega : 0<S)
  have htangent : Real.log ((h:ℝ)+1) ≤ 5*Real.log 2+((h:ℝ)-31)/32 := by
    have hp : (0:ℝ)<((h:ℝ)+1)/32 := by positivity
    have ht := Real.log_le_sub_one_of_pos hp
    have he : (h:ℝ)+1=32*(((h:ℝ)+1)/32) := by ring
    calc
      _ = Real.log 32+Real.log (((h:ℝ)+1)/32) := by
        conv_lhs => rw [he]
        rw [Real.log_mul (by norm_num) (ne_of_gt hp)]
      _ ≤ _ := by
        rw [show (32:ℝ)=2^5 by norm_num,Real.log_pow]
        norm_num at *
        linarith
  have hlogs : Real.log (S:ℝ) ≤ (3*(h:ℝ)+131)/16*Real.log 2 := by
    have hupper : (S:ℝ)≤((h:ℝ)+1)^3/2 := by
      have hs := hS.1
      have hm := Nat.mul_le_mul_right h hhi.le
      have hn : 2*S≤(h+1)^3 := by nlinarith
      have hnR : 2*(S:ℝ)≤((h:ℝ)+1)^3 := by exact_mod_cast hn
      linarith
    have hl := Real.log_le_log hspos hupper
    rw [Real.log_div (by positivity) (by norm_num),Real.log_pow] at hl
    norm_num at hl
    have hm := mul_nonneg (show (0:ℝ)≤(h:ℝ)-31 by linarith)
      (show (0:ℝ)≤Real.log 2-1/2 by linarith)
    nlinarith only [hl,htangent,hm]
  have hp := (div_le_iff₀ (Real.log_pos (by exact_mod_cast (by omega : 1<S)))).mp (Chebyshev.pi_ge S)
  have htail : Real.log ((S:ℝ)+1)≤2*Real.log (S:ℝ) := by
    have ht := Real.log_le_log (by positivity : (0:ℝ)<(S:ℝ)+1)
      (show (S:ℝ)+1≤(S:ℝ)^2 by
        have hs : (2:ℝ)≤S := by exact_mod_cast hS2
        nlinarith only [hs])
    simpa only [Real.log_pow,Nat.cast_ofNat] using ht
  have hpi : (S:ℝ)*Real.log 2≤((Nat.primeCounting S:ℝ)+2)*Real.log (S:ℝ) := by linarith
  by_contra hn
  change ¬ C+7≤Nat.primeCounting S at hn
  have hn' : (Nat.primeCounting S:ℝ)≤(C:ℝ)+6 := by exact_mod_cast (by omega : Nat.primeCounting S≤C+6)
  have hl := mul_le_mul_of_nonneg_left hlogs (show (0:ℝ)≤(Nat.primeCounting S:ℝ)+2 by positivity)
  have hb := mul_le_mul_of_nonneg_right hn' (show (0:ℝ)≤(3*(h:ℝ)+131)/16*Real.log 2 by positivity)
  have hslo : 15*(C:ℝ)*h<32*(S:ℝ)+32 := by exact_mod_cast hS.2
  have hclo : (h:ℝ)^2≤C := by exact_mod_cast hlo
  have hm := mul_nonneg (show (0:ℝ)≤(C:ℝ)-(h:ℝ)^2 by linarith)
    (show (0:ℝ)≤9*(h:ℝ)-262 by linarith)
  have hx : 0≤((h:ℝ)-31)^3 := pow_nonneg (by linarith) _
  have hbound : (S:ℝ)≤((C:ℝ)+8)*(3*(h:ℝ)+131)/16 := by
    apply (mul_le_mul_iff_left₀ (Real.log_pos (by norm_num : (1:ℝ)<2))).mp
    nlinarith only [hpi,hl,hb]
  have hpoly : 0 < (9*(h:ℝ)-262)*(h:ℝ)^2-48*(h:ℝ)-2128 := by
    nlinarith only [hx,sq_nonneg ((h:ℝ)-31),hhr]
  nlinarith only [hbound,hslo,hm,hpoly]

theorem ordinary_threshold_bound {C : ℕ} (hC : 962≤C) :
    40*ordinaryDigitThreshold C≤19*C^3 := by
  have hu := (economical_caps hC).2.1
  have hd : 32*(15*C^3/32)≤15*C^3 := Nat.mul_div_le _ _
  have hc : 962≤C := hC
  have hp := mul_nonneg (show (0:ℤ)≤(C:ℤ)-962 by omega) (show (0:ℤ)≤(C:ℤ)^2 by positivity)
  have hpoly : 160*(2*C^2+117)≤C^3 := by
    have hm := Nat.mul_le_mul_right (C^2) hC
    nlinarith
  unfold ordinaryDigitThreshold
  omega

/-- There are enough primes above the value threshold, rather than its index. -/
theorem ordinary_interval_count {C : ℕ} (hC : 962≤C) :
    Nat.primeCounting (ordinaryDigitThreshold C)+3*C+1≤Nat.primeCounting (C^3) := by
  let L := ordinaryDigitThreshold C
  let Q := C^3
  have hc : (962:ℝ)≤C := by exact_mod_cast hC
  have hpos : (0:ℝ)<C := by linarith
  have hQ : (Q:ℝ)=(C:ℝ)^3 := by simp [Q]
  have hL : 40*(L:ℝ)≤19*(C:ℝ)^3 := by exact_mod_cast ordinary_threshold_bound hC
  have hLQ : L≤Q := by exact_mod_cast (by nlinarith : (L:ℝ)≤(Q:ℝ))
  have hlog := log_le_div_sixtyfour (by omega : 768≤C)
  have h2 : (1/2:ℝ)≤Real.log 2 := by
    have ht := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at ht ⊢
    exact ht
  have hsqrt : Real.sqrt (Q:ℝ)≤(C:ℝ)^2/31 := by
    apply (Real.sqrt_le_iff).mpr
    constructor
    · positivity
    · rw [hQ]
      have hh := mul_nonneg (show (0:ℝ)≤(C:ℝ)-961 by linarith) (show (0:ℝ)≤(C:ℝ)^3 by positivity)
      nlinarith only [hh]
  have hlogQ : Real.log (Q:ℝ)=3*Real.log (C:ℝ) := by rw [hQ,Real.log_pow]; norm_num
  have htail : Real.log ((Q:ℝ)+1)≤6*Real.log (C:ℝ) := by
    have ht := Real.log_le_log (by positivity : (0:ℝ)<(Q:ℝ)+1)
      (show (Q:ℝ)+1≤(Q:ℝ)^2 by rw [hQ]; nlinarith [one_le_pow₀ (by linarith : (1:ℝ)≤C) (n:=3)])
    simp only [Real.log_pow,Nat.cast_ofNat,hlogQ] at ht
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
  have hmain : (C:ℝ)^3/50≤Chebyshev.theta (Q:ℝ)-Chebyshev.theta (L:ℝ) := by
    have hmL := mul_le_mul_of_nonneg_right hL (show (0:ℝ)≤Real.log 2 by positivity)
    have hm2 := mul_le_mul_of_nonneg_left h2 (show (0:ℝ)≤(C:ℝ)^3 by positivity)
    have hml := mul_le_mul_of_nonneg_left hlog (show (0:ℝ)≤(C:ℝ)^2/31 by positivity)
    have hms := mul_le_mul_of_nonneg_right hsqrt (show (0:ℝ)≤Real.log (Q:ℝ) by rw [hlogQ]; positivity)
    have hp := mul_nonneg (show (0:ℝ)≤(C:ℝ)-962 by linarith) (show (0:ℝ)≤(C:ℝ)^2 by positivity)
    have hcs : (C:ℝ)≤(C:ℝ)^3 := by exact_mod_cast (Nat.le_self_pow (by decide : 3≠0) C)
    push_cast at hlo
    rw [hlogQ] at hlo
    have hQmul : (Q:ℝ)*Real.log 2=(C:ℝ)^3*Real.log 2 := by rw [hQ]
    rw [hlogQ] at hms
    rw [hlog4] at hhi
    nlinarith only [hlo,hhi,hQmul,htail,hmL,hm2,hml,hms,hlog,hp,hcs,hc]
  have hmon := Nat.monotone_primeCounting hLQ
  by_contra hn
  change ¬ Nat.primeCounting L+3*C+1≤Nat.primeCounting Q at hn
  have hn' : (Nat.primeCounting Q-Nat.primeCounting L:ℕ)≤3*C := by omega
  have hh := mul_le_mul_of_nonneg_right (show ((Nat.primeCounting Q-Nat.primeCounting L:ℕ):ℝ)≤3*(C:ℝ) by exact_mod_cast hn')
    (show (0:ℝ)≤Real.log (Q:ℝ) by rw [hlogQ]; positivity)
  have hm := mul_le_mul_of_nonneg_left hlog (show (0:ℝ)≤9*(C:ℝ) by positivity)
  have hp := mul_nonneg (show (0:ℝ)≤(C:ℝ)-962 by linarith) (show (0:ℝ)≤(C:ℝ)^2 by positivity)
  rw [hlogQ] at hdiff hh
  nlinarith only [hmain,hdiff,hh,hm,hp,hc]

end
end TranslationTiling.Compiler.Size
