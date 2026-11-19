import TranslationTiling.Proofs.LogDifferenceBound
import Mathlib.Analysis.Complex.ExponentialBounds

namespace TranslationTiling.Stacking
noncomputable section
open scoped BigOperators
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem tight_bad_bound (s m X L : ℕ) (hs : 2 ≤ s) (hsX : s ≤ X)
    (hL : 2 ≤ L) (hX : 2*X < 2^L)
    (hlower : 3*X^2*L ≤ m) (hupper : 2*m ≤ (12*L+4)*X^2) :
    s*(2*m)*(s^2-1)^m < s^(2*m) := by
  have hsR : (2:ℝ) ≤ s := by exact_mod_cast hs
  have hXpos : (0:ℝ) < X := by exact_mod_cast (by omega : 0<X)
  have hspos : (0:ℝ) < s := by linarith
  have ha : ((s^2-1:ℕ):ℝ) = (s:ℝ)^2-1 := by
    have hsq : 1 ≤ s^2 := by nlinarith
    rw [Nat.cast_sub hsq,Nat.cast_pow,Nat.cast_one]
  have hstep : (((s^2-1:ℕ):ℝ)) ≤ (s:ℝ)^2 * Real.exp (-(1/(s:ℝ)^2)) := by
    have h := mul_le_mul_of_nonneg_left (Real.one_sub_le_exp_neg (1/(s:ℝ)^2))
      (show (0:ℝ) ≤ (s:ℝ)^2 by positivity)
    rw [ha]
    field_simp at h
    nlinarith
  have hpow : (((s^2-1)^m:ℕ):ℝ) ≤ (s:ℝ)^(2*m) * Real.exp (-(m:ℝ)/(s:ℝ)^2) := by
    have h := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ ((s^2-1:ℕ):ℝ)) hstep m
    rw [mul_pow,← pow_mul,← Real.exp_nat_mul] at h
    push_cast
    convert h using 1 <;> ring
  have hratio : (3:ℝ)*L ≤ (m:ℝ)/(s:ℝ)^2 := by
    apply (le_div_iff₀ (by positivity : (0:ℝ)<(s:ℝ)^2)).mpr
    have hlo : (3:ℝ)*(X:ℝ)^2*L≤m := by exact_mod_cast hlower
    calc
      _ ≤ (3:ℝ)*L*(X:ℝ)^2 := by gcongr
      _ = (3:ℝ)*(X:ℝ)^2*L := by ring
      _ ≤ m := hlo
  have he : (16:ℝ) ≤ Real.exp 3 := by
    have h' : (8/3:ℝ) < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
    have he := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤8/3) h'.le 3
    rw [←Real.exp_nat_mul] at he
    norm_num at he
    linarith
  have hgeom : ∀ k≥2, 12*k+4≤8*2^k := by
    intro k hk
    induction k,hk using Nat.le_induction with
    | base => decide
    | succ k hk ih =>
      rw [pow_succ]
      omega
  have hxpow : X < 2^(L-1) := by
    have hh : L=L-1+1 := by omega
    rw [hh,pow_succ] at hX
    omega
  have hexp : Real.exp (-(m:ℝ)/(s:ℝ)^2) ≤ ((16:ℝ)^L)⁻¹ := by
    have hh : (16:ℝ)^L ≤ Real.exp (3*(L:ℝ)) := by
      have h := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤16) he L
      rw [←Real.exp_nat_mul] at h
      simpa [mul_comm] using h
    rw [show -(m:ℝ)/(s:ℝ)^2 = -((m:ℝ)/(s:ℝ)^2) by ring,Real.exp_neg]
    apply inv_anti₀ (by positivity)
    exact hh.trans (Real.exp_le_exp.mpr hratio)
  have hpref : s*(2*m)<16^L := by
    calc
      _ ≤ (12*L+4)*X^3 := by
        calc
          s*(2*m) ≤ X*((12*L+4)*X^2) := Nat.mul_le_mul hsX hupper
          _ = _ := by ring
      _ < (12*L+4)*(2^(L-1))^3 :=
        Nat.mul_lt_mul_of_pos_left (Nat.pow_lt_pow_left hxpow (by decide)) (by omega)
      _ ≤ (8*2^L)*(2^(L-1))^3 := Nat.mul_le_mul_right _ (hgeom L hL)
      _ = _ := by
        calc
          _ = 2^(3+L+(L-1)*3) := by
            rw [pow_add,pow_add,pow_mul]
            rfl
          _ = 2^(4*L) := by congr 1; omega
          _ = 16^L := by rw [pow_mul]; rfl
  have hpref' : (s:ℝ)*(2*m)<(16:ℝ)^L := by exact_mod_cast hpref
  have hp16 : (0:ℝ)<(16:ℝ)^L := by positivity
  have hprob : (s:ℝ)*(2*m)*Real.exp (-(m:ℝ)/(s:ℝ)^2)<1 := by
    calc
      _ ≤ ((s:ℝ)*(2*m))*((16:ℝ)^L)⁻¹ :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
      _ < 1 := by rw [←div_eq_mul_inv]; exact (div_lt_one hp16).mpr hpref'
  have hp : (0:ℝ)<(s:ℝ)^(2*m) := by positivity
  have hfinal : ((s*(2*m)*(s^2-1)^m:ℕ):ℝ) < (s:ℝ)^(2*m) := by
    push_cast
    calc
      (s:ℝ)*(2*m)*((s^2-1:ℕ):ℝ)^m ≤ (s:ℝ)*(2*m)*((s:ℝ)^(2*m)*Real.exp (-(m:ℝ)/(s:ℝ)^2)) :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast hpow) (by positivity)
      _ = ((s:ℝ)*(2*m)*Real.exp (-(m:ℝ)/(s:ℝ)^2))*(s:ℝ)^(2*m) := by ring
      _ < 1*(s:ℝ)^(2*m) := mul_lt_mul_of_pos_right hprob hp
      _ = _ := one_mul _
  exact_mod_cast hfinal

def tightThreshold (X P : ℕ) := 6*X^2*differenceLog X+P+3

theorem partition_tight (s X P q : ℕ) (hs : 0<s) (hsX : s≤X)
    (hP : P+3≤2*X^2) (hq : q.Prime)
    (hlo : tightThreshold X P<q) (hhi : q≤2*tightThreshold X P) :
    ∃ E : Fin s → Finset (ZMod q), IsColorPartition E ∧ HasFullDifferences E := by
  letI : Fact q.Prime := ⟨hq⟩
  by_cases hs1 : s=1
  · subst s
    let c : Coloring q 1 := fun _ => 0
    obtain ⟨E,_,hpart,hfull⟩ := exists_partition_of_nonzero_coloring c (by
      intro ν d hd
      have hν : (0:Fin 1)=ν := Subsingleton.elim _ _
      exact ⟨d,0,hν,hν,sub_zero d⟩)
    exact ⟨E,hpart,hfull⟩
  · have hXL : 2*X < 2^differenceLog X :=
      Nat.lt_pow_succ_log_self (by decide : 1<2) _
    have hL : 2≤differenceLog X := by
      by_contra! h
      have he : differenceLog X=1 := by unfold differenceLog at *; omega
      rw [he] at hXL
      norm_num at hXL
      omega
    have hq2 : 2<q := by unfold tightThreshold at hlo; omega
    have hodd := hq.eq_two_or_odd.resolve_left (by omega)
    have hqm : q=2*(q/2)+1 := by omega
    have hmlo : 3*X^2*differenceLog X≤q/2 := by
      unfold tightThreshold at hlo
      nlinarith [hqm]
    have hmhi : 2*(q/2)≤(12*differenceLog X+4)*X^2 := by
      unfold tightThreshold at hhi
      nlinarith [hqm]
    obtain ⟨c,hc⟩ := exists_coloring_of_bad_bound hs hqm
      (tight_bad_bound s (q/2) X _ (by omega) hsX hL hXL hmlo hmhi)
    obtain ⟨E,_,hpart,hfull⟩ := exists_partition_of_nonzero_coloring c hc
    exact ⟨E,hpart,hfull⟩

end
end TranslationTiling.Stacking
