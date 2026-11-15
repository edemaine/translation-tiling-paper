import TranslationTiling.Proofs.FullDifferencePartition
import TranslationTiling.Proofs.StackingContributions
import Mathlib.Analysis.SpecialFunctions.Exp

namespace TranslationTiling.Stacking
noncomputable section
open scoped BigOperators
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

/-- Keep the probability estimate instead of truncating the binomial expansion. -/
theorem fullDifference_bad_bound_log (s m X L : ℕ) (hs : 2 ≤ s) (hsX : s ≤ X)
    (hL : 1 ≤ L) (hX : X ≤ 2^L)
    (hlower : 32*X^2*L ≤ m) (hupper : 2*m+1 ≤ 132*X^2*L) :
    s*(2*m)*(s^2-1)^m < s^(2*m) := by
  have hsR : (2:ℝ) ≤ s := by exact_mod_cast hs
  have hXpos : (0:ℝ) < X := by exact_mod_cast (by omega : 0<X)
  have hLpos : (1:ℝ) ≤ L := by exact_mod_cast hL
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
  have hratio : (32:ℝ)*L ≤ (m:ℝ)/(s:ℝ)^2 := by
    apply (le_div_iff₀ (by positivity : (0:ℝ)<(s:ℝ)^2)).mpr
    have hl : (32:ℝ)*(X:ℝ)^2*L ≤ m := by exact_mod_cast hlower
    have hx : (s:ℝ)^2 ≤ (X:ℝ)^2 := by exact_mod_cast (Nat.pow_le_pow_left hsX 2)
    nlinarith [mul_le_mul_of_nonneg_right hx (show (0:ℝ)≤32*(L:ℝ) by positivity)]
  have hexp : Real.exp (-(m:ℝ)/(s:ℝ)^2) ≤ Real.exp (-32*(L:ℝ)) := by
    apply Real.exp_le_exp.mpr
    convert neg_le_neg hratio using 1 <;> ring
  have htwo : (2:ℝ) ≤ Real.exp 1 := by have h := Real.add_one_le_exp (1:ℝ); norm_num at h ⊢; exact h
  have hXe : (X:ℝ) ≤ Real.exp (L:ℝ) := by
    have hx : (X:ℝ) ≤ (2:ℝ)^L := by exact_mod_cast hX
    apply hx.trans
    have h := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤2) htwo L
    simpa only [← Real.exp_nat_mul,mul_one] using h
  have hLe : (L:ℝ) ≤ Real.exp (L:ℝ) := by have h := Real.add_one_le_exp (L:ℝ); linarith
  have hpref : (s:ℝ)*(2*m) ≤ 132*(X:ℝ)^3*L := by
    have hu : (2:ℝ)*m+1 ≤ 132*(X:ℝ)^2*L := by exact_mod_cast hupper
    have hx : (s:ℝ) ≤ X := by exact_mod_cast hsX
    nlinarith [mul_le_mul_of_nonneg_left hu (show (0:ℝ) ≤ X by positivity),
      mul_le_mul_of_nonneg_right hx (show (0:ℝ) ≤ 2*(m:ℝ) by positivity)]
  have hprefexp : (s:ℝ)*(2*m) ≤ 132*Real.exp (4*(L:ℝ)) := by
    apply hpref.trans
    have h := mul_le_mul (pow_le_pow_left₀ (by positivity : (0:ℝ)≤X) hXe 3) hLe
      (by positivity : (0:ℝ) ≤ L) (by positivity : (0:ℝ)≤Real.exp (L:ℝ)^3)
    calc
      _ = 132*((X:ℝ)^3*L) := by ring
      _ ≤ 132*(Real.exp (L:ℝ)^3*Real.exp (L:ℝ)) := mul_le_mul_of_nonneg_left h (by norm_num)
      _ = _ := by
        rw [← Real.exp_nat_mul,← Real.exp_add]
        congr 2
        ring
  have hsmall : (132:ℝ)*Real.exp (-28*(L:ℝ)) < 1 := by
    have he28 : (132:ℝ) < Real.exp 28 := by
      have h := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤2) htwo 28
      rw [← Real.exp_nat_mul] at h
      norm_num at h
      linarith
    have he := Real.exp_le_exp.mpr (show (28:ℝ) ≤ 28*L by linarith)
    rw [show -28*(L:ℝ) = -(28*(L:ℝ)) by ring,Real.exp_neg,← div_eq_mul_inv]
    exact (div_lt_one (Real.exp_pos _)).mpr (he28.trans_le he)
  have hprob : (s:ℝ)*(2*m)*Real.exp (-(m:ℝ)/(s:ℝ)^2) < 1 := by
    calc
      _ ≤ (132*Real.exp (4*(L:ℝ)))*Real.exp (-32*(L:ℝ)) :=
        mul_le_mul hprefexp hexp (Real.exp_nonneg _) (by positivity)
      _ = 132*Real.exp (-28*(L:ℝ)) := by rw [mul_assoc,← Real.exp_add]; congr 2; ring
      _ < _ := hsmall
  push_cast at hpow
  have hp : (0:ℝ) < (s:ℝ)^(2*m) := by positivity
  have hfinal : ((s*(2*m)*(s^2-1)^m:ℕ):ℝ) < (s:ℝ)^(2*m) := by
    push_cast
    calc
      _ ≤ (s:ℝ)*(2*m)*((s:ℝ)^(2*m)*Real.exp (-(m:ℝ)/(s:ℝ)^2)) :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = ((s:ℝ)*(2*m)*Real.exp (-(m:ℝ)/(s:ℝ)^2)) * (s:ℝ)^(2*m) := by ring
      _ < 1*(s:ℝ)^(2*m) := mul_lt_mul_of_pos_right hprob hp
      _ = _ := one_mul _
  exact_mod_cast hfinal

/-- Any strict bound on bad colorings supplies the same full-difference partition. -/
theorem exists_coloring_of_bad_bound {q s m : ℕ} [Fact q.Prime]
    (hs : 0 < s) (hq : q = 2*m+1)
    (hbad : s*(2*m)*(s^2-1)^m < s^(2*m)) :
    ∃ c : Coloring q s, ∀ ν d, d ≠ 0 → ∃ x y, c x = ν ∧ c y = ν ∧ x-y=d := by
  have hstrict := Nat.mul_lt_mul_of_pos_left hbad hs
  have hcard : (someBadDifferenceColorings q s).card < (Finset.univ : Finset (Coloring q s)).card := by
    calc
      _ ≤ (s*(q-1))*(s*(s^2-1)^m) := someBadDifferenceColorings_card_le hq
      _ = s*(s*(2*m)*(s^2-1)^m) := by rw [hq]; simp only [Nat.add_sub_cancel]; ring
      _ < s*s^(2*m) := hstrict
      _ = _ := by simp only [Finset.card_univ,Fintype.card_fun,Fintype.card_fin,ZMod.card]; rw [hq,pow_succ]; ring
  obtain ⟨c,_,hc⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  refine ⟨c,fun ν d hd => ?_⟩
  by_contra hb
  exact hc (Finset.mem_biUnion.mpr ⟨(ν,d),Finset.mem_product.mpr
    ⟨Finset.mem_univ _,Finset.mem_erase.mpr ⟨hd,Finset.mem_univ _⟩⟩,
    (mem_badDifferenceColorings c ν d).mpr hb⟩)


def differenceLog (X : ℕ) : ℕ := Nat.log 2 (2*X)+1
def logPartitionThreshold (X P : ℕ) : ℕ := 64*X^2*differenceLog X+P+3

theorem partition_logarithmic (s X P q : ℕ) (hs : 0 < s) (hsX : s ≤ X)
    (hP : P ≤ X^2) (hq : q.Prime)
    (hlo : logPartitionThreshold X P < q) (hhi : q ≤ 2*logPartitionThreshold X P) :
    ∃ E : Fin s → Finset (ZMod q), IsColorPartition E ∧ HasFullDifferences E := by
  letI : Fact q.Prime := ⟨hq⟩
  by_cases hs1 : s = 1
  · subst s
    let c : Coloring q 1 := fun _ => 0
    obtain ⟨E,_,hpart,hfull⟩ := exists_partition_of_nonzero_coloring c (by
      intro ν d hd
      have hν : (0:Fin 1)=ν := Subsingleton.elim _ _
      exact ⟨d,0,hν,hν,sub_zero d⟩)
    exact ⟨E,hpart,hfull⟩
  · have hs2 : 2 ≤ s := by omega
    have hX2 : 2 ≤ X := by omega
    have hL : 1 ≤ differenceLog X := by unfold differenceLog; omega
    have hXL : X ≤ 2^differenceLog X := by
      apply (show X ≤ 2*X by omega).trans
      exact (Nat.lt_pow_succ_log_self (by decide : 1<2) _).le
    have hq2 : 2 < q := by unfold logPartitionThreshold at hlo; omega
    have hodd := hq.eq_two_or_odd.resolve_left (by omega)
    have hqm : q = 2*(q/2)+1 := by omega
    have hmlo : 32*X^2*differenceLog X ≤ q/2 := by
      unfold logPartitionThreshold at hlo
      nlinarith [hqm]
    have hmhi : 2*(q/2)+1 ≤ 132*X^2*differenceLog X := by
      have hp : 1 ≤ X^2 := by nlinarith
      have hxp : X^2 ≤ X^2*differenceLog X := Nat.le_mul_of_pos_right _ (by omega)
      have hx4 : 4 ≤ X^2 := by nlinarith
      unfold logPartitionThreshold at hhi
      nlinarith [hqm]
    obtain ⟨c,hc⟩ := exists_coloring_of_bad_bound (by omega) hqm
      (fullDifference_bad_bound_log s (q/2) X (differenceLog X) hs2 hsX hL hXL hmlo hmhi)
    obtain ⟨E,_,hpart,hfull⟩ := exists_partition_of_nonzero_coloring c hc
    exact ⟨E,hpart,hfull⟩

end
end TranslationTiling.Stacking
