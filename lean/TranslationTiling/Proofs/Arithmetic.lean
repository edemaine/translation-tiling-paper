/- Adapted from openai/math, OAI/Geometry/PeriodicTiling/LastDigit.lean, commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a. Apache 2.0; see
third_party/openai-math.LICENSE. Namespace and imports changed for Lean 4.31. -/
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Int.GCD
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega


noncomputable section

namespace TranslationTiling.Sudoku

def pFreeQuotient (p : ℕ) (t : ℤ) : ℤ :=
  t / (p : ℤ) ^ padicValInt p t

theorem pFreeQuotient_factor (p : ℕ) (_hp : p.Prime) (t : ℤ) :
    t = (p : ℤ) ^ padicValInt p t * pFreeQuotient p t := by
  exact (Int.mul_ediv_cancel' (padicValInt_dvd (p := p) t)).symm

theorem pFreeQuotient_not_dvd (p : ℕ) (hp : p.Prime) {t : ℤ}
    (ht : t ≠ 0) : ¬ (p : ℤ) ∣ pFreeQuotient p t := by
  let : Fact p.Prime := ⟨hp⟩
  rintro ⟨u, hu⟩
  have hpow : (p : ℤ) ^ (padicValInt p t + 1) ∣ t := by
    refine ⟨u, ?_⟩
    calc
      t = (p : ℤ) ^ padicValInt p t * pFreeQuotient p t :=
        pFreeQuotient_factor p hp t
      _ = (p : ℤ) ^ padicValInt p t * ((p : ℤ) * u) := by rw [hu]
      _ = (p : ℤ) ^ (padicValInt p t + 1) * u := by
        rw [pow_succ, mul_assoc]
  rcases (padicValInt_dvd_iff (p := p) (padicValInt p t + 1) t).mp hpow with h | h
  · exact ht h
  · omega

theorem pFreeQuotient_prime_pow_mul (p : ℕ) (hp : p.Prime)
    (r : ℕ) (u : ℤ) (hu : ¬ (p : ℤ) ∣ u) :
    pFreeQuotient p ((p : ℤ) ^ r * u) = u := by
  let : Fact p.Prime := ⟨hp⟩
  have hp0 : (p : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hp.ne_zero
  have hu0 : u ≠ 0 := by
    intro h
    apply hu
    rw [h]
    exact dvd_zero _
  have hvpow : padicValInt p ((p : ℤ) ^ r) = r := by
    rw [← Int.natCast_pow, padicValInt.of_nat, padicValNat.prime_pow]
  have hv : padicValInt p ((p : ℤ) ^ r * u) = r := by
    rw [padicValInt.mul (pow_ne_zero _ hp0) hu0, hvpow,
      padicValInt.eq_zero_of_not_dvd hu, add_zero]
  rw [pFreeQuotient, hv]
  exact Int.mul_ediv_cancel_left u (pow_ne_zero r hp0)

theorem pFreeQuotient_mul_prime_pow (p : ℕ) (hp : p.Prime)
    (r : ℕ) {t : ℤ} (ht : t ≠ 0) :
    pFreeQuotient p ((p : ℤ) ^ r * t) = pFreeQuotient p t := by
  have hfactor : (p : ℤ) ^ r * t =
      (p : ℤ) ^ (r + padicValInt p t) * pFreeQuotient p t := by
    calc
      (p : ℤ) ^ r * t =
          (p : ℤ) ^ r * ((p : ℤ) ^ padicValInt p t * pFreeQuotient p t) :=
        congrArg (fun z : ℤ => (p : ℤ) ^ r * z) (pFreeQuotient_factor p hp t)
      _ = (p : ℤ) ^ (r + padicValInt p t) * pFreeQuotient p t := by
        rw [pow_add, mul_assoc]
  rw [hfactor]
  exact pFreeQuotient_prime_pow_mul p hp _ _ (pFreeQuotient_not_dvd p hp ht)

theorem exists_primitive_pair (p : ℕ) (hp : p.Prime) (d e : ℤ)
    (hde : d ≠ 0 ∨ e ≠ 0) :
    ∃ r : ℕ, ∃ a b : ℤ, d = (p : ℤ) ^ r * a ∧
      e = (p : ℤ) ^ r * b ∧ (¬ (p : ℤ) ∣ a ∨ ¬ (p : ℤ) ∣ b) := by
  let : Fact p.Prime := ⟨hp⟩
  let r := padicValInt p (Int.gcd d e : ℤ)
  have hg : (Int.gcd d e : ℤ) ≠ 0 :=
    Int.natCast_ne_zero.mpr (ne_of_gt (Int.gcd_pos_iff.mpr hde))
  have hr : (p : ℤ) ^ r ∣ (Int.gcd d e : ℤ) := padicValInt_dvd _
  obtain ⟨a, ha⟩ := hr.trans (show (Int.gcd d e : ℤ) ∣ d from Int.gcd_dvd_left d e)
  obtain ⟨b, hb⟩ := hr.trans (show (Int.gcd d e : ℤ) ∣ e from Int.gcd_dvd_right d e)
  refine ⟨r, a, b, ha, hb, ?_⟩
  by_cases hpa : (p : ℤ) ∣ a
  · right
    intro hpb
    have hd' : (p : ℤ) ^ (r + 1) ∣ d := by
      obtain ⟨u, hu⟩ := hpa
      refine ⟨u, ?_⟩
      rw [ha, hu, pow_succ, mul_assoc]
    have he' : (p : ℤ) ^ (r + 1) ∣ e := by
      obtain ⟨v, hv⟩ := hpb
      refine ⟨v, ?_⟩
      rw [hb, hv, pow_succ, mul_assoc]
    rcases (padicValInt_dvd_iff (p := p) (r + 1) (Int.gcd d e : ℤ)).mp
        (Int.dvd_coe_gcd hd' he') with hzero | hle
    · exact hg hzero
    · change r + 1 ≤ r at hle
      omega
  · exact Or.inl hpa

def lastDigit (p : ℕ) (hp : p.Prime) (t : ℤ) : (ZMod p)ˣ := by
  letI : Fact p.Prime := ⟨hp⟩
  exact if ht : t = 0 then 1 else
    Units.mk0 (pFreeQuotient p t : ZMod p) (by
      intro h
      exact pFreeQuotient_not_dvd p hp ht
        ((ZMod.intCast_zmod_eq_zero_iff_dvd (pFreeQuotient p t) p).mp h))

@[simp] theorem lastDigit_zero (p : ℕ) (hp : p.Prime) :
    lastDigit p hp 0 = 1 := by
  simp [lastDigit]

theorem lastDigit_val_of_ne_zero (p : ℕ) (hp : p.Prime) {t : ℤ}
    (ht : t ≠ 0) :
    (lastDigit p hp t : ZMod p) = (pFreeQuotient p t : ZMod p) := by
  simp [lastDigit, ht]

theorem lastDigit_eq_of_not_dvd (p : ℕ) (hp : p.Prime) {t : ℤ}
    (ht : ¬ (p : ℤ) ∣ t) : (lastDigit p hp t : ZMod p) = (t : ZMod p) := by
  have ht0 : t ≠ 0 := by
    intro h
    apply ht
    rw [h]
    exact dvd_zero _
  rw [lastDigit_val_of_ne_zero p hp ht0]
  simp only [pFreeQuotient, padicValInt.eq_zero_of_not_dvd ht, pow_zero,
    Int.ediv_one]

@[simp] theorem lastDigit_one (p : ℕ) (hp : p.Prime) :
    lastDigit p hp 1 = 1 := by
  apply Units.ext
  have hnot : ¬ (p : ℤ) ∣ (1 : ℤ) :=
    fun h => hp.not_dvd_one (Int.natCast_dvd_natCast.mp h)
  simpa only [Units.val_one, Int.cast_one] using lastDigit_eq_of_not_dvd p hp hnot

theorem lastDigit_two (p : ℕ) (hp : p.Prime) (hlarge : 2 < p) :
    (lastDigit p hp 2 : ZMod p) = 2 := by
  have hnot : ¬ (p : ℤ) ∣ (2 : ℤ) := by
    intro h
    exact Nat.not_dvd_of_pos_of_lt (by decide : 0 < 2) hlarge
      (Int.natCast_dvd_natCast.mp h)
  simpa only [Int.cast_ofNat] using lastDigit_eq_of_not_dvd p hp hnot

theorem lastDigit_mul_prime_pow (p : ℕ) (hp : p.Prime) (r : ℕ) (t : ℤ) :
    lastDigit p hp ((p : ℤ) ^ r * t) = lastDigit p hp t := by
  by_cases ht : t = 0
  · subst t
    simp
  · have hp0 : (p : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hp.ne_zero
    have hprod : (p : ℤ) ^ r * t ≠ 0 := mul_ne_zero (pow_ne_zero _ hp0) ht
    apply Units.ext
    rw [lastDigit_val_of_ne_zero p hp hprod, lastDigit_val_of_ne_zero p hp ht,
      pFreeQuotient_mul_prime_pow p hp r ht]

theorem lastDigit_eq_div_of_dvd_not_sq_dvd (p : ℕ) (hp : p.Prime) {t : ℤ}
    (hdiv : (p : ℤ) ∣ t) (hsq : ¬ (p : ℤ) ^ 2 ∣ t) :
    (lastDigit p hp t : ZMod p) = ((t / (p : ℤ) : ℤ) : ZMod p) := by
  have ht : t ≠ 0 := by
    intro h
    apply hsq
    rw [h]
    exact dvd_zero _
  have hquot : ¬ (p : ℤ) ∣ t / (p : ℤ) := by
    rintro ⟨u, hu⟩
    apply hsq
    refine ⟨u, ?_⟩
    calc
      t = (p : ℤ) * (t / (p : ℤ)) := (Int.mul_ediv_cancel' hdiv).symm
      _ = (p : ℤ) * ((p : ℤ) * u) := by rw [hu]
      _ = (p : ℤ) ^ 2 * u := by rw [pow_two, mul_assoc]
  have hfree := pFreeQuotient_prime_pow_mul p hp 1 (t / (p : ℤ)) hquot
  rw [pow_one, Int.mul_ediv_cancel' hdiv] at hfree
  rw [lastDigit_val_of_ne_zero p hp ht, hfree]

end TranslationTiling.Sudoku
end
