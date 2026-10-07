import TranslationTiling.Proofs.Canonical

namespace TranslationTiling.Sudoku

/-- Equality of coefficients modulo the square of an arithmetic prime. -/
def SqCongr (r : ℕ) (x y : ℤ) : Prop := (r : ℤ) ^ 2 ∣ x - y

theorem dvd_iff_of_dvd_sub {r x y : ℤ} (h : r ∣ x - y) : r ∣ x ↔ r ∣ y := by
  constructor
  · intro hx
    have he : x - (x - y) = y := by ring
    rw [← he]
    exact dvd_sub hx h
  · intro hy
    simpa only [sub_add_cancel] using dvd_add h hy

theorem SqCongr.dvd_iff {r : ℕ} {x y : ℤ} (h : SqCongr r x y) :
    (r : ℤ) ∣ x ↔ (r : ℤ) ∣ y :=
  dvd_iff_of_dvd_sub ((dvd_pow_self (r : ℤ) (by decide : 2 ≠ 0)).trans h)

theorem SqCongr.square_dvd_iff {r : ℕ} {x y : ℤ} (h : SqCongr r x y) :
    (r : ℤ) ^ 2 ∣ x ↔ (r : ℤ) ^ 2 ∣ y := dvd_iff_of_dvd_sub h

theorem SqCongr.lowValuation_eq {r : ℕ} {x y : ℤ} (h : SqCongr r x y) :
    lowValuation r x = lowValuation r y := by
  simp only [lowValuation, h.dvd_iff, h.square_dvd_iff]

private theorem intCast_eq_of_dvd_sub (r : ℕ) (x y : ℤ) (h : (r : ℤ) ∣ x - y) :
    (x : ZMod r) = (y : ZMod r) := by
  apply sub_eq_zero.mp
  rw [← Int.cast_sub]
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd (x - y) r).mpr h

theorem SqCongr.lowDigit_eq {r : ℕ} (hr : r ≠ 0) {x y : ℤ} (h : SqCongr r x y) :
    lowDigit r x = lowDigit r y := by
  by_cases hx : (r : ℤ) ∣ x
  · have hy := h.dvd_iff.mp hx
    simp only [lowDigit, if_pos hx, if_pos hy]
    apply intCast_eq_of_dvd_sub
    obtain ⟨k, hk⟩ := h
    refine ⟨k, ?_⟩
    apply mul_left_cancel₀ (Int.natCast_ne_zero.mpr hr)
    calc
      (r : ℤ) * (x / r - y / r) = x - y := by
        rw [mul_sub, Int.mul_ediv_cancel' hx, Int.mul_ediv_cancel' hy]
      _ = (r : ℤ) * ((r : ℤ) * k) := by rw [hk, pow_two, mul_assoc]
  · have hy : ¬ (r : ℤ) ∣ y := fun hy => hx (h.dvd_iff.mpr hy)
    simp only [lowDigit, if_neg hx, if_neg hy]
    exact intCast_eq_of_dvd_sub r x y
      ((dvd_pow_self (r : ℤ) (by decide : 2 ≠ 0)).trans h)

theorem SqCongr.threshold_eq {r : ℕ} {a b : ℤ} (h : SqCongr r a b) :
    threshold r a = threshold r b := by simp only [threshold, h.dvd_iff]

theorem SqCongr.affine {r : ℕ} {a b c d : ℤ}
    (ha : SqCongr r a c) (hb : SqCongr r b d) (n : ℤ) :
    SqCongr r (a * n + b) (c * n + d) := by
  change (r : ℤ) ^ 2 ∣ (a * n + b) - (c * n + d)
  rw [show (a * n + b) - (c * n + d) = (a - c) * n + (b - d) by ring]
  exact dvd_add (dvd_mul_of_dvd_left ha n) hb

/-- A concrete CRT certificate for the fixed primes. Only the small Bezout
identity is evaluated; no Sudoku board or word is enumerated. -/
theorem exists_twoPrime_residue (x y : ℤ) :
    ∃ a : ℤ, SqCongr p a x ∧ SqCongr q a y := by
  have hbez : (p : ℤ) ^ 2 * 14447 + (q : ℤ) ^ 2 * (-12934) = 1 := by decide
  refine ⟨x * (q : ℤ) ^ 2 * (-12934) + y * (p : ℤ) ^ 2 * 14447, ?_, ?_⟩
  · refine ⟨14447 * (y - x), ?_⟩
    have hx := congrArg (fun z : ℤ => z * x) hbez
    nlinarith only [hx]
  · refine ⟨(-12934) * (x - y), ?_⟩
    have hy := congrArg (fun z : ℤ => z * y) hbez
    nlinarith only [hy]

/-- Low-valuation tests of a normalized line determine its original digit
and shift its valuation by the removed common prime power. -/
theorem normalized_line_data (r : ℕ) (hp : r.Prime) (k u : ℕ)
    (a b c d n : ℤ) (hc : SqCongr r a c) (hd : SqCongr r b d)
    (h : lowValuation r (a * n + b) = some u) :
    (r : ℤ) ^ k * (c * n + d) ≠ 0 ∧
    (lastDigit r hp ((r : ℤ) ^ k * (c * n + d))).val = lowDigit r (a * n + b) ∧
    padicValInt r ((r : ℤ) ^ k * (c * n + d)) = k + u := by
  letI : Fact r.Prime := ⟨hp⟩
  have hcong := hc.affine hd n
  have hl : lowValuation r (c * n + d) = some u := hcong.lowValuation_eq ▸ h
  obtain ⟨hz, hv⟩ := lowValuation_sound r hp _ u hl
  have hr : (r : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hp.ne_zero
  refine ⟨mul_ne_zero (pow_ne_zero k hr) hz, ?_, ?_⟩
  · rw [lastDigit_mul_prime_pow, lastDigit_eq_lowDigit r hp _ u hl]
    exact (hcong.lowDigit_eq hp.ne_zero).symm
  · rw [padicValInt.mul (pow_ne_zero k hr) hz, hv]
    have hpow : padicValInt r ((r : ℤ) ^ k) = k := by
      rw [← Int.natCast_pow, padicValInt.of_nat, padicValNat.prime_pow]
    rw [hpow]

end TranslationTiling.Sudoku
