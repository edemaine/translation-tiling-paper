import TranslationTiling.SudokuArithmetic.FiniteStructure

/-! Stability of valuations and last nonzero digits under finite congruences. -/

namespace TranslationTiling.Sudoku

theorem digit_congr_of_dvd_sub (r : ℕ) (hp : r.Prime) {x y : ℤ}
    (hy : y ≠ 0) (h : (r : ℤ) ^ (padicValInt r y + 1) ∣ x - y) :
    x ≠ 0 ∧ padicValInt r x = padicValInt r y ∧ lastDigit r hp x = lastDigit r hp y := by
  let : Fact r.Prime := ⟨hp⟩
  have hr0 : (r : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hp.ne_zero
  obtain ⟨a, ha⟩ := h
  let z := pFreeQuotient r y + (r : ℤ) * a
  have hz : ¬ (r : ℤ) ∣ z := by
    intro hd
    have hh := dvd_sub hd (dvd_mul_right (r : ℤ) a)
    exact pFreeQuotient_not_dvd r hp hy (by simpa only [z, add_sub_cancel_right] using hh)
  have hz0 : z ≠ 0 := fun hh => hz (hh ▸ dvd_zero _)
  have he : x = (r : ℤ) ^ padicValInt r y * z := by
    have hfactor := pFreeQuotient_factor r hp y
    dsimp [z]
    rw [pow_succ] at ha
    linear_combination ha + hfactor
  refine ⟨by rw [he]; exact mul_ne_zero (pow_ne_zero _ hr0) hz0, ?_, ?_⟩
  · rw [he, padicValInt.mul (pow_ne_zero _ hr0) hz0,
      padicValInt.eq_zero_of_not_dvd hz, add_zero, ← Int.natCast_pow,
      padicValInt.of_nat, padicValNat.prime_pow]
  · apply Units.ext
    rw [he, lastDigit_mul_prime_pow, lastDigit_eq_of_not_dvd r hp hz,
      lastDigit_val_of_ne_zero r hp hy]
    simp [z]

theorem digit_congr_bounded (r : ℕ) (hp : r.Prime) (k : ℕ) {x y : ℤ}
    (hy : y ≠ 0) (hv : padicValInt r y ≤ k) (h : (r : ℤ) ^ (k + 1) ∣ x - y) :
    x ≠ 0 ∧ padicValInt r x = padicValInt r y ∧ lastDigit r hp x = lastDigit r hp y :=
  digit_congr_of_dvd_sub r hp hy ((pow_dvd_pow _ (by omega)).trans h)

theorem exists_twoPrime_power_residue (k l : ℕ) (x y : ℤ) :
    ∃ a : ℤ, (p : ℤ) ^ k ∣ a - x ∧ (q : ℤ) ^ l ∣ a - y := by
  have hcop : Nat.Coprime (p ^ k) (q ^ l) :=
    (by decide : Nat.Coprime p q).pow k l
  have hbez := Nat.gcd_eq_gcd_ab (p ^ k) (q ^ l)
  rw [hcop.gcd_eq_one] at hbez
  simp only [Nat.cast_one, Nat.cast_pow] at hbez
  let b := Nat.gcdA (p ^ k) (q ^ l)
  let c := Nat.gcdB (p ^ k) (q ^ l)
  refine ⟨x * (q : ℤ) ^ l * c + y * (p : ℤ) ^ k * b, ?_, ?_⟩
  · refine ⟨b * (y - x), ?_⟩
    have hh := congrArg (fun t : ℤ => t * x) hbez
    dsimp only [b, c]
    linear_combination -hh
  · refine ⟨c * (x - y), ?_⟩
    have hh := congrArg (fun t : ℤ => t * y) hbez
    dsimp only [b, c]
    linear_combination -hh

/-- A single integral shear puts both arithmetic components in canonical form
on any prescribed finite rectangle of valuation depths. -/
theorem decorated_finite_structure {T : LeanWang.TileSet} {W : Array T}
    (hW : LineRule W) (hcols : NonconstantColumns W) (k l : ℕ) :
    ∃ (D E : ℤ) (Bₚ : ZMod p) (Bᵩ : ZMod q), Bₚ ≠ 0 ∧ Bᵩ ≠ 0 ∧
      (∀ (n : Column) (m : ℤ), m ≠ 0 → padicValInt p m ≤ k →
        (reparametrize W 1 D E n m).1.val = Bₚ * (lastDigit p (by decide) m).val) ∧
      (∀ (n : Column) (m : ℤ), m ≠ 0 → padicValInt q m ≤ l →
        (reparametrize W 1 D E n m).2.1.val = Bᵩ * (lastDigit q (by decide) m).val) := by
  obtain ⟨Dₚ, Eₚ, Bₚ, hBₚ, hₚ⟩ := arithmetic_finite_structure (by decide) (by decide)
    (by decide) _ (arithmeticLineRule_p hW) hcols.1 k
  obtain ⟨Dᵩ, Eᵩ, Bᵩ, hBᵩ, hᵩ⟩ := arithmetic_finite_structure (by decide) (by decide)
    (by decide) _ (arithmeticLineRule_q hW) hcols.2 l
  obtain ⟨D, hDp, hDq⟩ := exists_twoPrime_power_residue (k + 1) (l + 1) Dₚ Dᵩ
  obtain ⟨E, hEp, hEq⟩ := exists_twoPrime_power_residue (k + 1) (l + 1) Eₚ Eᵩ
  have affine_congr (r K : ℕ) (Dr Er : ℤ)
      (hD : (r : ℤ) ^ K ∣ D - Dr) (hE : (r : ℤ) ^ K ∣ E - Er)
      (n : Column) (m : ℤ) :
      (r : ℤ) ^ K ∣ (m + D * n.val + E - Dr * n.val - Er) - m := by
    rw [show (m + D * n.val + E - Dr * n.val - Er) - m =
      (D - Dr) * (n.val : ℤ) + (E - Er) by ring]
    exact dvd_add (dvd_mul_of_dvd_left hD (n.val : ℤ)) hE
  refine ⟨D, E, Bₚ, Bᵩ, hBₚ, hBᵩ, ?_, ?_⟩
  · intro n m hm hv
    obtain ⟨hnz, hval, hdigit⟩ := digit_congr_bounded p (by decide) k hm hv
      (affine_congr p (k + 1) Dₚ Eₚ hDp hEp n m)
    have hh := hₚ n (m + D * n.val + E) hnz (by rwa [hval])
    simpa only [reparametrize, one_mul, hdigit] using hh
  · intro n m hm hv
    obtain ⟨hnz, hval, hdigit⟩ := digit_congr_bounded q (by decide) l hm hv
      (affine_congr q (l + 1) Dᵩ Eᵩ hDq hEq n m)
    have hh := hᵩ n (m + D * n.val + E) hnz (by rwa [hval])
    simpa only [reparametrize, one_mul, hdigit] using hh

end TranslationTiling.Sudoku
