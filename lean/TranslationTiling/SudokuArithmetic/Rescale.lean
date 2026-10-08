import TranslationTiling.SudokuArithmetic.Reparametrize

/-! Compatibility of the initial affine form with removal of one prime factor. -/

set_option maxRecDepth 2000

namespace TranslationTiling.Sudoku

theorem FullAffineApproximation.nonconstant {r : ℕ} (hp : r.Prime)
    (hlarge : 200 < r) {V : Column → ℤ → (ZMod r)ˣ} {A B C : ZMod r}
    (hH : FullAffineApproximation V A B C) (hB : B ≠ 0) :
    ∀ n, ∃ m m', V n m ≠ V n m' := by
  let : Fact r.Prime := ⟨hp⟩
  have h12 : (1 : ZMod r) ≠ 2 := by
    intro he
    have hh := congrArg (fun z : ZMod r => z.val) he
    rw [ZMod.val_one_eq_one_mod, ZMod.val_two_eq_two_mod,
      Nat.mod_eq_of_lt (by omega : 1 < r), Nat.mod_eq_of_lt (by omega : 2 < r)] at hh
    omega
  have h2 : (2 : ZMod r) ≠ 0 := by
    intro he
    exact Nat.not_dvd_of_pos_of_lt (by decide : 0 < 2) (by omega : 2 < r)
      ((ZMod.natCast_eq_zero_iff 2 r).mp he)
  intro n
  have exists_value (t : ZMod r) :
      ∃ m : ℤ, A * (n.val : ZMod r) + B * (m : ZMod r) + C = t := by
    obtain ⟨m, hm⟩ := ZMod.intCast_surjective (B⁻¹ * (t - A * (n.val : ZMod r) - C))
    refine ⟨m, ?_⟩
    rw [hm, ← mul_assoc, mul_inv_cancel₀ hB, one_mul]
    ring
  obtain ⟨m, hm⟩ := exists_value 1
  obtain ⟨m', hm'⟩ := exists_value 2
  refine ⟨m, m', ?_⟩
  intro he
  have hval := congrArg (fun z : (ZMod r)ˣ => z.val) he
  rw [hH.2 n m (by rw [hm]; exact one_ne_zero), hm,
    hH.2 n m' (by rw [hm']; exact h2), hm'] at hval
  exact h12 hval

theorem normalized_line_coefficients {r : ℕ} (hp : r.Prime) (hlarge : 200 < r)
    (hr : r ^ 2 ≤ Width) {V : Column → ℤ → (ZMod r)ˣ} {B : ZMod r}
    (hH : FullAffineApproximation V 0 B 0) (hB : B ≠ 0)
    (d e a b : ℤ) (hab : ¬ (r : ℤ) ∣ a ∨ ¬ (r : ℤ) ∣ b)
    (ht : ∀ n u, lowValuation r (a * n.val + b) = some u → u ≤ threshold r a →
      (V n (d * n.val + e)).val = lowDigit r (a * n.val + b))
    (hde : (d : ZMod r) ≠ 0 ∨ (e : ZMod r) ≠ 0) :
    (a : ZMod r) = B * (d : ZMod r) ∧ (b : ZMod r) = B * (e : ZMod r) := by
  let : Fact r.Prime := ⟨hp⟩
  have hab' : (a : ZMod r) ≠ 0 ∨ (b : ZMod r) ≠ 0 := by
    simpa only [ne_eq, ZMod.intCast_zmod_eq_zero_iff_dvd] using hab
  have hBdBe : B * (d : ZMod r) ≠ 0 ∨ B * (e : ZMod r) ≠ 0 :=
    hde.imp (mul_ne_zero hB) (mul_ne_zero hB)
  let x : Fin 4 → ZMod r := fun i => (i.val : ZMod r)
  have hx : Function.Injective x := by
    simpa only [zero_add, Int.cast_natCast] using
      (ArithmeticRule.four_residues_injective (p := r) (by omega) 0)
  obtain ⟨i, j, hij, hi, hi', hj, hj'⟩ :=
    ArithmeticRule.two_common_nonzero_of_four x hx (a : ZMod r) (b : ZMod r)
      (B * (d : ZMod r)) (B * (e : ZMod r)) hab' hBdBe
  let c : Fin 4 → Column := fun k => ⟨k.val, by
    have := k.isLt; have := hp.one_lt; nlinarith⟩
  have agrees (k : Fin 4) (hk : (a : ZMod r) * x k + (b : ZMod r) ≠ 0)
      (hk' : (B * (d : ZMod r)) * x k + B * (e : ZMod r) ≠ 0) :
      (a : ZMod r) * x k + (b : ZMod r) =
        (B * (d : ZMod r)) * x k + B * (e : ZMod r) := by
    have hn : ¬ (r : ℤ) ∣ a * (c k).val + b := by
      intro hd
      apply hk
      simpa only [Int.cast_add, Int.cast_mul, Int.cast_natCast, c, x] using
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ r).mpr hd
    have htest := (arithmetic_tests r _ a b hab ht (c k)).1 hn
    have hform : 0 * ((c k).val : ZMod r) + B * ((d * (c k).val + e : ℤ) : ZMod r) + 0 =
        (B * (d : ZMod r)) * x k + B * (e : ZMod r) := by
      simp only [c, x, zero_mul, zero_add, add_zero, Int.cast_add, Int.cast_mul,
        Int.cast_natCast]
      ring
    have happrox := hH.2 (c k) _ (by rwa [hform])
    have hh : (a : ZMod r) * x k + (b : ZMod r) =
        (V (c k) (d * (c k).val + e)).val := by
      simpa only [Int.cast_add, Int.cast_mul, Int.cast_natCast, c, x] using htest.symm
    exact hh.trans (happrox.trans hform)
  exact ArithmeticRule.affine_coefficients_eq_of_two (fun he => hij (hx he))
    (agrees i hi hi') (agrees j hj hj')

/-- The vertical coefficient is unchanged when one prime factor is removed. -/
theorem rescale_vertical_coefficient {r : ℕ} (hp : r.Prime) (hlarge : 200 < r)
    (hr : r ^ 2 ≤ Width) {V : Column → ℤ → (ZMod r)ˣ} (hV : ArithmeticLineRule r V)
    {B A₁ B₁ C₁ : ZMod r} (hB : B ≠ 0) (hH : FullAffineApproximation V 0 B 0)
    (hH₁ : FullAffineApproximation (arithmeticReparametrize V r 0 0) A₁ B₁ C₁) :
    B₁ = B := by
  let : Fact r.Prime := ⟨hp⟩
  have hB₁ : B₁ ≠ 0 := ArithmeticRule.rescale_vertical_coefficient_ne_zero hp hlarge
    (arithmeticRestriction_lineRule r hr V hV) hB (hH.restrict hr)
    (by simpa only [ArithmeticRule.AffineApproximation, arithmeticRestriction,
      arithmeticReparametrize, zero_mul,
      add_zero, ArithmeticRule.rescale] using hH₁.restrict hr)
  obtain ⟨a, b, hab, ht⟩ := hV 1 0
  obtain ⟨ha, hb⟩ := normalized_line_coefficients hp hlarge hr hH hB 1 0 a b hab ht
    (Or.inl (by simp))
  simp only [Int.cast_one, mul_one, Int.cast_zero, mul_zero] at ha hb
  have hbd : (r : ℤ) ∣ b := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hb
  obtain ⟨z, hz⟩ := hbd
  let x : Fin 4 → ZMod r := fun i => (i.val : ZMod r)
  have hx : Function.Injective x := by
    simpa only [zero_add, Int.cast_natCast] using
      (ArithmeticRule.four_residues_injective (p := r) (by omega) 0)
  obtain ⟨i, j, hij, hi, hi', hj, hj'⟩ := ArithmeticRule.two_common_nonzero_of_four
    x hx (a : ZMod r) (z : ZMod r) B₁ C₁ (Or.inl (by rwa [ha])) (Or.inl hB₁)
  let c : Fin 4 → Column := fun k => ⟨r * k.val, by
    have := k.isLt; have := hp.one_lt; nlinarith⟩
  have agrees (k : Fin 4) (hk : (a : ZMod r) * x k + (z : ZMod r) ≠ 0)
      (hk' : B₁ * x k + C₁ ≠ 0) :
      (a : ZMod r) * x k + (z : ZMod r) = B₁ * x k + C₁ := by
    have hcv : ((c k).val : ℤ) = (r : ℤ) * k.val := by simp only [c, Nat.cast_mul]
    have he : a * (c k).val + b = (r : ℤ) * (a * k.val + z) := by
      rw [hcv, hz]; ring
    have hn : ¬ (r : ℤ) ∣ a * k.val + z := by
      intro hd
      apply hk
      simpa only [x, Int.cast_add, Int.cast_mul, Int.cast_natCast] using
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ r).mpr hd
    have hr0 : (r : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hp.ne_zero
    have hn2 : ¬ (r : ℤ) ^ 2 ∣ a * (c k).val + b := by
      intro hd
      apply hn
      apply (Int.mul_dvd_mul_iff_left hr0).mp
      simpa only [he, pow_two] using hd
    have ht' := (arithmetic_tests r _ a b hab ht (c k)).2
      ⟨a * k.val + z, he⟩ hn2
    simp only [one_mul, add_zero] at ht'
    rw [he, Int.mul_ediv_cancel_left _ hr0, hcv] at ht'
    simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast] at ht'
    have hnform : A₁ * ((c k).val : ZMod r) + B₁ * (k.val : ZMod r) + C₁ =
        B₁ * x k + C₁ := by
      simp [c, x]
    have hh := hH₁.2 (c k) (k.val : ℤ) (by
      simpa only [Int.cast_natCast, hnform] using hk')
    simp only [arithmeticReparametrize, zero_mul, add_zero] at hh
    exact ht'.symm.trans (by simpa only [Int.cast_natCast, hnform, x] using hh)
  obtain ⟨hcoeff, _⟩ := ArithmeticRule.affine_coefficients_eq_of_two
    (fun he => hij (hx he)) (agrees i hi hi') (agrees j hj hj')
  exact hcoeff.symm.trans ha

end TranslationTiling.Sudoku
