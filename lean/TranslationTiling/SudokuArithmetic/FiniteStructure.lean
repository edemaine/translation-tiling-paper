import TranslationTiling.SudokuArithmetic.Normalize

/-! Finite-depth arithmetic classification. No p-adic compactness is needed. -/

namespace TranslationTiling.Sudoku

theorem normalized_finite_structure {r : ℕ} (hp : r.Prime) (hlarge : 200 < r)
    (hr : r ^ 2 ≤ Width) (k : ℕ) :
    ∀ (V : Column → ℤ → (ZMod r)ˣ) (B : ZMod r), ArithmeticLineRule r V →
      B ≠ 0 → FullAffineApproximation V 0 B 0 →
      ∃ D E : ℤ, (r : ℤ) ∣ D ∧ (r : ℤ) ∣ E ∧
        ∀ (n : Column) (m : ℤ), m - D * n.val - E ≠ 0 →
          padicValInt r (m - D * n.val - E) ≤ k →
          (V n m).val = B * (lastDigit r hp (m - D * n.val - E)).val := by
  let : Fact r.Prime := ⟨hp⟩
  have hr0 : (r : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hp.ne_zero
  induction k with
  | zero =>
    intro V B hV hB hH
    refine ⟨0, 0, dvd_zero _, dvd_zero _, ?_⟩
    intro n m hm hv
    simp only [zero_mul, sub_zero] at hm hv ⊢
    have hnd : ¬ (r : ℤ) ∣ m := by
      intro hd
      have hh := (padicValInt_dvd_iff (p := r) 1 m).mp (by simpa using hd)
      rcases hh with hh | hh <;> omega
    have hmc : (m : ZMod r) ≠ 0 := by
      simpa only [ne_eq, ZMod.intCast_zmod_eq_zero_iff_dvd] using hnd
    have hh := hH.2 n m (by simpa using mul_ne_zero hB hmc)
    simpa only [zero_mul, zero_add, add_zero, lastDigit_eq_of_not_dvd r hp hnd] using hh
  | succ k ih =>
    intro V B hV hB hH
    let S := arithmeticReparametrize V r 0 0
    have hS : ArithmeticLineRule r S := arithmeticReparametrize_lineRule hV r 0 0
    obtain ⟨A₁, B₁, C₁, hH₁⟩ := arithmetic_initial_affine r hr hp hlarge S hS
    have hB₁ := rescale_vertical_coefficient hp hlarge hr hV hB hH hH₁
    subst B₁
    obtain ⟨u, hu⟩ := ZMod.intCast_surjective (-(B⁻¹ * A₁))
    obtain ⟨v, hv⟩ := ZMod.intCast_surjective (-(B⁻¹ * C₁))
    let S₀ := arithmeticReparametrize S 1 u v
    have hS₀ : ArithmeticLineRule r S₀ := arithmeticReparametrize_lineRule hS 1 u v
    have hN : FullAffineApproximation S₀ 0 B 0 := hH₁.straighten hp hB u v hu hv
    obtain ⟨D, E, _, _, hdepth⟩ := ih S₀ B hS₀ hB hN
    let D' := (r : ℤ) * (u + D)
    let E' := (r : ℤ) * (v + E)
    refine ⟨D', E', ⟨u + D, rfl⟩, ⟨v + E, rfl⟩, ?_⟩
    intro n m hm hval
    by_cases hmd : (r : ℤ) ∣ m
    · obtain ⟨t, rfl⟩ := hmd
      let s := t - u * (n.val : ℤ) - v
      have he : (r : ℤ) * t - D' * n.val - E' =
          (r : ℤ) * (s - D * n.val - E) := by dsimp [D', E', s]; ring
      have hnz : s - D * n.val - E ≠ 0 := by
        intro hz
        apply hm
        rw [he, hz, mul_zero]
      have hv' : padicValInt r (s - D * n.val - E) ≤ k := by
        rw [he, padicValInt.mul hr0 hnz, padicValInt_self] at hval
        omega
      have hh := hdepth n s hnz hv'
      have harg : (r : ℤ) * (1 * s + u * n.val + v) + 0 * n.val + 0 = r * t := by
        dsimp [s]; ring
      simp only [S₀, S, arithmeticReparametrize, harg] at hh
      rw [he, show (r : ℤ) * (s - D * n.val - E) =
        (r : ℤ) ^ 1 * (s - D * n.val - E) by rw [pow_one], lastDigit_mul_prime_pow]
      exact hh
    · have hDc : (D' : ZMod r) = 0 := by simp [D']
      have hEc : (E' : ZMod r) = 0 := by simp [E']
      have hzc : ((m - D' * n.val - E' : ℤ) : ZMod r) = (m : ZMod r) := by
        simp only [Int.cast_sub, Int.cast_mul, Int.cast_natCast, hDc, hEc, zero_mul, sub_zero]
      have hm0 : (m : ZMod r) ≠ 0 := by
        simpa only [ne_eq, ZMod.intCast_zmod_eq_zero_iff_dvd] using hmd
      have hznd : ¬ (r : ℤ) ∣ m - D' * n.val - E' := by
        intro hd
        apply hm0
        rw [← hzc]
        exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ r).mpr hd
      rw [lastDigit_eq_of_not_dvd r hp hznd, hzc]
      simpa only [zero_mul, zero_add, add_zero] using
        hH.2 n m (by simpa using mul_ne_zero hB hm0)

/-- At any finite valuation depth, a nonconstant arithmetic solution is a
constant multiple of the last nonzero digit of a sheared height. -/
theorem arithmetic_finite_structure {r : ℕ} (hp : r.Prime) (hlarge : 200 < r)
    (hr : r ^ 2 ≤ Width) (V : Column → ℤ → (ZMod r)ˣ)
    (hV : ArithmeticLineRule r V) (hcols : ∀ n, ∃ m m', V n m ≠ V n m') (k : ℕ) :
    ∃ (D E : ℤ) (B : ZMod r), B ≠ 0 ∧
      ∀ (n : Column) (m : ℤ), m - D * n.val - E ≠ 0 →
        padicValInt r (m - D * n.val - E) ≤ k →
        (V n m).val = B * (lastDigit r hp (m - D * n.val - E)).val := by
  let : Fact r.Prime := ⟨hp⟩
  obtain ⟨A, B, C, hB, hH⟩ := arithmetic_initial_structure r hr hp hlarge V hV hcols
  obtain ⟨u, hu⟩ := ZMod.intCast_surjective (-(B⁻¹ * A))
  obtain ⟨v, hv⟩ := ZMod.intCast_surjective (-(B⁻¹ * C))
  let V₀ := arithmeticReparametrize V 1 u v
  have hN : FullAffineApproximation V₀ 0 B 0 :=
    FullAffineApproximation.straighten hp ⟨Or.inr (Or.inl hB), hH⟩ hB u v hu hv
  obtain ⟨D, E, _, _, hdepth⟩ := normalized_finite_structure hp hlarge hr k V₀ B
    (arithmeticReparametrize_lineRule hV 1 u v) hB hN
  refine ⟨u + D, v + E, B, hB, ?_⟩
  intro n m hm hval
  let s := m - u * (n.val : ℤ) - v
  have he : s - D * n.val - E = m - (u + D) * n.val - (v + E) := by
    dsimp [s]; ring
  have hh := hdepth n s (by rwa [he]) (by rwa [he])
  have harg : 1 * s + u * n.val + v = m := by dsimp [s]; ring
  simpa only [V₀, arithmeticReparametrize, harg, he] using hh

end TranslationTiling.Sudoku
