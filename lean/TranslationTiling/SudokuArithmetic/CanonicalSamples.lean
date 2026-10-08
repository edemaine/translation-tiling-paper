import TranslationTiling.SudokuArithmetic.Decorations

/-! Sample arithmetic on the lines used to read Wang adjacencies. -/

namespace TranslationTiling.Sudoku

theorem sample_not_dvd (r : ℕ) (hlarge : 200 < r) (k : Fin 4) :
    ¬ (r : ℤ) ∣ (sample k).val := by
  intro hd
  have hk := k.isLt
  exact Nat.not_dvd_of_pos_of_lt (by simp [sample]) (by simp only [sample]; omega)
    (Int.natCast_dvd_natCast.mp hd)

theorem digit_mul_unit (r : ℕ) (hp : r.Prime) {M n : ℤ} (hM : M ≠ 0)
    (hn : ¬ (r : ℤ) ∣ n) :
    M * n ≠ 0 ∧ padicValInt r (M * n) = padicValInt r M ∧
      (lastDigit r hp (M * n)).val = (lastDigit r hp M).val * (n : ZMod r) := by
  let : Fact r.Prime := ⟨hp⟩
  have hn0 : n ≠ 0 := fun he => hn (he ▸ dvd_zero _)
  have hncast : (n : ZMod r) ≠ 0 := by
    simpa only [ne_eq, ZMod.intCast_zmod_eq_zero_iff_dvd] using hn
  have hfcast : (pFreeQuotient r M : ZMod r) ≠ 0 := by
    simpa only [ne_eq, ZMod.intCast_zmod_eq_zero_iff_dvd] using pFreeQuotient_not_dvd r hp hM
  have hfn : ¬ (r : ℤ) ∣ pFreeQuotient r M * n := by
    intro hd
    have hh := (ZMod.intCast_zmod_eq_zero_iff_dvd _ r).mpr hd
    rw [Int.cast_mul] at hh
    exact mul_ne_zero hfcast hncast hh
  refine ⟨mul_ne_zero hM hn0, ?_, ?_⟩
  · rw [padicValInt.mul hM hn0, padicValInt.eq_zero_of_not_dvd hn, add_zero]
  · have he : M * n = (r : ℤ) ^ padicValInt r M * (pFreeQuotient r M * n) := by
      rw [← mul_assoc, ← pFreeQuotient_factor r hp M]
    rw [he, lastDigit_mul_prime_pow, lastDigit_eq_of_not_dvd r hp hfn,
      lastDigit_val_of_ne_zero r hp hM, Int.cast_mul]

theorem canonical_scaled_coefficients (r : ℕ) (hp : r.Prime) (hlarge : 200 < r)
    (hr : r ^ 2 ≤ Width) {V : Column → ℤ → (ZMod r)ˣ} {B : ZMod r} {K : ℕ}
    (hC : CanonicalArithmetic r hp V B K) (M : ℤ) (hM : M ≠ 0)
    (hdepth : padicValInt r M + 1 ≤ K) (a b : ℤ)
    (hab : ¬ (r : ℤ) ∣ a ∨ ¬ (r : ℤ) ∣ b)
    (ht : ∀ n u, lowValuation r (a * n.val + b) = some u → u ≤ threshold r a →
      (V n (M * n.val)).val = lowDigit r (a * n.val + b)) :
    (a : ZMod r) = B * (lastDigit r hp M).val ∧ (r : ℤ) ^ 2 ∣ b := by
  let : Fact r.Prime := ⟨hp⟩
  apply scaled_word_coefficients r hp hlarge hr (fun n => V n (M * n.val)) a b hab ht
    (B * (lastDigit r hp M).val) (mul_ne_zero hC.1 (Units.ne_zero _))
  · intro k
    obtain ⟨hnz, hv, hd⟩ := digit_mul_unit r hp hM (sample_not_dvd r hlarge k)
    rw [hC.2 (sample k) _ hnz (by rw [hv]; omega), hd]
    simp only [Int.cast_natCast, mul_assoc]
  · intro k
    obtain ⟨hnz, hv, hd⟩ := digit_mul_unit r hp hM (sample_not_dvd r hlarge k)
    have hr0 : (r : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hp.ne_zero
    have he : M * (primeSample r hr hlarge k).val = (r : ℤ) * (M * (sample k).val) := by
      simp only [primeSample, sample, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      ring
    have hv' : padicValInt r (M * (primeSample r hr hlarge k).val) = padicValInt r M + 1 := by
      rw [he, padicValInt.mul hr0 hnz, padicValInt_self, hv]
      omega
    rw [hC.2 _ _ (by rw [he]; exact mul_ne_zero hr0 hnz) (by rwa [hv']), he]
    rw [show (r : ℤ) * (M * (sample k).val) = (r : ℤ) ^ 1 * (M * (sample k).val) by rw [pow_one],
      lastDigit_mul_prime_pow, hd]
    simp only [Int.cast_natCast, mul_assoc]

end TranslationTiling.Sudoku
