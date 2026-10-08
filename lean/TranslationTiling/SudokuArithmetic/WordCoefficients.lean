import TranslationTiling.SudokuArithmetic.Congruence

/-! Recovering decorated word coefficients from four arithmetic samples. -/

set_option maxRecDepth 2000

namespace TranslationTiling.Sudoku

theorem affine_eq_from_four {K : Type*} [Field K] (x f : Fin 4 → K)
    (hx : Function.Injective x) (a b c d : K) (hab : a ≠ 0 ∨ b ≠ 0)
    (hcd : c ≠ 0 ∨ d ≠ 0)
    (hf : ∀ k, a * x k + b ≠ 0 → f k = a * x k + b)
    (hg : ∀ k, c * x k + d ≠ 0 → f k = c * x k + d) : a = c ∧ b = d := by
  obtain ⟨i, j, hij, hi, hi', hj, hj'⟩ :=
    ArithmeticRule.two_common_nonzero_of_four x hx a b c d hab hcd
  exact ArithmeticRule.affine_coefficients_eq_of_two (fun he => hij (hx he))
    ((hf i hi).symm.trans (hg i hi')) ((hf j hj).symm.trans (hg j hj'))

def sample (k : Fin 4) : Column :=
  ⟨k.val + 1, by
    have := k.isLt
    have : 5 < Width := by decide
    omega⟩

def primeSample (r : ℕ) (hr : r ^ 2 ≤ Width) (hlarge : 200 < r) (k : Fin 4) : Column :=
  ⟨r * (k.val + 1), by have := k.isLt; nlinarith⟩

theorem sample_injective_mod (r : ℕ) (hlarge : 200 < r) :
    Function.Injective (fun k : Fin 4 => ((sample k).val : ZMod r)) := by
  simpa only [sample, Nat.cast_add, Nat.cast_one, Int.cast_add, Int.cast_natCast, Int.cast_one,
    add_comm (1 : ZMod r)] using
    (ArithmeticRule.four_residues_injective (p := r) (by omega) 1)

theorem word_coefficients_from_four (r : ℕ) (hp : r.Prime) (hlarge : 200 < r)
    (V : Column → (ZMod r)ˣ) (a b : ℤ)
    (hab : ¬ (r : ℤ) ∣ a ∨ ¬ (r : ℤ) ∣ b)
    (ht : ∀ n, ¬ (r : ℤ) ∣ a * n.val + b →
      (V n).val = ((a * n.val + b : ℤ) : ZMod r))
    (c d : ZMod r) (hcd : c ≠ 0 ∨ d ≠ 0)
    (hvals : ∀ k, c * ((sample k).val : ZMod r) + d ≠ 0 →
      (V (sample k)).val = c * ((sample k).val : ZMod r) + d) :
    (a : ZMod r) = c ∧ (b : ZMod r) = d := by
  let : Fact r.Prime := ⟨hp⟩
  apply affine_eq_from_four _ (fun k => (V (sample k)).val)
    (sample_injective_mod r hlarge) (a : ZMod r) (b : ZMod r) c d
    (by simpa only [ne_eq, ZMod.intCast_zmod_eq_zero_iff_dvd] using hab) hcd
    ?_ hvals
  intro k hk
  have hn : ¬ (r : ℤ) ∣ a * (sample k).val + b := by
    intro hd
    apply hk
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_natCast] using
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ r).mpr hd
  simpa only [Int.cast_add, Int.cast_mul, Int.cast_natCast] using ht (sample k) hn

/-- The valuation-one samples force the intercept to vanish modulo `r²`. -/
theorem scaled_word_coefficients (r : ℕ) (hp : r.Prime) (hlarge : 200 < r)
    (hr : r ^ 2 ≤ Width) (V : Column → (ZMod r)ˣ) (a b : ℤ)
    (hab : ¬ (r : ℤ) ∣ a ∨ ¬ (r : ℤ) ∣ b)
    (ht : ∀ n u, lowValuation r (a * n.val + b) = some u → u ≤ threshold r a →
      (V n).val = lowDigit r (a * n.val + b))
    (c : ZMod r) (hc : c ≠ 0)
    (hsmall : ∀ k, (V (sample k)).val = c * ((sample k).val : ZMod r))
    (hprime : ∀ k, (V (primeSample r hr hlarge k)).val = c * ((sample k).val : ZMod r)) :
    (a : ZMod r) = c ∧ (r : ℤ) ^ 2 ∣ b := by
  let : Fact r.Prime := ⟨hp⟩
  obtain ⟨ha, hb⟩ := word_coefficients_from_four r hp hlarge V a b hab
    (fun n => (arithmetic_tests r V a b hab ht n).1) c 0 (Or.inl hc)
    (fun k _ => by simpa only [add_zero] using hsmall k)
  have hbd : (r : ℤ) ∣ b := (ZMod.intCast_zmod_eq_zero_iff_dvd _ r).mp hb
  obtain ⟨z, hz⟩ := hbd
  have ha0 : (a : ZMod r) ≠ 0 := by rwa [ha]
  have hz0 : (z : ZMod r) = 0 := by
    apply (affine_eq_from_four
      (fun k => ((sample k).val : ZMod r))
      (fun k => (V (primeSample r hr hlarge k)).val)
      (sample_injective_mod r hlarge) (a : ZMod r) (z : ZMod r) c 0
      (Or.inl ha0) (Or.inl hc) ?_ (fun k _ => by simpa using hprime k)).2
    intro k hk
    let n := primeSample r hr hlarge k
    have hnv : (n.val : ℤ) = (r : ℤ) * (sample k).val := by
      simp only [n, primeSample, sample, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    have he : a * n.val + b = (r : ℤ) * (a * (sample k).val + z) := by
      rw [hnv, hz]; ring
    have hnd : ¬ (r : ℤ) ∣ a * (sample k).val + z := by
      intro hd
      apply hk
      simpa only [Int.cast_add, Int.cast_mul, Int.cast_natCast] using
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ r).mpr hd
    have hr0 : (r : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hp.ne_zero
    have hnd2 : ¬ (r : ℤ) ^ 2 ∣ a * n.val + b := by
      intro hd
      apply hnd
      apply (Int.mul_dvd_mul_iff_left hr0).mp
      simpa only [he, pow_two] using hd
    have hh := (arithmetic_tests r V a b hab ht n).2 ⟨a * (sample k).val + z, he⟩ hnd2
    rw [he, Int.mul_ediv_cancel_left _ hr0] at hh
    simpa only [n, Int.cast_add, Int.cast_mul, Int.cast_natCast] using hh
  have hzdiv := (ZMod.intCast_zmod_eq_zero_iff_dvd z r).mp hz0
  refine ⟨ha, ?_⟩
  obtain ⟨t, ht⟩ := hzdiv
  exact ⟨t, by rw [hz, ht, pow_two, mul_assoc]⟩

end TranslationTiling.Sudoku
