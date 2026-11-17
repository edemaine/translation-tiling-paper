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

def primeIndex (k : Fin 2) : Fin 4 := ⟨k.val,by have := k.isLt; omega⟩

def primeSample (r : ℕ) (hr : ArithmeticRule.wordWidth r ≤ Width) (hlarge : 10 < r) (k : Fin 2) : Column :=
  ⟨r * (k.val + 1), by have := k.isLt; nlinarith⟩

theorem sample_injective_mod (r : ℕ) (hlarge : 10 < r) :
    Function.Injective (fun k : Fin 4 => ((sample k).val : ZMod r)) := by
  simpa only [sample, Nat.cast_add, Nat.cast_one, Int.cast_add, Int.cast_natCast, Int.cast_one,
    add_comm (1 : ZMod r)] using
    (ArithmeticRule.four_residues_injective (p := r) (by omega) 1)

theorem word_coefficients_from_four (r : ℕ) (hp : r.Prime) (hlarge : 10 < r)
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
theorem scaled_word_coefficients (r : ℕ) (hp : r.Prime) (hlarge : 10 < r)
    (hr : ArithmeticRule.wordWidth r ≤ Width) (V : Column → (ZMod r)ˣ) (a b : ℤ)
    (hab : ¬ (r : ℤ) ∣ a ∨ ¬ (r : ℤ) ∣ b)
    (ht : ∀ n u, lowValuation r (a * n.val + b) = some u → u ≤ threshold r a →
      (V n).val = lowDigit r (a * n.val + b))
    (c : ZMod r) (hc : c ≠ 0)
    (hsmall : ∀ k, (V (sample k)).val = c * ((sample k).val : ZMod r))
    (hprime : ∀ k, (V (primeSample r hr hlarge k)).val = c * ((sample (primeIndex k)).val : ZMod r)) :
    (a : ZMod r) = c ∧ (r : ℤ) ^ 2 ∣ b := by
  let : Fact r.Prime := ⟨hp⟩
  obtain ⟨ha, hb⟩ := word_coefficients_from_four r hp hlarge V a b hab
    (fun n => (arithmetic_tests r V a b hab ht n).1) c 0 (Or.inl hc)
    (fun k _ => by simpa only [add_zero] using hsmall k)
  have hbd : (r : ℤ) ∣ b := (ZMod.intCast_zmod_eq_zero_iff_dvd _ r).mp hb
  obtain ⟨z, hz⟩ := hbd
  have ha0 : (a : ZMod r) ≠ 0 := by rwa [ha]
  have agrees (k : Fin 2)
      (hk : (a:ZMod r)*((sample (primeIndex k)).val:ZMod r)+(z:ZMod r)≠0) :
      (a:ZMod r)*((sample (primeIndex k)).val:ZMod r)+(z:ZMod r)=
        (a:ZMod r)*((sample (primeIndex k)).val:ZMod r) := by
    let n := primeSample r hr hlarge k
    have hnv : (n.val : ℤ) = (r : ℤ) * (sample (primeIndex k)).val := by
      simp only [n, primeSample, sample, primeIndex, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    have he : a * n.val + b = (r : ℤ) * (a * (sample (primeIndex k)).val + z) := by
      rw [hnv, hz]; ring
    have hnd : ¬ (r : ℤ) ∣ a * (sample (primeIndex k)).val + z := by
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
    have hh := (arithmetic_tests r V a b hab ht n).2 ⟨a * (sample (primeIndex k)).val + z, he⟩ hnd2
    rw [he, Int.mul_ediv_cancel_left _ hr0] at hh
    have hquot : (V n).val=(a:ZMod r)*((sample (primeIndex k)).val:ZMod r)+(z:ZMod r) := by
      simpa only [Int.cast_add,Int.cast_mul,Int.cast_natCast] using hh
    exact hquot.symm.trans (by simpa only [ha] using hprime k)
  have hz0 : (z:ZMod r)=0 := by
    have h1 : (a:ZMod r)+z≠0 → (a:ZMod r)+z=a := by
      simpa [sample,primeIndex] using agrees 0
    have h2 : 2*(a:ZMod r)+z≠0 → 2*(a:ZMod r)+z=2*a := by
      simpa [sample,primeIndex,mul_comm] using agrees 1
    by_cases he1 : (a:ZMod r)+z=0
    · have he2 : 2*(a:ZMod r)+z≠0 := by
        intro h
        apply ha0
        linear_combination h-he1
      linear_combination h2 he2
    · linear_combination h1 he1
  have hzdiv := (ZMod.intCast_zmod_eq_zero_iff_dvd z r).mp hz0
  refine ⟨ha, ?_⟩
  obtain ⟨t, ht⟩ := hzdiv
  exact ⟨t, by rw [hz, ht, pow_two, mul_assoc]⟩

end TranslationTiling.Sudoku
