import TranslationTiling.SudokuArithmetic.NineArithmetic
import TranslationTiling.SudokuArithmetic.CanonicalSamples

namespace TranslationTiling.Sudoku.NineArithmetic
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem affine_eq_from_four {K : Type*} [Field K] (x f : Fin 4 → K)
    (hx : Function.Injective x) (a b c d : K) (hab : a ≠ 0 ∨ b ≠ 0)
    (hcd : c ≠ 0 ∨ d ≠ 0)
    (hf : ∀ k, a * x k + b ≠ 0 → f k = a * x k + b)
    (hg : ∀ k, c * x k + d ≠ 0 → f k = c * x k + d) : a = c ∧ b = d := by
  obtain ⟨i, j, hij, hi, hi', hj, hj'⟩ :=
    ArithmeticRule.two_common_nonzero_of_four x hx a b c d hab hcd
  exact ArithmeticRule.affine_coefficients_eq_of_two (fun he => hij (hx he))
    ((hf i hi).symm.trans (hg i hi')) ((hf j hj).symm.trans (hg j hj'))

def sample (r : ℕ) (k : Fin 4) : Column r :=
  ⟨k.val+1,by have := k.isLt; have := prefix_width r; omega⟩
@[simp] theorem position_sample (r : ℕ) (k : Fin 4) : position r (sample r k)=k.val+1 := by
  simp [sample,position,NinePatch.position,show k.val+1<5 by have := k.isLt; omega]
def primeIndex (k : Fin 2) : Fin 4 := ⟨k.val,by have := k.isLt; omega⟩
def primeSample (r : ℕ) (_hr : r=5 ∨ r=7) (_hl : 4<r) (k : Fin 2) : Column r := atColumn r (r*(k.val+1))
@[simp] theorem position_primeSample (r : ℕ) (hr : r=5 ∨ r=7) (hl : 4<r) (k : Fin 2) : position r (primeSample r hr hl k)=r*(k.val+1) := by
  apply position_at hr
  rcases hr with rfl|rfl <;> fin_cases k <;> decide +kernel

theorem sample_injective_mod (r : ℕ) (hlarge : 4 < r)  :
    Function.Injective (fun k : Fin 4 => (position r (sample r k) : ZMod r)) := by
  simpa only [position_sample, Nat.cast_add, Nat.cast_one, Int.cast_add, Int.cast_natCast, Int.cast_one,
    add_comm (1 : ZMod r)] using
    (ArithmeticRule.four_residues_injective (p := r) (by omega) 1)

theorem word_coefficients_from_four (r : ℕ) (hp : r.Prime) (hlarge : 4 < r) 
    (V : (Column r) → (ZMod r)ˣ) (a b : ℤ)
    (hab : ¬ (r : ℤ) ∣ a ∨ ¬ (r : ℤ) ∣ b)
    (ht : ∀ n, ¬ (r : ℤ) ∣ a * (position r n) + b →
      (V n).val = ((a * (position r n) + b : ℤ) : ZMod r))
    (c d : ZMod r) (hcd : c ≠ 0 ∨ d ≠ 0)
    (hvals : ∀ k, c * (position r (sample r k) : ZMod r) + d ≠ 0 →
      (V (sample r k)).val = c * (position r (sample r k) : ZMod r) + d) :
    (a : ZMod r) = c ∧ (b : ZMod r) = d := by
  let : Fact r.Prime := ⟨hp⟩
  apply affine_eq_from_four _ (fun k => (V (sample r k)).val)
    (sample_injective_mod r hlarge) (a : ZMod r) (b : ZMod r) c d
    (by simpa only [ne_eq, ZMod.intCast_zmod_eq_zero_iff_dvd] using hab) hcd
    ?_ hvals
  intro k hk
  have hn : ¬ (r : ℤ) ∣ a * position r (sample r k) + b := by
    intro hd
    apply hk
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_natCast] using
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ r).mpr hd
  simpa only [Int.cast_add, Int.cast_mul, Int.cast_natCast] using ht (sample r k) hn

/-- The valuation-one samples force the intercept to vanish modulo `r²`. -/
theorem scaled_word_coefficients (r : ℕ) (hp : r.Prime) (hlarge : 4 < r)
    (hr : r=5 ∨ r=7) (V : (Column r) → (ZMod r)ˣ) (a b : ℤ)
    (hab : ¬ (r : ℤ) ∣ a ∨ ¬ (r : ℤ) ∣ b)
    (ht : ∀ n u, lowValuation r (a * (position r n) + b) = some u → u ≤ threshold r a →
      (V n).val = lowDigit r (a * (position r n) + b))
    (c : ZMod r) (hc : c ≠ 0)
    (hsmall : ∀ k, (V (sample r k)).val = c * (position r (sample r k) : ZMod r))
    (hprime : ∀ k, (V (primeSample r hr hlarge k)).val = c * (position r (sample r (primeIndex k)) : ZMod r)) :
    (a : ZMod r) = c ∧ (r : ℤ) ^ 2 ∣ b := by
  let : Fact r.Prime := ⟨hp⟩
  obtain ⟨ha, hb⟩ := word_coefficients_from_four r hp hlarge V a b hab
    (fun n => (arithmetic_tests r V a b hab ht n).1) c 0 (Or.inl hc)
    (fun k _ => by simpa only [add_zero] using hsmall k)
  have hbd : (r : ℤ) ∣ b := (ZMod.intCast_zmod_eq_zero_iff_dvd _ r).mp hb
  obtain ⟨z, hz⟩ := hbd
  have ha0 : (a : ZMod r) ≠ 0 := by rwa [ha]
  have agrees (k : Fin 2)
      (hk : (a:ZMod r)*(position r (sample r (primeIndex k)):ZMod r)+(z:ZMod r)≠0) :
      (a:ZMod r)*(position r (sample r (primeIndex k)):ZMod r)+(z:ZMod r)=
        (a:ZMod r)*(position r (sample r (primeIndex k)):ZMod r) := by
    let n := primeSample r hr hlarge k
    have hnv : (position r n : ℤ) = (r : ℤ) * position r (sample r (primeIndex k)) := by
      simp only [n, position_primeSample, position_sample, primeIndex, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    have he : a * (position r n) + b = (r : ℤ) * (a * position r (sample r (primeIndex k)) + z) := by
      rw [hnv, hz]; ring
    have hnd : ¬ (r : ℤ) ∣ a * position r (sample r (primeIndex k)) + z := by
      intro hd
      apply hk
      simpa only [Int.cast_add, Int.cast_mul, Int.cast_natCast] using
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ r).mpr hd
    have hr0 : (r : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hp.ne_zero
    have hnd2 : ¬ (r : ℤ) ^ 2 ∣ a * (position r n) + b := by
      intro hd
      apply hnd
      apply (Int.mul_dvd_mul_iff_left hr0).mp
      simpa only [he, pow_two] using hd
    have hh := (arithmetic_tests r V a b hab ht n).2 ⟨a * position r (sample r (primeIndex k)) + z, he⟩ hnd2
    rw [he, Int.mul_ediv_cancel_left _ hr0] at hh
    have hquot : (V n).val=(a:ZMod r)*(position r (sample r (primeIndex k)):ZMod r)+(z:ZMod r) := by
      simpa only [Int.cast_add,Int.cast_mul,Int.cast_natCast] using hh
    exact hquot.symm.trans (by simpa only [ha] using hprime k)
  have hz0 : (z:ZMod r)=0 := by
    have h1 : (a:ZMod r)+z≠0 → (a:ZMod r)+z=a := by
      simpa [position_sample,primeIndex] using agrees 0
    have h2 : 2*(a:ZMod r)+z≠0 → 2*(a:ZMod r)+z=2*a := by
      simpa [position_sample,primeIndex,mul_comm] using agrees 1
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

theorem constant_word_coefficients (r : ℕ) (hp : r.Prime) (hlarge : 4 < r) 
    (V : (Column r) → (ZMod r)ˣ) (a b : ℤ)
    (hab : ¬ (r : ℤ) ∣ a ∨ ¬ (r : ℤ) ∣ b)
    (ht : ∀ n u, lowValuation r (a * (position r n) + b) = some u → u ≤ threshold r a →
      (V n).val = lowDigit r (a * (position r n) + b))
    (c : ZMod r) (hc : c ≠ 0) (hvals : ∀ n, (V n).val = c) :
    (a : ZMod r) = 0 ∧ (b : ZMod r) = c := by
  apply word_coefficients_from_four r hp hlarge V a b hab
    (fun n => (arithmetic_tests r V a b hab ht n).1) 0 c (Or.inr hc)
  intro k _
  simpa only [zero_mul, zero_add] using hvals (sample r k)


def Canonical (r : ℕ) (hp : r.Prime) (V : Column r → ℤ → (ZMod r)ˣ)
    (B : ZMod r) (k : ℕ) : Prop :=
  B≠0 ∧ ∀ n m, m≠0 → padicValInt r m≤k →
    (V n m).val=B*(lastDigit r hp m).val

theorem sample_not_dvd (r : ℕ) (hlarge : 4 < r)  (k : Fin 4) :
    ¬ (r : ℤ) ∣ position r (sample r k) := by
  intro hd
  have hk := k.isLt
  exact Nat.not_dvd_of_pos_of_lt (by simp [position_sample]) (by simp only [position_sample]; omega)
    (Int.natCast_dvd_natCast.mp hd)

theorem canonical_scaled_coefficients (r : ℕ) (hp : r.Prime) (hlarge : 4 < r)
    (hr : r=5 ∨ r=7) {V : (Column r) → ℤ → (ZMod r)ˣ} {B : ZMod r} {K : ℕ}
    (hC : Canonical r hp V B K) (M : ℤ) (hM : M ≠ 0)
    (hdepth : padicValInt r M + 1 ≤ K) (a b : ℤ)
    (hab : ¬ (r : ℤ) ∣ a ∨ ¬ (r : ℤ) ∣ b)
    (ht : ∀ n u, lowValuation r (a * (position r n) + b) = some u → u ≤ threshold r a →
      (V n (M * (position r n))).val = lowDigit r (a * (position r n) + b)) :
    (a : ZMod r) = B * (lastDigit r hp M).val ∧ (r : ℤ) ^ 2 ∣ b := by
  let : Fact r.Prime := ⟨hp⟩
  apply scaled_word_coefficients r hp hlarge hr (fun n => V n (M * (position r n))) a b hab ht
    (B * (lastDigit r hp M).val) (mul_ne_zero hC.1 (Units.ne_zero _))
  · intro k
    obtain ⟨hnz, hv, hd⟩ := digit_mul_unit r hp hM (sample_not_dvd r hlarge k)
    rw [hC.2 (sample r k) _ hnz (by rw [hv]; omega), hd]
    simp only [Int.cast_natCast, mul_assoc]
  · intro k
    obtain ⟨hnz, hv, hd⟩ := digit_mul_unit r hp hM (sample_not_dvd r hlarge (primeIndex k))
    have hr0 : (r : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hp.ne_zero
    have he : M * position r (primeSample r hr hlarge k) = (r : ℤ) * (M * position r (sample r (primeIndex k))) := by
      simp only [position_primeSample, position_sample, primeIndex, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      ring
    have hv' : padicValInt r (M * position r (primeSample r hr hlarge k)) = padicValInt r M + 1 := by
      rw [he, padicValInt.mul hr0 hnz, padicValInt_self, hv]
      omega
    rw [hC.2 _ _ (by rw [he]; exact mul_ne_zero hr0 hnz) (by rwa [hv']), he]
    rw [show (r : ℤ) * (M * position r (sample r (primeIndex k))) = (r : ℤ) ^ 1 * (M * position r (sample r (primeIndex k))) by rw [pow_one],
      lastDigit_mul_prime_pow, hd]
    simp only [Int.cast_natCast, mul_assoc]


end
end TranslationTiling.Sudoku.NineArithmetic
