import TranslationTiling.SudokuArithmetic.NineSamples

namespace TranslationTiling.Sudoku.NineArithmetic
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
set_option Elab.async false

/-- Recover the primitive word coefficients on a shifted canonical line. -/
theorem canonical_shifted_coefficients (r : ℕ) (hp : r.Prime) (hlarge : 4<r)
    {V : Column r → ℤ → (ZMod r)ˣ} {B : ZMod r} {K : ℕ}
    (hC : Canonical r hp V B K) (M d : ℤ) (hM : M≠0)
    (hdepth : padicValInt r M≤K) (a b : ℤ)
    (hab : ¬(r:ℤ)∣a ∨ ¬(r:ℤ)∣b)
    (ht : ∀ n u, lowValuation r (a*position r n+b)=some u → u≤threshold r a →
      (V n (M*(d*position r n+1))).val=lowDigit r (a*position r n+b)) :
    (a:ZMod r)=(B*(lastDigit r hp M).val)*(d:ZMod r) ∧
      (b:ZMod r)=B*(lastDigit r hp M).val := by
  letI : Fact r.Prime := ⟨hp⟩
  let c := B*(lastDigit r hp M).val
  have hc : c≠0 := mul_ne_zero hC.1 (Units.ne_zero _)
  apply word_coefficients_from_four r hp hlarge
    (fun n => V n (M*(d*position r n+1))) a b hab
    (fun n => (arithmetic_tests r _ a b hab ht n).1) (c*d) c (Or.inr hc)
  intro k hk
  have hf : ¬(r:ℤ)∣d*position r (sample r k)+1 := by
    intro hd
    have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd _ r).mpr hd
    apply hk
    calc
      _ = c*((d*position r (sample r k)+1:ℤ):ZMod r) := by push_cast; ring
      _ = 0 := by rw [hz,mul_zero]
  obtain ⟨hnz,hv,hd⟩ := digit_mul_unit r hp hM hf
  have he := hC.2 (sample r k) _ hnz (hv ▸ hdepth)
  rw [hd] at he
  simpa only [c,Int.cast_add,Int.cast_mul,Int.cast_natCast,Int.cast_one,mul_add,mul_one,mul_assoc] using he

private theorem canonical_root_value (r : ℕ) (hp : r.Prime)
    {V : Column r → ℤ → (ZMod r)ˣ} {B : ZMod r} {K : ℕ}
    (hC : Canonical r hp V B K) (M d t : ℤ) (hM : M≠0)
    (hdepth : padicValInt r M+1≤K) (n : Column r)
    (he : d*position r n+1=(r:ℤ)*t) (ht : ¬(r:ℤ)∣t) :
    (V n (M*(d*position r n+1))).val=(B*(lastDigit r hp M).val)*(t:ZMod r) := by
  letI : Fact r.Prime := ⟨hp⟩
  obtain ⟨hnz,hv,hd⟩ := digit_mul_unit r hp hM ht
  have hr0 : (r:ℤ)≠0 := Int.natCast_ne_zero.mpr hp.ne_zero
  have harg : M*(d*position r n+1)=(r:ℤ)*(M*t) := by rw [he]; ring
  have hval : padicValInt r (M*(d*position r n+1))=padicValInt r M+1 := by
    rw [harg,padicValInt.mul hr0 hnz,padicValInt_self,hv]; omega
  rw [hC.2 n _ (by rw [harg]; exact mul_ne_zero hr0 hnz) (by rwa [hval]),harg]
  rw [show (r:ℤ)*(M*t)=(r:ℤ)^1*(M*t) by rw [pow_one],lastDigit_mul_prime_pow,hd]
  ring

/-- The two retained samples on the root fibre identify valuation one. -/
theorem shifted_root_one (r : ℕ) (hp : r.Prime) (hr : r=5 ∨ r=7)
    {V : Column r → ℤ → (ZMod r)ˣ} {B : ZMod r} {K : ℕ}
    (hC : Canonical r hp V B K) (M d : ℤ) (hM : M≠0)
    (hdepth : padicValInt r M+1≤K) (hrel : 2*d+1=(r:ℤ))
    (hd : ¬(r:ℤ)∣d) (hd1 : ¬(r:ℤ)∣d+1) (a b : ℤ)
    (hab : ¬(r:ℤ)∣a ∨ ¬(r:ℤ)∣b)
    (ht : ∀ n u, lowValuation r (a*position r n+b)=some u → u≤threshold r a →
      (V n (M*(d*position r n+1))).val=lowDigit r (a*position r n+b)) :
    lowValuation r (2*a+b)=some 1 := by
  letI : Fact r.Prime := ⟨hp⟩
  have hl : 4<r := by rcases hr with rfl|rfl <;> decide
  obtain ⟨ha,hb⟩ := canonical_shifted_coefficients r hp hl hC M d hM (by omega) a b hab ht
  let c := B*(lastDigit r hp M).val
  have hc : c≠0 := mul_ne_zero hC.1 (Units.ne_zero _)
  have hd' : (d:ZMod r)≠0 := by simpa [ZMod.intCast_zmod_eq_zero_iff_dvd] using hd
  have ha0 : (a:ZMod r)≠0 := by rw [ha]; exact mul_ne_zero hc hd'
  have hdiv : (r:ℤ)∣2*a+b := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ r).mp
    have hrr := congrArg (fun z : ℤ => (z:ZMod r)) hrel
    push_cast at hrr ⊢
    simp only [ZMod.natCast_self] at hrr
    rw [ha,hb]
    change 2*(c*d)+c=0
    linear_combination c*hrr
  obtain ⟨z,hz⟩ := hdiv
  let n0 := atColumn r 2
  let n1 := atColumn r (2+r)
  have hn0 : position r n0=2 := position_at hr _ (by omega)
  have hn1 : position r n1=2+r := position_at hr _ (by omega)
  have hr0 : (r:ℤ)≠0 := Int.natCast_ne_zero.mpr hp.ne_zero
  have he1 : a*position r n1+b=(r:ℤ)*(z+a) := by
    rw [hn1]; push_cast; linear_combination hz
  have hz0 : ¬(r:ℤ)∣z := by
    intro hdv
    have hzc : (z:ZMod r)=0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ r).mpr hdv
    have hza : ¬(r:ℤ)∣z+a := by
      intro hh
      have he := (ZMod.intCast_zmod_eq_zero_iff_dvd _ r).mpr hh
      apply ha0
      simpa [Int.cast_add,hzc] using he
    have hsq : ¬(r:ℤ)^2∣a*position r n1+b := by
      intro hh
      apply hza
      apply (Int.mul_dvd_mul_iff_left hr0).mp
      simpa only [he1,pow_two] using hh
    have htest := (arithmetic_tests r _ a b hab ht n1).2 ⟨z+a,he1⟩ hsq
    rw [he1,Int.mul_ediv_cancel_left _ hr0] at htest
    have hcanon := canonical_root_value r hp hC M d (d+1) hM hdepth n1 (by
      rw [hn1]; push_cast; linear_combination hrel) hd1
    have hh := htest.symm.trans hcanon
    simp only [Int.cast_add,Int.cast_one,hzc,zero_add,ha] at hh
    change c*d=c*(d+1) at hh
    apply hc
    linear_combination -hh
  have hsq : ¬(r:ℤ)^2∣2*a+b := by
    intro hh
    apply hz0
    apply (Int.mul_dvd_mul_iff_left hr0).mp
    simpa only [hz,pow_two] using hh
  simp [lowValuation,show (r:ℤ)∣2*a+b from ⟨z,hz⟩,hsq]

end
end TranslationTiling.Sudoku.NineArithmetic
