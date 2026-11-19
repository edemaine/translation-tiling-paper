import TranslationTiling.SudokuArithmetic.PairSamples

namespace TranslationTiling.Sudoku.NineArithmetic
noncomputable section

/-- The three samples recover the coefficients on each of the canonical query lines. -/
def baseSample (r : ℕ) (i : Fin 3) : Column r := atColumn r (![0,1,4] i)

/-- Arithmetic compatibility on selected columns only. -/
def SelectedAgreement (r : ℕ) (S : Column r → Prop)
    (V : Column r → (ZMod r)ˣ) (a b : ℤ) : Prop :=
  ∀ n, S n → ∀ u, lowValuation r (a*position r n+b)=some u → u≤threshold r a →
    (V n).val=lowDigit r (a*position r n+b)

private def SampleCheck (r : ℕ) (d : ℤ) : Prop :=
  ∀ (a b c : ZMod r), (a≠0 ∨ b≠0) → c≠0 →
    (∀ i : Fin 3, a*(position r (baseSample r i):ZMod r)+b≠0 →
      a*(position r (baseSample r i):ZMod r)+b=c*((d:ZMod r)*position r (baseSample r i)+1)) →
    a=c*(d:ZMod r) ∧ b=c

private instance (r : ℕ) [NeZero r] (d : ℤ) : Decidable (SampleCheck r d) := by
  unfold SampleCheck
  infer_instance

theorem sampleCheck (r : ℕ) (d : ℤ) (hr : r=5 ∨ r=7)
    (hd : d=0 ∨ d=2 ∨ d=3) : SampleCheck r d := by
  rcases hr with rfl|rfl <;> rcases hd with rfl|rfl|rfl <;> decide +kernel

theorem sample_units (r : ℕ) (d : ℤ) (hr : r=5 ∨ r=7)
    (hd : d=0 ∨ d=2 ∨ d=3) (i : Fin 3) :
    ¬ (r:ℤ) ∣ d*position r (baseSample r i)+1 := by
  rcases hr with rfl|rfl <;> rcases hd with rfl|rfl|rfl <;> fin_cases i <;> decide +kernel

theorem selected_coefficients (r : ℕ) (hp : r.Prime) (hr : r=5 ∨ r=7)
    {V : Column r → ℤ → (ZMod r)ˣ} {B : ZMod r} {K : ℕ}
    (hC : Canonical r hp V B K) (M d : ℤ) (hM : M≠0)
    (hd : d=0 ∨ d=2 ∨ d=3) (hdepth : padicValInt r M≤K) (a b : ℤ)
    (hab : ¬(r:ℤ)∣a ∨ ¬(r:ℤ)∣b) {S : Column r → Prop}
    (hs : ∀ i, S (baseSample r i))
    (ht : SelectedAgreement r S (fun n => V n (M*(d*position r n+1))) a b) :
    (a:ZMod r)=(B*(lastDigit r hp M).val)*(d:ZMod r) ∧
      (b:ZMod r)=B*(lastDigit r hp M).val := by
  letI : Fact r.Prime := ⟨hp⟩
  let c := B*(lastDigit r hp M).val
  have hc : c≠0 := mul_ne_zero hC.1 (Units.ne_zero _)
  apply sampleCheck r d hr hd (a:ZMod r) (b:ZMod r) c
    (by simpa only [ne_eq,ZMod.intCast_zmod_eq_zero_iff_dvd] using hab) hc
  intro i hi
  let n := baseSample r i
  have hn : ¬ (r:ℤ) ∣ a*position r n+b := by
    intro he
    apply hi
    exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ r).mpr he
  have hv := ht n (hs i) 0 (lowValuation_zero_of_cast_ne _ _ (by
    simpa only [Int.cast_add,Int.cast_mul,Int.cast_natCast] using hi)) (Nat.zero_le _)
  have hleft : (V n (M*(d*position r n+1))).val=(a:ZMod r)*position r n+b := by
    simpa only [lowDigit,if_neg hn,Int.cast_add,Int.cast_mul,Int.cast_natCast] using hv
  obtain ⟨hnz,hval,hdig⟩ := digit_mul_unit r hp hM (sample_units r d hr hd i)
  have hright := hC.2 n _ hnz (hval ▸ hdepth)
  rw [hdig] at hright
  rw [←hleft]
  simpa only [c,Int.cast_add,Int.cast_mul,Int.cast_natCast,Int.cast_one,mul_assoc] using hright


theorem canonical_root_value (r : ℕ) (hp : r.Prime)
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
theorem selected_root_one (r : ℕ) (hp : r.Prime) (hr : r=5 ∨ r=7)
    {V : Column r → ℤ → (ZMod r)ˣ} {B : ZMod r} {K : ℕ}
    (hC : Canonical r hp V B K) (M d : ℤ) (hM : M≠0)
    (hdepth : padicValInt r M+1≤K) (hrel : 2*d+1=(r:ℤ))
    (hd : ¬(r:ℤ)∣d) (hd1 : ¬(r:ℤ)∣d+1) (a b : ℤ)
    (hab : ¬(r:ℤ)∣a ∨ ¬(r:ℤ)∣b)
    {S : Column r → Prop} (hs : ∀ i, S (baseSample r i))
    (hx : S (atColumn r (2+r))) (hquery : d=0 ∨ d=2 ∨ d=3)
    (ht : SelectedAgreement r S (fun n => V n (M*(d*position r n+1))) a b) :
    lowValuation r (2*a+b)=some 1 := by
  letI : Fact r.Prime := ⟨hp⟩
  obtain ⟨ha,hb⟩ := selected_coefficients r hp hr hC M d hM hquery (by omega) a b hab hs ht
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
  let n1 := atColumn r (2+r)
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
    have hdiv1 : (r:ℤ) ∣ a*position r n1+b := ⟨z+a,he1⟩
    have hval : lowValuation r (a*position r n1+b)=some 1 := by
      simp [lowValuation,hdiv1,hsq]
    have haunit := primitive_slope_not_dvd r a b (position r n1) hab hdiv1
    have htest := ht n1 hx 1 hval (by simp [threshold,haunit])
    simp only [lowDigit,if_pos hdiv1] at htest
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
