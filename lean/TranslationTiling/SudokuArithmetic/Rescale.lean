import TranslationTiling.SudokuArithmetic.Reparametrize

/-! Compatibility of the initial affine form with removal of one prime factor. -/

set_option maxRecDepth 2000

namespace TranslationTiling.Sudoku

theorem FullAffineApproximation.nonconstant {r : ℕ} (hp : r.Prime)
    (hlarge : 4 < r) {V : Column → ℤ → (ZMod r)ˣ} {A B C : ZMod r}
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

theorem normalized_line_coefficients {r : ℕ} (hp : r.Prime) (hlarge : 4 < r)
    {V : Column → ℤ → (ZMod r)ˣ} {B : ZMod r}
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
theorem rescale_vertical_coefficient {r : ℕ} (hp : r.Prime) (hlarge : 4 < r)
    (hr : ArithmeticRule.wordWidth r ≤ Width) {V : Column → ℤ → (ZMod r)ˣ} (hV : ArithmeticLineRule r V)
    {B A₁ B₁ C₁ : ZMod r} (hB : B ≠ 0) (hH : FullAffineApproximation V 0 B 0)
    (hH₁ : FullAffineApproximation (arithmeticReparametrize V r 0 0) A₁ B₁ C₁) :
    B₁ = B := by
  let : Fact r.Prime := ⟨hp⟩
  have hB₁ : B₁ ≠ 0 := ArithmeticRule.rescale_vertical_coefficient_ne_zero hp hlarge
    (arithmeticRestriction_lineRule r hr V hV) hB (hH.restrict hr)
    (by simpa only [ArithmeticRule.AffineApproximation, arithmeticRestriction,
      arithmeticReparametrize, zero_mul,
      add_zero, ArithmeticRule.rescale] using hH₁.restrict hr)
  have htwo : (2:ZMod r)≠0 := by
    intro h
    have hd := (ZMod.natCast_eq_zero_iff 2 r).mp h
    exact Nat.not_dvd_of_pos_of_lt (by decide) (by omega) hd
  have hshift : ∃ t : ℤ, ∀ k : Fin 3, B₁*((t+k.val:ℤ):ZMod r)+C₁≠0 := by
    obtain ⟨t,ht⟩ := ZMod.intCast_surjective (1-B₁⁻¹*C₁)
    have hbase : B₁*(t:ZMod r)+C₁=B₁ := by
      rw [ht]
      calc
        _ = B₁-(B₁*B₁⁻¹)*C₁+C₁ := by ring
        _ = B₁ := by rw [mul_inv_cancel₀ hB₁]; ring
    refine ⟨t,fun k => ?_⟩
    have hk : ((k.val+1:ℕ):ZMod r)≠0 := by
      intro hz
      have hv := congrArg ZMod.val hz
      rw [ZMod.val_natCast_of_lt (by have := k.isLt; omega),ZMod.val_zero] at hv
      omega
    have he : B₁*((t+k.val:ℤ):ZMod r)+C₁=B₁*((k.val+1:ℕ):ZMod r) := by
      push_cast
      linear_combination hbase
    rw [he]
    exact mul_ne_zero hB₁ hk
  obtain ⟨t,htnonzero⟩ := hshift
  obtain ⟨a,b,hab,ht⟩ := hV 1 ((r:ℤ)*t)
  obtain ⟨ha,hb⟩ := normalized_line_coefficients hp hlarge hH hB 1 ((r:ℤ)*t) a b hab ht (Or.inl (by simp))
  simp only [Int.cast_one,mul_one,Int.cast_mul,Int.cast_natCast,ZMod.natCast_self,zero_mul,mul_zero] at ha hb
  have hbd : (r:ℤ)∣b := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hb
  obtain ⟨z,hz⟩ := hbd
  have ha0 : (a:ZMod r)≠0 := by rwa [ha]
  let c : Fin 3 → Column := fun k => ⟨r*k.val,by
    have hk := k.isLt
    have hr' : 2*r+2≤Width := hr
    nlinarith⟩
  have agrees (k : Fin 3) (hk : (a:ZMod r)*(k.val:ZMod r)+(z:ZMod r)≠0) :
      (a:ZMod r)*(k.val:ZMod r)+(z:ZMod r)=B₁*(k.val:ZMod r)+(B₁*(t:ZMod r)+C₁) := by
    have hcv : ((c k).val:ℤ)=(r:ℤ)*k.val := by simp only [c,Nat.cast_mul]
    have he : a*(c k).val+b=(r:ℤ)*(a*k.val+z) := by rw [hcv,hz]; ring
    have hn : ¬(r:ℤ)∣a*k.val+z := by
      intro hd
      apply hk
      simpa only [Int.cast_add,Int.cast_mul,Int.cast_natCast] using
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ r).mpr hd
    have hr0 : (r:ℤ)≠0 := Int.natCast_ne_zero.mpr hp.ne_zero
    have hn2 : ¬(r:ℤ)^2∣a*(c k).val+b := by
      intro hd
      apply hn
      apply (Int.mul_dvd_mul_iff_left hr0).mp
      simpa only [he,pow_two] using hd
    have ht' := (arithmetic_tests r _ a b hab ht (c k)).2 ⟨a*k.val+z,he⟩ hn2
    simp only [one_mul] at ht'
    rw [he,Int.mul_ediv_cancel_left _ hr0,hcv] at ht'
    simp only [Int.cast_add,Int.cast_mul,Int.cast_natCast] at ht'
    have hh := hH₁.2 (c k) (t+k.val) (by simpa [c] using htnonzero k)
    simp only [arithmeticReparametrize,zero_mul,add_zero] at hh
    have hearg : (r:ℤ)*(t+k.val)=(r:ℤ)*k.val+(r:ℤ)*t := by ring
    rw [hearg] at hh
    have heq := ht'.symm.trans hh
    simpa [c,mul_add,add_assoc,add_comm,add_left_comm] using heq
  have hslope : (a:ZMod r)=B₁ := by
    by_cases hz0 : (z:ZMod r)=0
    · have h1 := agrees 1 (by simpa [hz0] using ha0)
      have h2 := agrees 2 (by simpa [hz0,mul_comm] using mul_ne_zero htwo ha0)
      norm_num at h1 h2
      linear_combination h2-h1
    · have h0 := agrees 0 (by simpa using hz0)
      norm_num at h0
      by_cases hz1 : (a:ZMod r)+z=0
      · have hz2 : (a:ZMod r)*2+z≠0 := by
          intro he; apply ha0; linear_combination he-hz1
        have h2 := agrees 2 (by simpa using hz2)
        norm_num at h2
        apply mul_left_cancel₀ htwo
        linear_combination h2-h0
      · have h1 := agrees 1 (by simpa using hz1)
        norm_num at h1
        linear_combination h1-h0
  exact hslope.symm.trans ha

end TranslationTiling.Sudoku
