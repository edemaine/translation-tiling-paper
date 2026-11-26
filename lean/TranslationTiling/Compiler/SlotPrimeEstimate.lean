import TranslationTiling.Compiler.SlotBound

namespace TranslationTiling.Compiler.Size

open FiniteCompiler.Packed FiniteCompiler.Packed.SlotParameters FiniteCompiler.SharedCoordinates

noncomputable section

private theorem prime_cap_scale {x : ℕ} {C u g : ℝ} (j : ℕ)
    (hx : 0 < x) (hC : 1 ≤ C) (hu : 1 ≤ u) (hg : 1 ≤ g)
    (hLu : Real.logb 2 u ≤ g) (hL : Real.logb 2 g ≤ g)
    (hb : (x : ℝ) ≤ C*u*g^j) :
    (guardedPrimeCap x : ℝ) ≤ 4*C*(2+Real.logb 2 C+j)*u*g^(j+1) := by
  have hl := (lg_natLog_le hx).trans
    (lg_mono (show 0 < (x : ℝ) by exact_mod_cast hx) hb)
  rw [Real.logb_mul (by positivity) (by positivity),
    Real.logb_mul (by positivity) (by positivity), Real.logb_pow] at hl
  have hc : 0 ≤ Real.logb 2 C := Real.logb_nonneg (by norm_num) hC
  have h₁ := mul_le_mul_of_nonneg_left hL (show (0 : ℝ) ≤ j by positivity)
  have h₂ := mul_le_mul_of_nonneg_right hg hc
  have hf : (Nat.log 2 x : ℝ)+1 ≤ (2+Real.logb 2 C+j)*g := by
    nlinarith only [hl,hLu,h₁,h₂,hg]
  unfold guardedPrimeCap
  push_cast
  have hprod := mul_le_mul hb hf (show 0 ≤ (Nat.log 2 x : ℝ)+1 by positivity)
    (by positivity : 0 ≤ C*u*g^j)
  calc
    _ = 4*((x : ℝ)*((Nat.log 2 x : ℝ)+1)) := by ring
    _ ≤ 4*((C*u*g^j)*((2+Real.logb 2 C+j)*g)) :=
      mul_le_mul_of_nonneg_left hprod (by norm_num)
    _ = 4*C*(2+Real.logb 2 C+j)*u*g^(j+1) := by rw [pow_succ]; ring

private theorem le_double_pow (p : ℕ) {x y : ℝ} (hx : x ≤ (2 : ℝ)^p) (hy : y ≤ (2 : ℝ)^p) :
    x + y ≤ (2 : ℝ)^(p+1) := by
  rw [pow_succ]
  linarith

private theorem dyadic_prime_coefficient {x j : ℝ} (p q : ℕ)
    (hx₁ : 1 ≤ x) (hx : x ≤ (2 : ℝ)^p) (hj₀ : 0 ≤ j) (hj : 2+(p : ℝ)+j ≤ (2 : ℝ)^q) :
    4*x*(2+Real.logb 2 x+j) ≤ (2 : ℝ)^(p+q+2) := by
  have hl := lg_mono (by linarith : 0 < x) hx
  rw [lg_two_pow] at hl
  have hf : 2+Real.logb 2 x+j ≤ (2 : ℝ)^q := by linarith
  have hp : 0 ≤ 2+Real.logb 2 x+j := by
    linarith [Real.logb_nonneg (by norm_num : (1 : ℝ) < 2) hx₁]
  calc
    _ ≤ 4*(2 : ℝ)^p*(2 : ℝ)^q := by gcongr
    _ = _ := by rw [pow_add, pow_add]; ring

/-- The shared factors have polylogarithmic caps in the width, and all
prime caps are bounded by the first logarithm times a fixed power of the
second logarithm, with the fixed factor bounded by `2^56`. -/
theorem slot_prime_caps_scale_explicit :
    ∀ (k m : ℕ) (u g : ℝ), 1 ≤ u → 1 ≤ g → g^2 ≤ u →
      Real.logb 2 u ≤ g → Real.logb 2 g ≤ g → (m : ℝ) ≤ g →
      (k : ℝ)*(m : ℝ) ≤ 2*u →
      (fallbackCap m : ℝ) ≤ (2 : ℝ)^56*g^2 ∧
      (markerCap k m : ℝ) ≤ (2 : ℝ)^56*u*g^4 ∧
      (SlotParameters.lowCap k m : ℝ) ≤ (2 : ℝ)^56*u*g^4 := by
  let N := slotBasePrimeCap
  let A := (N : ℝ)+20
  let a := 4*A*(2+Real.logb 2 A+1)
  let B := a+28
  let b := 4*B*(2+Real.logb 2 B+0)
  let D := a*b+20
  let d := 4*D*(2+Real.logb 2 D+3)
  have hA : 1 ≤ A := by dsimp [A]; linarith [Nat.cast_nonneg (α := ℝ) N]
  have ha : 0 ≤ a := by
    have := Real.logb_nonneg (by norm_num : (1 : ℝ) < 2) hA
    dsimp [a]
    positivity
  have hB : 1 ≤ B := by dsimp [B]; linarith
  have hb : 0 ≤ b := by
    have := Real.logb_nonneg (by norm_num : (1 : ℝ) < 2) hB
    dsimp [b]
    positivity
  have hD : 1 ≤ D := by dsimp [D]; nlinarith only [mul_nonneg ha hb]
  have hpow {i j : ℕ} (h : i ≤ j) : (2 : ℝ)^i ≤ (2 : ℝ)^j :=
    pow_le_pow_right₀ (by norm_num) h
  have hNA : A ≤ (2 : ℝ)^12 := by norm_num [A,N,slotBasePrimeCap]
  have hap : a ≤ (2 : ℝ)^18 :=
    dyadic_prime_coefficient 12 4 hA hNA (by norm_num) (by norm_num)
  have hBp : B ≤ (2 : ℝ)^19 :=
    le_double_pow 18 hap (by norm_num)
  have hbp : b ≤ (2 : ℝ)^26 :=
    dyadic_prime_coefficient 19 5 hB hBp (by norm_num) (by norm_num)
  have hDP : a*b ≤ (2 : ℝ)^44 := by
    rw [show 44 = 18+26 by decide,pow_add]
    exact mul_le_mul hap hbp hb (by positivity)
  have hDp : D ≤ (2 : ℝ)^45 :=
    le_double_pow 44 hDP (by norm_num)
  have hdp : d ≤ (2 : ℝ)^53 :=
    dyadic_prime_coefficient 45 6 hD hDp (by norm_num) (by norm_num)
  let C : ℝ := 2^56
  have hCa : a ≤ C := hap.trans (hpow (by decide))
  have hCb : b ≤ C := hbp.trans (hpow (by decide))
  have hCd : d ≤ C := hdp.trans (hpow (by decide))
  intro k m u g hu hg hgu hlu hlg hm hkm
  have hfb : (fallbackCap m : ℝ) ≤ a*g^2 := by
    apply (Nat.cast_le.mpr (slotSearchCap_le_guarded N (4*m))).trans
    change (guardedPrimeCap (N+4*m+16) : ℝ) ≤ _
    have h₁ : (↑(N+4*m+16) : ℝ) ≤ A*1*g^1 := by
      push_cast
      dsimp [A]
      have := mul_nonneg (show (0 : ℝ) ≤ (N : ℝ) by positivity) (sub_nonneg.mpr hg)
      nlinarith only [hm,hg,this]
    have h₂ := prime_cap_scale 1 (by omega : 0 < N+4*m+16)
      hA (show (1 : ℝ) ≤ 1 by rfl) hg (by rw [Real.logb_one]; linarith : Real.logb 2 1 ≤ g) hlg h₁
    simpa [a] using h₂
  have hmk : (separateMarkerCap k m : ℝ) ≤ b*u*g := by
    apply (Nat.cast_le.mpr (slotSearchCap_le_guarded (fallbackCap m) (6*k*m))).trans
    have h₁ : (↑(fallbackCap m+6*k*m+16) : ℝ) ≤ B*u*g^0 := by
      push_cast
      dsimp [B]
      have ha' := mul_le_mul_of_nonneg_left hgu ha
      linarith only [hfb,ha',hkm,hu]
    have h₂ := prime_cap_scale 0 (by omega : 0 < fallbackCap m+6*k*m+16)
      hB hu hg hlu hlg h₁
    simpa [b] using h₂
  have hlw : (separateLowCap k m : ℝ) ≤ d*u*g^4 := by
    apply (Nat.cast_le.mpr (slotSearchCap_le_guarded (fallbackCap m*separateMarkerCap k m) (2*k*m))).trans
    have h₁ : (↑(fallbackCap m*separateMarkerCap k m+2*k*m+16) : ℝ) ≤ D*u*g^3 := by
      push_cast
      have hprod := mul_le_mul hfb hmk (show (0 : ℝ) ≤ separateMarkerCap k m by positivity)
        (by positivity : 0 ≤ a*g^2)
      have hg3 : 1 ≤ g^3 := one_le_pow₀ hg
      have hu3 : u ≤ u*g^3 := by
        simpa using mul_le_mul_of_nonneg_left hg3 (show 0 ≤ u by linarith)
      dsimp [D]
      nlinarith only [hprod, hkm,hu,hu3]
    exact prime_cap_scale 3 (by omega : 0 < fallbackCap m*separateMarkerCap k m+2*k*m+16)
      hD hu hg hlu hlg h₁
  have hg4 : g ≤ g^4 := by
    simpa using pow_le_pow_right₀ hg (show 1 ≤ (4 : ℕ) by decide)
  have hM : (matchedSlotCap k m : ℝ) ≤ C*u*g^4 := by
    have hA' : (fallbackCap m : ℝ) ≤ a*u := hfb.trans (by gcongr)
    have hD' : ((matchedSlotCount k m+16 : ℕ) : ℝ) ≤ (3*a+32)*u := by
      unfold matchedSlotCount
      push_cast
      nlinarith only [hA',hkm,hu]
    have hc : 1 ≤ 3*a+32 := by linarith
    have hc' : 3*a+32 ≤ (2 : ℝ)^20 := by linarith only [hap,show (2 : ℝ)^20 = 4*2^18 by norm_num]
    have hB' := prime_cap_scale 0 (by omega : 0 < matchedSlotCount k m+16)
      hc hu hg hlu hlg (by simpa using hD')
    simp only [Nat.zero_add,pow_one,Nat.cast_zero,add_zero] at hB'
    have hco := dyadic_prime_coefficient 20 5 hc hc' (show (0 : ℝ) ≤ 0 by norm_num)
      (by norm_num : 2+(20 : ℝ)+0 ≤ 2^5)
    simp only [add_zero] at hco
    have hG : (guardedPrimeCap (matchedSlotCount k m+16) : ℝ) ≤ (2 : ℝ)^27*u*g := by
      apply hB'.trans
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by norm_num at hco ⊢; exact hco) (by linarith)) (by linarith)
    have hAA : (fallbackCap m : ℝ)^2 ≤ (2 : ℝ)^36*g^4 := by
      calc
        _ ≤ (a*g^2)^2 := by gcongr
        _ ≤ ((2 : ℝ)^18*g^2)^2 := by gcongr
        _ = _ := by ring
    unfold matchedSlotCap slotWindowCap
    push_cast
    have h1 : (8 : ℝ)*((2 : ℝ)^36*g^4) ≤ C*u*g^4 := by
      have h : (8 : ℝ)*2^36 ≤ C*u := (show (8 : ℝ)*2^36 ≤ C by norm_num [C]).trans (by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hu (show 0 ≤ C by positivity))
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right h (show 0 ≤ g^4 by positivity)
    have h2 : (8 : ℝ)*((2 : ℝ)^27*u*g) ≤ C*u*g^4 := by
      have h : (8 : ℝ)*2^27 ≤ C := by norm_num [C]
      calc
        _ ≤ C*u*g := by
          rw [← mul_assoc, ← mul_assoc]
          gcongr
        _ ≤ _ := by gcongr
    apply le_trans (mul_le_mul_of_nonneg_left (max_le_max hAA hG) (by norm_num))
    rw [mul_max_of_nonneg _ _ (by norm_num)]
    exact max_le h1 h2
  refine ⟨hfb.trans (mul_le_mul_of_nonneg_right hCa (by positivity)), ?_, ?_⟩
  · unfold markerCap
    split
    · exact hM
    · exact (hmk.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hCb (by linarith)) (by linarith))).trans
        (mul_le_mul_of_nonneg_left hg4 (by positivity))
  · unfold SlotParameters.lowCap
    split
    · exact hM
    · exact hlw.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hCd (by linarith)) (by positivity))

theorem slot_prime_caps_scale :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (k m : ℕ) (u g : ℝ), 1 ≤ u → 1 ≤ g → g^2 ≤ u →
      Real.logb 2 u ≤ g → Real.logb 2 g ≤ g → (m : ℝ) ≤ g →
      (k : ℝ)*(m : ℝ) ≤ 2*u →
      (fallbackCap m : ℝ) ≤ C*g^2 ∧
      (markerCap k m : ℝ) ≤ C*u*g^4 ∧
      (SlotParameters.lowCap k m : ℝ) ≤ C*u*g^4 :=
  ⟨2^56,one_le_pow₀ (by norm_num),slot_prime_caps_scale_explicit⟩

end

end TranslationTiling.Compiler.Size
