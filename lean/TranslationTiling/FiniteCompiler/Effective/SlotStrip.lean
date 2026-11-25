import TranslationTiling.FiniteCompiler.Effective.SlotFrame
import TranslationTiling.FiniteCompiler.Effective.SlotDependence

namespace TranslationTiling.FiniteCompiler.Packed.SlotParameters

open SharedCoordinates Compiler Compiler.Effective Compiler.StripLift Compiler.Size Effective
open scoped Classical BigOperators
noncomputable section

set_option maxRecDepth 5000
variable {k m : ℕ} (s : SlotParameters k m)
variable [Fintype (Factor s.layout)]

theorem strip_mono {H H' : ℕ} (h : H ≤ H') {x : Plane}
    (hx : TestSupportAt 35 (fun _ => H) x) : TestSupportAt 35 (fun _ => H') x := by
  rcases hx with ⟨ha,hb⟩ | ⟨j,hj,ha,hb⟩
  · exact Or.inl ⟨ha.trans h,hb⟩
  · exact Or.inr ⟨j,hj,ha.trans h,hb⟩

theorem invariance_strip {Y : Type*} [AddCommGroup Y] {H : ℕ}
    (ψ : Factor s.layout →+ Y) (σ : SharedCoordinates.Base s.layout)
    (hs : TestSupportAt 35 (fun _ => H) σ.1) (v : SharedCoordinates.Ambient s.layout)
    (hv : v ∈ productInvariance s.layout ψ σ) :
    TestSupportAt 35 (fun _ => H) v.1 := by
  simp only [productInvariance,Finset.mem_union,Finset.mem_filter,Finset.mem_map,
    Finset.mem_univ,true_and] at hv
  rcases hv with ⟨h,_⟩ | ⟨⟨a,ha⟩,_,_⟩
  · have hk : SharedCoordinates.baseProjection s.layout v = 0 :=
      (mem_productKernel s.layout v).mp h
    have he : v.1 = 0 := congrArg Prod.fst hk
    rw [he]
    exact zero_strip H
  · have he : σ.1 = v.1 := congrArg Prod.fst ha
    exact he ▸ hs

omit [Fintype (Factor s.layout)] in
theorem arithmetic_strip {H : ℕ} (hH : fourValueRadius 0 ≤ H)
    (F : Finset (SharedCoordinates.Ambient s.layout)) (hF : F ∈ s.arithmeticTiles)
    (v : SharedCoordinates.Ambient s.layout) (hv : v ∈ F) : TestSupportAt 35 (fun _ => H) v.1 := by
  obtain ⟨f,hf,rfl⟩ := List.mem_map.mp hF
  unfold oldTileLift at hv
  obtain ⟨z,hz,hEq⟩ := Finset.mem_map.mp hv
  have hz' := (Finset.mem_product.mp hz).1
  obtain ⟨p,hp,he⟩ := Finset.mem_image.mp hz'
  have hp' := List.mem_toFinset.mp hp
  have hf' : f ∈ fourValueRawDeck [] 0 := by
    unfold arithmeticBaseline at hf
    unfold fourValueRawDeck
    exact List.mem_cons_of_mem _ (List.mem_append_left _ hf)
  apply strip_mono hH
  have hh := fourValueRawDeck_strip [] 0 f hf' p hp'
  have hpz : p.1 = z.1.1 := congrArg Prod.fst he
  have hzv : z.1.1 = v.1 := congrArg Prod.fst hEq
  have heq := hpz.trans hzv
  exact heq ▸ hh

omit [Fintype (Factor s.layout)] in
set_option linter.constructorNameAsVariable false in
theorem anchor_strip (H : ℕ) (F : Finset (SharedCoordinates.Ambient s.layout)) (hF : F ∈ s.anchorTests)
    (v : SharedCoordinates.Ambient s.layout) (hv : v ∈ F) : TestSupportAt 35 (fun _ => H) v.1 := by
  obtain ⟨⟨i,j⟩,_,rfl⟩ := List.mem_map.mp hF
  simp only [productInvariance,Finset.mem_union,Finset.mem_filter,Finset.mem_map,
    Finset.mem_univ,true_and] at hv
  have h0 : v.1 = 0 := by
    rcases hv with ⟨h,_⟩ | ⟨⟨a,ha⟩,_,_⟩
    · simp only [productKernel,Finset.mem_filter,Finset.mem_map,Finset.mem_univ,true_and] at h
      obtain ⟨⟨a,ha⟩,_⟩ := h
      exact (congrArg Prod.fst ha).symm
    · exact (congrArg Prod.fst ha).symm
  rw [h0]
  exact zero_strip H

private theorem lineStep_strip (g : Bool) {H : ℕ} (hH : 1 ≤ H) :
    TestSupportAt 35 (fun _ => H) (1,-slopeNumber g) := by
  apply Or.inl
  cases g <;> exact ⟨hH,by decide⟩

theorem marker_strip {H : ℕ} (hH : 1 ≤ H) (i : WangSlot k m) (j : Fin 3)
    (F : Finset (SharedCoordinates.Ambient s.layout)) (hF : F ∈ s.markerTests i j) (v : SharedCoordinates.Ambient s.layout)
    (hv : v ∈ F) : TestSupportAt 35 (fun _ => H) v.1 := by
  simp only [markerTests,List.mem_cons,List.mem_map,Finset.mem_toList,Finset.mem_erase,
    Finset.mem_univ,and_true] at hF
  rcases hF with rfl | ⟨p,_,rfl⟩
  · exact s.invariance_strip (s.observeMarker i j) ((1,-slopeNumber i.1),0)
      (lineStep_strip i.1 hH) v hv
  · exact s.invariance_strip (s.observeMarker i j) (lowStep s.layout p) (zero_strip H) v hv

theorem fallback_strip {H : ℕ} (hH : 1 ≤ H) (g : Bool) (i : Fin m)
    (F : Finset (SharedCoordinates.Ambient s.layout)) (hF : F ∈ s.fallbackTests g i) (v : SharedCoordinates.Ambient s.layout)
    (hv : v ∈ F) : TestSupportAt 35 (fun _ => H) v.1 := by
  simp only [fallbackTests,List.mem_cons,List.mem_map,Finset.mem_toList,Finset.mem_filter,
    Finset.mem_univ,true_and] at hF
  rcases hF with rfl | ⟨p,_,rfl⟩
  · exact s.invariance_strip (s.observeFallback (g,i,false)) ((1,-slopeNumber g),0)
      (lineStep_strip g hH) v hv
  · exact s.invariance_strip (s.observeFallback (g,i,false)) (lowStep s.layout p) (zero_strip H) v hv

theorem mask_strip_factors {A B C : ℕ}
    (hA : ∀ i, s.fallback i ≤ A) (hB : ∀ i j, s.marker i j ≤ B)
    (hC : ∀ i, s.low i ≤ C) (hAB : A ≤ B)
    (g : Bool) (d : Fin k) (S : Finset (Fin m)) [NeZero (ShiftCount S)]
    (v : SharedCoordinates.Ambient s.layout) (hv : v ∈ s.mask g d S) :
    TestSupportAt 35 (fun _ => (C^2*B^8*A)^S.card) v.1 := by
  unfold mask selectedSlotTile slotActivationTile at hv
  simp only [Finset.mem_biUnion,Finset.mem_univ,true_and,Finset.mem_filter,Finset.mem_map] at hv
  obtain ⟨p,⟨a,hEq⟩,_⟩ := hv
  let z : s.LowShifts g d S × s.ShiftType g d S := ((s.highEquiv g d S).symm p.1,p.2)
  have hxy : (s.offset g d S z) = v.1 := congrArg Prod.fst hEq
  obtain ⟨hline,hlo,hhidden,hobs,hpos,hcap⟩ :=
    (s.slotOffset_spec g d S (slopeNumber g)).2 z
  have hshift (j : ZMod (ShiftCount S)) : s.shiftModulus g d S j ≤ B := by
    change s.observationPrime g d (shiftIndex S j) ≤ B
    rcases shiftIndex S j with ⟨i,j⟩
    cases j with
    | none => exact (hA _).trans hAB
    | some j => exact hB _ j
  have hp {I : Type} [Fintype I] (f : I → ℕ) (b : ℕ) (h : ∀ i, f i ≤ b) :
      (∏ i, f i) ≤ b^Fintype.card I := by
    simpa only [Finset.prod_const,Finset.card_univ] using
      (Finset.prod_le_prod (s := Finset.univ) (g := fun _ => b) fun i _ => h i)
  have hb : (∏ j, s.shiftModulus g d S j) ≤ B^(4*S.card) := by
    simpa only [ZMod.card,shiftCount_eq,Nat.mul_comm 4 S.card] using
      hp (s.shiftModulus g d S) B hshift
  have hc : (∏ i : SelectedSlot S, s.low (g,d,i)) ≤ C^S.card := by
    simpa only [Fintype.card_coe] using
      hp (fun i : SelectedSlot S => s.low (g,d,i)) C (fun i => hC (g,d,i))
  have ha : (∏ i : SelectedSlot S, s.fallback (g,i,true)) ≤ A^S.card := by
    simpa only [Fintype.card_coe] using
      hp (fun i : SelectedSlot S => s.fallback (g,i,true)) A (fun i => hA (g,i,true))
  have hmod : (∏ i, s.offsetModuli g d S i) ≤ B^(4*S.card)*(C^S.card*A^S.card) := by
    rw [Fintype.prod_sum_type,Fintype.prod_prod_type]
    apply Nat.mul_le_mul hb
    calc
      _ = (∏ i : SelectedSlot S, s.low (g,d,i)) *
          (∏ i : SelectedSlot S, s.fallback (g,i,true)) := by
        simp only [Fintype.prod_bool,offsetModuli,Finset.prod_mul_distrib]
        ac_rfl
      _ ≤ _ := Nat.mul_le_mul hc ha
  have huv : (∏ i, s.offsetModuli g d S i) * Fintype.card (s.LowShifts g d S × s.ShiftType g d S) ≤
      (C^2*B^8*A)^S.card := by
    rw [Fintype.card_prod, Fintype.card_pi, Fintype.card_pi]
    simp only [ZMod.card]
    refine (Nat.mul_le_mul hmod (Nat.mul_le_mul hc hb)).trans_eq ?_
    simp only [mul_pow, ← pow_mul]
    rw [show 8*S.card = 4*S.card+4*S.card by omega, pow_add,
        show 2*S.card = S.card+S.card by omega, pow_add]
    ring
  have habs : ((s.offset g d S z).1).natAbs ≤ (C^2*B^8*A)^S.card := by
    change 0 ≤ (s.offset g d S z).1 at hpos
    have hh : (s.offset g d S z).1 ≤ ((C^2*B^8*A)^S.card : ℕ) :=
      (le_of_lt hcap).trans (Int.ofNat_le.mpr huv)
    cases ev : (s.offset g d S z).1 with
    | ofNat j =>
      rw [ev] at hh
      exact Int.ofNat_le.mp hh
    | negSucc j =>
      rw [ev] at hpos
      omega
  rw [← hxy]
  refine Or.inr ⟨if g then 0 else 2,by cases g <;> decide,habs,?_⟩
  cases g <;> exact s.offset_slope _ d S z

theorem mask_strip {Q : ℕ} (hQ : ∀ j, s.prime j ≤ Q)
    (g : Bool) (d : Fin k) (S : Finset (Fin m)) [NeZero (ShiftCount S)]
    (v : SharedCoordinates.Ambient s.layout) (hv : v ∈ s.mask g d S) :
    TestSupportAt 35 (fun _ => Q^(11*m)) v.1 := by
  apply strip_mono _ (s.mask_strip_factors (fun i => hQ (.inr i))
    (fun i j => hQ (.inl (i,some j))) (fun i => hQ (.inl (i,none))) le_rfl g d S v hv)
  rw [show Q^2*Q^8*Q = Q^11 by ring, ← pow_mul]
  apply Nat.pow_le_pow_right
  · have hpos := NeZero.pos (ShiftCount S)
    rw [shiftCount_eq] at hpos
    obtain ⟨i,_⟩ := Finset.card_pos.mp (by omega : 0 < S.card)
    exact (s.prime_isPrime (.inl ((g,d,i),none))).pos.trans_le (hQ _)
  · have hcard := Finset.card_le_card (Finset.subset_univ S)
    rw [Finset.card_univ, Fintype.card_fin] at hcard
    omega

end
end TranslationTiling.FiniteCompiler.Packed.SlotParameters
