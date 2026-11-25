import TranslationTiling.FiniteCompiler.Effective.SlotFrame
import TranslationTiling.FiniteCompiler.Effective.SlotDependence

namespace TranslationTiling.FiniteCompiler.Packed.SlotParameters

open SharedCoordinates Compiler Compiler.Effective Compiler.StripLift Compiler.Size Effective
open scoped Classical BigOperators
noncomputable section

set_option maxRecDepth 5000
variable {k m : ℕ} (s : SlotParameters k m)
variable [Fintype (Factor s.layout)]

private theorem strip_mono {H H' : ℕ} (h : H ≤ H') {x : Plane}
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

theorem mask_strip {Q : ℕ} (hQ : ∀ j, s.prime j ≤ Q)
    (g : Bool) (d : Fin k) (S : Finset (Fin m)) [NeZero (ShiftCount S)]
    (v : SharedCoordinates.Ambient s.layout) (hv : v ∈ s.mask g d S) :
    TestSupportAt 35 (fun _ => Q^(11*m)) v.1 := by
  unfold mask selectedSlotTile slotActivationTile at hv
  simp only [Finset.mem_biUnion,Finset.mem_univ,true_and,Finset.mem_filter,Finset.mem_map] at hv
  obtain ⟨p,⟨a,hEq⟩,_⟩ := hv
  let z : s.LowShifts g d S × s.ShiftType g d S := ((s.highEquiv g d S).symm p.1,p.2)
  have hxy : (s.offset g d S z) = v.1 := congrArg Prod.fst hEq
  obtain ⟨hline,hlo,hhidden,hobs,hpos,hcap⟩ :=
    (s.slotOffset_spec g d S (slopeNumber g)).2 z
  have hmod : ∀ i, s.offsetModuli g d S i ≤ Q := by
    rintro (j | ⟨i,_ | _⟩)
    · change s.shiftModulus g d S j ≤ Q
      change s.observationPrime g d (shiftIndex S j) ≤ Q
      rcases shiftIndex S j with ⟨i,_ | b⟩ <;> exact hQ _
    · exact hQ _
    · exact hQ _
  have hcard : Fintype.card (SlotParameters.OffsetKey S) = 6*S.card := by
    simp [OffsetKey]
    omega
  have hprod : (∏ i, s.offsetModuli g d S i) ≤ Q^(6*S.card) := by
    simpa only [Finset.prod_const,Finset.card_univ,hcard] using
      (Finset.prod_le_prod (s := Finset.univ) (g := fun _ => Q) fun i _ => hmod i)
  have hlw : Fintype.card (s.LowShifts g d S) ≤ Q^S.card := by
    rw [Fintype.card_pi]
    simp only [ZMod.card]
    have hb (i : SelectedSlot S) : s.low (g,d,i) ≤ Q := hQ (.inl ((g,d,i),none))
    simpa only [Finset.prod_const,Finset.card_univ,Fintype.card_coe] using
      (Finset.prod_le_prod (s := Finset.univ) (g := fun _ : SelectedSlot S => Q) fun i _ => hb i)
  have hsw : Fintype.card (s.ShiftType g d S) ≤ Q^(S.card*4) := by
    rw [Fintype.card_pi]
    simp only [ZMod.card]
    have hb (j : ZMod (ShiftCount S)) : s.shiftModulus g d S j ≤ Q := hmod (.inl j)
    simpa only [Finset.prod_const,Finset.card_univ,ZMod.card,shiftCount_eq] using
      (Finset.prod_le_prod (s := Finset.univ) (g := fun _ : ZMod (ShiftCount S) => Q) fun j _ => hb j)
  have huv : (∏ i, s.offsetModuli g d S i) * Fintype.card (s.LowShifts g d S × s.ShiftType g d S) ≤
      Q^(11*m) := by
    rw [Fintype.card_prod]
    apply (Nat.mul_le_mul hprod (Nat.mul_le_mul hlw hsw)).trans
    rw [← pow_add,← pow_add]
    have hs := Finset.card_le_card (Finset.subset_univ S)
    rw [Finset.card_univ,Fintype.card_fin] at hs
    apply Nat.pow_le_pow_right
    · have : 0 < ShiftCount S := NeZero.pos _
      rw [shiftCount_eq] at this
      obtain ⟨i,_⟩ := Finset.card_pos.mp (by omega : 0 < S.card)
      exact (s.prime_isPrime (.inl ((g,d,i),none))).pos.trans_le (hQ _)
    · omega
  have habs : ((s.offset g d S z).1).natAbs ≤ Q^(11*m) := by
    change 0 ≤ (s.offset g d S z).1 at hpos
    have hh : (s.offset g d S z).1 ≤ (Q^(11*m) : ℕ) :=
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

end
end TranslationTiling.FiniteCompiler.Packed.SlotParameters
