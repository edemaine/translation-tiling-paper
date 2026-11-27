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

theorem strip_mono_at {H H' : ℕ → ℕ} (h : ∀ i < 17, H i ≤ H' i) {x : Plane}
    (hx : TestSupportAt 35 H x) : TestSupportAt 35 H' x := by
  rcases hx with ⟨ha,hb⟩ | ⟨j,hj,ha,hb⟩
  · exact Or.inl ⟨ha.trans (h 0 (by decide)),hb⟩
  · exact Or.inr ⟨j,hj,ha.trans (h j hj),hb⟩

theorem invariance_strip {Y : Type*} [AddCommGroup Y] {H : ℕ → ℕ}
    (ψ : Factor s.layout →+ Y) (σ : SharedCoordinates.Base s.layout)
    (hs : TestSupportAt 35 H σ.1) (v : SharedCoordinates.Ambient s.layout)
    (hv : v ∈ productInvariance s.layout ψ σ) :
    TestSupportAt 35 H v.1 := by
  simp only [productInvariance,Finset.mem_union,Finset.mem_filter,Finset.mem_map,
    Finset.mem_univ,true_and] at hv
  rcases hv with ⟨h,_⟩ | ⟨⟨a,ha⟩,_,_⟩
  · have hk : SharedCoordinates.baseProjection s.layout v = 0 :=
      (mem_productKernel s.layout v).mp h
    have he : v.1 = 0 := congrArg Prod.fst hk
    rw [he]
    exact Or.inl (by simp)
  · have he : σ.1 = v.1 := congrArg Prod.fst ha
    exact he ▸ hs

omit [Fintype (Factor s.layout)] in
theorem arithmetic_strip {H : ℕ → ℕ} (hH : ∀ j < 17, arithmeticStripRadii.getD j 0 ≤ H j)
    (F : Finset (SharedCoordinates.Ambient s.layout)) (hF : F ∈ s.arithmeticTiles)
    (v : SharedCoordinates.Ambient s.layout) (hv : v ∈ F) : TestSupportAt 35 H v.1 := by
  obtain ⟨f,hf,rfl⟩ := List.mem_map.mp hF
  unfold oldTileLift at hv
  obtain ⟨z,hz,hEq⟩ := Finset.mem_map.mp hv
  have hz' := (Finset.mem_product.mp hz).1
  obtain ⟨p,hp,he⟩ := Finset.mem_image.mp hz'
  have hp' := List.mem_toFinset.mp hp
  apply strip_mono_at hH
  have hh := arithmeticBaseline_strip f hf p hp'
  have hpz : p.1 = z.1.1 := congrArg Prod.fst he
  have hzv : z.1.1 = v.1 := congrArg Prod.fst hEq
  have heq := hpz.trans hzv
  exact heq ▸ hh

omit [Fintype (Factor s.layout)] in
set_option linter.constructorNameAsVariable false in
theorem anchor_strip (H : ℕ → ℕ) (F : Finset (SharedCoordinates.Ambient s.layout)) (hF : F ∈ s.anchorTests)
    (v : SharedCoordinates.Ambient s.layout) (hv : v ∈ F) : TestSupportAt 35 H v.1 := by
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
  exact Or.inl (by simp)

private theorem lineStep_strip (g : Bool) {H : ℕ → ℕ} (hH : 1 ≤ H 0) :
    TestSupportAt 35 H (1,-slopeNumber g) := by
  apply Or.inl
  cases g <;> exact ⟨hH,by decide⟩

theorem marker_strip {H : ℕ → ℕ} (hH : 1 ≤ H 0) (i : WangSlot k m) (j : Fin 3)
    (F : Finset (SharedCoordinates.Ambient s.layout)) (hF : F ∈ s.markerTests i j) (v : SharedCoordinates.Ambient s.layout)
    (hv : v ∈ F) : TestSupportAt 35 H v.1 := by
  simp only [markerTests,List.mem_cons,List.mem_map,Finset.mem_toList,Finset.mem_erase,
    Finset.mem_univ,and_true] at hF
  rcases hF with rfl | ⟨p,_,rfl⟩
  · exact s.invariance_strip (s.observeMarker i j) ((1,-slopeNumber i.1),0)
      (lineStep_strip i.1 hH) v hv
  · exact s.invariance_strip (s.observeMarker i j) (lowStep s.layout p) (show TestSupportAt 35 H 0 from Or.inl (by simp)) v hv

theorem fallback_strip {H : ℕ → ℕ} (hH : 1 ≤ H 0) (g : Bool) (i : Fin m)
    (F : Finset (SharedCoordinates.Ambient s.layout)) (hF : F ∈ s.fallbackTests g i) (v : SharedCoordinates.Ambient s.layout)
    (hv : v ∈ F) : TestSupportAt 35 H v.1 := by
  simp only [fallbackTests,List.mem_cons,List.mem_map,Finset.mem_toList,Finset.mem_filter,
    Finset.mem_univ,true_and] at hF
  rcases hF with rfl | ⟨p,_,rfl⟩
  · exact s.invariance_strip (s.observeFallback (g,i,false)) ((1,-slopeNumber g),0)
      (lineStep_strip g hH) v hv
  · exact s.invariance_strip (s.observeFallback (g,i,false)) (lowStep s.layout p) (show TestSupportAt 35 H 0 from Or.inl (by simp)) v hv

theorem mask_strip_order
    (g : Bool) (d : Fin k) (S : Finset (Fin m)) [NeZero (ShiftCount S)]
    (v : SharedCoordinates.Ambient s.layout) (hv : v ∈ s.mask g d S) :
    TestSupportAt 35 (fun _ => s.offsetOrder g d S) v.1 := by
  unfold mask selectedSlotTile slotActivationTile at hv
  simp only [Finset.mem_biUnion,Finset.mem_univ,true_and,Finset.mem_filter,Finset.mem_map] at hv
  obtain ⟨p,⟨a,hEq⟩,_⟩ := hv
  let z : s.LowShifts g d S × s.ShiftType g d S := ((s.highEquiv g d S).symm p.1,p.2)
  have hxy : (s.offset g d S z) = v.1 := congrArg Prod.fst hEq
  obtain ⟨hline,_,_,_,hcap⟩ := s.slotOffset_spec g d S (slopeNumber g) z
  rw [← hxy]
  refine Or.inr ⟨if g then 0 else 2,by cases g <;> decide,hcap.le,?_⟩
  cases g <;> exact hline

def slotOffsetFactor (i : WangSlot k m) : ℕ :=
  s.low i * (∏ j, s.marker i j) * s.fallback (i.1,i.2.2,false) * s.fallback (i.1,i.2.2,true)

omit [Fintype (Factor s.layout)] in
theorem offsetOrder_factors (g : Bool) (d : Fin k) (S : Finset (Fin m)) [NeZero (ShiftCount S)] :
    s.offsetOrder g d S = ∏ i : SelectedSlot S, s.slotOffsetFactor (g,d,i) := by
  unfold offsetOrder
  rw [Fintype.prod_sum_type,Fintype.prod_prod_type]
  have h : (∏ j, s.offsetModuli g d S (.inl j)) =
      ∏ x : SlotIndex S, s.observationPrime g d x :=
    Fintype.prod_equiv (shiftIndex S) _ _ (fun _ => rfl)
  rw [h,Fintype.prod_prod_type]
  simp only [Fintype.prod_option,observationPrime, Fintype.prod_bool,offsetModuli]
  simp only [← Finset.prod_mul_distrib,slotOffsetFactor]
  apply Finset.prod_congr rfl
  intro i _
  ac_rfl

omit [Fintype (Factor s.layout)] in
theorem slotOffsetFactor_le {A B C : ℕ}
    (hA : ∀ i, s.fallback i ≤ A) (hB : ∀ i j, s.marker i j ≤ B)
    (hC : ∀ i, s.low i ≤ C) (i : WangSlot k m) :
    s.slotOffsetFactor i ≤ C*B^3*A^2 := by
  have hb : (∏ j, s.marker i j) ≤ B^3 := by
    simpa using (Finset.prod_le_prod (s := Finset.univ) (f := s.marker i)
      (g := fun _ => B) (fun j _ => hB i j))
  unfold slotOffsetFactor
  calc
    _ ≤ C*B^3*A*A := Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (hC i) hb) (hA _)) (hA _)
    _ = _ := by ring

theorem mask_strip_factors {D : ℕ}
    (hD : ∀ i, s.slotOffsetFactor i ≤ D)
    (g : Bool) (d : Fin k) (S : Finset (Fin m)) [NeZero (ShiftCount S)]
    (v : SharedCoordinates.Ambient s.layout) (hv : v ∈ s.mask g d S) :
    TestSupportAt 35 (fun _ => D^S.card) v.1 := by
  apply strip_mono _ (s.mask_strip_order g d S v hv)
  rw [s.offsetOrder_factors]
  simpa only [Finset.prod_const,Finset.card_univ,Fintype.card_coe] using
    (Finset.prod_le_prod (s := Finset.univ) (g := fun _ : SelectedSlot S => D)
      (fun i _ => hD (g,d,i)))

theorem mask_strip {Q : ℕ} (hQ : ∀ j, s.prime j ≤ Q)
    (g : Bool) (d : Fin k) (S : Finset (Fin m)) [NeZero (ShiftCount S)]
    (v : SharedCoordinates.Ambient s.layout) (hv : v ∈ s.mask g d S) :
    TestSupportAt 35 (fun _ => Q^(11*m)) v.1 := by
  apply strip_mono _ (s.mask_strip_factors (s.slotOffsetFactor_le (fun i => hQ (.inr i))
    (fun i j => hQ (.inl (i,some j))) (fun i => hQ (.inl (i,none)))) g d S v hv)
  rw [show Q*Q^3*Q^2 = Q^6 by ring, ← pow_mul]
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
