import TranslationTiling.FiniteCompiler.Effective.AxisSlotFrame
import TranslationTiling.FiniteCompiler.Effective.AxisSlotDependence

namespace TranslationTiling.FiniteCompiler.Packed.AxisParameters

open SharedCoordinates Compiler Compiler.Effective Compiler.StripLift Compiler.Size Effective
open scoped Classical BigOperators
noncomputable section

set_option maxRecDepth 5000
variable {k m : ℕ} (s : AxisParameters k m)
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

theorem fallback_strip {H : ℕ → ℕ} (hH : 1 ≤ H 0) (g : Bool) (i : Fin m) (a : Bool)
    (F : Finset (SharedCoordinates.Ambient s.layout)) (hF : F ∈ s.fallbackTests g i a)
    (v : SharedCoordinates.Ambient s.layout) (hv : v ∈ F) : TestSupportAt 35 H v.1 := by
  simp only [fallbackTests,List.mem_cons,List.mem_append,List.mem_map,Finset.mem_toList,
    Finset.mem_filter,Finset.mem_univ,true_and] at hF
  rcases hF with rfl | ⟨j,_,rfl⟩ | ⟨d,_,rfl⟩
  · exact s.invariance_strip (s.observeFallback (g,i,a,false)) ((1,-slopeNumber g),0)
      (lineStep_strip g hH) v hv
  · exact s.invariance_strip (s.observeFallback (g,i,a,false)) (lowStep s.layout j)
      (show TestSupportAt 35 H 0 from Or.inl (by simp)) v hv
  · exact s.invariance_strip (s.observeFallback (g,i,a,false)) (s.axisStep (g,d,i) (!a))
      (show TestSupportAt 35 H 0 from Or.inl (by simp)) v hv

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

omit [Fintype (Factor s.layout)] in
theorem offsetOrder_le {P : ℕ} (hP : ∀ j, s.prime j ≤ P) (g : Bool) (d : Fin k)
    (S : Finset (Fin m)) [NeZero (ShiftCount S)] :
    s.offsetOrder g d S ≤ P^(9*S.card) := by
  have h (i : OffsetKey S) : s.offsetModuli g d S i ≤ P := by
    rw [s.offsetModuli_eq]
    exact hP _
  have hcard : Fintype.card (OffsetKey S) = 9*S.card := by
    simp [OffsetKey,SelectedSlot,shiftCount_eq,ZMod.card]
    ring
  simpa only [offsetOrder,Finset.prod_const,Finset.card_univ,hcard] using
    (Finset.prod_le_prod (s := Finset.univ) (g := fun _ : OffsetKey S => P) (fun j _ => h j))

theorem mask_strip_bound {P : ℕ} (hP : ∀ j, s.prime j ≤ P)
    (g : Bool) (d : Fin k) (S : Finset (Fin m)) [NeZero (ShiftCount S)]
    (v : SharedCoordinates.Ambient s.layout) (hv : v ∈ s.mask g d S) :
    TestSupportAt 35 (fun _ => P^(9*S.card)) v.1 :=
  strip_mono (s.offsetOrder_le hP g d S) (s.mask_strip_order g d S v hv)

end
end TranslationTiling.FiniteCompiler.Packed.AxisParameters
