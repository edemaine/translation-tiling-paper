import TranslationTiling.FiniteCompiler.Effective.AxisSlotModel
import TranslationTiling.FiniteCompiler.SlotActivationComplete

namespace TranslationTiling.FiniteCompiler.Packed.AxisParameters

open SharedCoordinates
open scoped Classical BigOperators

noncomputable section

set_option allowUnsafeReducibility true
attribute [local reducible] AxisParameters.layout AxisParameters.low
  AxisParameters.firstBlock AxisParameters.secondBlock AxisParameters.shiftModulus
  AxisParameters.observationPrime AxisParameters.offset AxisParameters.source AxisParameters.axisState


variable {k m : ℕ} (s : AxisParameters k m) (g : Bool) (d : Fin k)
  (S : Finset (Fin m)) [NeZero (ShiftCount S)]

def unshift (u : ShiftType s g d S) : ∀ i : SlotIndex S, ZMod (s.observationPrime g d i) :=
  Equiv.piCongrLeft (fun i => ZMod (s.observationPrime g d i)) (shiftIndex S) u

@[simp] theorem unshift_index (u : ShiftType s g d S) (j : ZMod (ShiftCount S)) :
    s.unshift g d S u (shiftIndex S j) = u j :=
  Equiv.piCongrLeft_apply_apply _ _ _ _

theorem offset_residue (v : ShiftPair s g d S) (i : SlotIndex S) :
    ((s.offset g d S v).1 : ZMod (s.observationPrime g d i)) =
      s.unshift g d S v.2 i - s.unshift g d S (SlotShift.shift v.2) i := by
  obtain ⟨j,rfl⟩ := (shiftIndex S).surjective i
  simpa only [unshift_index] using s.offset_observed g d S v j

private theorem rotation_congr {K A B : Type*} {a b : ℕ}
    (D : LabeledBlocks K A B a b) {x y : ℤ}
    (ha : (x : ZMod a) = y) (hb : (x : ZMod b) = y) : D.T x = D.T y := by
  ext u
  apply D.decode.injective
  simp only [LabeledBlocks.decode_T]
  rcases D.decode u with ⟨a,u⟩ | ⟨b,u⟩
  · simp [LabeledBlocks.labelRotation,ha]
  · simp [LabeledBlocks.labelRotation,hb]

private theorem first_coord {K A B : Type*} {a b : ℕ} (D : LabeledBlocks K A B a b)
    (u : K) (x h : ℤ) :
    (D.C u).1 = (D.C (D.T (x-h) u)).1 -
      (if (D.decode (D.T (x-h) u)).isLeft then (x : ZMod a) else 0) +
      (if (D.decode (D.T (x-h) u)).isLeft then (h : ZMod a) else 0) := by
  rw [LabeledBlocks.decode_T]
  simp only [LabeledBlocks.C,LabeledBlocks.decode_T]
  rcases D.decode u with ⟨a,y⟩ | ⟨b,y⟩ <;>
    simp [LabeledBlocks.labelRotation,Int.cast_sub]
  all_goals abel

private theorem second_coord {K A B : Type*} {a b : ℕ} (D : LabeledBlocks K A B a b)
    (u : K) (x h : ℤ) :
    (D.C u).2 = (D.C (D.T (x-h) u)).2 -
      (if (D.decode (D.T (x-h) u)).isRight then (x : ZMod b) else 0) +
      (if (D.decode (D.T (x-h) u)).isRight then (h : ZMod b) else 0) := by
  rw [LabeledBlocks.decode_T]
  simp only [LabeledBlocks.C,LabeledBlocks.decode_T]
  rcases D.decode u with ⟨a,y⟩ | ⟨b,y⟩ <;>
    simp [LabeledBlocks.labelRotation,Int.cast_sub]
  all_goals abel

private def chosen (pick : SlotPicker k m) (x : SharedCoordinates.Base s.layout)
    (i : SelectedSlot S) := stateAt pick (g,d,i) x.1

def rotation (pick : SlotPicker k m) (x : SharedCoordinates.Base s.layout)
    (z : ShiftType s g d S) : LowShifts s g d S ≃ LowShifts s g d S :=
  Equiv.piCongrRight fun i =>
    (Equiv.subLeft (x.2 (wangRow (g,d,i)))).trans
      (s.blockRotation (g,d,i) (chosen s g d S pick x i) (x.1.1-(s.offset g d S (0,z)).1))

private theorem axis_rotation_congr (pick : SlotPicker k m) (x : SharedCoordinates.Base s.layout)
    (v : ShiftPair s g d S) (i : SelectedSlot S) (a : Bool) :
    let D := s.blocks (g,d,i) a (axisState (chosen s g d S pick x i) a)
    D.T (x.1.1-(s.offset g d S v).1) = D.T (x.1.1-(s.offset g d S (0,v.2)).1) := by
  let σ := axisState (chosen s g d S pick x i) a
  change (s.blocks (g,d,i) a σ).T _ = _
  apply rotation_congr
  · simp only [Int.cast_sub]
    congr 1
    exact (s.offset_residue g d S v (i,.inl a)).trans
      (s.offset_residue g d S (0,v.2) (i,.inl a)).symm
  · simp only [Int.cast_sub]
    congr 1
    cases σ with
    | none => exact (s.offset_hidden g d S v i a).trans (s.offset_hidden g d S (0,v.2) i a).symm
    | some b =>
      exact (s.offset_residue g d S v (i,.inr b)).trans
        (s.offset_residue g d S (0,v.2) (i,.inr b)).symm

theorem model_high_source (old : FourValueOutputGraph 0) (pick : SlotPicker k m)
    (x : SharedCoordinates.Base s.layout) (v : ShiftPair s g d S)
    (i : SelectedSlot S) :
    (s.slotModel old pick).high (s.source g d S x v) (wangRow (g,d,i)) =
      s.rotation g d S pick x v.2 v.1 i := by
  have hc : stateAt pick (g,d,i) (s.source g d S x v).1 = chosen s g d S pick x i :=
    congrArg (pick (g,d,i)) (s.source_line g d S x v)
  rw [high_model,source_selected,hc]
  have hx : (s.source g d S x v).1.1 = x.1.1-(s.offset g d S v).1 := rfl
  rw [hx]
  apply (s.lowEquiv (g,d,i)).injective
  apply Prod.ext
  · change s.axisInput (g,d,i) false (s.blockRotation _ _ _ _) =
      s.axisInput (g,d,i) false (s.blockRotation _ _ _ _)
    simp only [axisInput_blockRotation]
    rw [s.axis_rotation_congr g d S pick x v i false]
    rfl
  · change s.axisInput (g,d,i) true (s.blockRotation _ _ _ _) =
      s.axisInput (g,d,i) true (s.blockRotation _ _ _ _)
    simp only [axisInput_blockRotation]
    rw [s.axis_rotation_congr g d S pick x v i true]
    rfl

private theorem fallback_other_digit (pick : SlotPicker k m) (x : SharedCoordinates.Base s.layout)
    (v : ShiftPair s g d S) (i : SelectedSlot S) (a : Bool)
    (d' : Fin k) (hne : d' ≠ d) :
    s.fallbackContribution pick g d' i a (s.source g d S x v) =
      s.fallbackContribution pick g d' i a x := by
  have hrow : wangRow (g,d',i) ∉ selectedRows g d S := by
    intro hm
    obtain ⟨j,_,h⟩ := Finset.mem_map.mp hm
    exact hne (congrArg (fun a : WangSlot k m => a.2.1)
      (Sum.inl.inj (Sum.inr.inj h))).symm
  have hc : stateAt pick (g,d',i) (s.source g d S x v).1 = stateAt pick (g,d',i) x.1 :=
    congrArg (pick (g,d',i)) (s.source_line g d S x v)
  dsimp only [fallbackContribution]
  rw [hc,s.source_other g d S x v hrow]

private def isLeftAt (i : WangSlot k m) (a : Bool) (j : Option (Fin 3))
    (v : ZMod (s.low i)) : Bool :=
  ((s.blocks i a j).decode (s.axisInput i a v)).isLeft

private def isLeft (pick : SlotPicker k m) (x : SharedCoordinates.Base s.layout)
    (t : LowShifts s g d S) (i : SelectedSlot S) (a : Bool) : Bool :=
  s.isLeftAt (g,d,i) a (axisState (chosen s g d S pick x i) a) (t i)

private theorem isLeftAt_eq_false (i : WangSlot k m) (a : Bool) (j : Option (Fin 3))
    (v : ZMod (s.low i)) :
    s.isLeftAt i a j v = false ↔
      ((s.blocks i a j).decode (s.axisInput i a v)).isRight = true := by
  unfold isLeftAt
  cases (s.blocks i a j).decode (s.axisInput i a v) <;> simp

private def restores (pick : SlotPicker k m) (x : SharedCoordinates.Base s.layout)
    (t : LowShifts s g d S) (z : SlotIndex S) : Prop :=
  match z with
  | (i,.inl a) => s.isLeft g d S pick x t i a = true
  | (i,.inr b) => ∃ a, chosen s g d S pick x i = some (a,b) ∧
      s.isLeft g d S pick x t i a = false

private def center (pick : SlotPicker k m) (x : SharedCoordinates.Base s.layout)
    (t : LowShifts s g d S) (z : SlotIndex S) : ZMod (s.observationPrime g d z) :=
  let y := match z with
    | (i,.inl a) =>
      (∑ d' ∈ Finset.univ.erase d, s.fallbackContribution pick g d' i a x) +
      ((s.blocks (g,d,i) a (axisState (chosen s g d S pick x i) a)).C
        (s.axisInput (g,d,i) a (t i))).1
    | (i,.inr b) => s.markerValue (g,d,i) (chosen s g d S pick x i) b (t i)
  y - if restores s g d S pick x t z then (x.1.1 : ZMod (s.observationPrime g d z)) else 0

private theorem axis_value_source (old : FourValueOutputGraph 0) (pick : SlotPicker k m)
    (x : SharedCoordinates.Base s.layout) (v : ShiftPair s g d S)
    (i : SelectedSlot S) (a : Bool) :
    let u := s.source g d S x v
    let t := s.rotation g d S pick x v.2 v.1
    let D := s.blocks (g,d,i) a (axisState (chosen s g d S pick x i) a)
    s.axisInput (g,d,i) a (t i) =
      D.T (x.1.1-(s.offset g d S v).1) (s.axisInput (g,d,i) a (u.2 (wangRow (g,d,i)))) := by
  dsimp only
  rw [← s.model_high_source g d S old pick x v i, high_model, axisInput_blockRotation]
  have hc : stateAt pick (g,d,i) (s.source g d S x v).1 = chosen s g d S pick x i :=
    congrArg (pick (g,d,i)) (s.source_line g d S x v)
  rw [hc]
  rfl

private theorem coord_source (old : FourValueOutputGraph 0) (pick : SlotPicker k m)
    (x : SharedCoordinates.Base s.layout) (v : ShiftPair s g d S) (z : SlotIndex S) :
    let u := s.source g d S x v
    let t := s.rotation g d S pick x v.2 v.1
    s.observe g d z (SharedCoordinates.point s.layout (s.slotModel old pick) u).2 =
      s.center g d S pick x t z +
        (if s.restores g d S pick x t z then ((s.offset g d S v).1 : ZMod (s.observationPrime g d z))
         else 0) := by
  let u := s.source g d S x v
  let t := s.rotation g d S pick x v.2 v.1
  rcases z with ⟨i,a | b⟩
  all_goals
    have hstate : stateAt pick (g,d,i) u.1 = chosen s g d S pick x i :=
      congrArg (pick (g,d,i)) (s.source_line g d S x v)
  · change s.observeFallback (g,i,a,false) _ = _
    rw [observeFallback_model,← Finset.sum_erase_add _ _ (Finset.mem_univ d)]
    have hsum : (∑ e ∈ Finset.univ.erase d, s.fallbackContribution pick g e i a u) =
        ∑ e ∈ Finset.univ.erase d, s.fallbackContribution pick g e i a x :=
      Finset.sum_congr rfl (fun e he => s.fallback_other_digit g d S pick x v i a e
        (Finset.ne_of_mem_erase he))
    rw [hsum]
    change (∑ e ∈ Finset.univ.erase d, s.fallbackContribution pick g e i a x) +
      ((s.blocks (g,d,i) a (axisState (stateAt pick (g,d,i) u.1) a)).C
        (s.axisInput (g,d,i) a (u.2 (wangRow (g,d,i))))).1 = _
    rw [hstate]
    have h := s.axis_value_source g d S old pick x v i a
    dsimp only at h
    simp only [center,restores,isLeft,isLeftAt,observationPrime,h]
    rw [first_coord _ _ x.1.1 (s.offset g d S v).1]
    abel
  · change s.observeMarker (g,d,i) b _ = _
    rw [observeMarker_model]
    unfold slotMarkerAt
    rw [hstate]
    by_cases h₀ : chosen s g d S pick x i = some (false,b)
    · have h := s.axis_value_source g d S old pick x v i false
      dsimp only at h
      rw [h₀] at h
      simp [axisState] at h
      simp [center,restores,isLeft,markerValue,observationPrime,h₀,axisState,isLeftAt_eq_false,h]
      simpa only [LabeledBlocks.decode_T] using
        second_coord (s.blocks (g,d,i) false (some b))
          (s.axisInput (g,d,i) false (u.2 (wangRow (g,d,i)))) x.1.1 (s.offset g d S v).1
    by_cases h₁ : chosen s g d S pick x i = some (true,b)
    · have h := s.axis_value_source g d S old pick x v i true
      dsimp only at h
      rw [h₁] at h
      simp [axisState] at h
      simp [center,restores,isLeft,markerValue,observationPrime,h₁,axisState,isLeftAt_eq_false,h]
      simpa only [LabeledBlocks.decode_T] using
        second_coord (s.blocks (g,d,i) true (some b))
          (s.axisInput (g,d,i) true (u.2 (wangRow (g,d,i)))) x.1.1 (s.offset g d S v).1
    simp [center,restores,markerValue,h₀,h₁,observationPrime]

theorem model_mask [Fintype (Factor s.layout)]
    (old : FourValueOutputGraph 0) (pick : SlotPicker k m)
    (ha : ∀ x : Plane, ∃ i : SelectedSlot S, stateAt pick (g,d,i) x ≠ none) :
    Tiles (s.mask g d S) (Set.range (SharedCoordinates.point s.layout (s.slotModel old pick))) := by
  apply (s.mask_iff g d S _).mpr
  intro x
  let C (t : LowShifts s g d S) : ShiftType s g d S :=
    fun j => s.center g d S pick x t (shiftIndex S j)
  let R (t : LowShifts s g d S) : Set (ZMod (ShiftCount S)) :=
    {j | s.restores g d S pick x t (shiftIndex S j)}
  have hR (t : LowShifts s g d S) : (R t).Nonempty := by
    obtain ⟨i,hi⟩ := ha x.1
    have h (z : SlotIndex S) (hz : s.restores g d S pick x t z) : (R t).Nonempty :=
      ⟨(shiftIndex S).symm z,by simpa [R] using hz⟩
    cases hs : chosen s g d S pick x i with
    | none => exact False.elim (hi hs)
    | some l =>
      rcases l with ⟨a,b⟩
      cases hh : s.isLeft g d S pick x t i a
      · exact h (i,.inr b) ⟨a,hs,hh⟩
      · exact h (i,.inl a) hh
  have hmap (v : ShiftPair s g d S) :
      let u := s.source g d S x v
      let t := s.rotation g d S pick x v.2 v.1
      (s.projection g d S (SharedCoordinates.point s.layout (s.slotModel old pick) u).2 +
          SlotShift.shift v.2,fun i : SelectedSlot S => (s.slotModel old pick).high u (wangRow (g,d,i))) =
        (C t + SlotShift.restore (R t) v.2,t) := by
    dsimp only
    apply Prod.ext _ (funext fun i => s.model_high_source g d S old pick x v i)
    funext j
    let u := s.source g d S x v
    let t := s.rotation g d S pick x v.2 v.1
    let z := shiftIndex S j
    change s.observe g d z (SharedCoordinates.point s.layout (s.slotModel old pick) u).2 +
      SlotShift.shift v.2 j = C t j + SlotShift.restore (R t) v.2 j
    have h := s.coord_source g d S old pick x v z
    have ho := s.offset_observed g d S v j
    change s.observe g d z (SharedCoordinates.point s.layout (s.slotModel old pick) u).2 =
      C t j + (if j ∈ R t then ((s.offset g d S v).1 : ZMod (s.shiftModulus g d S j))
        else 0) at h
    rw [h,ho]
    by_cases hj : j ∈ R t <;> simp [SlotShift.restore,hj,add_assoc]
  rw [funext hmap]
  exact SlotShift.block_map_bijective (fun j => (s.shiftModulus_prime g d S j).one_lt)
    (s.rotation g d S pick x) R hR C

end
end TranslationTiling.FiniteCompiler.Packed.AxisParameters
