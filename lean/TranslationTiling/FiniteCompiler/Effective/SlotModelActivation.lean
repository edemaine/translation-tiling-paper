import TranslationTiling.FiniteCompiler.Effective.SlotModel
import TranslationTiling.FiniteCompiler.SlotActivationComplete

namespace TranslationTiling.FiniteCompiler.Packed.SlotParameters

open SharedCoordinates
open scoped Classical BigOperators
noncomputable section

set_option allowUnsafeReducibility true
attribute [local reducible] SlotParameters.layout SlotParameters.low SlotParameters.firstBlock
  SlotParameters.secondBlock SlotParameters.shiftModulus SlotParameters.observationPrime

variable {k m : ℕ} (s : SlotParameters k m) (g : Bool) (d : Fin k)
  (S : Finset (Fin m)) [NeZero (ShiftCount S)]

def unshift (u : ShiftType s g d S) : ∀ i : SlotIndex S, ZMod (s.observationPrime g d i) :=
  Equiv.piCongrLeft (fun i => ZMod (s.observationPrime g d i)) (shiftIndex S) u

@[simp] theorem unshift_index (u : ShiftType s g d S) (j : ZMod (ShiftCount S)) :
    s.unshift g d S u (shiftIndex S j) = u j :=
  Equiv.piCongrLeft_apply_apply _ _ _ _

theorem offset_residue (v : LowShifts s g d S × ShiftType s g d S) (i : SlotIndex S) :
    ((s.offset g d S v).1 : ZMod (s.observationPrime g d i)) =
      s.unshift g d S v.2 i - s.unshift g d S (SlotShift.shift v.2) i := by
  obtain ⟨j,rfl⟩ := (shiftIndex S).surjective i
  rw [unshift_index,unshift_index]
  exact s.offset_observed g d S v j

private theorem rotation_congr {K A B : Type*} {a b : ℕ}
    (D : LabeledBlocks K A B a b) {x y : ℤ}
    (ha : (x : ZMod a) = y) (hb : (x : ZMod b) = y) :
    D.T x = D.T y := by
  ext u
  apply D.decode.injective
  simp only [LabeledBlocks.decode_T]
  rcases D.decode u with ⟨a,u⟩ | ⟨b,u⟩
  · simp [LabeledBlocks.labelRotation,ha]
  · simp [LabeledBlocks.labelRotation,hb]

private def chosen (pick : SlotPicker k m) (x : SharedCoordinates.Base s.layout)
    (i : SelectedSlot S) := stateAt pick (g,d,i) x.1

def rotation (pick : SlotPicker k m) (x : SharedCoordinates.Base s.layout)
    (u : ShiftType s g d S) : LowShifts s g d S ≃ LowShifts s g d S :=
  Equiv.piCongrRight fun i =>
    (Equiv.subLeft (x.2 (wangRow (g,d,i)))).trans
      ((s.blocks (g,d,i) (chosen s g d S pick x i)).T (x.1.1-(s.offset g d S (0,u)).1))

theorem model_high_source (old : FourValueOutputGraph 0) (pick : SlotPicker k m)
    (x : SharedCoordinates.Base s.layout) (v : LowShifts s g d S × ShiftType s g d S)
    (i : SelectedSlot S) :
    (s.slotModel old pick).high (s.source g d S x v) (wangRow (g,d,i)) =
      s.rotation g d S pick x v.2 v.1 i := by
  have hc : stateAt pick (g,d,i) (s.source g d S x v).1 = chosen s g d S pick x i :=
    congrArg (pick (g,d,i)) (s.source_line g d S x v)
  rw [high_model,source_selected,hc]
  have hrot : (s.blocks (g,d,i) (chosen s g d S pick x i)).T
      (x.1.1-(s.offset g d S v).1) =
      (s.blocks (g,d,i) (chosen s g d S pick x i)).T (x.1.1-(s.offset g d S (0,v.2)).1) := by
    apply rotation_congr
    · simp only [Int.cast_sub]
      congr 1
      exact (s.offset_residue g d S v (i,none)).trans (s.offset_residue g d S (0,v.2) (i,none)).symm
    · simp only [Int.cast_sub]
      congr 1
      cases he : chosen s g d S pick x i with
      | none =>
        exact (s.offset_hidden g d S v i).trans (s.offset_hidden g d S (0,v.2) i).symm
      | some b =>
        exact (s.offset_residue g d S v (i,some b)).trans (s.offset_residue g d S (0,v.2) (i,some b)).symm
  change (s.blocks (g,d,i) (chosen s g d S pick x i)).T (x.1.1-(s.offset g d S v).1)
    ((show ZMod (s.low (g,d,i)) from x.2 (wangRow (g,d,i)))-v.1 i) = _
  rw [hrot]
  rfl

private theorem fallback_other_digit (pick : SlotPicker k m) (x : SharedCoordinates.Base s.layout)
    (v : LowShifts s g d S × ShiftType s g d S) (i : SelectedSlot S)
    (d' : Fin k) (hne : d' ≠ d) :
    s.fallbackContribution pick g d' i (s.source g d S x v) =
      s.fallbackContribution pick g d' i x := by
  have hrow : wangRow (g,d',i) ∉ selectedRows g d S := by
    intro hm
    obtain ⟨j,_,h⟩ := Finset.mem_map.mp hm
    exact hne (congrArg (fun a : WangSlot k m => a.2.1)
      (Sum.inl.inj (Sum.inr.inj h))).symm
  have hc : stateAt pick (g,d',i) (s.source g d S x v).1 = stateAt pick (g,d',i) x.1 :=
    congrArg (pick (g,d',i)) (s.source_line g d S x v)
  unfold fallbackContribution
  rw [hc,s.source_other g d S x v hrow]

private def restores (pick : SlotPicker k m) (x : SharedCoordinates.Base s.layout)
    (t : LowShifts s g d S) (z : SlotIndex S) : Prop :=
  match z with
  | (i,none) => ((s.blocks (g,d,i) (chosen s g d S pick x i)).decode (t i)).isLeft = true
  | (i,some b) => chosen s g d S pick x i = some b ∧
    ((s.blocks (g,d,i) (chosen s g d S pick x i)).decode (t i)).isRight = true

private def center (pick : SlotPicker k m) (x : SharedCoordinates.Base s.layout)
    (t : LowShifts s g d S) (z : SlotIndex S) : ZMod (s.observationPrime g d z) :=
  match z with
  | (i,none) =>
    (∑ d' ∈ Finset.univ.erase d, s.fallbackContribution pick g d' i x) +
      (show ZMod (s.fallback (g,i,false)) from
        s.firstValue (g,d,i) (chosen s g d S pick x i) (t i) -
          if restores s g d S pick x t (i,none) then (x.1.1 : ZMod (s.firstBlock (g,d,i))) else 0)
  | (i,some b) =>
    s.markerValue (g,d,i) (chosen s g d S pick x i) b (t i) -
      if restores s g d S pick x t (i,some b) then (x.1.1 : ZMod (s.marker (g,d,i) b)) else 0

theorem model_mask [Fintype (Factor s.layout)]
    (old : FourValueOutputGraph 0) (pick : SlotPicker k m)
    (ha : ∀ x : Plane, ∃ i : SelectedSlot S, stateAt pick (g,d,i) x ≠ none) :
    Tiles (s.mask g d S) (Set.range (SharedCoordinates.point s.layout (s.slotModel old pick))) := by
  apply (s.mask_iff g d S _).mpr
  intro x
  let C (t : LowShifts s g d S) : ShiftType s g d S :=
    fun j => center s g d S pick x t (shiftIndex S j)
  let R (t : LowShifts s g d S) : Set (ZMod (ShiftCount S)) :=
    {j | restores s g d S pick x t (shiftIndex S j)}
  have hR (t : LowShifts s g d S) : (R t).Nonempty := by
    obtain ⟨i,hi⟩ := ha x.1
    have h (z : SlotIndex S) (hz : restores s g d S pick x t z) : (R t).Nonempty :=
      ⟨(shiftIndex S).symm z,by simpa [R] using hz⟩
    cases hstate : chosen s g d S pick x i with
    | none => exact False.elim (hi hstate)
    | some b =>
      cases hd : (s.blocks (g,d,i) (chosen s g d S pick x i)).decode (t i) with
      | inl _ => apply h (i,none); simp [restores,hd]
      | inr _ => apply h (i,some b); simp [restores,hstate] at hd ⊢; rw [hd]; simp
  have hmap (v : LowShifts s g d S × ShiftType s g d S) :
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
    have hcoord (z : SlotIndex S) :
        s.observe g d z (SharedCoordinates.point s.layout (s.slotModel old pick) u).2 +
          s.unshift g d S (SlotShift.shift v.2) z =
        center s g d S pick x t z + (if restores s g d S pick x t z
          then s.unshift g d S v.2 z else s.unshift g d S (SlotShift.shift v.2) z) := by
      have hh := s.offset_residue g d S v z
      rcases z with ⟨i,_ | b⟩
      all_goals
        have hs : stateAt pick (g,d,i) u.1 = chosen s g d S pick x i :=
          congrArg (pick (g,d,i)) (s.source_line g d S x v)
        let D := s.blocks (g,d,i) (chosen s g d S pick x i)
        let lo : ZMod (s.low (g,d,i)) := u.2 (wangRow (g,d,i))
        let z := x.1.1-(s.offset g d S v).1
        have hraw := s.high_model old pick (g,d,i) u
        rw [hs] at hraw
        have ht : t i = D.T z lo :=
          (s.model_high_source g d S old pick x v i).symm.trans hraw
        have hlabel := (congrArg D.decode ht).trans (LabeledBlocks.decode_T D z lo)
        change (s.blocks (g,d,i) (chosen s g d S pick x i)).decode (t i) =
          LabeledBlocks.labelRotation (x.1.1-(s.offset g d S v).1)
            ((s.blocks (g,d,i) (chosen s g d S pick x i)).decode lo) at hlabel
      · change s.observeFallback (g,i,false) _ + _ = _
        rw [observeFallback_model,← Finset.sum_erase_add _ _ (Finset.mem_univ d)]
        have hsum :
            (∑ d' ∈ Finset.univ.erase d, s.fallbackContribution pick g d' i u) =
              ∑ d' ∈ Finset.univ.erase d, s.fallbackContribution pick g d' i x :=
          Finset.sum_congr rfl (fun d' hd' => s.fallback_other_digit g d S pick x v i d'
            (Finset.ne_of_mem_erase hd'))
        rw [hsum]
        change (∑ d' ∈ Finset.univ.erase d, s.fallbackContribution pick g d' i x) +
          s.firstValue (g,d,i) (stateAt pick (g,d,i) u.1) lo + _ = _
        rw [hs]
        dsimp only [center,restores,firstValue,LabeledBlocks.C]
        cases hsrc : (s.blocks (g,d,i) (chosen s g d S pick x i)).decode
          lo with
        | inl a =>
          rcases a with ⟨a,y⟩
          rw [hsrc] at hlabel
          simp [hlabel,LabeledBlocks.labelRotation,Int.cast_sub,hh]; abel
        | inr a =>
          rcases a with ⟨a,y⟩
          rw [hsrc] at hlabel
          simp [hlabel,LabeledBlocks.labelRotation]
      · change s.observeMarker (g,d,i) b _ + _ = _
        rw [observeMarker_model]
        unfold slotMarkerAt
        rw [hs]
        by_cases hs' : chosen s g d S pick x i = some b
        · rw [hs'] at hlabel
          simp only [center,restores,hs',true_and,markerValue]
          unfold LabeledBlocks.C
          cases hsrc : (s.blocks (g,d,i) (some b)).decode lo with
          | inl a =>
            rcases a with ⟨a,y⟩
            rw [hsrc] at hlabel
            rw [hs',hlabel]
            simp [LabeledBlocks.labelRotation]
          | inr a =>
            rcases a with ⟨a,y⟩
            rw [hsrc] at hlabel
            rw [hs',hlabel]
            simp [LabeledBlocks.labelRotation,Int.cast_sub,hh]; abel
        · simp [center,restores,markerValue,hs']
    change s.observe g d (shiftIndex S j) (SharedCoordinates.point s.layout (s.slotModel old pick) u).2 +
      SlotShift.shift v.2 j = _
    change _ = C t j + SlotShift.restore (R t) v.2 j
    simpa only [unshift_index,SlotShift.restore,Set.mem_ofPred_eq,C,R] using hcoord (shiftIndex S j)
  rw [funext hmap]
  exact SlotShift.block_map_bijective (fun j => (s.shiftModulus_prime g d S j).one_lt)
    (s.rotation g d S pick x) R hR C

end
end TranslationTiling.FiniteCompiler.Packed.SlotParameters
