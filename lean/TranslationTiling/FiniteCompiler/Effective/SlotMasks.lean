import TranslationTiling.FiniteCompiler.Effective.SlotOffsetTable

namespace TranslationTiling.FiniteCompiler.Packed.SlotParameters

open SharedCoordinates
open scoped Classical
noncomputable section

variable {k m : ℕ} (s : SlotParameters k m)

abbrev wangRow (i : WangSlot k m) : SlotRow k m := .inr (.inl i)

def slotEmbedding (g : Bool) (d : Fin k) : Fin m ↪ SlotRow k m :=
  ⟨fun i => wangRow (g,d,i), fun _ _ h => congrArg (fun i : WangSlot k m => i.2.2)
    (Sum.inl.inj (Sum.inr.inj h))⟩

def selectedRows (g : Bool) (d : Fin k) (S : Finset (Fin m)) := S.map (slotEmbedding g d)

def selectedEquiv (g : Bool) (d : Fin k) (S : Finset (Fin m)) :
    SelectedSlot S ≃ {i // i ∈ selectedRows g d S} :=
  Finset.equivMap (slotEmbedding g d) S

def highEquiv (g : Bool) (d : Fin k) (S : Finset (Fin m)) :
    LowShifts s g d S ≃ SlotHigh s.layout (selectedRows g d S) :=
  Equiv.piCongrLeft (fun i : {i // i ∈ selectedRows g d S} => SharedCoordinates.Low s.layout i.val) (selectedEquiv g d S)

@[simp] theorem highEquiv_apply_selected (g : Bool) (d : Fin k) (S : Finset (Fin m))
    (v : LowShifts s g d S) (i : SelectedSlot S) :
    s.highEquiv g d S v (selectedEquiv g d S i) = v i :=
  Equiv.piCongrLeft_apply_apply (fun j : {j // j ∈ selectedRows g d S} =>
    SharedCoordinates.Low s.layout j.val) (selectedEquiv g d S) v i

def slopeNumber (g : Bool) : ℤ := if g then 0 else 2

def slotLine (g : Bool) (p : Plane) : ℤ := p.2 + slopeNumber g * p.1

theorem slotLine_sub (g : Bool) (p h : Plane) (hh : h.2 = -slopeNumber g * h.1) :
    slotLine g (p-h) = slotLine g p := by
  change p.2-h.2+slopeNumber g*(p.1-h.1) = _
  rw [hh]
  unfold slotLine
  ring

section Mask

variable (g : Bool) (d : Fin k) (S : Finset (Fin m)) [NeZero (ShiftCount S)]

abbrev ShiftType := SlotShift.Shift (s.shiftModulus g d S)

def projection : Factor s.layout →+ ShiftType s g d S :=
  AddMonoidHom.pi fun j => s.observe g d (shiftIndex S j)

theorem projection_target (x : SharedCoordinates.Base s.layout)
    (y : ShiftType s g d S × SlotHigh s.layout (selectedRows g d S)) :
    ∃ v : SharedCoordinates.Ambient s.layout, baseProjection s.layout v = x ∧
      (s.projection g d S v.2,fun i : {i // i ∈ selectedRows g d S} =>
        highCoordinate s.layout i v) = y := by
  let e := shiftIndex S
  let y' := Equiv.piCongrLeft (fun i => ZMod (s.observationPrime g d i)) e y.1
  let H (i : SlotRow k m) : SharedCoordinates.Low s.layout i :=
    if hi : i ∈ selectedRows g d S then y.2 ⟨i,hi⟩ else 0
  obtain ⟨v,hv,ho,hh⟩ := s.observe_target g d S x H y'
  refine ⟨v,hv,Prod.ext (funext fun j => ?_) (funext fun i => ?_)⟩
  · exact (ho (e j)).trans (Equiv.piCongrLeft_apply_apply _ e _ j)
  · exact (hh i).trans (dite_eq_left i.property)

def offset := s.slotOffset g d S (slopeNumber g)

theorem offset_injective : Function.Injective (s.offset g d S) :=
  (s.slotOffset_spec g d S _).1

theorem offset_slope (v : LowShifts s g d S × ShiftType s g d S) :
    (s.offset g d S v).2 = -slopeNumber g * (s.offset g d S v).1 :=
  ((s.slotOffset_spec g d S _).2 v).1

theorem offset_low (v : LowShifts s g d S × ShiftType s g d S) (i : SelectedSlot S) :
    ((s.offset g d S v).1 : ZMod (s.low (g,d,i))) = v.1 i :=
  ((s.slotOffset_spec g d S _).2 v).2.1 i

theorem offset_hidden (v : LowShifts s g d S × ShiftType s g d S) (i : SelectedSlot S) :
    ((s.offset g d S v).1 : ZMod (s.fallback (g,i,true))) = 0 :=
  ((s.slotOffset_spec g d S _).2 v).2.2.1 i

theorem offset_observed (v : LowShifts s g d S × ShiftType s g d S) (j : ZMod (ShiftCount S)) :
    ((s.offset g d S v).1 : ZMod (s.shiftModulus g d S j)) = v.2 j - SlotShift.shift v.2 j :=
  ((s.slotOffset_spec g d S _).2 v).2.2.2.1 j

def liftedOffset (v : SlotHigh s.layout (selectedRows g d S) × ShiftType s g d S) : Plane :=
  s.offset g d S ((s.highEquiv g d S).symm v.1,v.2)

theorem liftedOffset_injective : Function.Injective (s.liftedOffset g d S) :=
  (s.offset_injective g d S).comp (((s.highEquiv g d S).symm.prodCongr (.refl _)).injective)

def source (x : SharedCoordinates.Base s.layout) (v : LowShifts s g d S × ShiftType s g d S) :=
  slotActivationSource s.layout (selectedRows g d S) (s.offset g d S v) x

@[simp] theorem source_selected (x : SharedCoordinates.Base s.layout)
    (v : LowShifts s g d S × ShiftType s g d S) (i : SelectedSlot S) :
    (s.source g d S x v).2 (wangRow (g,d,i)) =
      x.2 (wangRow (g,d,i)) - (show SharedCoordinates.Low s.layout (wangRow (g,d,i)) from v.1 i) := by
  have hm : wangRow (g,d,i) ∈ selectedRows g d S := Finset.mem_map.mpr ⟨i.val,i.property,rfl⟩
  let z : ZMod (s.low (g,d,i)) := x.2 (wangRow (g,d,i))
  simp only [source,slotActivationSource,hm,ite_true]
  exact congrArg (z - ·) (s.offset_low g d S v i)

theorem source_other (x : SharedCoordinates.Base s.layout)
    (v : LowShifts s g d S × ShiftType s g d S) {i : SlotRow k m}
    (hi : i ∉ selectedRows g d S) : (s.source g d S x v).2 i = x.2 i := by
  exact ite_eq_right hi

theorem source_line (x : SharedCoordinates.Base s.layout)
    (v : LowShifts s g d S × ShiftType s g d S) :
    slotLine g (s.source g d S x v).1 = slotLine g x.1 :=
  slotLine_sub g _ _ (s.offset_slope g d S v)

def mask [Fintype (Factor s.layout)] : Finset (SharedCoordinates.Ambient s.layout) :=
  selectedSlotTile s.layout (selectedRows g d S) (s.projection g d S) (s.liftedOffset g d S)

theorem mask_iff [Fintype (Factor s.layout)] (o : SharedCoordinates.Outputs s.layout) :
    Tiles (s.mask g d S) (Set.range (SharedCoordinates.point s.layout o)) ↔
      ∀ x, Function.Bijective (fun v : LowShifts s g d S × ShiftType s g d S =>
        let u := s.source g d S x v
        (s.projection g d S (SharedCoordinates.point s.layout o u).2 + SlotShift.shift v.2,
          fun i : SelectedSlot S => o.high u (wangRow (g,d,i)))) := by
  rw [mask, selectedSlotTile_iff _ _ _ _ (s.liftedOffset_injective g d S) _ (s.projection_target g d S)]
  apply forall_congr'
  intro x
  let e := (s.highEquiv g d S).prodCongr (Equiv.refl (ShiftType s g d S))
  let e' := (Equiv.refl (ShiftType s g d S)).prodCongr (s.highEquiv g d S).symm
  let f (v : SlotHigh s.layout (selectedRows g d S) × ShiftType s g d S) :=
    let u := slotActivationSource s.layout (selectedRows g d S) (s.liftedOffset g d S v) x
    (s.projection g d S (SharedCoordinates.point s.layout o u).2 + SlotShift.shift v.2,
      fun i : {i // i ∈ selectedRows g d S} => o.high u i)
  have h (v : LowShifts s g d S × ShiftType s g d S) :
      e' (f (e v)) =
        (s.projection g d S (SharedCoordinates.point s.layout o (s.source g d S x v)).2 +
          SlotShift.shift v.2,fun i : SelectedSlot S => o.high (s.source g d S x v) (wangRow (g,d,i))) := by
    have hu : slotActivationSource s.layout (selectedRows g d S) (s.liftedOffset g d S (e v)) x =
      s.source g d S x v := by
      unfold liftedOffset
      change slotActivationSource s.layout (selectedRows g d S)
        (s.offset g d S ((s.highEquiv g d S).symm (s.highEquiv g d S v.1),v.2)) x = _
      rw [Equiv.symm_apply_apply]
      rfl
    unfold f
    rw [hu]
    exact Prod.ext rfl (funext fun i => by
      change (s.highEquiv g d S).symm (fun j => o.high (s.source g d S x v) j.val) i = _
      rfl)
  change Function.Bijective f ↔ _
  rw [← funext h]
  exact ⟨fun hf => e'.bijective.comp (hf.comp e.bijective),
    fun hf => by
      have hp := e'.symm.bijective.comp (hf.comp e.symm.bijective)
      convert hp using 1
      funext u
      change f u = e'.symm (e' (f (e (e.symm u))))
      rw [Equiv.apply_symm_apply,Equiv.symm_apply_apply]⟩

end Mask
end
end TranslationTiling.FiniteCompiler.Packed.SlotParameters
