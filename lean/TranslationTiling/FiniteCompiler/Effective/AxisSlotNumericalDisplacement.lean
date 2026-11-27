import TranslationTiling.FiniteCompiler.Effective.SlotNumericalActivation
import TranslationTiling.FiniteCompiler.Effective.AxisSlotNumericalBatch

namespace TranslationTiling.FiniteCompiler.Packed.AxisParameters

open SharedCoordinates Compiler.Effective
open scoped BigOperators Classical
noncomputable section

set_option maxHeartbeats 1000000

variable {k m : ℕ} (s : AxisParameters k m)
variable (g : Bool) (d : Fin k) (S : Finset (Fin m)) [NeZero (ShiftCount S)]

/-- The observed moduli in the order used by the cyclic shift. -/
def observedModuli : List ℕ :=
  List.ofFn fun j : Fin (ShiftCount S) => s.shiftModulus g d S (j.val : ZMod (ShiftCount S))

private theorem observedModuli_length :
    (s.observedModuli g d S).length = ShiftCount S := List.length_ofFn

private theorem observedModuli_get (j : ZMod (ShiftCount S)) :
    (s.observedModuli g d S).getD j.val 0 = s.shiftModulus g d S j := by
  rw [List.getD_eq_getElem _ _ (by rw [s.observedModuli_length]; exact ZMod.val_lt j)]
  simp only [observedModuli,List.getElem_ofFn]
  rw [ZMod.natCast_zmod_val]

theorem observedModuli_prod : (s.observedModuli g d S).prod = s.outputShiftOrder g d S := by
  rw [observedModuli,List.prod_ofFn,outputShiftOrder]
  have hfin (n : ℕ) [NeZero n] (i : Fin n) :
      (i.val : ZMod n) = ZMod.finEquiv n i := by
    cases n with
    | zero => exact i.elim0
    | succ n =>
      apply ZMod.val_injective
      rw [ZMod.val_natCast,Nat.mod_eq_of_lt i.isLt]
      rfl
  apply Fintype.prod_equiv (ZMod.finEquiv (ShiftCount S)).toEquiv
  intro i
  exact congrArg (s.shiftModulus g d S) (hfin _ i)

private theorem observedModuli_coords (output : ℕ) :
    (s.observedModuli g d S).map (output % ·) =
      List.ofFn (fun i : Fin (ShiftCount S) =>
        (s.outputShiftCRT g d S (output : ZMod (s.outputShiftOrder g d S))
          (i.val : ZMod (ShiftCount S))).val) := by
  rw [observedModuli,List.map_ofFn]
  congr 1
  funext i
  have he := congrFun (map_natCast (s.outputShiftCRT g d S) output) (i.val : ZMod (ShiftCount S))
  rw [he]
  exact (ZMod.val_natCast _ _).symm

private theorem offsetOrder_product (hiddenOrder : ℕ)
    (hh : hiddenOrder = ∏ i : SelectedSlot S, ∏ a : Bool, s.fallback (g,i,a,true)) :
    s.lowShiftOrder g d S * s.outputShiftOrder g d S * hiddenOrder = s.offsetOrder g d S := by
  rw [hh,offsetOrder,Fintype.prod_sum_type,Fintype.prod_prod_type,lowShiftOrder,outputShiftOrder]
  simp_rw [Fintype.prod_prod_type,Fintype.prod_bool,offsetModuli,low,Finset.prod_mul_distrib]
  ac_rfl

/-- The two packed indices determine the same plane displacement as the
typed CRT construction. The output equation also gives the exact batch
conditions after applying the cyclic shift. -/
theorem numericalSlotRecord_correct
    (selected remaining hidden : List ℕ)
    (hlP : selected.prod = s.lowShiftOrder g d S)
    (hhP : hidden.prod = ∏ i : SelectedSlot S, ∏ a : Bool, s.fallback (g,i,a,true))
    (hl : ∀ r, r ∈ selected ↔ ∃ i : SelectedSlot S, s.low (g,d,i) = r)
    (hh : ∀ r, r ∈ hidden ↔ ∃ (i : SelectedSlot S) (a : Bool), s.fallback (g,i,a,true) = r)
    {low output : ℕ} (_hlo : low < selected.prod) (_hout : output < (s.observedModuli g d S).prod) :
    let observed := s.observedModuli g d S
    let b : NumericalSlotBatch := (order s.layout,slopeNumber g,selected,remaining,observed,hidden)
    let v : ShiftPair s g d S :=
      (s.lowShiftCRT g d S (low : ZMod (s.lowShiftOrder g d S)),
       s.outputShiftCRT g d S (output : ZMod (s.outputShiftOrder g d S)))
    let h := s.offset g d S v
    (numericalSlotRecord b low output).1 = h ∧
      (numericalSlotRecord b low output).2 =
        (selected.map fun r => (r^2,(h.1 % (r^2 : ℕ)).toNat)) ++ (remaining.map (·,0)) ++
        (List.range observed.length).map fun j =>
          (observed.getD j 0,(numericalSlotShift (observed.map (output % ·))).getD j 0) := by
  let observed := s.observedModuli g d S
  let v : ShiftPair s g d S :=
    (s.lowShiftCRT g d S (low : ZMod (s.lowShiftOrder g d S)),
     s.outputShiftCRT g d S (output : ZMod (s.outputShiftOrder g d S)))
  let coords := observed.map (output % ·)
  let shifts := numericalSlotShift coords
  let cs := (selected.map fun p => (p,low % p)) ++ (hidden.map (·,0)) ++
    (List.range observed.length).map (fun j => (observed.getD j 0,
      differenceResidue (observed.getD j 0) (coords.getD j 0) (shifts.getD j 0)))
  have hmod : selected.prod * observed.prod * hidden.prod = s.offsetOrder g d S := by
    rw [hlP,s.observedModuli_prod]
    exact s.offsetOrder_product g d S hidden.prod hhP
  have hget (j : ZMod (ShiftCount S)) : coords.getD j.val 0 = (v.2 j).val := by
    rw [show coords = List.ofFn (fun i : Fin (ShiftCount S) =>
      (v.2 (i.val : ZMod (ShiftCount S))).val) from s.observedModuli_coords g d S output]
    rw [List.getD_eq_getElem _ _ (by simpa using ZMod.val_lt j)]
    simp only [List.getElem_ofFn]
    rw [ZMod.natCast_zmod_val]
  have hshift (j : ZMod (ShiftCount S)) : shifts.getD j.val 0 = (SlotShift.shift v.2 j).val := by
    unfold shifts coords
    rw [s.observedModuli_coords g d S]
    exact numericalSlotShift_correct (fun i => (s.shiftModulus_prime g d S i).one_lt) v.2 j
  have hcong (n : ℕ) : Congruences cs n ↔
      s.offsetCRT g d S (n : ZMod (s.offsetOrder g d S)) = s.offsetResidues g d S v := by
    rw [funext_iff]
    have hcast (i : OffsetKey S) := congrFun (map_natCast (s.offsetCRT g d S) n) i
    simp only [hcast]
    have htest : Congruences cs n ↔
        (∀ i : SelectedSlot S, n % (s.low (g,d,i)) = low % (s.low (g,d,i))) ∧
        (∀ (i : SelectedSlot S) (a : Bool), n % (s.fallback (g,i,a,true)) = 0) ∧
        (∀ j : ZMod (ShiftCount S),
          n % (s.shiftModulus g d S j) = (v.2 j-SlotShift.shift v.2 j).val) := by
      unfold cs Congruences
      simp only [List.mem_append,or_imp,forall_and,List.mem_map,hl,hh,List.mem_range,
        forall_exists_index,and_imp, forall_apply_eq_imp_iff, Nat.mod_mod]
      have hj (j : ZMod (ShiftCount S)) :
          differenceResidue (observed.getD j.val 0) (coords.getD j.val 0) (shifts.getD j.val 0) =
            (v.2 j-SlotShift.shift v.2 j).val := by
        rw [s.observedModuli_get,hget,hshift,differenceResidue_eq,
          ZMod.natCast_zmod_val,ZMod.natCast_zmod_val]
      constructor
      · rintro ⟨⟨ha,hb⟩,hc⟩
        refine ⟨ha,?_,fun j => ?_⟩
        · intro i a
          simpa only [Nat.zero_mod] using hb (s.fallback (g,i,a,true),0)
            (s.fallback (g,i,a,true)) i a rfl rfl
        have hr : j.val < observed.length := by rw [s.observedModuli_length]; exact ZMod.val_lt j
        have hu := hc _ j.val hr rfl
        change n % observed.getD j.val 0 =
          differenceResidue (observed.getD j.val 0) (coords.getD j.val 0) (shifts.getD j.val 0) %
            observed.getD j.val 0 at hu
        rw [hj] at hu
        rw [show observed.getD j.val 0 = s.shiftModulus g d S j from s.observedModuli_get g d S j,
          Nat.mod_eq_of_lt (ZMod.val_lt (v.2 j-SlotShift.shift v.2 j))] at hu
        exact hu
      · rintro ⟨ha,hb,hc⟩
        refine ⟨⟨ha,?_⟩,fun _ j hr he => ?_⟩
        · rintro _ _ i a rfl rfl
          simpa only [Nat.zero_mod] using hb i a
        subst_vars
        rw [s.observedModuli_length] at hr
        let j' : ZMod (ShiftCount S) := j
        have hval : j'.val = j := by unfold j'; rw [ZMod.val_natCast,Nat.mod_eq_of_lt hr]
        change n % observed.getD j 0 =
          differenceResidue (observed.getD j 0) (coords.getD j 0) (shifts.getD j 0) %
            observed.getD j 0
        rw [← hval,hj, show observed.getD j'.val 0 = s.shiftModulus g d S j' from
          s.observedModuli_get g d S j', Nat.mod_eq_of_lt (ZMod.val_lt (v.2 j'-SlotShift.shift v.2 j'))]
        exact hc j'
    rw [htest]
    have hlo := fun i => congrFun (map_natCast (s.lowShiftCRT g d S) low) i
    have hleft (i : SelectedSlot S) :
        ((n : ZMod (s.offsetModuli g d S (.inr (i,false,false)))) =
          s.offsetResidues g d S v (.inr (i,false,false))) ↔
          (s.lowEquiv (g,d,i) (n : ZMod (s.low (g,d,i)))).1 =
            (s.lowEquiv (g,d,i) (v.1 i)).1 := by
      rw [map_natCast]
      rfl
    have hright (i : SelectedSlot S) :
        ((n : ZMod (s.offsetModuli g d S (.inr (i,true,false)))) =
          s.offsetResidues g d S v (.inr (i,true,false))) ↔
          (s.lowEquiv (g,d,i) (n : ZMod (s.low (g,d,i)))).2 =
            (s.lowEquiv (g,d,i) (v.1 i)).2 := by
      rw [map_natCast]
      rfl
    have hhidden (i : SelectedSlot S) (a : Bool) :
        n % s.fallback (g,i,a,true) = 0 ↔
        (n : ZMod (s.offsetModuli g d S (.inr (i,a,true)))) =
          s.offsetResidues g d S v (.inr (i,a,true)) := by
      cases a <;> exact (Nat.dvd_iff_mod_eq_zero.symm.trans (ZMod.natCast_eq_zero_iff _ _).symm)
    constructor
    · rintro ⟨ha,hb,hc⟩ (j | ⟨i,a,b⟩)
      · change (n : ZMod (s.shiftModulus g d S j)) = v.2 j-SlotShift.shift v.2 j
        exact ZMod.val_injective _ (by rw [ZMod.val_natCast]; exact hc j)
      · have h : (n : ZMod (s.low (g,d,i))) = v.1 i := by
          rw [show v.1 i = (low : ZMod (s.low (g,d,i))) from hlo i]
          exact ZMod.val_injective _ (by simpa only [ZMod.val_natCast] using ha i)
        cases b
        · cases a
          · exact (hleft i).mpr (congrArg Prod.fst (congrArg (s.lowEquiv (g,d,i)) h))
          · exact (hright i).mpr (congrArg Prod.snd (congrArg (s.lowEquiv (g,d,i)) h))
        · exact (hhidden i a).mp (hb i a)
    · intro he
      refine ⟨fun i => ?_,fun i a => (hhidden i a).mpr (he (.inr (i,a,true))),fun j => ?_⟩
      · have hi : (n : ZMod (s.low (g,d,i))) = v.1 i :=
          (s.lowEquiv (g,d,i)).injective (Prod.ext
            ((hleft i).mp (he (.inr (i,false,false)))) ((hright i).mp (he (.inr (i,true,false)))))
        rw [show v.1 i = (low : ZMod (s.low (g,d,i))) from hlo i] at hi
        simpa only [ZMod.val_natCast] using congrArg ZMod.val hi
      · have hj : (n : ZMod (s.shiftModulus g d S j)) = v.2 j-SlotShift.shift v.2 j := he (.inl j)
        simpa only [ZMod.val_natCast] using congrArg ZMod.val hj
  have heval : evaluatedSlotOffset (selected.prod*observed.prod*hidden.prod) cs
      (slopeNumber g) = s.offset g d S v := by
    rw [hmod]
    unfold evaluatedSlotOffset offset slotOffset
    rw [residueSearch_of_equiv (s.offsetCRT g d S).toEquiv
      (s.offsetResidues g d S v) cs hcong]
    rfl
  dsimp only [numericalSlotRecord]
  change _ = _ ∧
    (selected.map fun r => (r^2,((evaluatedSlotOffset (selected.prod*observed.prod*hidden.prod) cs
      (slopeNumber g)).1 % (r^2 : ℕ)).toNat)) ++ _ ++ _ = _
  exact ⟨heval,by rw [heval]⟩

private theorem shiftCongruences_mem (out : ℕ) (c : ℕ × ℕ) :
    let L := s.observedModuli g d S
    let z := s.outputShiftCRT g d S (out : ZMod (s.outputShiftOrder g d S))
    c ∈ (List.range L.length).map (fun j =>
      (L.getD j 0,(numericalSlotShift (L.map (out % ·))).getD j 0)) ↔
      ∃ j, (s.shiftModulus g d S j,(SlotShift.shift z j).val) = c := by
  let L := s.observedModuli g d S
  let z := s.outputShiftCRT g d S (out : ZMod (s.outputShiftOrder g d S))
  have he (j : ZMod (ShiftCount S)) :
      (L.getD j.val 0,(numericalSlotShift (L.map (out % ·))).getD j.val 0) =
        (s.shiftModulus g d S j,(SlotShift.shift z j).val) := by
    apply Prod.ext
    · exact s.observedModuli_get g d S j
    · dsimp only
      unfold L
      rw [s.observedModuli_coords]
      exact numericalSlotShift_correct (fun i => (s.shiftModulus_prime g d S i).one_lt) z j
  dsimp only
  rw [List.mem_map]
  constructor
  · rintro ⟨j,hj,hc⟩
    rw [List.mem_range,s.observedModuli_length] at hj
    let j' : ZMod (ShiftCount S) := j
    have hv : j'.val = j := by unfold j'; rw [ZMod.val_natCast,Nat.mod_eq_of_lt hj]
    refine ⟨j',(he j').symm.trans ?_⟩
    simpa only [hv] using hc
  · rintro ⟨j,rfl⟩
    exact ⟨j.val,by rw [List.mem_range,s.observedModuli_length]; exact ZMod.val_lt j,he j⟩

local instance numericalDisplacementDecEq : DecidableEq (SharedCoordinates.Ambient s.layout) :=
  fun a b => Classical.propDecidable (a = b)

/-- Collecting the numerical batches yields exactly the mixed-slope
activation mask used by the tiling theorem. -/
theorem numericalSlotActivation_correct
    (selected remaining hidden : List ℕ)
    (hlP : selected.prod = s.lowShiftOrder g d S)
    (hhP : hidden.prod = ∏ i : SelectedSlot S, ∏ a : Bool, s.fallback (g,i,a,true))
    (hl : ∀ r, r ∈ selected ↔ ∃ i : SelectedSlot S, s.low (g,d,i) = r)
    (hh : ∀ r, r ∈ hidden ↔ ∃ (i : SelectedSlot S) (a : Bool), s.fallback (g,i,a,true) = r)
    (hr : ∀ r, r ∈ remaining ↔ ∃ i ∉ selectedRows g d S, s.layout.lowSize i = r) :
    let b : NumericalSlotBatch :=
      (order s.layout,slopeNumber g,selected,remaining,s.observedModuli g d S,hidden)
    (numericalSlotActivation b).toFinset.image (decodePoint s.layout) = s.mask g d S := by
  let L := s.observedModuli g d S
  let b : NumericalSlotBatch := (order s.layout,slopeNumber g,selected,remaining,L,hidden)
  let pair (l o : ℕ) : ShiftPair s g d S :=
    (s.lowShiftCRT g d S (l : ZMod (s.lowShiftOrder g d S)),
     s.outputShiftCRT g d S (o : ZMod (s.outputShiftOrder g d S)))
  let B (v : ShiftPair s g d S) := SlotActivationBatch s.layout (selectedRows g d S)
    (s.projection g d S) (s.offset g d S v) (SlotShift.shift v.2)
  have hsel (r : ℕ) : r ∈ selected ↔ ∃ i ∈ selectedRows g d S, s.layout.lowSize i = r := by
    rw [hl]
    constructor
    · rintro ⟨i,hi⟩
      exact ⟨wangRow (g,d,i),Finset.mem_map.mpr ⟨i.val,i.property,rfl⟩,hi⟩
    · rintro ⟨i,hm,hi⟩
      obtain ⟨j,hj,rfl⟩ := Finset.mem_map.mp hm
      exact ⟨⟨j,hj⟩,hi⟩
  have hbatch (l o : ℕ) (hl' : l < selected.prod) (ho' : o < L.prod)
      (v : SharedCoordinates.Ambient s.layout) :
      v ∈ (numericalBatchPoints b.1 (numericalSlotRecord b l o)).toFinset.image
        (decodePoint s.layout) ↔ B (pair l o) v := by
    obtain ⟨he,hs⟩ := s.numericalSlotRecord_correct g d S selected remaining hidden hlP hhP hl hh hl' ho'
    unfold numericalBatchPoints
    rw [he,hs]
    exact s.mem_numericalSlotBatch g d S _ _ selected remaining _ hsel hr (s.shiftCongruences_mem g d S o) v
  have hmask (v : SharedCoordinates.Ambient s.layout) :
      v ∈ s.mask g d S ↔ ∃ u : ShiftPair s g d S, B u v := by
    simp only [mask,selectedSlotTile,slotActivationTile,Finset.mem_biUnion,Finset.mem_univ,
      true_and,Finset.mem_filter,Finset.mem_map]
    constructor
    · rintro ⟨j,_,hj⟩
      exact ⟨((s.highEquiv g d S).symm j.1,j.2),hj⟩
    · rintro ⟨u,hu⟩
      let j := (s.highEquiv g d S u.1,u.2)
      have h : s.liftedOffset g d S j = s.offset g d S u := by
        unfold liftedOffset j
        rw [Equiv.symm_apply_apply,Prod.mk.eta]
      refine ⟨j,⟨v.2,Prod.ext (h.trans hu.1.symm) rfl⟩,?_⟩
      simpa only [h] using hu
  ext v
  change v ∈ (numericalSlotActivation b).toFinset.image (decodePoint s.layout) ↔ _
  rw [hmask]
  simp only [numericalSlotActivation,Finset.mem_image,List.mem_toFinset,List.mem_flatMap,List.mem_range]
  constructor
  · rintro ⟨p,⟨l,hl',o,ho',hp⟩,he⟩
    exact ⟨pair l o,(hbatch l o hl' ho' v).mp (Finset.mem_image.mpr ⟨p,List.mem_toFinset.mpr hp,he⟩)⟩
  · rintro ⟨u,hu⟩
    let l := ((s.lowShiftCRT g d S).symm u.1).val
    let o := ((s.outputShiftCRT g d S).symm u.2).val
    have hl' : l < selected.prod := by rw [hlP]; exact ZMod.val_lt _
    have ho' : o < L.prod := by unfold L; rw [s.observedModuli_prod]; exact ZMod.val_lt _
    have he : pair l o = u := by
      unfold pair l o
      rw [ZMod.natCast_zmod_val,ZMod.natCast_zmod_val,RingEquiv.apply_symm_apply,
        RingEquiv.apply_symm_apply,Prod.mk.eta]
    obtain ⟨p,hp,hv⟩ := Finset.mem_image.mp ((hbatch l o hl' ho' v).mpr (he.symm ▸ hu))
    exact ⟨p,⟨l,hl',o,ho',List.mem_toFinset.mp hp⟩,hv⟩

end
end TranslationTiling.FiniteCompiler.Packed.AxisParameters
