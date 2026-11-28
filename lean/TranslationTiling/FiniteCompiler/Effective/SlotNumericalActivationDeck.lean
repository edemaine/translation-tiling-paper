import TranslationTiling.FiniteCompiler.Effective.SlotNumericalDisplacement
import TranslationTiling.FiniteCompiler.Effective.SlotNumericalLocalMasks
import TranslationTiling.Proofs.FiniteSearch
import TranslationTiling.FiniteCompiler.Effective.SlotDecode

namespace TranslationTiling.FiniteCompiler.Packed.SlotParameters

open SharedCoordinates Compiler Compiler.Effective
open scoped BigOperators
set_option maxHeartbeats 1500000
set_option maxRecDepth 5000

private def selectedPositions (m r : ℕ) : List (List ℕ) :=
  (List.range m).sublists'.filter fun xs => decide (xs.length = r)

private theorem selectedPositions_primrec :
    Primrec (fun z : ℕ × ℕ => selectedPositions z.1 z.2) := by
  have hf := sublists_primrec.comp (Primrec.list_range.comp (Primrec.fst : Primrec (Prod.fst : ℕ × ℕ → ℕ)))
  have ht : PrimrecPred (fun z : (ℕ × ℕ) × List ℕ => z.2.length = z.1.2) := by fun_prop
  exact filterList (p := fun z xs => xs.length = z.2) hf ht

private theorem selectedPositions_mem (m r : ℕ) (xs : List ℕ) :
    xs ∈ selectedPositions m r ↔ List.Sublist xs (List.range m) ∧ xs.length = r := by
  simp [selectedPositions,List.mem_sublists']

theorem selectedPositions_length (m r : ℕ) : (selectedPositions m r).length = m.choose r := by
  rw [← List.length_range (n := m),← List.length_sublistsLen]
  have hp : List.Perm (selectedPositions m r) ((List.range m).sublistsLen r) := by
    have hd : (selectedPositions m r).Nodup :=
      (List.nodup_sublists'.mpr (List.nodup_range : (List.range m).Nodup)).filter _
    apply (List.perm_ext_iff_of_nodup hd (List.nodup_sublistsLen _ List.nodup_range)).mpr
    intro xs
    rw [selectedPositions_mem,List.mem_sublistsLen]
  simpa only [List.length_range] using hp.length_eq

private def listedSlots {m : ℕ} (S : Finset (Fin m)) : List ℕ := S.sort.map Fin.val

private theorem listedSlots_sublist {m : ℕ} (S : Finset (Fin m)) :
    List.Sublist (listedSlots S) (List.range m) := by
  apply List.sublist_of_subperm_of_sortedLE
  · apply List.subperm_of_subset
    · exact (Finset.sort_nodup _ _).map Fin.val_injective
    · intro i hi
      obtain ⟨j,_,rfl⟩ := List.mem_map.mp hi
      exact List.mem_range.mpr j.isLt
  · apply List.Pairwise.sortedLE
    exact (Finset.pairwise_sort S (· ≤ ·)).map _ (fun _ _ h => h)
  · exact (List.sortedLT_range _).sortedLE

private theorem listedSlots_eq {m : ℕ} (xs : List ℕ) (hx : List.Sublist xs (List.range m)) :
    ∃ S : Finset (Fin m), listedSlots S = xs ∧ S.card = xs.length := by
  let S := (Finset.univ : Finset (Fin m)).filter fun i => i.val ∈ xs
  have hsort : (listedSlots S).SortedLE :=
    ((Finset.pairwise_sort S (· ≤ ·)).map Fin.val (fun _ _ h => h)).sortedLE
  have hsort' : xs.SortedLE := ((List.sortedLT_range _).pairwise.sublist hx).sortedLT.sortedLE
  have he : listedSlots S = xs := by
    apply List.Perm.eq_of_sortedLE hsort hsort'
    apply (List.perm_ext_iff_of_nodup ((Finset.sort_nodup _ _).map Fin.val_injective)
      (hx.nodup List.nodup_range)).mpr
    intro i
    simp only [List.mem_map,Finset.mem_sort,S,Finset.mem_filter,
      Finset.mem_univ,true_and]
    constructor
    · rintro ⟨j,h,hj⟩
      exact hj ▸ h
    · intro h
      exact ⟨⟨i,List.mem_range.mp (hx.subset h)⟩,h,rfl⟩
  refine ⟨S,he,?_⟩
  rw [← he,listedSlots,List.length_map,Finset.length_sort]

private def selectedNumbers (k m : ℕ) (g : Bool) (d : ℕ) (xs : List ℕ) : List ℕ :=
  xs.map fun i => 20 + wangCode k m g d i

private def numberedObservations (k m : ℕ) (g : Bool) (d : ℕ) (xs : List ℕ) : List ℕ :=
  (List.range (4*xs.length)).map fun q =>
    let i := xs.getD (q/4) 0
    let j := q%4
    if j = 0 then numericalFallback k m (fallbackCode m g i false)
    else numericalMarker k m (wangCode k m g d i) (j-1)

/-- A batch reads the selected low rows and the four observations
per slot, and keeps the invisible fallback factors separate. -/
def numberedSlotBatch (N k m : ℕ) (g : Bool) (d : ℕ) (xs : List ℕ) : NumericalSlotBatch :=
  let chosen := selectedNumbers k m g d xs
  let low := fun i => (numericalSlotRow k m i).1
  let rest := (List.range (20+2*k*m+4*m)).filter fun i => decide (i ∉ chosen)
  (N,if g then 0 else 2,chosen.map low,rest.map low,numberedObservations k m g d xs,
    xs.map fun i => numericalFallback k m (fallbackCode m g i true))

/-- There is one activation mask per subset of the required size,
for each direction and each packed digit. -/
def numericalSlotActivationMasks (N k m w : ℕ) : List CyclicTile :=
  [false,true].flatMap fun g =>
    (List.range k).flatMap fun d =>
      (selectedPositions m (m+1-w)).map fun xs =>
        numericalSlotActivation (numberedSlotBatch N k m g d xs)

private abbrev SelectedArgs := ℕ × ℕ × Bool × ℕ × List ℕ

@[fun_prop] private theorem selectedNumbers_primrec : Primrec (fun z : SelectedArgs =>
    selectedNumbers z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2) := by
  unfold selectedNumbers
  apply mapList (by fun_prop)
  fun_prop

private theorem numberedObservations_primrec : Primrec (fun z : SelectedArgs =>
    numberedObservations z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2) := by
  unfold numberedObservations
  apply mapList (by fun_prop)
  let slot (z : SelectedArgs × ℕ) := z.1.2.2.2.2.getD (z.2/4) 0
  have hslot : Primrec slot := by unfold slot; fun_prop
  have htest : PrimrecPred (fun z : SelectedArgs × ℕ => z.2%4 = 0) := by fun_prop
  let fallArgs (z : SelectedArgs × ℕ) : ℕ × ℕ × ℕ :=
    (z.1.1,z.1.2.1,fallbackCode z.1.2.1 z.1.2.2.1 (slot z) false)
  let markArgs (z : SelectedArgs × ℕ) : ℕ × ℕ × ℕ × ℕ :=
    (z.1.1,z.1.2.1,wangCode z.1.1 z.1.2.1 z.1.2.2.1 z.1.2.2.2.1 (slot z),z.2%4-1)
  have hf : Primrec fallArgs := by unfold fallArgs; fun_prop
  have hm : Primrec markArgs := by unfold markArgs; fun_prop
  have h := Primrec.ite htest (numericalFallback_primrec.comp hf) (numericalMarker_primrec.comp hm)
  exact h.of_eq (by intro z; rfl)

set_option maxHeartbeats 8000000 in
private theorem numberedSlotBatch_primrec :
    Primrec (fun z : ℕ × SelectedArgs =>
      numberedSlotBatch z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2.1 z.2.2.2.2.2) := by
  let chosen (z : ℕ × SelectedArgs) := selectedNumbers z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2.1 z.2.2.2.2.2
  let rest (z : ℕ × SelectedArgs) :=
    (List.range (20+2*z.2.1*z.2.2.1+4*z.2.2.1)).filter fun i => decide (i ∉ chosen z)
  have hc : Primrec chosen := selectedNumbers_primrec.comp Primrec.snd
  let allRows (z : ℕ × SelectedArgs) := List.range (20+2*z.2.1*z.2.2.1+4*z.2.2.1)
  have hrows : Primrec allRows := by unfold allRows; fun_prop
  have hkeep : PrimrecPred (fun z : (ℕ × SelectedArgs) × ℕ => z.2 ∉ chosen z.1) := by fun_prop
  have hr : Primrec rest := filterList hrows hkeep
  let readLow (z : (ℕ × SelectedArgs) × ℕ) := (numericalSlotRow z.1.2.1 z.1.2.2.1 z.2).1
  have hread : Primrec readLow := Primrec.fst.comp
    (numericalSlotRow_primrec.comp (show Primrec (fun z : (ℕ × SelectedArgs) × ℕ =>
      (z.1.2.1,z.1.2.2.1,z.2)) by fun_prop))
  have hselected := mapList (g := fun z i => readLow (z,i)) hc (hread.of_eq (by intro z; cases z; rfl))
  have hremaining := mapList (g := fun z i => readLow (z,i)) hr (hread.of_eq (by intro z; cases z; rfl))
  have hobs := numberedObservations_primrec.comp (Primrec.snd : Primrec (Prod.snd : ℕ × SelectedArgs → SelectedArgs))
  have hxs : Primrec (fun z : ℕ × SelectedArgs => z.2.2.2.2.2) := by fun_prop
  have hhid : Primrec (fun z : ℕ × SelectedArgs => z.2.2.2.2.2.map (fun i =>
      numericalFallback z.2.1 z.2.2.1 (fallbackCode z.2.2.1 z.2.2.2.1 i true))) := by
    apply mapList hxs
    let a (z : (ℕ × SelectedArgs) × ℕ) : ℕ × ℕ × ℕ :=
      (z.1.2.1,z.1.2.2.1,fallbackCode z.1.2.2.1 z.1.2.2.2.1 z.2 true)
    have ha : Primrec a := by unfold a; fun_prop
    exact (numericalFallback_primrec.comp ha).of_eq (by intro z; rfl)
  have hs : Primrec (fun z : ℕ × SelectedArgs => (if z.2.2.2.1 then 0 else 2 : ℤ)) :=
    (Primrec.dom_bool (fun g => if g then (0 : ℤ) else 2)).comp (by fun_prop)
  exact (Primrec.fst.pair (hs.pair (hselected.pair (hremaining.pair (hobs.pair hhid))))).of_eq
    (by intro z; rfl)

theorem numericalSlotActivationMasks_primrec : Primrec (fun z : ℕ × ℕ × ℕ × ℕ =>
    numericalSlotActivationMasks z.1 z.2.1 z.2.2.1 z.2.2.2) := by
  unfold numericalSlotActivationMasks
  apply flatMapList (Primrec.const [false,true])
  apply flatMapList (by fun_prop)
  let dimensions (z : ((ℕ × ℕ × ℕ × ℕ) × Bool) × ℕ) := (z.1.1.2.2.1,z.1.1.2.2.1+1-z.1.1.2.2.2)
  have hd : Primrec dimensions := by unfold dimensions; fun_prop
  apply mapList (selectedPositions_primrec.comp hd)
  let args (z : (((ℕ × ℕ × ℕ × ℕ) × Bool) × ℕ) × List ℕ) : ℕ × SelectedArgs :=
    (z.1.1.1.1,z.1.1.1.2.1,z.1.1.1.2.2.1,z.1.1.2,z.1.2,z.2)
  have ha : Primrec args := by unfold args; fun_prop
  exact (numericalSlotActivation_primrec.comp (numberedSlotBatch_primrec.comp ha)).of_eq (by intro z; rfl)

theorem numericalSlotActivationMasks_length (N k m w : ℕ) :
    (numericalSlotActivationMasks N k m w).length = 2*k*m.choose (m+1-w) := by
  unfold numericalSlotActivationMasks
  simp [List.length_flatMap,selectedPositions_length,List.sum_replicate]
  ring

noncomputable section
open scoped Classical

variable {k m : ℕ} (s : SlotParameters k m)

local instance activationDeckDecEq : DecidableEq (SharedCoordinates.Ambient s.layout) :=
  fun a b => Classical.propDecidable (a = b)


private theorem listedSlots_get {m : ℕ} (S : Finset (Fin m)) (j : ℕ) (hj : j < S.card) :
    (listedSlots S).getD j 0 =
      (S.sort[j]'(by rw [Finset.length_sort]; exact hj)).val := by
  unfold listedSlots
  rw [List.getD_eq_getElem _ _ (by simpa using hj),List.getElem_map]

private theorem listedSlots_ofFn {m : ℕ} (S : Finset (Fin m)) :
    listedSlots S = List.ofFn (fun i : Fin S.card => (S.orderIsoOfFin rfl i).val.val) := by
  apply List.ext_getElem
  · simp [listedSlots]
  · intro i hi hj
    simp only [listedSlots,List.getElem_map,List.getElem_ofFn,Finset.coe_orderIsoOfFin_apply,
      Finset.orderEmbOfFin_apply]
    rfl

private theorem listedSlots_map_mem {m : ℕ} (S : Finset (Fin m)) (f : ℕ → ℕ) (r : ℕ) :
    r ∈ (listedSlots S).map f ↔ ∃ i : SelectedSlot S, f i.val.val = r := by
  simp only [listedSlots,List.map_map,List.mem_map,Finset.mem_sort,Subtype.exists,
    Function.comp_def,exists_prop]

private theorem listedSlots_map_prod {m : ℕ} (S : Finset (Fin m)) (f : ℕ → ℕ) :
    ((listedSlots S).map f).prod = ∏ i : SelectedSlot S, f i.val.val := by
  rw [listedSlots_ofFn,List.map_ofFn,List.prod_ofFn]
  exact Fintype.prod_equiv (S.orderIsoOfFin rfl).toEquiv _ _ (by intro i; rfl)

private theorem numberedObservations_eq (hs : s.prime = rankedSlotPrime k m)
    (g : Bool) (d : Fin k) (S : Finset (Fin m)) [NeZero (ShiftCount S)] :
    numberedObservations k m g d (listedSlots S) = s.observedModuli g d S := by
  have hlen : 4*(listedSlots S).length = ShiftCount S := by
    rw [listedSlots,List.length_map,Finset.length_sort,shiftCount_eq,Nat.mul_comm]
  apply List.ext_getElem
  · simp [numberedObservations,observedModuli,hlen]
  · intro j hj hj'
    have hJ : j < ShiftCount S := by simpa [observedModuli] using hj'
    let z : ZMod (ShiftCount S) := j
    have hz : z.val = j := by unfold z; rw [ZMod.val_natCast,Nat.mod_eq_of_lt hJ]
    have hdiv : z.val/4 < S.card := by
      apply Nat.div_lt_of_lt_mul
      rw [Nat.mul_comm,← shiftCount_eq S]
      exact ZMod.val_lt z
    let i : Fin m := (shiftIndex S z).1
    have hi : (listedSlots S).getD (j/4) 0 = i.val := by
      rw [← hz,listedSlots_get _ _ hdiv]
      exact congrArg Fin.val (shiftIndex_slot S z).symm
    simp only [numberedObservations,observedModuli,List.getElem_map,List.getElem_range,List.getElem_ofFn]
    change (if j%4 = 0 then numericalFallback k m (fallbackCode m g ((listedSlots S).getD (j/4) 0) false)
      else numericalMarker k m (wangCode k m g d ((listedSlots S).getD (j/4) 0)) (j%4-1)) =
        s.shiftModulus g d S z
    rw [hi,← hz,shiftModulus]
    have he : (shiftIndex S z).2 = finSuccEquiv 3 ⟨z.val%4,Nat.mod_lt _ (by decide)⟩ :=
      shiftIndex_label S z
    by_cases h : z.val%4 = 0
    · rw [ite_eq_left h, numericalFallback_eq s hs]
      have hnone : (shiftIndex S z).2 = none := he.trans
        (show finSuccEquiv 3 ⟨z.val%4,_⟩ = none by
          rw [show (⟨z.val%4,Nat.mod_lt _ (by decide)⟩ : Fin 4) = 0 from Fin.ext h]; rfl)
      change _ = (match (shiftIndex S z).2 with
        | none => s.fallback (g,i,false)
        | some a => s.marker (g,d,i) a)
      rw [hnone]
    · let a : Fin 3 := ⟨z.val%4-1,by have := Nat.mod_lt z.val (by decide : 0 < 4); omega⟩
      have hsome : (shiftIndex S z).2 = some a := by
        apply he.trans
        rw [← (finSuccEquiv 3).apply_symm_apply (some a)]
        apply congrArg (finSuccEquiv 3)
        exact Fin.ext (by change z.val%4 = a.val+1; change z.val%4 = (z.val%4-1)+1; omega)
      rw [ite_eq_right h]
      change numericalMarker k m (wangCode k m g d i) a = _
      rw [numericalMarker_eq s hs]
      change _ = (match (shiftIndex S z).2 with
        | none => s.fallback (g,i,false)
        | some a => s.marker (g,d,i) a)
      rw [hsome]

theorem numberedSlotBatch_correct (hs : s.prime = rankedSlotPrime k m)
    (g : Bool) (d : Fin k) (S : Finset (Fin m)) [NeZero (ShiftCount S)] :
    (numericalSlotActivation (numberedSlotBatch (order s.layout) k m g d (listedSlots S))).toFinset.image
      (decodePoint s.layout) = s.mask g d S := by
  let f := fun i => (numericalSlotRow k m i).1
  let chosen := selectedNumbers k m g d (listedSlots S)
  let selected := chosen.map f
  let remaining := ((List.range (20+2*k*m+4*m)).filter fun i => decide (i ∉ chosen)).map f
  let hidden := (listedSlots S).map (fun i => numericalFallback k m (fallbackCode m g i true))
  have hlo (i : Fin m) : f (20+wangCode k m g d i) = s.low (g,d,i) :=
    congrArg Prod.fst (numericalSlotRow_eq s hs (wangRow (g,d,i)))
  have hselect (i : SlotRow k m) : slotRowNumber i ∈ chosen ↔ i ∈ selectedRows g d S := by
    unfold chosen selectedNumbers selectedRows
    rw [listedSlots_map_mem,Finset.mem_map]
    constructor
    · rintro ⟨j,h⟩
      refine ⟨j.val,j.property,(slotRowEquiv k m).injective (Fin.ext ?_)⟩
      rw [slotRowEquiv_val,slotRowEquiv_val]
      exact h
    · rintro ⟨j,hj,rfl⟩
      exact ⟨⟨j,hj⟩,rfl⟩
  have hls : selected.prod = s.lowShiftOrder g d S := by
    unfold selected chosen selectedNumbers lowShiftOrder
    rw [List.map_map,listedSlots_map_prod]
    apply Finset.prod_congr rfl
    intro i _
    exact hlo i.val
  have hhs : hidden.prod = ∏ i : SelectedSlot S, s.fallback (g,i,true) := by
    unfold hidden
    rw [listedSlots_map_prod]
    exact Finset.prod_congr rfl (fun i _ => numericalFallback_eq s hs g i.val true)
  have hsl (r : ℕ) : r ∈ selected ↔ ∃ i : SelectedSlot S, s.low (g,d,i) = r := by
    unfold selected chosen selectedNumbers
    rw [List.map_map,listedSlots_map_mem]
    exact exists_congr (fun i => by rw [Function.comp_apply,hlo])
  have hhl (r : ℕ) : r ∈ hidden ↔ ∃ i : SelectedSlot S, s.fallback (g,i,true) = r := by
    unfold hidden
    rw [listedSlots_map_mem]
    exact exists_congr (fun i => by rw [numericalFallback_eq s hs g i.val true])
  have hrl (r : ℕ) : r ∈ remaining ↔ ∃ i ∉ selectedRows g d S, s.layout.lowSize i = r := by
    simp only [remaining,List.mem_map,List.mem_filter,List.mem_range,decide_eq_true_eq]
    constructor
    · rintro ⟨j,⟨hj,hn⟩,he⟩
      let i := (slotRowEquiv k m).symm ⟨j,hj⟩
      have hi : slotRowNumber i = j := by
        rw [← slotRowEquiv_val]
        exact congrArg Fin.val ((slotRowEquiv k m).apply_symm_apply ⟨j,hj⟩)
      refine ⟨i,fun hm => hn (hi ▸ (hselect i).mpr hm),?_⟩
      have hf := congrArg Prod.fst (numericalSlotRow_eq s hs i)
      exact hf.symm.trans (by simpa only [hi] using he)
    · rintro ⟨i,hi,rfl⟩
      exact ⟨slotRowNumber i,⟨by rw [← slotRowEquiv_val]; exact (slotRowEquiv k m i).isLt,
        mt (hselect i).mp hi⟩,congrArg Prod.fst (numericalSlotRow_eq s hs i)⟩
  unfold numberedSlotBatch
  rw [s.numberedObservations_eq hs g d S]
  change (numericalSlotActivation (_,_,selected,remaining,_,hidden)).toFinset.image
    (decodePoint s.layout) = _
  have hb : (if g then (0 : ℤ) else 2) = slopeNumber g := rfl
  rw [hb]
  exact s.numericalSlotActivation_correct g d S selected remaining hidden hls hhs hsl hhl hrl


theorem numericalSlotActivationMasks_correct (hs : s.prime = rankedSlotPrime k m)
    {w : ℕ} (hwm : w ≤ m) (F : Finset (SharedCoordinates.Ambient s.layout)) :
    (∃ G ∈ numericalSlotActivationMasks (order s.layout) k m w,
      G.toFinset.image (decodePoint s.layout) = F) ↔
      ∃ g, ∃ d, ∃ S : Finset (Fin m), ∃ hS : S.card = m+1-w,
        s.activationTest g d S (selected_nonempty hwm hS) = F := by
  simp only [numericalSlotActivationMasks,List.mem_flatMap,List.mem_range,List.mem_map,
    selectedPositions_mem]
  constructor
  · rintro ⟨G,⟨g,_,j,hj,xs,⟨hxs,hlen⟩,rfl⟩,he⟩
    obtain ⟨S,hS,hcard⟩ := listedSlots_eq xs hxs
    let d : Fin k := ⟨j,hj⟩
    have hcard' := hcard.trans hlen
    have := shiftCount_neZero (selected_nonempty hwm hcard')
    refine ⟨g,d,S,hcard',?_⟩
    rw [activationTest,← s.numberedSlotBatch_correct hs g d S,hS]
    exact he
  · rintro ⟨g,d,S,hS,rfl⟩
    refine ⟨_,⟨g,by cases g <;> simp,d.val,d.isLt,listedSlots S,⟨listedSlots_sublist S,?_⟩,rfl⟩,?_⟩
    · simpa only [listedSlots,List.length_map,Finset.length_sort] using hS
    · have := shiftCount_neZero (selected_nonempty hwm hS)
      exact s.numberedSlotBatch_correct hs g d S

end

end TranslationTiling.FiniteCompiler.Packed.SlotParameters
