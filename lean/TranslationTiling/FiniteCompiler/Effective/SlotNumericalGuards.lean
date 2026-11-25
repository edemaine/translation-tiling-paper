import TranslationTiling.FiniteCompiler.Effective.SlotPatternCycle
import TranslationTiling.FiniteCompiler.Effective.SlotNumericalCycle
import TranslationTiling.FiniteCompiler.Effective.SlotRankedWords
import TranslationTiling.FiniteCompiler.Effective.SlotNumericalLocalMasks
import TranslationTiling.FiniteCompiler.Effective.PackedPatternCorrect
import TranslationTiling.FiniteCompiler.Effective.SlotParameterEvaluation

namespace TranslationTiling.FiniteCompiler.Packed.SlotParameters

open SharedCoordinates Compiler Compiler.Effective TranslationTiling.FiniteCompiler.SlotWords
open TranslationTiling.FiniteCompiler.Effective
noncomputable section
set_option autoImplicit false

set_option maxRecDepth 8000
set_option maxHeartbeats 1600000

def wangWordLabel (_k m w : ℕ) (p : RawMask) (g : Bool) (d i : ℕ) : Option ℕ :=
  (p.getD (if g then 18 else 19) none).bind fun a =>
    let code := numericalWordDigit m w (a / slotRadix m w ^ d % slotRadix m w) i
    if code = 0 then none else some (code-1)

def indexedLabels (is : List ℕ) (label : ℕ → Option ℕ) : GuardedAssignments :=
  is.filterMap fun i => (label i).map (i,·)

/-- Decode the selected arithmetic letters and the occupied Wang slots
of each guarded partial assignment. -/
def expandSlotMask (k m w : ℕ) (p : RawMask) : GuardedAssignments :=
  indexedLabels (List.range 18) (fun i => p.getD i none) ++
    [false,true].flatMap fun g =>
      (List.range k).flatMap fun d =>
        ((List.range m).filterMap fun i =>
          (wangWordLabel k m w p g d i).map (20+wangCode k m g d i,·))

private def numericalCycleRead (k m i label : ℕ) : ℕ × ℕ :=
  if 20 ≤ i ∧ i < 20+2*k*m then
    (1,numericalMarker k m (i-20) label)
  else if i < 20 then (numericalSlotRow k m i).2 else (1,1)

private def numericalCycleStep (k m i label : ℕ) : ℕ :=
  if i < 20 then rowR (fourValueRows 0) i / (rowDigits (fourValueRows 0) i).getD label 0
  else if i < 20+2*k*m then 1 else 0

/-- Evaluate each row of the vertical cycle from the immediately preceding
row in the list of selected labels. -/
def numericalSlotCycleRows (k m : ℕ) (xs : GuardedAssignments) : List CycleRow :=
  let keys := xs.map Prod.fst
  (List.range (20+2*k*m+4*m)).map fun i =>
    let r := (numericalSlotRow k m i).1
    let j := keys.idxOf i
    if j < xs.length then
      let pred := xs.getD ((j + xs.length - 1) % xs.length) (0,0)
      let a := numericalCycleRead k m pred.1 pred.2
      let step := numericalCycleStep k m i (xs.getD j (0,0)).2
      (r,a.1,a.2,triggerTable a.1 a.2 step)
    else (r,1,1,[0])

/-- An empty partial assignment supplies no cycle. The guarded
construction only needs the masks attached to nonempty assignments. -/
def numericalSlotCycle (N k m : ℕ) (xs : GuardedAssignments) : List CyclicTile :=
  if xs.length = 0 then [] else [cycleCodes N (numericalSlotCycleRows k m xs)]

def numericalGuardMasks (T : LeanWang.TileSet) (N k m w : ℕ) : List CyclicTile :=
  (rawGuardedMasks T ((slotRadix m w)^k)).flatMap fun p =>
    numericalSlotCycle N k m (expandSlotMask k m w p)

def numericalSeedMasks (N k m : ℕ) : List CyclicTile :=
  (tailSeedTests 0).flatMap (numericalSlotCycle N k m)

private abbrev WordLabelArgs := (ℕ × ℕ × ℕ × RawMask) × Bool × ℕ × ℕ

private theorem wangWordLabel_primrec : Primrec (fun z : WordLabelArgs =>
    wangWordLabel z.1.1 z.1.2.1 z.1.2.2.1 z.1.2.2.2 z.2.1 z.2.2.1 z.2.2.2) := by
  unfold wangWordLabel
  let col (z : WordLabelArgs) := if z.2.1 then (18 : ℕ) else 19
  have hcol : Primrec col := (Primrec.dom_bool (fun g => if g then (18 : ℕ) else 19)).comp (by fun_prop)
  have hsym : Primrec (fun z : WordLabelArgs => z.1.2.2.2.getD (col z) none) := by fun_prop
  let params (z : WordLabelArgs × ℕ) : ℕ × ℕ := (z.1.1.2.1,z.1.1.2.2.1)
  have hparams : Primrec params := by unfold params; fun_prop
  let radix (z : WordLabelArgs × ℕ) := slotRadix (params z).1 (params z).2
  have hradix : Primrec radix := slotRadix_primrec.comp hparams
  let args (z : WordLabelArgs × ℕ) : ℕ × ℕ × ℕ × ℕ :=
    (z.1.1.2.1,z.1.1.2.2.1,z.2 / radix z ^ z.1.2.2.1 % radix z,z.1.2.2.2)
  have hargs : Primrec args := by unfold args; fun_prop
  let digit (z : WordLabelArgs × ℕ) := numericalWordDigit
    (args z).1 (args z).2.1 (args z).2.2.1 (args z).2.2.2
  have hdigit : Primrec digit := numericalWordDigit_primrec.comp hargs
  have htest := Primrec.eq.comp hdigit (Primrec.const 0)
  have hsub := Primrec.nat_sub.comp hdigit (Primrec.const 1)
  have hbody := Primrec.ite htest (Primrec.const (none : Option ℕ))
    (Primrec.option_some.comp hsub)
  exact (Primrec.option_bind hsym hbody.to₂).of_eq (by intro z; rfl)

private abbrev ExpandArgs := ℕ × ℕ × ℕ × RawMask
private abbrev ExpandIndex := ((ExpandArgs × Bool) × ℕ) × ℕ

private theorem expandSlotMask_primrec :
    Primrec (fun z : ExpandArgs => expandSlotMask z.1 z.2.1 z.2.2.1 z.2.2.2) := by
  unfold expandSlotMask indexedLabels
  apply appendList
  · have hlabel : Primrec (fun z : ExpandArgs × ℕ => z.1.2.2.2.getD z.2 none) := by fun_prop
    have hpair : Primrec₂ (fun (z : ExpandArgs × ℕ) (v : ℕ) => (z.2,v)) :=
      ((Primrec.snd.comp Primrec.fst).pair Primrec.snd).to₂
    exact (Primrec.listFilterMap (Primrec.const (List.range 18))
      (Primrec.option_map hlabel hpair).to₂).to₂
  · apply flatMapList (Primrec.const [false,true])
    apply flatMapList (by fun_prop)
    have hin : Primrec (fun z : (ExpandArgs × Bool) × ℕ => List.range z.1.1.2.1) := by fun_prop
    let args (z : ExpandIndex) : WordLabelArgs := (z.1.1.1,z.1.1.2,z.1.2,z.2)
    have ha : Primrec args := by unfold args; fun_prop
    have hlabel := wangWordLabel_primrec.comp ha
    let row (z : ExpandIndex) := 20+wangCode z.1.1.1.1 z.1.1.1.2.1 z.1.1.2 z.1.2 z.2
    have hrow : Primrec row := by unfold row; fun_prop
    have hpair : Primrec₂ (fun (z : ExpandIndex) (v : ℕ) => (row z,v)) :=
      ((hrow.comp Primrec.fst).pair Primrec.snd).to₂
    exact (Primrec.listFilterMap hin (Primrec.option_map hlabel hpair).to₂).to₂

private abbrev CycleLocal := ℕ × ℕ × ℕ × ℕ

@[fun_prop] private theorem numericalCycleRead_primrec :
    Primrec (fun z : CycleLocal => numericalCycleRead z.1 z.2.1 z.2.2.1 z.2.2.2) := by
  unfold numericalCycleRead
  have hrow := numericalSlotRow_primrec.comp (show Primrec (fun z : CycleLocal =>
    (z.1,z.2.1,z.2.2.1)) by fun_prop)
  have hmark := numericalMarker_primrec.comp (show Primrec (fun z : CycleLocal =>
    (z.1,z.2.1,z.2.2.1-20,z.2.2.2)) by fun_prop)
  fun_prop

@[fun_prop] private theorem numericalCycleStep_primrec :
    Primrec (fun z : CycleLocal => numericalCycleStep z.1 z.2.1 z.2.2.1 z.2.2.2) := by
  unfold numericalCycleStep
  fun_prop

private abbrev CycleArgs := ℕ × ℕ × GuardedAssignments
private abbrev CycleIndex := CycleArgs × ℕ

@[fun_prop] private theorem numericalSlotCycleRows_primrec :
    Primrec (fun z : CycleArgs => numericalSlotCycleRows z.1 z.2.1 z.2.2) := by
  unfold numericalSlotCycleRows
  apply mapList (by fun_prop)
  let ix (z : CycleIndex) := (z.1.2.2.map Prod.fst).idxOf z.2
  have hix : Primrec ix := Primrec.list_idxOf.comp Primrec.snd (by fun_prop)
  let len (z : CycleIndex) := z.1.2.2.length
  have hlen : Primrec len := by unfold len; fun_prop
  let low (z : CycleIndex) := (numericalSlotRow z.1.1 z.1.2.1 z.2).1
  have hlow : Primrec low := Primrec.fst.comp (numericalSlotRow_primrec.comp
    (show Primrec (fun z : CycleIndex => (z.1.1,z.1.2.1,z.2)) by fun_prop))
  let pred (z : CycleIndex) := z.1.2.2.getD ((ix z + len z - 1) % len z) (0,0)
  have hpred : Primrec pred := by unfold pred; fun_prop
  let read (z : CycleIndex) := numericalCycleRead z.1.1 z.1.2.1 (pred z).1 (pred z).2
  have hread : Primrec read := by unfold read; fun_prop
  let step (z : CycleIndex) := numericalCycleStep z.1.1 z.1.2.1 z.2 (z.1.2.2.getD (ix z) (0,0)).2
  have hstep : Primrec step := by unfold step; fun_prop
  have htrig := triggerTable_primrec.comp (show Primrec (fun z : CycleIndex =>
    ((read z).1,(read z).2,step z)) by fun_prop)
  have ha : Primrec (fun z : CycleIndex =>
    (low z,(read z).1,(read z).2,triggerTable (read z).1 (read z).2 (step z))) := by fun_prop
  have hb : Primrec (fun z : CycleIndex => (low z,1,1,([0] : List ℕ))) :=
    hlow.pair (Primrec.const _)
  exact (Primrec.ite (Primrec.nat_lt.comp hix hlen) ha hb).of_eq (by intro z; rfl)

private abbrev CycleMaskArgs := ℕ × ℕ × ℕ × GuardedAssignments

theorem numericalSlotCycle_primrec :
    Primrec (fun z : CycleMaskArgs => numericalSlotCycle z.1 z.2.1 z.2.2.1 z.2.2.2) := by
  unfold numericalSlotCycle
  have hcodes := cycleCodes_primrec.comp (show Primrec (fun z : CycleMaskArgs =>
    (z.1,numericalSlotCycleRows z.2.1 z.2.2.1 z.2.2.2)) by fun_prop)
  have hsingle := Primrec.list_cons.comp hcodes (Primrec.const ([] : List CyclicTile))
  exact Primrec.ite (by fun_prop) (Primrec.const []) hsingle

theorem numericalGuardMasks_primrec :
    Primrec (fun z : LeanWang.TileSet × ℕ × ℕ × ℕ × ℕ =>
      numericalGuardMasks z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2) := by
  unfold numericalGuardMasks
  let harg (z : LeanWang.TileSet × ℕ × ℕ × ℕ × ℕ) :=
    (z.1,(slotRadix z.2.2.2.1 z.2.2.2.2)^z.2.2.1)
  have hradix : Primrec (fun z : LeanWang.TileSet × ℕ × ℕ × ℕ × ℕ =>
      slotRadix z.2.2.2.1 z.2.2.2.2) := slotRadix_primrec.comp (by fun_prop)
  have ha : Primrec harg := by unfold harg; fun_prop
  apply flatMapList (rawGuardedMasks_primrec.comp ha)
  let args (z : (LeanWang.TileSet × ℕ × ℕ × ℕ × ℕ) × RawMask) : ExpandArgs :=
    (z.1.2.2.1,z.1.2.2.2.1,z.1.2.2.2.2,z.2)
  have he : Primrec args := by unfold args; fun_prop
  let cyargs (z : (LeanWang.TileSet × ℕ × ℕ × ℕ × ℕ) × RawMask) : CycleMaskArgs :=
    (z.1.2.1,z.1.2.2.1,z.1.2.2.2.1,
      expandSlotMask (args z).1 (args z).2.1 (args z).2.2.1 (args z).2.2.2)
  have hmask := expandSlotMask_primrec.comp he
  have hc : Primrec cyargs := by unfold cyargs; fun_prop
  exact (numericalSlotCycle_primrec.comp hc).of_eq (by intro z; rfl)

theorem numericalSeedMasks_primrec :
    Primrec (fun z : ℕ × ℕ × ℕ => numericalSeedMasks z.1 z.2.1 z.2.2) := by
  unfold numericalSeedMasks
  apply flatMapList (Primrec.const (tailSeedTests 0))
  let args (z : (ℕ × ℕ × ℕ) × GuardedAssignments) : CycleMaskArgs :=
    (z.1.1,z.1.2.1,z.1.2.2,z.2)
  have ha : Primrec args := by unfold args; fun_prop
  exact (numericalSlotCycle_primrec.comp ha).of_eq (by intro z; rfl)

private theorem numericalCycle_length (N k m : ℕ) (xs : GuardedAssignments) :
    (numericalSlotCycle N k m xs).length ≤ 1 := by
  unfold numericalSlotCycle
  split <;> simp

theorem numericalGuardMasks_length (T : LeanWang.TileSet) (N k m w : ℕ) :
    (numericalGuardMasks T N k m w).length ≤ 2313+72*((slotRadix m w)^k)^2 := by
  unfold numericalGuardMasks
  rw [List.length_flatMap]
  have hb := listSumMap_le (as := rawGuardedMasks T ((slotRadix m w)^k))
    (f := fun p => (numericalSlotCycle N k m (expandSlotMask k m w p)).length)
    (g := fun _ => 1) (fun p _ => numericalCycle_length N k m _)
  simpa using hb.trans (by simpa using rawGuardedMasks_length T ((slotRadix m w)^k))

theorem numericalSeedMasks_length (N k m : ℕ) :
    (numericalSeedMasks N k m).length ≤ 180 := by
  unfold numericalSeedMasks
  rw [List.length_flatMap]
  have hb := listSumMap_le (as := tailSeedTests 0)
    (f := fun xs => (numericalSlotCycle N k m xs).length) (g := fun _ => 1)
    (fun xs _ => numericalCycle_length N k m xs)
  simpa using hb.trans (by simpa using tailSeedTests_length 0)

noncomputable section
open scoped Classical

variable {k m : ℕ} (s : SlotParameters k m)

def rowLabelNumber (i : SlotRow k m) (a : RowLabel i) : ℕ :=
  match i with
  | .inl _ => a.val
  | .inr (.inl _) => a.val
  | .inr (.inr _) => 0

private theorem numericalCycleRead_eq (hs : s.prime = rankedSlotPrime k m)
    (i : SlotRow k m) (a : RowLabel i) :
    numericalCycleRead k m (slotRowNumber i) (rowLabelNumber i a) = s.cycleReadModuli i a := by
  rcases i with i | ⟨g,d,i⟩ | ⟨g,i,b⟩
  · have h : i.val < 20 := by simpa [fourValueRows_length] using i.isLt
    unfold numericalCycleRead
    rw [ite_eq_right (by change ¬ (20 ≤ i.val ∧ _); omega),
      ite_eq_left (show slotRowNumber (.inl i : SlotRow k m) < 20 from h),numericalSlotRow_eq s hs]
    rfl
  · have h := wangCode_lt g d i
    unfold numericalCycleRead
    rw [ite_eq_left (by change 20 ≤ 20+wangCode k m g d i ∧ 20+wangCode k m g d i < _; omega)]
    change (1,numericalMarker k m (20+wangCode k m g d i-20) a.val) = _
    rw [Nat.add_sub_cancel_left,numericalMarker_eq s hs]
    rfl
  · unfold numericalCycleRead
    rw [ite_eq_right (by change ¬ (_ ∧ 20+2*k*m+fallbackCode m g i b < _); omega),
      ite_eq_right (by change ¬ (20+2*k*m+fallbackCode m g i b < 20); omega)]
    rfl

private theorem numericalCycleStep_eq (i : SlotRow k m) (a : RowLabel i) :
    numericalCycleStep k m (slotRowNumber i) (rowLabelNumber i a) = cycleStepCode i a := by
  rcases i with i | ⟨g,d,i⟩ | ⟨g,i,b⟩
  · have h : i.val < 20 := by simpa [fourValueRows_length] using i.isLt
    unfold numericalCycleStep
    rw [ite_eq_left (show slotRowNumber (.inl i : SlotRow k m) < 20 from h)]
    change rowR (fourValueRows 0) i.val / (rowDigits (fourValueRows 0) i.val).getD a.val 0 =
      fourValueStep i a
    rw [List.getD_eq_getElem _ _ a.isLt]
    rfl
  · have h := wangCode_lt g d i
    unfold numericalCycleStep
    rw [ite_eq_right (by change ¬ (20+wangCode k m g d i < 20); omega),
      ite_eq_left (by change 20+wangCode k m g d i < 20+2*k*m; omega)]
    rfl
  · unfold numericalCycleStep
    rw [ite_eq_right (by change ¬ (20+2*k*m+fallbackCode m g i b < 20); omega),
      ite_eq_right (by change ¬ (20+2*k*m+fallbackCode m g i b < 20+2*k*m); omega)]
    rfl

variable {t : ℕ} [NeZero t] (cyc : ZMod t ↪ SlotRow k m)
    (a : ∀ i : SlotRow k m, RowLabel i)

def numberedCycleAssignments : GuardedAssignments :=
  List.ofFn fun j =>
    let i := cyc (ZMod.finEquiv t j)
    (slotRowNumber i,rowLabelNumber i (a i))

private theorem cycleIndex_value (j : ZMod t) : ((ZMod.finEquiv t).symm j).val = j.val := by
  cases t with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ t => rfl

private theorem numberedCycleAssignments_get (j : ZMod t) :
    (numberedCycleAssignments cyc a).getD j.val (0,0) =
      (slotRowNumber (cyc j),rowLabelNumber (cyc j) (a (cyc j))) := by
  rw [← cycleIndex_value j]
  simp only [numberedCycleAssignments,List.getD_eq_getElem?_getD,List.getElem?_ofFn,
    dite_eq_left ((ZMod.finEquiv t).symm j).isLt,Option.getD_some]
  exact congrArg (fun z : ZMod t => (slotRowNumber (cyc z),rowLabelNumber (cyc z) (a (cyc z))))
    ((ZMod.finEquiv t).apply_symm_apply j)

private theorem numberedCycleAssignments_idx (j : ZMod t) :
    ((numberedCycleAssignments cyc a).map Prod.fst).idxOf (slotRowNumber (cyc j)) = j.val := by
  let f (u : Fin t) := slotRowNumber (cyc (ZMod.finEquiv t u))
  have hf : Function.Injective f := by
    intro i j h
    apply (ZMod.finEquiv t).injective
    apply cyc.injective
    apply (slotRowEquiv k m).injective
    exact Fin.ext (by simpa only [slotRowEquiv_val] using h)
  let b := (ZMod.finEquiv t).symm j
  have hm : slotRowNumber (cyc j) ∈ List.ofFn f := List.mem_ofFn.mpr ⟨b, by simp [f,b]⟩
  have hi := List.idxOf_lt_length_of_mem hm
  rw [List.length_ofFn] at hi
  have he := List.getElem_idxOf (List.idxOf_lt_length_of_mem hm)
  rw [List.getElem_ofFn] at he
  have he' : f ⟨(List.ofFn f).idxOf (slotRowNumber (cyc j)),hi⟩ = f b := by simpa [f,b] using he
  have e : (numberedCycleAssignments cyc a).map Prod.fst = List.ofFn f := by
    simp [numberedCycleAssignments,List.map_ofFn,Function.comp_def,f]
  rw [e,← cycleIndex_value j]
  exact congrArg Fin.val (hf he')
private theorem numberedCycleAssignments_previous (j : ZMod t) :
    (numberedCycleAssignments cyc a).getD ((j.val+t-1)%t) (0,0) =
      (slotRowNumber (cyc (j-1)),rowLabelNumber (cyc (j-1)) (a (cyc (j-1)))) := by
  have ht := NeZero.pos t
  have h : ((j.val+t-1 : ℕ) : ZMod t) = j-1 := by
    rw [Nat.cast_sub (by omega),Nat.cast_add,ZMod.natCast_zmod_val,ZMod.natCast_self,
      Nat.cast_one,add_zero]
  have hm : (j.val+t-1)%t = (j-1).val := by
    simpa only [ZMod.val_natCast] using congrArg ZMod.val h
  rw [hm,numberedCycleAssignments_get]

private def cyclePredecessor (i : SlotRow k m) : Option (SlotRow k m) :=
  if h : ∃ j, cyc j = i then some (cyc (h.choose-1)) else none

@[simp] private theorem cyclePredecessor_on (j : ZMod t) :
    cyclePredecessor cyc (cyc j) = some (cyc (j-1)) := by
  unfold cyclePredecessor
  let h : ∃ j', cyc j' = cyc j := ⟨j,rfl⟩
  rw [dite_eq_left h,cyc.injective h.choose_spec]

private theorem cyclePredecessor_off (i : SlotRow k m) (h : ∀ j, cyc j ≠ i) :
    cyclePredecessor cyc i = none := by
  unfold cyclePredecessor
  exact dite_eq_right (not_exists.mpr h)

private theorem numericalCycleRow_get (hs : s.prime = rankedSlotPrime k m)
    (i : SlotRow k m) :
    let xs := numberedCycleAssignments cyc a
    let j := (xs.map Prod.fst).idxOf (slotRowNumber i)
    (if j < xs.length then
      let p := xs.getD ((j+xs.length-1)%xs.length) (0,0)
      let read := numericalCycleRead k m p.1 p.2
      let step := numericalCycleStep k m (slotRowNumber i) (xs.getD j (0,0)).2
      ((numericalSlotRow k m (slotRowNumber i)).1,read.1,read.2,triggerTable read.1 read.2 step)
    else ((numericalSlotRow k m (slotRowNumber i)).1,1,1,([0] : List ℕ))) =
      s.slotCycleRow a (cyclePredecessor cyc) i := by
  have hlen : (numberedCycleAssignments cyc a).length = t := List.length_ofFn
  by_cases hi : ∃ j, cyc j = i
  · obtain ⟨j,rfl⟩ := hi
    dsimp only
    rw [numberedCycleAssignments_idx,hlen,ite_eq_left (ZMod.val_lt j),
      numberedCycleAssignments_previous,numberedCycleAssignments_get]
    simp only [numericalSlotRow_eq s hs,numericalCycleRead_eq s hs,numericalCycleStep_eq,
      slotCycleRow,cyclePredecessor_on]
  · have ha : ¬ ((numberedCycleAssignments cyc a).map Prod.fst).idxOf (slotRowNumber i) <
        (numberedCycleAssignments cyc a).length := by
      rw [← List.length_map (f := Prod.fst),List.idxOf_lt_length_iff]
      intro hm
      simp only [numberedCycleAssignments,List.map_ofFn,Function.comp_def,List.mem_ofFn] at hm
      obtain ⟨j,hj⟩ := hm
      exact hi ⟨ZMod.finEquiv t j,(slotRowEquiv k m).injective
        (Fin.ext (by simpa only [slotRowEquiv_val] using hj))⟩
    dsimp only
    rw [ite_eq_right ha,numericalSlotRow_eq s hs,slotCycleRow, cyclePredecessor_off _ _ (not_exists.mp hi)]

local instance numericalGuardAmbientDecEq : DecidableEq (SharedCoordinates.Ambient s.layout) :=
  fun a b => Classical.propDecidable (a = b)

theorem numericalSlotCycle_correct (hs : s.prime = rankedSlotPrime k m) :
    (cycleCodes (order s.layout) (numericalSlotCycleRows k m (numberedCycleAssignments cyc a))).toFinset.image
      (decodePoint s.layout) = s.rowCycleMask cyc a := by
  apply s.numericalCycle_correct cyc a (cyclePredecessor cyc)
  · exact cyclePredecessor_on cyc
  · exact cyclePredecessor_off cyc
  · intro r
    simp only [numericalSlotCycleRows,List.mem_map,List.mem_range]
    constructor
    · rintro ⟨i,hi,he⟩
      let row := (slotRowEquiv k m).symm ⟨i,hi⟩
      have hv : slotRowNumber row = i := by
        rw [← slotRowEquiv_val]
        exact congrArg Fin.val ((slotRowEquiv k m).apply_symm_apply ⟨i,hi⟩)
      refine ⟨row,(s.numericalCycleRow_get cyc a hs row).symm.trans ?_⟩
      simpa only [hv] using he
    · rintro ⟨i,rfl⟩
      exact ⟨slotRowNumber i,by rw [← slotRowEquiv_val]; exact (slotRowEquiv k m i).isLt,
        s.numericalCycleRow_get cyc a hs i⟩
/-- A numerical list containing each selected row once determines
the cyclic ordering of that partial pattern. -/
theorem exists_numberedCycle {W : Type} [Nonempty W] (xs : GuardedAssignments)
    (rows : W ↪ SlotRow k m) (label : ∀ i, RowLabel (rows i))
    (hn : (xs.map Prod.fst).Nodup)
    (hm : ∀ p, p ∈ xs ↔ ∃ i, (slotRowNumber (rows i),rowLabelNumber (rows i) (label i)) = p) :
    ∃ (h : NeZero xs.length) (e : ZMod xs.length ≃ W),
      xs = @numberedCycleAssignments k m xs.length h (e.toEmbedding.trans rows) (assignLabels rows label) := by
  have ht : NeZero xs.length := by
    obtain ⟨i⟩ := ‹Nonempty W›
    have hi := (hm _).mpr ⟨i,rfl⟩
    exact ⟨by intro he; rw [List.length_eq_zero_iff.mp he] at hi; exact List.not_mem_nil hi⟩
  let f : Fin xs.length → W := fun j => ((hm _).mp (List.getElem_mem j.isLt)).choose
  have hf (j : Fin xs.length) :
      (slotRowNumber (rows (f j)),rowLabelNumber (rows (f j)) (label (f j))) = xs[j.val] :=
    ((hm _).mp (List.getElem_mem j.isLt)).choose_spec
  have hinj : Function.Injective (fun i : W => slotRowNumber (rows i)) := fun _ _ h =>
    rows.injective ((slotRowEquiv k m).injective (Fin.ext (by simpa only [slotRowEquiv_val] using h)))
  have hb : Function.Bijective f := by
    constructor
    · intro i j hij
      have hi := hn.idxOf_getElem i.val (by simpa only [List.length_map] using i.isLt)
      have hj := hn.idxOf_getElem j.val (by simpa only [List.length_map] using j.isLt)
      simp only [List.getElem_map,← hf i,← hf j,hij] at hi hj
      exact Fin.ext (hi.symm.trans hj)
    · intro i
      obtain ⟨j,hj,he⟩ := List.mem_iff_getElem.mp ((hm _).mpr ⟨i,rfl⟩)
      let a : Fin xs.length := ⟨j,hj⟩
      exact ⟨a,hinj (congrArg Prod.fst ((hf a).trans he))⟩
  let e := (ZMod.finEquiv xs.length).symm.toEquiv.trans (Equiv.ofBijective f hb)
  refine ⟨ht,e,?_⟩
  apply List.ext_getElem
  · exact List.length_ofFn.symm
  · intro j hj h'
    simp only [numberedCycleAssignments,List.getElem_ofFn]
    change xs[j] = (slotRowNumber (rows (e (ZMod.finEquiv xs.length ⟨j,hj⟩))),
      rowLabelNumber _ (assignLabels rows label (rows (e (ZMod.finEquiv xs.length ⟨j,hj⟩)))))
    rw [assignLabels_selected]
    have hid : e (ZMod.finEquiv xs.length ⟨j,hj⟩) = f ⟨j,hj⟩ := by simp [e]
    rw [hid]
    exact (hf ⟨j,hj⟩).symm

end

end

end TranslationTiling.FiniteCompiler.Packed.SlotParameters
