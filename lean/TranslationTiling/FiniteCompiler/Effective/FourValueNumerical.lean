import TranslationTiling.FiniteCompiler.Effective.FourValueBatch
import TranslationTiling.FiniteCompiler.Effective.FourValueParameters
import TranslationTiling.FiniteCompiler.Effective.PackedPatternData

namespace TranslationTiling.FiniteCompiler.Packed

open Compiler Compiler.Size Compiler.Effective Effective SharedCoordinates

noncomputable section

set_option maxRecDepth 10000
set_option maxHeartbeats 3000000

/-- The order is the shared output followed by the outputs for values 0 through 3. -/
def fourValueModuli (k i : ℕ) : List ℕ :=
  (fourValueWangRow k i).1 :: (List.range 4).map (fourValueOutput k i)

def numericalShifts (coords : List ℕ) : List ℕ :=
  if coords.getD 0 0 < 2 ∧ coords.getD 1 0 < 2 ∧ coords.getD 2 0 < 2 ∧
      coords.getD 3 0 < 2 ∧ coords.getD 4 0 < 2 then
    (List.range 5).map fun j => (coords.getD j 0 + coords.getD ((j+1)%5) 0)%2
  else coords

private theorem numericalShifts_primrec : Primrec numericalShifts := by
  unfold numericalShifts
  apply Primrec.ite (by fun_prop) _ Primrec.id
  apply mapList (Primrec.const (List.range 5))
  fun_prop

/-- An activation record indexed by a low input and a CRT residue of the five
observed coordinates. The useful shift is stored with the horizontal offset. -/
def fourValueRecord (r s : ℕ) (ms other : List ℕ) (l z : ℕ) :
    Plane × CongruenceList :=
  let coords := ms.map (z % ·)
  let es := numericalShifts coords
  let inds := List.range ms.length
  let M := r*ms.prod
  let h := residueSearch M ((r,l) :: inds.map (fun j =>
    (ms.getD j 0,differenceResidue (ms.getD j 0) (coords.getD j 0) (es.getD j 0))))
  (((h : ℤ),-(s : ℤ)*(h : ℤ)),
    (inds.map fun j => (ms.getD j 0,es.getD j 0)) ++ other.map (·,0))

def fourValueActivationRecords (r s : ℕ) (ms other : List ℕ) : List (Plane × CongruenceList) :=
  (List.range r).flatMap fun l =>
    (List.range ms.prod).map (fourValueRecord r s ms other l)

def wangActivationInputs (k i : ℕ) : ℕ × ℕ × List ℕ × List ℕ :=
  (fourValueLow k i, if i < k then 0 else 2, fourValueModuli k i,
    guardedOther (fourValueRows k) (18+i))

def recordsOfInputs (v : ℕ × ℕ × List ℕ × List ℕ) :=
  fourValueActivationRecords v.1 v.2.1 v.2.2.1 v.2.2.2

def activationDeckArgs (k i : ℕ) : (ℕ × ℕ) × List (Plane × CongruenceList) :=
  ((sharedOrder (fourValueRows k),fourValueLow k i),
    recordsOfInputs (wangActivationInputs k i))

def fourValueWangActivation (k i : ℕ) : CyclicTile :=
  congruenceBatchDeck (activationDeckArgs k i).1.1 (activationDeckArgs k i).1.2
    (activationDeckArgs k i).2

def fourValueActivation (k : ℕ) : List CyclicTile :=
  let rs := fourValueRows k
  ((List.range 18).map fun i => compactCodes (sharedEnvironment rs i) ((tailSlopes k).getD i 0)) ++
  (List.range (2*k)).map (fourValueWangActivation k) ++
  (List.range 2).map fun t => seedCodes (sharedEnvironment rs (rs.length-2+t))
    (rowA rs (rs.length-2+(1-t))) 35

def fourValueCycleRows (k : ℕ) (xs : GuardedAssignments) : List CycleRow :=
  let rs := fourValueRows k
  let keys := xs.map Prod.fst
  (List.range rs.length).map fun i =>
    let j := keys.idxOf i
    if j < xs.length then
      let pred := xs.getD ((j + xs.length - 1) % xs.length) (0,0)
      let a := sharedObservedA rs pred.1
      let b := if 18 ≤ pred.1 ∧ pred.1 < rs.length-2 then
        fourValueOutput k (pred.1-18) pred.2
      else rowB rs pred.1
      let step := if 18 ≤ i ∧ i < rs.length-2 then 1
        else rowR rs i / ((rowDigits rs i).getD (xs.getD j (0,0)).2 0)
      (rowR rs i,a,b,triggerTable a b step)
    else (rowR rs i,1,1,[0])

def fourValueCycle (k : ℕ) (xs : GuardedAssignments) : List CyclicTile :=
  if xs.length = 0 then [] else [cycleCodes (sharedOrder (fourValueRows k)) (fourValueCycleRows k xs)]

def fourValueTests (T : LeanWang.TileSet) (k : ℕ) : List GuardedAssignments :=
  tailSeedTests k ++ (rawGuardedMasks T (4^k)).map (expandMask 4 k)

def fourValueRawDeck (T : LeanWang.TileSet) (k : ℕ) : List CyclicTile :=
  let rs := fourValueRows k
  kernelCodes (sharedOrder rs) (guardedModuli rs) ::
    (sharedDependence rs (tailSlopes k) ++ fourValueActivation k ++
      (fourValueTests T k).flatMap (fourValueCycle k))

@[fun_prop] theorem fourValueModuli_primrec :
    Primrec (fun z : ℕ × ℕ => fourValueModuli z.1 z.2) := by
  unfold fourValueModuli
  fun_prop

private abbrev RecordInput := (ℕ × ℕ × List ℕ × List ℕ) × ℕ × ℕ

@[fun_prop] theorem fourValueRecord_primrec :
    Primrec (fun v : (ℕ × ℕ × List ℕ × List ℕ) × ℕ × ℕ =>
      fourValueRecord v.1.1 v.1.2.1 v.1.2.2.1 v.1.2.2.2 v.2.1 v.2.2) := by
  let mods (v : RecordInput) := v.1.2.2.1
  let coords (v : RecordInput) := (mods v).map (v.2.2 % ·)
  let es (v : RecordInput) := numericalShifts (coords v)
  have hm : Primrec mods := by unfold mods; fun_prop
  have hc : Primrec coords := by
    unfold coords
    exact mapList hm (by fun_prop)
  have he : Primrec es := numericalShifts_primrec.comp hc
  have hind := Primrec.list_range.comp (Primrec.list_length.comp hm)
  let batchData (v : RecordInput) :=
    (List.range (mods v).length).map fun j => ((mods v).getD j 0,
      differenceResidue ((mods v).getD j 0) ((coords v).getD j 0) ((es v).getD j 0))
  have hbatch : Primrec batchData := by
    unfold batchData
    apply mapList hind
    have hd : Primrec (fun z : RecordInput × ℕ =>
        ((mods z.1).getD z.2 0,(coords z.1).getD z.2 0,(es z.1).getD z.2 0)) := by
      fun_prop
    exact Primrec.pair (by fun_prop) (differenceResidue_primrec.comp hd)
  have hsearch : Primrec (fun v : RecordInput =>
      (v.1.1*(mods v).prod,(v.1.1,v.2.1) :: batchData v)) :=
    (natMul (by fun_prop) (product_primrec.comp hm)).pair
      (consList (show Primrec (fun v : RecordInput => (v.1.1,v.2.1))
        by fun_prop) hbatch)
  have hh := residueSearch_primrec.comp hsearch
  let horizontal (v : RecordInput) :=
    residueSearch (v.1.1*(mods v).prod) ((v.1.1,v.2.1) :: batchData v)
  change Primrec (fun v : RecordInput =>
    (((horizontal v : ℤ),-(v.1.2.1 : ℤ)*(horizontal v : ℤ)),
      (List.range (mods v).length).map (fun j => ((mods v).getD j 0,(es v).getD j 0)) ++
        (v.1.2.2.2).map (·,0)))
  apply Primrec.pair
  · exact Primrec.pair (by fun_prop) (by fun_prop)
  · exact appendList (mapList hind (by fun_prop)) (mapList (by fun_prop) (by fun_prop))

@[fun_prop] theorem fourValueActivationRecords_primrec :
    Primrec (fun v : ℕ × ℕ × List ℕ × List ℕ =>
      fourValueActivationRecords v.1 v.2.1 v.2.2.1 v.2.2.2) := by
  unfold fourValueActivationRecords
  apply flatMapList (by fun_prop)
  apply mapList
  · apply Primrec.list_range.comp
    exact product_primrec.comp (show Primrec (fun v : (ℕ × ℕ × List ℕ × List ℕ) × ℕ =>
      v.1.2.2.1) by fun_prop)
  · exact fourValueRecord_primrec.comp (show Primrec (fun v :
      ((ℕ × ℕ × List ℕ × List ℕ) × ℕ) × ℕ => (v.1.1,v.1.2,v.2)) by fun_prop)

@[fun_prop] theorem fourValueWangActivation_primrec :
    Primrec (fun z : ℕ × ℕ => fourValueWangActivation z.1 z.2) := by
  have hg : Primrec (fun z : ℕ × ℕ => guardedOther (fourValueRows z.1) (18+z.2)) := by
    unfold guardedOther
    fun_prop
  have horder : Primrec (fun z : ℕ × ℕ => sharedOrder (fourValueRows z.1)) := by fun_prop
  have hlow : Primrec (fun z : ℕ × ℕ => fourValueLow z.1 z.2) := fourValueLow_primrec
  have hs : Primrec (fun z : ℕ × ℕ => if z.2 < z.1 then (0 : ℕ) else 2) := by fun_prop
  have hrecArg : Primrec (fun z : ℕ × ℕ => wangActivationInputs z.1 z.2) := by
    unfold wangActivationInputs
    exact hlow.pair (hs.pair (fourValueModuli_primrec.pair hg))
  have hbody : Primrec recordsOfInputs := fourValueActivationRecords_primrec
  have hrecords : Primrec (fun z : ℕ × ℕ => recordsOfInputs (wangActivationInputs z.1 z.2)) :=
    hbody.comp hrecArg
  have hargs : Primrec (fun z : ℕ × ℕ => activationDeckArgs z.1 z.2) := by
    unfold activationDeckArgs
    exact (horder.pair hlow).pair hrecords
  unfold fourValueWangActivation
  exact congruenceBatchDeck_primrec.comp hargs

@[fun_prop] theorem fourValueActivation_primrec : Primrec fourValueActivation := by
  unfold fourValueActivation
  dsimp only
  have ho := compactCodes_primrec.comp (show Primrec (fun z : ℕ × ℕ =>
    (sharedEnvironment (fourValueRows z.1) z.2,(tailSlopes z.1).getD z.2 0)) by fun_prop)
  have hs := seedCodes_primrec.comp (show Primrec (fun z : ℕ × ℕ =>
    let rs := fourValueRows z.1
    (sharedEnvironment rs (rs.length-2+z.2),rowA rs (rs.length-2+(1-z.2)),35)) by fun_prop)
  apply appendList (appendList (mapList (Primrec.const _) ho) ?_) (mapList (Primrec.const _) hs)
  apply mapList (by fun_prop) fourValueWangActivation_primrec

@[fun_prop] theorem fourValueCycleRows_primrec :
    Primrec (fun z : ℕ × GuardedAssignments => fourValueCycleRows z.1 z.2) := by
  unfold fourValueCycleRows
  dsimp only
  apply mapList (by fun_prop)
  have hi : Primrec (fun z : (ℕ × GuardedAssignments) × ℕ =>
      (z.1.2.map Prod.fst).idxOf z.2) :=
    Primrec.list_idxOf.comp Primrec.snd (by fun_prop)
  fun_prop

@[fun_prop] theorem fourValueCycle_primrec :
    Primrec (fun z : ℕ × GuardedAssignments => fourValueCycle z.1 z.2) := by
  unfold fourValueCycle
  have h := cycleCodes_primrec.comp (show Primrec (fun z : ℕ × GuardedAssignments =>
    (sharedOrder (fourValueRows z.1),fourValueCycleRows z.1 z.2)) by fun_prop)
  fun_prop

@[fun_prop] theorem fourValueTests_primrec :
    Primrec (fun z : LeanWang.TileSet × ℕ => fourValueTests z.1 z.2) := by
  unfold fourValueTests
  have hm := rawGuardedMasks_primrec.comp
    (show Primrec (fun z : LeanWang.TileSet × ℕ => (z.1,4^z.2)) by fun_prop)
  exact appendList (tailSeedTests_primrec.comp Primrec.snd)
    (mapList hm (expandMask_primrec.comp
      (show Primrec (fun z : (LeanWang.TileSet × ℕ) × RawMask => (4,z.1.2,z.2)) by fun_prop)))

private theorem fourValueCycleDeck_primrec : Primrec (fun z : LeanWang.TileSet × ℕ =>
    (fourValueTests z.1 z.2).flatMap (fourValueCycle z.2)) :=
  flatMapList fourValueTests_primrec (fourValueCycle_primrec.comp (show Primrec
    (fun z : (LeanWang.TileSet × ℕ) × GuardedAssignments => (z.1.2,z.2)) by fun_prop))

@[fun_prop] theorem fourValueRawDeck_primrec :
    Primrec (fun z : LeanWang.TileSet × ℕ => fourValueRawDeck z.1 z.2) := by
  unfold fourValueRawDeck
  dsimp only
  have hk := kernelCodes_primrec.comp (show Primrec (fun z : LeanWang.TileSet × ℕ =>
    (sharedOrder (fourValueRows z.2),guardedModuli (fourValueRows z.2))) by fun_prop)
  have hd := sharedDependence_primrec.comp (show Primrec (fun z : LeanWang.TileSet × ℕ =>
    (fourValueRows z.2,tailSlopes z.2)) by fun_prop)
  exact consList hk (appendList (appendList hd (fourValueActivation_primrec.comp Primrec.snd))
    fourValueCycleDeck_primrec)

end
end TranslationTiling.FiniteCompiler.Packed
