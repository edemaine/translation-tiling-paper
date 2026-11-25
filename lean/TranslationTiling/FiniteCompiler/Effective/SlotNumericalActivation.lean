import TranslationTiling.FiniteCompiler.Effective.SlotShiftEvaluation
import TranslationTiling.Compiler.EffectiveLists
import TranslationTiling.Compiler.EffectiveLattice

namespace TranslationTiling.FiniteCompiler.Packed

open TranslationTiling.Compiler TranslationTiling.Compiler.Effective

set_option maxHeartbeats 1000000

/-- Evaluate the cyclic XOR exactly on the binary part of the product. -/
def numericalSlotShift (coords : List ℕ) : List ℕ :=
  if ∀ a ∈ coords, a < 2 then
    (List.range coords.length).map fun j =>
      (coords.getD j 0 + coords.getD ((j+1)%coords.length) 0)%2
  else coords

@[fun_prop] theorem numericalSlotShift_primrec : Primrec numericalSlotShift := by
  unfold numericalSlotShift
  apply Primrec.ite (by fun_prop) _ Primrec.id
  apply mapList (by fun_prop)
  fun_prop

/-- The cyclic order, the line slope, selected low moduli, remaining low
moduli, observed output primes, and the hidden fallback primes. -/
abbrev NumericalSlotBatch := ℕ × ℤ × List ℕ × List ℕ × List ℕ × List ℕ

/-- The first congruence list determines the displacement, and the
second determines which cyclic representatives are at that displacement. -/
def numericalSlotRecord (b : NumericalSlotBatch) (low output : ℕ) : Plane × CongruenceList :=
  let selected := b.2.2.1
  let remaining := b.2.2.2.1
  let observed := b.2.2.2.2.1
  let hidden := b.2.2.2.2.2
  let coords := observed.map (output % ·)
  let shifts := numericalSlotShift coords
  let indices := List.range observed.length
  let modulus := selected.prod * observed.prod * hidden.prod
  let h := evaluatedSlotOffset modulus
    ((selected.map fun p => (p,low % p)) ++ (hidden.map (·,0)) ++
      indices.map (fun j => (observed.getD j 0,
        differenceResidue (observed.getD j 0) (coords.getD j 0) (shifts.getD j 0))))
    (low*observed.prod+output) b.2.1
  (h,(selected.map fun r => (r^2,(h.1 % (r^2 : ℕ)).toNat)) ++
    (remaining.map (·,0)) ++ indices.map (fun j => (observed.getD j 0,shifts.getD j 0)))

private abbrev SlotRecordInput := NumericalSlotBatch × ℕ × ℕ

@[fun_prop] theorem numericalSlotRecord_primrec : Primrec (fun z : NumericalSlotBatch × ℕ × ℕ =>
    numericalSlotRecord z.1 z.2.1 z.2.2) := by
  let selected (z : SlotRecordInput) := z.1.2.2.1
  let remaining (z : SlotRecordInput) := z.1.2.2.2.1
  let observed (z : SlotRecordInput) := z.1.2.2.2.2.1
  let hidden (z : SlotRecordInput) := z.1.2.2.2.2.2
  let coords (z : SlotRecordInput) := (observed z).map (z.2.2 % ·)
  let shifts (z : SlotRecordInput) := numericalSlotShift (coords z)
  let indices (z : SlotRecordInput) := List.range (observed z).length
  have hs : Primrec selected := by unfold selected; fun_prop
  have hr : Primrec remaining := by unfold remaining; fun_prop
  have hv : Primrec observed := by unfold observed; fun_prop
  have hh : Primrec hidden := by unfold hidden; fun_prop
  have hc : Primrec coords := mapList hv (by fun_prop)
  have hshift : Primrec shifts := numericalSlotShift_primrec.comp hc
  have hi : Primrec indices := Primrec.list_range.comp (Primrec.list_length.comp hv)
  let moduli (z : SlotRecordInput) := (selected z).prod * (observed z).prod * (hidden z).prod
  have hp := product_primrec
  have hM : Primrec moduli := by unfold moduli; fun_prop
  let diffs (z : SlotRecordInput) := (indices z).map fun j =>
    ((observed z).getD j 0,differenceResidue ((observed z).getD j 0)
      ((coords z).getD j 0) ((shifts z).getD j 0))
  have hdiff : Primrec diffs := by
    apply mapList hi
    have hdata : Primrec (fun z : SlotRecordInput × ℕ =>
      ((observed z.1).getD z.2 0,(coords z.1).getD z.2 0,(shifts z.1).getD z.2 0)) := by
      fun_prop
    exact (by fun_prop : Primrec (fun z : SlotRecordInput × ℕ => (observed z.1).getD z.2 0)).pair
      (differenceResidue_primrec.comp hdata)
  let cs (z : SlotRecordInput) :=
    ((selected z).map fun p => (p,z.2.1 % p)) ++ (hidden z).map (·,0) ++ diffs z
  have hcs : Primrec cs := by
    unfold cs
    exact appendList (appendList (mapList hs (by fun_prop)) (mapList hh (by fun_prop))) hdiff
  let offset (z : SlotRecordInput) :=
    evaluatedSlotOffset (moduli z) (cs z) (z.2.1*(observed z).prod+z.2.2) z.1.2.1
  have hargs : Primrec (fun z : SlotRecordInput =>
      ((moduli z,cs z),z.2.1*(observed z).prod+z.2.2,z.1.2.1)) := by fun_prop
  have hoffset : Primrec offset := evaluatedSlotOffset_primrec.comp hargs
  change Primrec (fun z : SlotRecordInput => (offset z,
    ((selected z).map fun r => (r^2,((offset z).1 % (r^2 : ℕ)).toNat)) ++
      (remaining z).map (·,0) ++ (indices z).map
        (fun j => ((observed z).getD j 0,(shifts z).getD j 0))))
  simp only [pow_two]
  exact hoffset.pair (appendList
    (appendList (mapList hs (by fun_prop)) (mapList hr (by fun_prop))) (mapList hi (by fun_prop)))

private abbrev SlotRecord := Plane × CongruenceList

def numericalBatchPoints (N : ℕ) (batch : SlotRecord) : CyclicTile :=
  ((List.range N).filter fun n => decide (Congruences batch.2 n)).map fun n => (batch.1,n)

private theorem numericalBatchPoints_primrec :
    Primrec (fun z : ℕ × SlotRecord => numericalBatchPoints z.1 z.2) := by
  unfold numericalBatchPoints
  have hr : Primrec (fun z : ℕ × SlotRecord => List.range z.1) :=
    Primrec.list_range.comp Primrec.fst
  have hc : Primrec (fun z : (ℕ × SlotRecord) × ℕ => (z.1.2.2,z.2)) :=
    (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)).pair Primrec.snd
  have hf := filterList (p := fun z n => Congruences z.2.2 n) hr (congruences_primrec.comp hc)
  exact mapList hf ((Primrec.fst.comp (Primrec.snd.comp Primrec.fst)).pair Primrec.snd)

/-- One batch per low vector and observed vector, each encoded by its CRT
representative. This uses the same separated-offset bound as the slot mask. -/
def numericalSlotActivation (b : NumericalSlotBatch) : CyclicTile :=
  (List.range b.2.2.1.prod).flatMap fun low =>
    (List.range b.2.2.2.2.1.prod).flatMap fun output =>
      numericalBatchPoints b.1 (numericalSlotRecord b low output)

private abbrev SlotActivationInput := (NumericalSlotBatch × ℕ) × ℕ

theorem numericalSlotActivation_primrec : Primrec numericalSlotActivation := by
  let args (a : SlotActivationInput) : SlotRecordInput := (a.1.1,a.1.2,a.2)
  have ha : Primrec args :=
    (Primrec.fst.comp Primrec.fst).pair ((Primrec.snd.comp Primrec.fst).pair Primrec.snd)
  have hb : Primrec (fun a : SlotActivationInput =>
      numericalSlotRecord (args a).1 (args a).2.1 (args a).2.2) :=
    numericalSlotRecord_primrec.comp ha
  have hN : Primrec (fun a : SlotActivationInput => a.1.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have hp := numericalBatchPoints_primrec.comp (hN.pair hb)
  have hlo : Primrec (fun b : NumericalSlotBatch => List.range b.2.2.1.prod) :=
    Primrec.list_range.comp (product_primrec.comp (by fun_prop))
  have hout : Primrec (fun p : NumericalSlotBatch × ℕ => List.range p.1.2.2.2.2.1.prod) :=
    Primrec.list_range.comp (product_primrec.comp (by fun_prop))
  exact flatMapList hlo (flatMapList hout hp)

/-- The array implementation and the verified cyclic shift return the
same residue in each coordinate. -/
theorem numericalSlotShift_correct {d : ℕ} [NeZero d] {m : ZMod d → ℕ}
    (hm : ∀ j, 1 < m j) (z : SlotShift.Shift m) (j : ZMod d) :
    let vals := List.ofFn fun i : Fin d => (z (i.val : ZMod d)).val
    (numericalSlotShift vals).getD j.val 0 = (SlotShift.shift z j).val := by
  let vals := List.ofFn fun i : Fin d => (z (i.val : ZMod d)).val
  have hlen : vals.length = d := List.length_ofFn
  have hj := ZMod.val_lt j
  have he (v : ZMod d) : vals.getD v.val 0 = (z v).val := by
    rw [List.getD_eq_getElem _ _ (by rw [hlen]; exact ZMod.val_lt v)]
    simp only [vals,List.getElem_ofFn]
    rw [ZMod.natCast_zmod_val]
  have hbin : (∀ a ∈ vals, a < 2) ↔
      (List.finRange d).all (fun i => decide ((z (i.val : ZMod d)).val ≤ 1)) = true := by
    rw [List.all_eq_true]
    constructor
    · intro h i _
      have hu := h _ (List.mem_ofFn.mpr ⟨i,rfl⟩)
      exact decide_eq_true (by omega)
    · intro h a ha
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ha
      have hu := of_decide_eq_true (h i (List.mem_finRange i))
      omega
  change (numericalSlotShift vals).getD j.val 0 = _
  rw [← SlotShift.evaluate_eq_shift hm z]
  by_cases hb : ∀ a ∈ vals, a < 2
  · rw [numericalSlotShift,ite_eq_left hb,SlotShift.evaluate,ite_eq_left (hbin.mp hb)]
    have hnext : (j+1).val = (j.val+1)%vals.length := by
      have hh : ((j.val+1 : ℕ) : ZMod d) = j+1 := by simp
      rw [← hh,ZMod.val_natCast,hlen]
    have hk : j.val < ((List.range vals.length).map (fun u =>
        (vals.getD u 0 + vals.getD ((u+1)%vals.length) 0)%2)).length := by simpa [hlen] using hj
    rw [List.getD_eq_getElem _ _ hk]
    simp only [List.getElem_map,List.getElem_range,← hnext,he]
    have hmem (v : ZMod d) : (z v).val ∈ vals := by
      apply List.mem_ofFn.mpr
      refine ⟨⟨v.val,ZMod.val_lt v⟩,?_⟩
      change (z (v.val : ZMod d)).val = (z v).val
      rw [ZMod.natCast_zmod_val]
    have hleft : (z j).val ≤ 1 := Nat.lt_succ_iff.mp (hb _ (hmem j))
    have hright : (z (j+1)).val ≤ 1 := Nat.lt_succ_iff.mp (hb _ (hmem (j+1)))
    have : Fact (1 < m j) := ⟨hm j⟩
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hleft with h₀ | h₀ <;>
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hright with h₁ | h₁ <;>
      simp [h₀,h₁,ZMod.val_one]
  · rw [numericalSlotShift,ite_eq_right hb,SlotShift.evaluate,ite_eq_right (mt hbin.mpr hb)]
    exact he j

end TranslationTiling.FiniteCompiler.Packed
