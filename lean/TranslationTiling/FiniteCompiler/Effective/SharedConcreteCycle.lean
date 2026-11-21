import TranslationTiling.FiniteCompiler.Effective.SharedCycle
import TranslationTiling.FiniteCompiler.Effective.SharedDigits

namespace TranslationTiling.FiniteCompiler.Packed

open Compiler.Effective Effective SharedCoordinates
open scoped Classical
noncomputable section

variable {k : ℕ} {t : ℕ} [NeZero t]
  (c : ZMod t ↪ SharedRow k) (lab : ∀ j, SharedLabel (c j))

def sharedAssignments : GuardedAssignments := List.ofFn fun j =>
  ((c (ZMod.finEquiv t j)).val,(lab (ZMod.finEquiv t j)).val)

private theorem finEquiv_symm_val (j : ZMod t) : ((ZMod.finEquiv t).symm j).val = j.val := by
  cases t with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ t => rfl

private theorem sharedAssignments_get (j : ZMod t) :
    (sharedAssignments c lab).getD j.val (0,0) = ((c j).val,(lab j).val) := by
  have h : (((ZMod.finEquiv t).symm j) : ℕ) = j.val := finEquiv_symm_val j
  rw [← h]
  simp only [sharedAssignments,List.getD_eq_getElem?_getD,List.getElem?_ofFn,
    dif_pos ((ZMod.finEquiv t).symm j).isLt,Option.getD_some]
  exact congrArg (fun z : ZMod t => ((c z).val,(lab z).val)) ((ZMod.finEquiv t).apply_symm_apply j)

private theorem sharedAssignments_idx (j : ZMod t) :
    ((sharedAssignments c lab).map Prod.fst).idxOf (c j).val = j.val := by
  let f (u : Fin t) := (c (ZMod.finEquiv t u)).val
  have hf : Function.Injective f :=
    fun _ _ h => (ZMod.finEquiv t).injective (c.injective (Fin.ext h))
  let b := (ZMod.finEquiv t).symm j
  have hm : (c j).val ∈ List.ofFn f := List.mem_ofFn.mpr ⟨b, by simp [f,b]⟩
  have hi := List.idxOf_lt_length_of_mem hm
  rw [List.length_ofFn] at hi
  have he := List.getElem_idxOf (List.idxOf_lt_length_of_mem hm)
  rw [List.getElem_ofFn] at he
  have he' : f ⟨(List.ofFn f).idxOf (c j).val,hi⟩ = f b := by simpa [f,b] using he
  have e : (sharedAssignments c lab).map Prod.fst = List.ofFn f := by
    simp [sharedAssignments,List.map_ofFn,Function.comp_def,f]
  rw [e,← finEquiv_symm_val j]
  exact congrArg Fin.val (hf he')

private theorem sharedAssignments_absent (i : SharedRow k) (hi : ∀ j, c j ≠ i) :
    (sharedAssignments c lab).length ≤ ((sharedAssignments c lab).map Prod.fst).idxOf i.val := by
  by_contra! h
  have hm : i.val ∈ (sharedAssignments c lab).map Prod.fst :=
    List.idxOf_lt_length_iff.mp (by simpa only [List.length_map] using h)
  simp only [sharedAssignments,List.map_ofFn,Function.comp_def,List.mem_ofFn] at hm
  exact hi _ (Fin.ext hm.choose_spec)

private theorem sharedAssignments_previous (j : ZMod t) :
    previousColumn (sharedAssignments c lab) j.val = (c (j-1)).val := by
  have ht := NeZero.pos t
  have h : ((j.val+t-1 : ℕ) : ZMod t) = j-1 := by
    rw [Nat.cast_sub (by omega),Nat.cast_add,ZMod.natCast_zmod_val,ZMod.natCast_self,
      Nat.cast_one,add_zero]
  have hm : (j.val+t-1)%t = (j-1).val := by
    simpa only [ZMod.val_natCast] using congrArg ZMod.val h
  unfold previousColumn
  rw [show (sharedAssignments c lab).length = t by simp [sharedAssignments],hm,
    sharedAssignments_get c lab]

/-- An actual compiled exclusion mask rules out simultaneous activity of
the labels in its assignment, in the private output coordinates. -/
theorem sharedCycle_iff (o : SharedOutput k) (g : Plane → ∀ i : SharedRow k,
    SharedCoordinates.Low (sharedLayout k) i → SharedCoordinates.Useful (sharedLayout k) i)
    (hg : ∀ x a i, o.privateOutput (x,a) i = g x i (a i)) :
    (∀ F ∈ sharedCycle (sharedRows k) (sharedAssignments c lab),
      Tiles (F.toFinset.image (decodePoint (sharedLayout k)))
        (Set.range (SharedCoordinates.point (sharedLayout k) o))) ↔
    ∀ x, ∃ j, ¬ DigitActive (g x (c j)) (sharedDigitSubgroup (c j) (lab j)) := by
  let L := sharedLayout k
  let rs := sharedRows k
  let xs := sharedAssignments c lab
  let pred (i : SharedRow k) := if h : ∃ j, c j = i then some (c (h.choose-1)) else none
  let sc (i : SharedRow k) := if h : ∃ j, c j = i then
    rowR rs i / (rowDigits rs i).getD (lab h.choose).val 0 else 0
  have hp (j : ZMod t) : pred (c j) = some (c (j-1)) := by
    unfold pred
    split
    · rename_i h
      rw [c.injective h.choose_spec]
    · rename_i h
      exact (h ⟨j,rfl⟩).elim
  have hstep (j : ZMod t) : sc (c j) = sharedStep (c j) (lab j) := by
    unfold sc
    split
    · rename_i h
      have e := congrArg (fun z : ZMod t => (lab z).val) (c.injective h.choose_spec)
      rw [e]
      unfold sharedStep sharedDigit
      rw [List.getD_eq_getElem _ _ (lab j).isLt]
      rfl
    · rename_i h
      exact (h ⟨j,rfl⟩).elim
  let raw := sharedCycleRows rs xs
  let rows := fixedRows (raw.map Prod.fst) (raw.map Prod.snd)
  have hlen : raw.length = rs.length := by simp [raw,sharedCycleRows]
  have hrows : ∀ y, y ∈ rows ↔ ∃ i, privateCycleRow L pred sc i = y := by
    intro y
    have he (i : SharedRow k) :
        fixedRow ((raw.map Prod.fst).getD i.val (0,[],0,0,false))
          ((raw.map Prod.snd).getD i.val 0) = privateCycleRow L pred sc i := by
      have hi : i.val < raw.length := hlen.symm ▸ i.isLt
      simp only [List.getD_eq_getElem _ _ (show i.val < (raw.map _).length by simpa using hi),
        List.getElem_map]
      unfold raw sharedCycleRows
      simp only [List.getElem_map,List.getElem_range]
      by_cases h : ∃ j, c j = i
      · obtain ⟨j,rfl⟩ := h
        rw [privateCycleRow,hp,sharedAssignments_idx c lab,sharedAssignments_previous c lab,
          sharedAssignments_get c lab,hstep]
        have hj : j.val < xs.length := by simpa [xs,sharedAssignments] using ZMod.val_lt j
        simp only [fixedRow,hj,decide_true,ite_true]
        unfold sharedStep sharedDigit
        rw [List.getD_eq_getElem _ _ (lab j).isLt]
        rfl
      · have ha : xs.length ≤ (xs.map Prod.fst).idxOf i.val :=
          sharedAssignments_absent c lab i (by simpa only [not_exists] using h)
        simp [fixedRow,not_lt_of_ge ha,privateCycleRow,pred,h,L,rs,sharedLayout]
    simp only [rows,fixedRows,List.mem_map,List.mem_range,List.length_map,hlen]
    constructor
    · rintro ⟨i,hi,rfl⟩
      exact ⟨⟨i,hi⟩,(he ⟨i,hi⟩).symm⟩
    · rintro ⟨i,rfl⟩
      exact ⟨i.val,i.isLt,he i⟩
  have hnon : xs.length ≠ 0 := by simpa [xs,sharedAssignments] using NeZero.ne t
  change (∀ F ∈ sharedCycle rs xs, _) ↔ _
  simp only [sharedCycle,hnon,ite_false,fixedGadgets,List.mem_singleton,forall_eq]
  rw [← sharedLayout_order k]
  exact tiles_private_cycle_exclusion_iff L (sharedLayoutCRT k) c
    (fun j => sharedDigitSubgroup (c j) (lab j))
    (fun j => ⟨sharedStep (c j) (lab j),sharedStep_mem (c j) (lab j)⟩)
    (fun j => sharedStep_spans (c j) (lab j)) pred sc hp
    (fun i hi => by simp [pred,not_exists.mpr hi])
    (fun j => by simp [hstep]) rows hrows o g hg

end
end TranslationTiling.FiniteCompiler.Packed
