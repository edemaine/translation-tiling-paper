import TranslationTiling.FiniteCompiler.Effective.ObservedCycle
import TranslationTiling.FiniteCompiler.Effective.FourValueFixed
import TranslationTiling.FiniteCompiler.Effective.FourValueNumerical

namespace TranslationTiling.FiniteCompiler.Packed

open Compiler Compiler.Effective Effective SharedCoordinates
open scoped Classical
noncomputable section

set_option maxRecDepth 10000
set_option maxHeartbeats 3000000

variable {k : ℕ} {t : ℕ} [NeZero t]
  (c : ZMod t ↪ FourValueRow k) (lab : ZMod t → ℕ)

def fourValueAssignments : GuardedAssignments := List.ofFn fun j =>
  ((c (ZMod.finEquiv t j)).val,lab (ZMod.finEquiv t j))

private theorem finEquiv_symm_val (j : ZMod t) : ((ZMod.finEquiv t).symm j).val = j.val := by
  cases t with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ t => rfl

private theorem fourValueAssignments_get (j : ZMod t) :
    (fourValueAssignments c lab).getD j.val (0,0) = ((c j).val,lab j) := by
  have h : (((ZMod.finEquiv t).symm j) : ℕ) = j.val := finEquiv_symm_val j
  rw [← h]
  simp only [fourValueAssignments,List.getD_eq_getElem?_getD,List.getElem?_ofFn,
    dif_pos ((ZMod.finEquiv t).symm j).isLt,Option.getD_some]
  exact congrArg (fun z : ZMod t => ((c z).val,lab z)) ((ZMod.finEquiv t).apply_symm_apply j)

private theorem fourValueAssignments_idx (j : ZMod t) :
    ((fourValueAssignments c lab).map Prod.fst).idxOf (c j).val = j.val := by
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
  have e : (fourValueAssignments c lab).map Prod.fst = List.ofFn f := by
    simp [fourValueAssignments,List.map_ofFn,Function.comp_def,f]
  rw [e,← finEquiv_symm_val j]
  exact congrArg Fin.val (hf he')

private theorem fourValueAssignments_absent (i : FourValueRow k) (hi : ∀ j, c j ≠ i) :
    (fourValueAssignments c lab).length ≤ ((fourValueAssignments c lab).map Prod.fst).idxOf i.val := by
  by_contra! h
  have hm : i.val ∈ (fourValueAssignments c lab).map Prod.fst :=
    List.idxOf_lt_length_iff.mp (by simpa only [List.length_map] using h)
  simp only [fourValueAssignments,List.map_ofFn,Function.comp_def,List.mem_ofFn] at hm
  exact hi _ (Fin.ext hm.choose_spec)

private theorem fourValueAssignments_previous (j : ZMod t) :
    previousColumn (fourValueAssignments c lab) j.val = (c (j-1)).val := by
  have ht := NeZero.pos t
  have h : ((j.val+t-1 : ℕ) : ZMod t) = j-1 := by
    rw [Nat.cast_sub (by omega),Nat.cast_add,ZMod.natCast_zmod_val,ZMod.natCast_self,
      Nat.cast_one,add_zero]
  have hm : (j.val+t-1)%t = (j-1).val := by
    simpa only [ZMod.val_natCast] using congrArg ZMod.val h
  unfold previousColumn
  rw [show (fourValueAssignments c lab).length = t by simp [fourValueAssignments],hm,
    fourValueAssignments_get c lab]

def IsWangRow (i : FourValueRow k) : Prop := 18 ≤ i.val ∧ i.val < (fourValueRows k).length-2

instance (i : FourValueRow k) : Decidable (IsWangRow i) := inferInstanceAs (Decidable (_ ∧ _))

def wangRowOf (i : FourValueRow k) (h : IsWangRow i) : WangDigitRow k :=
  ⟨i.val-18,by have ho := fourValueRows_length k; unfold IsWangRow at h; omega⟩

theorem wangRowOf_eq (i : FourValueRow k) (h : IsWangRow i) :
    wangDigitRow (wangRowOf i h) = i := by
  apply Fin.ext
  change 18+(i.val-18) = i.val
  unfold IsWangRow at h
  omega

theorem isWangRow_digit (w : WangDigitRow k) : IsWangRow (wangDigitRow w) := by
  change 18 ≤ 18+w.val ∧ 18+w.val < (fourValueRows k).length-2
  rw [fourValueRows_length]
  have := w.isLt
  omega

def fourValueCycleModulus (i : FourValueRow k) (v : ℕ) : ℕ :=
  if IsWangRow i then fourValueOutput k (i.val-18) v else (fourValueLayout k).secondSize i

theorem fourValueCycleModulus_dvd (i : FourValueRow k) (v : ℕ)
    (hv : IsWangRow i → v < 4) :
    fourValueCycleModulus i v ∣ (fourValueLayout k).secondSize i := by
  unfold fourValueCycleModulus
  split_ifs with h
  · have he := wangDigitRow_second (wangRowOf i h)
    rw [wangRowOf_eq] at he
    rw [he]
    exact List.dvd_prod (List.mem_map.mpr ⟨v,List.mem_range.mpr (hv h),rfl⟩)
  · exact dvd_refl _

theorem fourValueCycleModulus_pos (i : FourValueRow k) (v : ℕ)
    (hv : IsWangRow i → v < 4) : 0 < fourValueCycleModulus i v := by
  unfold fourValueCycleModulus
  split_ifs with h
  · exact (fourValueOutput_prime (wangRowOf i h).isLt (hv h)).pos
  · exact NeZero.pos _

def fourValueCycleRead (i : FourValueRow k) (v : ℕ) (hv : IsWangRow i → v < 4) :
    SharedCoordinates.Useful (fourValueLayout k) i →+
      ZMod ((fourValueLayout k).firstSize i) × ZMod (fourValueCycleModulus i v) :=
  (AddMonoidHom.id _).prodMap
    (ZMod.castHom (fourValueCycleModulus_dvd i v hv) (ZMod (fourValueCycleModulus i v))).toAddMonoidHom

theorem fourValueCycleRead_surjective (i : FourValueRow k) (v : ℕ)
    (hv : IsWangRow i → v < 4) : Function.Surjective (fourValueCycleRead i v hv) := by
  intro y
  obtain ⟨x,hx⟩ := ZMod.castHom_surjective (fourValueCycleModulus_dvd i v hv) y.2
  exact ⟨(y.1,x),Prod.ext rfl hx⟩

def fourValueCycleSubgroup (i : FourValueRow k) (v : ℕ)
    (hv : ¬ IsWangRow i → v < (rowDigits (fourValueRows k) i).length) :
    AddSubgroup (FourValueLow i) :=
  if h : IsWangRow i then ⊤ else fourValueDigitSubgroup i ⟨v,hv h⟩

def fourValueCycleStep (i : FourValueRow k) (v : ℕ) : ℕ :=
  if IsWangRow i then 1 else rowR (fourValueRows k) i / (rowDigits (fourValueRows k) i).getD v 0

theorem fourValueCycleStep_mem (i : FourValueRow k) (v : ℕ)
    (hv : ¬ IsWangRow i → v < (rowDigits (fourValueRows k) i).length) :
    (fourValueCycleStep i v : FourValueLow i) ∈ fourValueCycleSubgroup i v hv := by
  unfold fourValueCycleStep fourValueCycleSubgroup
  split_ifs with h
  · exact AddSubgroup.mem_top _
  · rw [List.getD_eq_getElem _ _ (hv h)]
    exact fourValueStep_mem i ⟨v,hv h⟩

theorem fourValueCycleStep_spans (i : FourValueRow k) (v : ℕ)
    (hv : ¬ IsWangRow i → v < (rowDigits (fourValueRows k) i).length)
    (u : FourValueLow i) (hu : u ∈ fourValueCycleSubgroup i v hv) :
    ∃ d : ℕ, d • (fourValueCycleStep i v : FourValueLow i) = u := by
  unfold fourValueCycleSubgroup at hu
  unfold fourValueCycleStep
  by_cases h : IsWangRow i
  · rw [if_pos h]
    exact ⟨u.val,by rw [Nat.cast_one,nsmul_eq_mul,mul_one,ZMod.natCast_zmod_val]⟩
  · rw [if_neg h,List.getD_eq_getElem _ _ (hv h)]
    exact fourValueStep_spans i ⟨v,hv h⟩ u (by simpa only [dif_neg h] using hu)

variable
  (hw : ∀ j, IsWangRow (c j) → lab j < 4)
  (hf : ∀ j, ¬ IsWangRow (c j) → lab j < (rowDigits (fourValueRows k) (c j)).length)

theorem fourValueCycle_iff (o : FourValueOutputGraph k)
    (hd : HasFourValueDependence k (tailSlopes k) o) :
    (∀ F ∈ fourValueCycle k (fourValueAssignments c lab),
      Tiles (F.toFinset.image (decodePoint (fourValueLayout k)))
        (Set.range (SharedCoordinates.point (fourValueLayout k) o))) ↔
    ∀ x, ∃ j, ¬ DigitActive (fun d =>
      fourValueCycleRead (c j) (lab j) (hw j) (fourValuePrivateAt o x (c j) d))
        (fourValueCycleSubgroup (c j) (lab j) (hf j)) := by
  let L := fourValueLayout k
  let xs := fourValueAssignments c lab
  let a (i : FourValueRow k) := L.firstSize i
  let val (i : FourValueRow k) := if h : ∃ j, c j = i then lab h.choose else 0
  have hv (i : FourValueRow k) : IsWangRow i → val i < 4 := by
    intro hi
    unfold val
    split
    · rename_i h
      exact hw h.choose (h.choose_spec.symm ▸ hi)
    · decide
  let b (i : FourValueRow k) := fourValueCycleModulus i (val i)
  letI (i : FourValueRow k) : NeZero (b i) := ⟨(fourValueCycleModulus_pos i (val i) (hv i)).ne'⟩
  let read (i : FourValueRow k) := fourValueCycleRead i (val i) (hv i)
  let observe : Factor L →+ (∀ i, ZMod (a i) × ZMod (b i)) :=
    AddMonoidHom.pi fun i => (read i).comp (privateUseful L i)
  have hdecode (n : ℕ) (i : FourValueRow k) :
      observe (decode L n) i = ((n : ZMod (a i)),(n : ZMod (b i))) := by
    change read i (privateUseful L i (decode L n)) = _
    rw [privateUseful_decode]
    exact Prod.ext rfl (map_natCast (ZMod.castHom (fourValueCycleModulus_dvd i (val i) (hv i)) (ZMod (b i))) n)
  have hsurj : Function.Surjective (fun v : SharedCoordinates.Ambient L => (baseProjection L v,observe v.2)) := by
    intro y
    choose p hp using fun i => fourValueCycleRead_surjective i (val i) (hv i) (y.2 i)
    let out : SharedCoordinates.Outputs L := ⟨fun _ => 0,fun _ => p,fun _ => 0⟩
    refine ⟨SharedCoordinates.point L out y.1,Prod.ext (baseProjection_point L out y.1) ?_⟩
    exact funext hp
  let pred (i : FourValueRow k) := if h : ∃ j, c j = i then some (c (h.choose-1)) else none
  let sc (i : FourValueRow k) := fourValueCycleStep i (val i)
  have hp (j : ZMod t) : pred (c j) = some (c (j-1)) := by
    unfold pred
    let h : ∃ q, c q = c j := ⟨j,rfl⟩
    rw [dif_pos h,c.injective h.choose_spec]
  have hvj (j : ZMod t) : val (c j) = lab j := by
    unfold val
    let h : ∃ q, c q = c j := ⟨j,rfl⟩
    rw [dif_pos h,c.injective h.choose_spec]
  let U (j : ZMod t) := fourValueCycleSubgroup (c j) (lab j) (hf j)
  let step (j : ZMod t) : U j := ⟨fourValueCycleStep (c j) (lab j),fourValueCycleStep_mem _ _ _⟩
  have hstep (j : ZMod t) : (sc (c j) : FourValueLow (c j)) = step j := by
    simp only [sc,hvj,step]
  let rows := fourValueCycleRows k xs
  have hlen : rows.length = (fourValueRows k).length := by
    simp only [rows,fourValueCycleRows,List.length_map,List.length_range]
  have hrow (i : FourValueRow k) :
      rows.getD i.val (0,0,0,[]) = observedCycleRow L a b pred sc i := by
    rw [List.getD_eq_getElem _ _ (hlen.symm ▸ i.isLt)]
    unfold rows fourValueCycleRows
    simp only [List.getElem_map,List.getElem_range]
    by_cases h : ∃ j, c j = i
    · obtain ⟨j,rfl⟩ := h
      have hj : j.val < xs.length := by simpa [xs,fourValueAssignments] using ZMod.val_lt j
      rw [fourValueAssignments_idx c lab,if_pos hj]
      change (_,_,_,_) = _
      simp only [observedCycleRow,hp,sc,hvj]
      rw [fourValueAssignments_get c lab j]
      have hpr : xs.getD ((j.val+xs.length-1)%xs.length) (0,0) = ((c (j-1)).val,lab (j-1)) := by
        have hval := congrArg ZMod.val (show ((j.val+t-1 : ℕ) : ZMod t) = j-1 by
          rw [Nat.cast_sub (by have := NeZero.pos t; omega),Nat.cast_add,ZMod.natCast_zmod_val,
            ZMod.natCast_self,Nat.cast_one,add_zero])
        simp only [ZMod.val_natCast] at hval
        rw [show xs.length = t by simp [xs,fourValueAssignments],hval]
        exact fourValueAssignments_get c lab (j-1)
      rw [hpr]
      simp only [b,hvj,fourValueCycleModulus,fourValueCycleStep,IsWangRow]
      rfl
    · have ha : xs.length ≤ (xs.map Prod.fst).idxOf i.val :=
        fourValueAssignments_absent c lab i (by simpa only [not_exists] using h)
      simp only [if_neg (not_lt_of_ge ha),observedCycleRow,pred,dif_neg h]
      rfl
  have hrows : ∀ y, y ∈ rows ↔ ∃ i, observedCycleRow L a b pred sc i = y := by
    intro y
    rw [List.mem_iff_getElem]
    constructor
    · rintro ⟨i,hi,rfl⟩
      let q : FourValueRow k := ⟨i,hlen ▸ hi⟩
      exact ⟨q,(hrow q).symm.trans (List.getD_eq_getElem _ _ hi)⟩
    · rintro ⟨i,rfl⟩
      have h : i.val < rows.length := hlen.symm ▸ i.isLt
      exact ⟨i.val,h,(List.getD_eq_getElem _ _ h).symm.trans (hrow i)⟩
  have hnon : xs.length ≠ 0 := by simpa [xs,fourValueAssignments] using NeZero.ne t
  change (∀ F ∈ fourValueCycle k xs, _) ↔ _
  simp only [fourValueCycle,hnon,ite_false,List.mem_singleton,forall_eq]
  rw [← fourValueLayout_order k]
  let g (x : Plane) (i : FourValueRow k) (d : FourValueLow i) := read i (fourValuePrivateAt o x i d)
  have hg (x : Plane) (u : ∀ i, SharedCoordinates.Low L i) (i : FourValueRow k) :
      observe (SharedCoordinates.point L o (x,u)).2 i = g x i (u i) :=
    congrArg (read i) (hd.privateAt_eq (x,u) i)
  rw [tiles_observed_cycle_exclusion_iff L a b observe hdecode (fourValueLayoutCRT k) c U step
    (fun j => fourValueCycleStep_spans _ _ _) pred sc hp
    (fun i hi => by simp [pred,not_exists.mpr hi]) hstep rows hrows hsurj o g hg]
  simp only [g,read]
  refine forall_congr' fun x => exists_congr fun j => not_congr ?_
  have he (v u : ℕ) (e : v = u) (hv : IsWangRow (c j) → v < 4)
      (hu : IsWangRow (c j) → u < 4) :
      DigitActive (fun d => fourValueCycleRead (c j) v hv (fourValuePrivateAt o x (c j) d))
        (U j) ↔
      DigitActive (fun d => fourValueCycleRead (c j) u hu (fourValuePrivateAt o x (c j) d))
        (U j) := by subst u; rfl
  exact he _ _ (hvj j) _ _

end
end TranslationTiling.FiniteCompiler.Packed
