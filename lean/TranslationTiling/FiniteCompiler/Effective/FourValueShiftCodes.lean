import TranslationTiling.FiniteCompiler.Effective.FourValueNumerical
import TranslationTiling.FiniteCompiler.Effective.FourValueActivation

namespace TranslationTiling.FiniteCompiler.Packed

open Compiler Compiler.Effective SharedCoordinates
open scoped BigOperators

private abbrev J := FourValueShift.Index

set_option maxRecDepth 2000
set_option maxHeartbeats 1200000

private theorem binaryShift_value (u v : Bool) :
    ((if u then 1 else 0) + (if v then 1 else 0)) % 2 =
      (if xor u v then 1 else 0) := by
  cases u <;> cases v <;> decide

noncomputable section

variable {m : J → ℕ} [∀ j, NeZero (m j)]

def numericalShiftList (z : FourValueShift.Shift m) : List ℕ :=
  (List.range 5).map fun j : ℕ => (z (j : J)).val

omit [∀ j, NeZero (m j)] in
private theorem numericalShiftList_at (z : FourValueShift.Shift m) (j : J) :
    (numericalShiftList z).getD j.val 0 = (z j).val := by
  unfold numericalShiftList
  rw [List.getD_eq_getElem _ _ (by simpa using ZMod.val_lt j)]
  rw [List.getElem_map]
  have hidx : (List.range 5)[j.val]'(by simpa using ZMod.val_lt j) = j.val :=
    List.getElem_range _
  rw [hidx,ZMod.natCast_zmod_val]

theorem fourValueModuli_get {k : ℕ} (w : WangDigitRow k) (j : J) :
    (fourValueModuli k w).getD j.val 0 = wangValueModulus w j := by
  by_cases h : j = 0
  · subst j
    change (fourValueModuli k w).getD 0 0 = _
    rw [wangValueModulus_zero]
    unfold fourValueModuli fourValueWangRow wangSlopeFactor sharedPrime
    simp
  · rw [wangValueModulus,ite_eq_right h]
    have hv := ZMod.val_lt j
    have hp : 0 < j.val := Nat.pos_of_ne_zero (fun he => h ((ZMod.val_injective 5)
      (he.trans ZMod.val_zero.symm)))
    have hlt : j.val-1 < 4 := by omega
    have hh : j.val = (j.val-1)+1 := (Nat.sub_add_cancel hp).symm
    unfold fourValueModuli
    rw [hh]
    simp only [List.getD_cons_succ]
    rw [List.getD_eq_getElem _ _ (by simpa using hlt)]
    simp

private theorem fourValueModuli_length (k i : ℕ) : (fourValueModuli k i).length = 5 := by
  simp [fourValueModuli]

theorem numericalShiftList_shift (hm : ∀ j, 1 < m j) (z : FourValueShift.Shift m) :
    numericalShifts (numericalShiftList z) = numericalShiftList (FourValueShift.shift z) := by
  have hn (j : J) : (if (z j).val = 1 then (1 : ZMod (m j)) else 0).val =
      if (z j).val = 1 then 1 else 0 := by
    split <;> simp_all [ZMod.val_one_eq_one_mod,Nat.mod_eq_of_lt (hm j)]
  have hb : (∀ j : J, (z j).val < 2) ↔ ∃ w : FourValueShift.Bits,
      FourValueShift.bitPoint w = z := by
    constructor
    · intro h
      refine ⟨fun j => decide ((z j).val = 1),?_⟩
      funext j
      apply ZMod.val_injective (m j)
      have hj := h j
      simpa only [FourValueShift.bitPoint,decide_eq_true_eq,hn] using
        (show (if (z j).val = 1 then 1 else 0) = (z j).val by split <;> omega)
    · rintro ⟨w,rfl⟩ j
      have hval : (1 : ZMod (m j)).val = 1 := by
        rw [ZMod.val_one_eq_one_mod,Nat.mod_eq_of_lt (hm j)]
      cases hw : w j <;> simp [FourValueShift.bitPoint,hw,hval]
  have htest : ((numericalShiftList z).getD 0 0 < 2 ∧
      (numericalShiftList z).getD 1 0 < 2 ∧ (numericalShiftList z).getD 2 0 < 2 ∧
      (numericalShiftList z).getD 3 0 < 2 ∧ (numericalShiftList z).getD 4 0 < 2) ↔
      ∀ j : J, (z j).val < 2 := by
    have h (j : Fin 5) : (numericalShiftList z).getD j.val 0 = (z (ZMod.finEquiv 5 j)).val :=
      numericalShiftList_at z (ZMod.finEquiv 5 j)
    constructor
    · rintro ⟨h₀,h₁,h₂,h₃,h₄⟩ j
      obtain ⟨i,rfl⟩ := (ZMod.finEquiv 5).surjective j
      rw [← h i]
      fin_cases i <;> assumption
    · intro hh
      exact ⟨h 0 ▸ hh _,h 1 ▸ hh _,h 2 ▸ hh _,h 3 ▸ hh _,h 4 ▸ hh _⟩
  by_cases h : ∃ w : FourValueShift.Bits, FourValueShift.bitPoint w = z
  · rw [numericalShifts,ite_eq_left (htest.mpr (hb.mpr h))]
    obtain ⟨w,rfl⟩ := h
    rw [FourValueShift.shift_bitPoint hm]
    change (List.range 5).map _ = (List.range 5).map (fun j : ℕ =>
      (FourValueShift.bitPoint (m := m) (FourValueShift.changeBits w) (j : J)).val)
    apply List.map_congr_left
    intro j hj
    have hlt : j < 5 := List.mem_range.mp hj
    have hidx : (j : J).val = j := ZMod.val_natCast_of_lt hlt
    have hidx' : ((j : J)+1).val = (j+1)%5 := by
      rw [← Nat.cast_succ,ZMod.val_natCast]
    change (((numericalShiftList (FourValueShift.bitPoint (m := m) w)).getD j 0 +
      (numericalShiftList (FourValueShift.bitPoint (m := m) w)).getD ((j+1)%5) 0) % 2) = _
    rw [← hidx,numericalShiftList_at]
    rw [show ((j : J).val+1)%5 = ((j : J)+1).val by rw [hidx',hidx],
      numericalShiftList_at]
    have bitVal (i : J) (a : FourValueShift.Bits) :
        (FourValueShift.bitPoint (m := m) a i).val = if a i then 1 else 0 := by
      cases hi : a i <;> simp [FourValueShift.bitPoint,hi,ZMod.val_one_eq_one_mod,
        Nat.mod_eq_of_lt (hm i)]
    simp only [bitVal,FourValueShift.changeBits]
    simpa only [ZMod.natCast_zmod_val] using binaryShift_value (w (j : J)) (w ((j : J)+1))
  · rw [numericalShifts,ite_eq_right (fun ht => h (hb.mp (htest.mp ht)))]
    rw [FourValueShift.shift,dite_eq_right h]

theorem fourValueModuli_prod {k : ℕ} (w : WangDigitRow k) :
    (fourValueModuli k w).prod = ∏ j : J, wangValueModulus w j := by
  rw [← (ZMod.finEquiv 5).prod_comp (wangValueModulus w),← Fin.prod_ofFn]
  apply congrArg List.prod
  apply List.ext_getElem
  · simp [fourValueModuli_length]
  · intro j hj hj'
    have hj5 : j < 5 := by simpa [fourValueModuli_length] using hj
    rw [List.getElem_ofFn,← List.getD_eq_getElem _ _ hj]
    exact fourValueModuli_get w (ZMod.finEquiv 5 ⟨j,hj5⟩)

theorem fourValueModuli_residues {k : ℕ} (w : WangDigitRow k) (z : ℕ) :
    (fourValueModuli k w).map (z % ·) =
      numericalShiftList (fun j => (z : ZMod (wangValueModulus w j))) := by
  unfold numericalShiftList
  apply List.ext_getElem
  · simp [fourValueModuli_length]
  · intro j hj hj'
    have hj5 : j < 5 := by simpa [fourValueModuli_length] using hj
    have he : (j : J).val = j := ZMod.val_natCast_of_lt hj5
    simp only [List.getElem_map,List.getElem_range,ZMod.val_natCast]
    rw [← fourValueModuli_get w (j : J),he,List.getD_eq_getElem]


abbrev WangShift {k : ℕ} (w : WangDigitRow k) :=
  FourValueShift.Shift (wangValueModulus w)

abbrev WangActivationIndex {k : ℕ} (w : WangDigitRow k) :=
  ZMod (fourValueLow k w) × WangShift w

instance {k : ℕ} (w : WangDigitRow k) : NeZero (fourValueLow k w) :=
  ⟨(fourValueLow_prime w.isLt).ne_zero⟩

instance {k : ℕ} (w : WangDigitRow k) : NeZero (∏ j : J, wangValueModulus w j) :=
  ⟨(Finset.prod_pos fun j _ => (wangValueModulus_big w j).pos).ne'⟩

instance {k : ℕ} (w : WangDigitRow k) :
    NeZero (fourValueLow k w * (fourValueModuli k w).prod) := by
  rw [fourValueModuli_prod]
  infer_instance

private def recordCRT (r : ℕ) (ms : List ℕ) (f : J → ℕ)
    (hprod : ms.prod = ∏ j, f j) (hr : ∀ j, Nat.Coprime r (f j))
    (hf : Pairwise fun i j => Nat.Coprime (f i) (f j)) :
    ZMod (r*ms.prod) ≃+* (ZMod r × FourValueShift.Shift f) :=
  (ZMod.ringEquivCongr (congrArg (r * ·) hprod)).trans
    ((ZMod.chineseRemainder (Nat.coprime_fintype_prod_right_iff.mpr hr)).trans
      ((RingEquiv.refl (ZMod r)).prodCongr (ZMod.prodEquivPi f hf)))

def wangRecordCRT {k : ℕ} (w : WangDigitRow k) :
    ZMod (fourValueLow k w * (fourValueModuli k w).prod) ≃+*
      (ZMod (fourValueLow k w) × WangShift w) :=
  recordCRT (fourValueLow k w) (fourValueModuli k w) (wangValueModulus w)
    (fourValueModuli_prod w) (wangLow_coprime w) (wangValueModulus_pairwise w)

attribute [local irreducible] wangValueModulus fourValueLow fourValueModuli

def wangRecordOffset {k : ℕ} (w : WangDigitRow k) (v : WangActivationIndex w) : ℕ :=
  @ZMod.val (fourValueLow k w * (fourValueModuli k w).prod)
    ((wangRecordCRT w).symm (v.1,shiftDifference (m := wangValueModulus w) v.2))

private theorem recordOffset_natCast {M r : ℕ} [NeZero M] {m : J → ℕ}
    (e : ZMod M ≃+* (ZMod r × FourValueShift.Shift m))
    (z : ZMod r × FourValueShift.Shift m) :
    (((e.symm z).val : ZMod r),fun j => ((e.symm z).val : ZMod (m j))) = z := by
  have h := map_natCast e (e.symm z).val
  rw [ZMod.natCast_zmod_val,e.apply_symm_apply] at h
  exact h.symm

theorem wangRecordOffset_natCast {k : ℕ} (w : WangDigitRow k) (v : WangActivationIndex w) :
    ((wangRecordOffset w v : ZMod (fourValueLow k w)),
      (fun j : J => (wangRecordOffset w v : ZMod (wangValueModulus w j)))) =
      (v.1,shiftDifference (m := wangValueModulus w) v.2) :=
  recordOffset_natCast (m := wangValueModulus w) (wangRecordCRT w)
    (v.1,shiftDifference (m := wangValueModulus w) v.2)

set_option maxRecDepth 1000 in
theorem wangRecordOffset_injective {k : ℕ} (w : WangDigitRow k) :
    Function.Injective (fun v : WangActivationIndex w =>
      (wangRecordOffset w v,FourValueShift.shift (m := wangValueModulus w) v.2)) := by
  have : NeZero (fourValueLow k w * (fourValueModuli k w).prod) := by
    rw [fourValueModuli_prod]
    exact ⟨(Nat.mul_pos (fourValueLow_prime w.isLt).pos
      (Finset.prod_pos fun j _ => (wangValueModulus_big w j).pos)).ne'⟩
  exact activation_record_injective (m := wangValueModulus w) (wangRecordCRT w).toEquiv


def wangRecordHorizontal {k : ℕ} (w : WangDigitRow k) (v : WangActivationIndex w) :
    Plane :=
  let h := wangRecordOffset w v
  ((h : ℤ), -(if w.val < k then (0 : ℤ) else 2)*(h : ℤ))

def wangRecord {k : ℕ} (w : WangDigitRow k) (v : WangActivationIndex w) :
    Plane × CongruenceList :=
  let e : ZMod (∏ j : J, wangValueModulus w j) ≃+* WangShift w :=
      ZMod.prodEquivPi (wangValueModulus w) (wangValueModulus_pairwise w)
  fourValueRecord (fourValueLow k w) (if w.val < k then 0 else 2)
    (fourValueModuli k w) (Effective.guardedOther (fourValueRows k) (18+w.val))
    v.1.val (e.symm v.2).val

private def wangRecordCongruences {k : ℕ} (w : WangDigitRow k) (v : WangActivationIndex w) :
    CongruenceList :=
  let ms := fourValueModuli k w
  let shifts := numericalShiftList (FourValueShift.shift (m := wangValueModulus w) v.2)
  (List.range 5).map (fun j => (ms.getD j 0,shifts.getD j 0)) ++
    (Effective.guardedOther (fourValueRows k) (18+w.val)).map (·,0)

set_option maxHeartbeats 1600000 in
private theorem wangRecord_eq {k : ℕ} (w : WangDigitRow k) (v : WangActivationIndex w) :
    wangRecord w v = (wangRecordHorizontal w v,wangRecordCongruences w v) := by
  let r := fourValueLow k w
  let ms := fourValueModuli k w
  let M := r*ms.prod
  let other := Effective.guardedOther (fourValueRows k) (18+w.val)
  let s : ℕ := if w.val < k then 0 else 2
  let e : ZMod (∏ j : J, wangValueModulus w j) ≃+* WangShift w :=
      ZMod.prodEquivPi (wangValueModulus w) (wangValueModulus_pairwise w)
  have hprod : ms.prod = ∏ j : J, wangValueModulus w j := fourValueModuli_prod w
  have : NeZero (∏ j : J, wangValueModulus w j) :=
    ⟨(Finset.prod_pos fun j _ => (wangValueModulus_big w j).pos).ne'⟩
  have : NeZero M := by
    change NeZero (r*ms.prod)
    rw [hprod]
    exact ⟨(Nat.mul_pos (fourValueLow_prime w.isLt).pos (NeZero.pos _)).ne'⟩
  let z : ℕ := (e.symm v.2).val
  have hz : (fun j : J => (z : ZMod (wangValueModulus w j))) = v.2 := by
    have h := map_natCast e z
    rw [show (z : ZMod _) = e.symm v.2 from ZMod.natCast_zmod_val _,
      RingEquiv.apply_symm_apply] at h
    exact h.symm
  let y := FourValueShift.shift (m := wangValueModulus w) v.2
  let row := List.range 5
  let shifts := numericalShiftList y
  let cs := (r,v.1.val) :: row.map (fun j => (ms.getD j 0,
    differenceResidue (ms.getD j 0) ((numericalShiftList (m := wangValueModulus w) v.2).getD j 0) (shifts.getD j 0)))
  have hcs (n : ℕ) : Congruences cs n ↔
      wangRecordCRT w (n : ZMod M) = (v.1,shiftDifference (m := wangValueModulus w) v.2) := by
    have hcast : wangRecordCRT w (n : ZMod M) =
        ((n : ZMod r),fun j => (n : ZMod (wangValueModulus w j))) := map_natCast _ _
    rw [hcast]
    have hmods (j : J) : ms.getD j.val 0 = wangValueModulus w j :=
      fourValueModuli_get w j
    have hl : n % r = v.1.val % r ↔ (n : ZMod r) = v.1 := by
      have : NeZero r := ⟨(fourValueLow_prime w.isLt).ne_zero⟩
      rw [Nat.mod_eq_of_lt (ZMod.val_lt v.1),← ZMod.val_natCast]
      exact (ZMod.val_injective r).eq_iff
    have ht (j : J) :
        n % ms.getD j.val 0 = differenceResidue (ms.getD j.val 0)
          ((numericalShiftList (m := wangValueModulus w) v.2).getD j.val 0) (shifts.getD j.val 0) %
          ms.getD j.val 0 ↔ (n : ZMod (wangValueModulus w j)) = shiftDifference (m := wangValueModulus w) v.2 j := by
      rw [hmods,numericalShiftList_at,numericalShiftList_at,differenceResidue_eq,
        ZMod.natCast_zmod_val,ZMod.natCast_zmod_val,Nat.mod_eq_of_lt (ZMod.val_lt _),
        ← ZMod.val_natCast]
      exact (ZMod.val_injective _).eq_iff
    unfold cs Congruences
    rw [List.forall_mem_cons,Prod.ext_iff,hl,funext_iff]
    apply and_congr_right
    intro _
    simp only [List.forall_mem_map,row,List.mem_range]
    constructor
    · intro h j
      exact (ht j).mp (h j.val (ZMod.val_lt j))
    · intro h j hj
      have hval : (j : J).val = j := ZMod.val_natCast_of_lt hj
      simpa only [hval] using (ht (j : J)).mpr (h (j : J))
  have hoff : residueSearch M cs = wangRecordOffset w v :=
    residueSearch_of_equiv (wangRecordCRT w).toEquiv _ cs hcs
  have hrecord : fourValueRecord r s ms other v.1.val z =
      (wangRecordHorizontal w v,(row.map fun j => (ms.getD j 0,shifts.getD j 0)) ++ other.map (·,0)) := by
    unfold fourValueRecord
    have hcoords : ms.map (z % ·) = numericalShiftList (m := wangValueModulus w) v.2 :=
      (fourValueModuli_residues w z).trans
        (congrArg (numericalShiftList (m := wangValueModulus w)) hz)
    rw [hcoords]
    dsimp only
    rw [numericalShiftList_shift (m := wangValueModulus w) (wangValueModulus_big w) v.2,
      show ms.length = 5 from fourValueModuli_length k w]
    change (((residueSearch M cs : ℤ),-(s : ℤ)*(residueSearch M cs : ℤ)),_) = _
    rw [hoff]
    by_cases h : w.val < k <;> simp [wangRecordHorizontal,s,h,shifts,row,y]
  exact hrecord

/-- The numerical record specifies the shift congruences and fixes the other low inputs at zero. -/
theorem fourValueRecord_spec {k : ℕ} (w : WangDigitRow k) (v : WangActivationIndex w) :
    (wangRecord w v).1 = wangRecordHorizontal w v ∧
      ∀ n, Congruences (wangRecord w v).2 n ↔
        wangActivationProjection w (SharedCoordinates.decode (fourValueLayout k) n) =
          FourValueShift.shift (m := wangValueModulus w) v.2 ∧
        ∀ j ≠ wangDigitRow w, (n : SharedCoordinates.Low (fourValueLayout k) j) = 0 := by
  rw [wangRecord_eq]
  refine ⟨rfl,fun n => ?_⟩
  let ms := fourValueModuli k w
  let y := FourValueShift.shift (m := wangValueModulus w) v.2
  let shifts := numericalShiftList y
  change Congruences ((List.range 5).map (fun j => (ms.getD j 0,shifts.getD j 0)) ++
    (Effective.guardedOther (fourValueRows k) (18+w.val)).map (·,0)) n ↔ _
  rw [wangActivationProjection_decode]
  unfold Congruences
  simp only [List.forall_mem_append,List.forall_mem_map,List.mem_range]
  have test (j : J) :
      n % ms.getD j.val 0 = shifts.getD j.val 0 % ms.getD j.val 0 ↔
        (n : ZMod (wangValueModulus w j)) = y j := by
    rw [fourValueModuli_get w,numericalShiftList_at,Nat.mod_eq_of_lt (ZMod.val_lt _),
      ← ZMod.val_natCast]
    exact (ZMod.val_injective _).eq_iff
  constructor
  · rintro ⟨h₁,h₂⟩
    refine ⟨funext (fun j => (test j).mp (h₁ j.val (ZMod.val_lt j))),fun j hj => ?_⟩
    have hh := h₂ _ ((fourValueOther_membership k (wangDigitRow w) _).mpr ⟨j,hj,rfl⟩)
    exact (ZMod.natCast_eq_zero_iff _ _).mpr
      (Nat.dvd_iff_mod_eq_zero.mpr (by simpa only [Nat.zero_mod] using hh))
  · rintro ⟨h₁,h₂⟩
    refine ⟨fun j hj => ?_,fun p hp => ?_⟩
    · have hval : (j : J).val = j := ZMod.val_natCast_of_lt hj
      simpa only [hval] using (test (j : J)).mpr (congrFun h₁ (j : J))
    · obtain ⟨j,hj,rfl⟩ := (fourValueOther_membership k (wangDigitRow w) p).mp hp
      simpa only [Nat.zero_mod] using Nat.dvd_iff_mod_eq_zero.mp
        ((ZMod.natCast_eq_zero_iff _ _).mp (h₂ j hj))


theorem fourValueActivationRecords_toFinset {k : ℕ} (w : WangDigitRow k) :
    (recordsOfInputs (wangActivationInputs k w)).toFinset =
      (Finset.univ : Finset (WangActivationIndex w)).image (wangRecord w) := by
  let e : ZMod (∏ j : J, wangValueModulus w j) ≃+* WangShift w :=
      ZMod.prodEquivPi (wangValueModulus w) (wangValueModulus_pairwise w)
  classical
  ext p
  simp only [recordsOfInputs,wangActivationInputs,fourValueActivationRecords,List.mem_toFinset,
    List.mem_flatMap,List.mem_map,List.mem_range,Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨l,hl,z,hz,rfl⟩
    rw [fourValueModuli_prod w] at hz
    let v : WangActivationIndex w := ((l : ZMod _),e (z : ZMod _))
    refine ⟨v,?_⟩
    change fourValueRecord _ _ _ _ (l : ZMod (fourValueLow k w)).val (e.symm (e (z : ZMod _))).val =
      fourValueRecord _ _ _ _ l z
    rw [RingEquiv.symm_apply_apply,ZMod.val_natCast_of_lt hz,ZMod.val_natCast_of_lt hl]
  · rintro ⟨v,rfl⟩
    refine ⟨v.1.val,ZMod.val_lt _,(e.symm v.2).val,?_,rfl⟩
    rw [fourValueModuli_prod w]
    exact ZMod.val_lt _

theorem fourValueActivationRecords_list_mem {k : ℕ} (w : WangDigitRow k)
    (p : Plane × CongruenceList) :
    p ∈ recordsOfInputs (wangActivationInputs k w) ↔ ∃ v, wangRecord w v = p := by
  classical
  rw [← List.mem_toFinset,fourValueActivationRecords_toFinset]
  simp

theorem wangRecordSlope {k : ℕ} (w : WangDigitRow k) (v : WangActivationIndex w) :
    (wangRecordHorizontal w v).2 =
      -(if w.val < k then (0 : ℤ) else 2)*(wangRecordHorizontal w v).1 := rfl

theorem wangRecordLow {k : ℕ} (w : WangDigitRow k) (v : WangActivationIndex w) :
    ((wangRecordHorizontal w v).1 : ZMod (fourValueLow k w)) = v.1 := by
  simpa only [wangRecordHorizontal,Int.cast_natCast] using
    congrArg Prod.fst (wangRecordOffset_natCast w v)

theorem wangRecordShift {k : ℕ} (w : WangDigitRow k) (v : WangActivationIndex w) (j : J) :
    ((wangRecordHorizontal w v).1 : ZMod (wangValueModulus w j)) =
      v.2 j - FourValueShift.shift (m := wangValueModulus w) v.2 j := by
  simpa only [wangRecordHorizontal,Int.cast_natCast,shiftDifference,Pi.sub_apply] using
    congrFun (congrArg Prod.snd (wangRecordOffset_natCast w v)) j


end
end TranslationTiling.FiniteCompiler.Packed
