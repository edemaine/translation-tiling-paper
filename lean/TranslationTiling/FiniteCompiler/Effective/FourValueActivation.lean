import TranslationTiling.FiniteCompiler.Effective.FourValueCRT
import TranslationTiling.FiniteCompiler.Effective.FourValueOffsets
import TranslationTiling.FiniteCompiler.ChannelDigitBlocks
import TranslationTiling.FiniteCompiler.SharedActivationBatch

namespace TranslationTiling.FiniteCompiler.Packed

open Compiler Compiler.Size Compiler.Effective Effective SharedCoordinates
open scoped BigOperators

noncomputable section

set_option maxRecDepth 10000
set_option maxHeartbeats 5000000

abbrev WangDigitRow (k : ℕ) := Fin (2*k)

def wangDigitRow {k : ℕ} (w : WangDigitRow k) : FourValueRow k :=
  ⟨18+w.val,by rw [fourValueRows_length]; have := w.isLt; omega⟩

abbrev FourValueOutputGraph (k : ℕ) := SharedCoordinates.Outputs (fourValueLayout k)

private abbrev J := FourValueShift.Index

def wangSlopeFactor {k : ℕ} (w : WangDigitRow k) : Bool := decide (w.val < k)

def wangValueModulus {k : ℕ} (w : WangDigitRow k) (j : J) : ℕ :=
  if j = 0 then sharedPrime (wangSlopeFactor w) else fourValueOutput k w (j.val-1)

private theorem wangValueModulus_prime {k : ℕ} (w : WangDigitRow k) (j : J) :
    (wangValueModulus w j).Prime := by
  by_cases h : j = 0
  · rw [wangValueModulus,ite_eq_left h]
    unfold sharedPrime
    split <;> decide
  · rw [wangValueModulus,ite_eq_right h]
    have hj := ZMod.val_lt j
    exact fourValueOutput_prime w.isLt (by omega)

instance {k : ℕ} (w : WangDigitRow k) (j : J) : NeZero (wangValueModulus w j) :=
  ⟨(wangValueModulus_prime w j).ne_zero⟩

theorem wangValueModulus_big {k : ℕ} (w : WangDigitRow k) (j : J) :
    1 < wangValueModulus w j := (wangValueModulus_prime w j).one_lt

private theorem index_val_pos (j : J) (h : j ≠ 0) : 0 < j.val :=
  Nat.pos_of_ne_zero (fun he => h ((ZMod.val_injective 5) (he.trans ZMod.val_zero.symm)))

theorem wangValueModulus_pairwise {k : ℕ} (w : WangDigitRow k) :
    Pairwise (fun i j => Nat.Coprime (wangValueModulus w i) (wangValueModulus w j)) := by
  intro i j hij
  apply (Nat.coprime_primes (wangValueModulus_prime w i) (wangValueModulus_prime w j)).mpr
  intro he
  by_cases hi : i = 0
  · subst i
    simp only [wangValueModulus,ite_eq_right (Ne.symm hij),ite_true] at he
    apply fourValueOutput_not_reserved w.isLt (show j.val-1 < 4 by have := ZMod.val_lt j; omega)
    rw [← he]
    unfold sharedPrime
    split <;> simp only [sharedReservedPrimes,List.mem_cons,true_or,or_true]
  · by_cases hj : j = 0
    · subst j
      simp only [wangValueModulus,ite_eq_right hi,ite_true] at he
      apply fourValueOutput_not_reserved w.isLt (show i.val-1 < 4 by have := ZMod.val_lt i; omega)
      rw [he]
      unfold sharedPrime
      split <;> simp only [sharedReservedPrimes,List.mem_cons,true_or,or_true]
    · simp only [wangValueModulus,ite_eq_right hi,ite_eq_right hj] at he
      have hi' := ZMod.val_lt i
      have hj' := ZMod.val_lt j
      obtain ⟨_,heq⟩ := fourValueOutput_inj (i := w) (i' := w)
        (j := ⟨i.val-1,by omega⟩) (j' := ⟨j.val-1,by omega⟩) he
      have h : i.val-1 = j.val-1 := congrArg Fin.val heq
      have := index_val_pos i hi
      have := index_val_pos j hj
      exact hij (ZMod.val_injective 5 (by omega))

theorem wangLow_coprime {k : ℕ} (w : WangDigitRow k) (j : J) :
    Nat.Coprime (fourValueLow k w) (wangValueModulus w j) := by
  apply (Nat.coprime_primes (fourValueLow_prime w.isLt) (wangValueModulus_prime w j)).mpr
  by_cases h : j = 0
  · rw [wangValueModulus,ite_eq_left h]
    intro he
    apply fourValueLow_not_reserved w.isLt
    rw [he]
    unfold sharedPrime
    split <;> simp only [sharedReservedPrimes,List.mem_cons,true_or,or_true]
  · rw [wangValueModulus,ite_eq_right h]
    exact fourValueLow_ne_output w.isLt w.isLt (by have := ZMod.val_lt j; omega)

theorem wangDigitRow_low {k : ℕ} (w : WangDigitRow k) :
    (fourValueLayout k).lowSize (wangDigitRow w) = fourValueLow k w := by
  change rowR (fourValueRows k) (18+w.val) = _
  unfold rowR rowDigits
  rw [fourValueRows_wang_at w.isLt]
  simp [fourValueWangRow]

theorem wangDigitRow_second {k : ℕ} (w : WangDigitRow k) :
    (fourValueLayout k).secondSize (wangDigitRow w) =
      ((List.range 4).map (fourValueOutput k w)).prod := by
  change rowB (fourValueRows k) (18+w.val) = _
  unfold rowB
  rw [fourValueRows_wang_at w.isLt]
  rfl

theorem wangValueModulus_zero {k : ℕ} (w : WangDigitRow k) :
    wangValueModulus w 0 = sharedPrime (wangSlopeFactor w) := by
  simp [wangValueModulus]

theorem wangValueModulus_representation {k : ℕ} (w : WangDigitRow k) (j : J) (hj : j ≠ 0) :
    ∃ u v : ℕ, 0 < u ∧ 0 < v ∧ (fourValueLayout k).lowSize (wangDigitRow w) =
      u * wangValueModulus w 0 + v * wangValueModulus w j := by
  rw [wangDigitRow_low,wangValueModulus_zero,wangValueModulus,ite_eq_right hj]
  have h := fourValueLow_representation w.isLt (show j.val-1 < 4 by have := ZMod.val_lt j; omega)
  simpa [fourValueWangRow,sharedPrime,wangSlopeFactor] using h

/-- The CRT for the four value outputs of a Wang row. -/
def wangValueCRT {k : ℕ} (w : WangDigitRow k) :
    ZMod ((fourValueLayout k).secondSize (wangDigitRow w)) ≃+*
      (∀ j : Fin 4, ZMod (fourValueOutput k w j)) := by
  rw [wangDigitRow_second]
  have hprod : ((List.range 4).map (fourValueOutput k w)).prod =
      ∏ j : Fin 4, fourValueOutput k w j := by
    rw [← Fin.prod_ofFn,show List.range 4 = (List.finRange 4).map Fin.val by decide,
      List.map_map]
    rfl
  rw [hprod]
  apply ZMod.prodEquivPi
  intro i j hij
  exact (Nat.coprime_primes (fourValueOutput_prime w.isLt i.isLt)
    (fourValueOutput_prime w.isLt j.isLt)).mpr (fun h =>
      hij (fourValueOutput_inj (i := w) (i' := w) (j := i) (j' := j) h).2)

def labelIndex (j : Fin 4) : J := (j.val+1 : ℕ)

theorem labelIndex_val (j : Fin 4) : (labelIndex j).val = j.val+1 :=
  ZMod.val_natCast_of_lt (by have := j.isLt; omega)

theorem labelIndex_ne (j : Fin 4) : labelIndex j ≠ 0 := by
  intro he
  have h := congrArg ZMod.val he
  rw [labelIndex_val,ZMod.val_zero] at h
  omega

theorem wangValueModulus_label {k : ℕ} (w : WangDigitRow k) (j : Fin 4) :
    wangValueModulus w (labelIndex j) = fourValueOutput k w j := by
  rw [wangValueModulus,ite_eq_right (labelIndex_ne j),labelIndex_val,Nat.add_sub_cancel]

private def usefulIndex : Option (Fin 4) ≃ J where
  toFun
    | none => 0
    | some j => labelIndex j
  invFun j := if h : j = 0 then none else some ⟨j.val-1,by have := ZMod.val_lt j; omega⟩
  left_inv := by
    intro j
    cases j with
    | none => rfl
    | some j => simp [labelIndex_ne,labelIndex_val]
  right_inv := by
    intro j
    by_cases hj : j = 0
    · subst j; rfl
    · simp only [dite_eq_right hj]
      apply ZMod.val_injective
      rw [labelIndex_val]
      change j.val - 1 + 1 = j.val
      exact Nat.sub_add_cancel (index_val_pos j hj)

/-- All five observed coordinates can be set freely in an activation fibre. -/
def joinWangUseful {k : ℕ} (w : WangDigitRow k) :
    (ZMod (sharedPrime (wangSlopeFactor w)) ×
      ZMod ((fourValueLayout k).secondSize (wangDigitRow w))) ≃+
        FourValueShift.Shift (wangValueModulus w) := by
  let P (j : J) := ZMod (wangValueModulus w j)
  let f := usefulIndex
  let first := (ZMod.ringEquivCongr (wangValueModulus_zero w)).toAddEquiv.symm
  let last (j : Fin 4) := (ZMod.ringEquivCongr (wangValueModulus_label w j)).symm
  let e₀ : (ZMod (sharedPrime (wangSlopeFactor w)) ×
      ZMod ((fourValueLayout k).secondSize (wangDigitRow w))) ≃
        (P (f none) × ∀ j : Fin 4, P (f (some j))) :=
    first.toEquiv.prodCongr
      ((wangValueCRT w).toEquiv.trans (Equiv.piCongrRight fun j => (last j).toEquiv))
  let e := e₀.trans
    (Equiv.piOptionEquivProd (β := fun j => P (f j))).symm |>.trans (Equiv.piCongrLeft P f)
  refine { e with map_add' := ?_ }
  intro a b
  funext j
  obtain ⟨i,rfl⟩ := f.surjective j
  change Equiv.piCongrLeft P f _ (f i) =
    Equiv.piCongrLeft P f _ (f i) + Equiv.piCongrLeft P f _ (f i)
  simp only [Equiv.piCongrLeft_apply_apply]
  cases i with
  | none => exact first.map_add a.1 b.1
  | some j =>
    change last j ((wangValueCRT w) (a.2 + b.2) j) =
      last j ((wangValueCRT w) a.2 j) + last j ((wangValueCRT w) b.2 j)
    rw [map_add,Pi.add_apply,map_add]

theorem joinWangUseful_nonzero {k : ℕ} (w : WangDigitRow k) (j : J) (hj : j ≠ 0)
    (a : ZMod (sharedPrime (wangSlopeFactor w)))
    (b : ZMod ((fourValueLayout k).secondSize (wangDigitRow w))) :
    joinWangUseful w (a,b) j = joinWangUseful w (0,b) j := by
  obtain ⟨i,rfl⟩ := usefulIndex.surjective j
  cases i with
  | none => exact (hj rfl).elim
  | some i =>
    unfold joinWangUseful
    simp only [AddEquiv.coe_mk,Equiv.trans_apply,Equiv.piCongrLeft_apply_apply]
    rfl

def wangActivationProjection {k : ℕ} (w : WangDigitRow k) :
    Factor (fourValueLayout k) →+ FourValueShift.Shift (wangValueModulus w) :=
  (joinWangUseful w).toAddMonoidHom.comp (sharedUseful (fourValueLayout k)
    (wangSlopeFactor w) (wangDigitRow w))

theorem joinWangUseful_natCast {k : ℕ} (w : WangDigitRow k) (n : ℕ) :
    joinWangUseful w ((n : ZMod _),(n : ZMod _)) = fun j => (n : ZMod (wangValueModulus w j)) := by
  funext j
  obtain ⟨i,rfl⟩ := usefulIndex.surjective j
  unfold joinWangUseful
  simp only [AddEquiv.coe_mk,Equiv.trans_apply,Equiv.piCongrLeft_apply_apply]
  cases i with
  | none =>
      change (ZMod.ringEquivCongr (wangValueModulus_zero w)).symm (n : ZMod _) = _
      rw [map_natCast]
      rfl
  | some i =>
      change (ZMod.ringEquivCongr (wangValueModulus_label w i)).symm
        (wangValueCRT w (n : ZMod _) i) = _
      rw [map_natCast,Pi.natCast_apply,map_natCast]
      rfl

theorem labelIndex_inverse (j : J) (hj : j ≠ 0) :
    labelIndex ⟨j.val-1,by have := ZMod.val_lt j; omega⟩ = j := by
  apply ZMod.val_injective
  rw [labelIndex_val]
  exact Nat.sub_add_cancel (index_val_pos j hj)

theorem wangActivationProjection_decode {k : ℕ} (w : WangDigitRow k) (n : ℕ) :
    wangActivationProjection w (decode (fourValueLayout k) n) =
      fun j => (n : ZMod (wangValueModulus w j)) := by
  simp only [wangActivationProjection,AddMonoidHom.comp_apply,AddEquiv.coe_toAddMonoidHom,
    sharedUseful_decode,joinWangUseful_natCast]

theorem wangActivationProjection_target {k : ℕ} (w : WangDigitRow k)
    (x : SharedCoordinates.Base (fourValueLayout k))
    (v : FourValueShift.Shift (wangValueModulus w) × SharedCoordinates.Low (fourValueLayout k) (wangDigitRow w)) :
    ∃ z : SharedCoordinates.Ambient (fourValueLayout k), baseProjection (fourValueLayout k) z = x ∧
      (wangActivationProjection w z.2,highCoordinate (fourValueLayout k) (wangDigitRow w) z) = v := by
  let L := fourValueLayout k
  let i := wangDigitRow w
  let g := wangSlopeFactor w
  let u := (joinWangUseful w).symm v.1
  have setShared (g : Bool) (a : ZMod (sharedPrime g)) :
      ∃ b : Fixed, (sharedLineUseful L g (b,0)).1 = a := by
    cases g
    · exact ⟨((0,0),a),rfl⟩
    · exact ⟨((0,a),0),rfl⟩
  obtain ⟨b,hb⟩ := setShared g u.1
  let o : SharedCoordinates.Outputs L := ⟨fun _ => b,
    fun _ => Function.update 0 i (0,u.2),fun _ => Function.update 0 i v.2⟩
  refine ⟨SharedCoordinates.point L o x,baseProjection_point L o x,Prod.ext ?_ ?_⟩
  · apply (joinWangUseful w).symm.injective
    change (joinWangUseful w).symm
      (joinWangUseful w (sharedUseful L g i (SharedCoordinates.point L o x).2)) = u
    rw [AddEquiv.symm_apply_apply]
    apply Prod.ext
    · have hp (a : Factor L) : (sharedUseful L g i a).1 = (sharedLineUseful L g (a.1,0)).1 := by
        generalize g = g'
        cases g' <;> rfl
      exact (hp _).trans hb
    · have hp (a : Factor L) : (sharedUseful L g i a).2 = (a.2 i).2 := by
        generalize g = g'
        cases g' <;> rfl
      rw [hp]
      change (Function.update (0 : ∀ i, ZMod (L.firstSize i) × ZMod (L.secondSize i)) i
        (0,u.2) i).2 = u.2
      rw [Function.update_self]
  · rw [highCoordinate_point]
    exact Function.update_self _ _ _


/-- A block partition for any selected Wang digit value. -/
def wangBlocks {k : ℕ} (w : WangDigitRow k) (j : J) (hj : j ≠ 0) :
    let h := wangValueModulus_representation w j hj
    LabeledBlocks (SharedCoordinates.Low (fourValueLayout k) (wangDigitRow w))
      (Fin h.choose) (Fin h.choose_spec.choose) (wangValueModulus w 0) (wangValueModulus w j) :=
  let h := wangValueModulus_representation w j hj
  LabeledBlocks.digit _ _ _ _ _ h.choose_spec.choose_spec.2.2

/-- A graph whose observed value outputs factor through the digit input
must activate at least one value when its activation map is bijective. -/
theorem wangActivation_active {k : ℕ} (w : WangDigitRow k)
    (c : SharedCoordinates.Low (fourValueLayout k) (wangDigitRow w) →
      FourValueShift.Shift (wangValueModulus w))
    (high : (SharedCoordinates.Low (fourValueLayout k) (wangDigitRow w) ×
      FourValueShift.Shift (wangValueModulus w)) →
      SharedCoordinates.Low (fourValueLayout k) (wangDigitRow w))
    (hcover : Function.Bijective (fun v => (c v.1 + FourValueShift.shift v.2,high v))) :
    ∃ j ≠ 0, ¬ ∃ t, ∀ d, c d j = t := by
  apply FourValueShift.activation_nonconstant (wangValueModulus_big w) _ c high hcover
  rw [ZMod.card,wangDigitRow_low]
  exact ((wangValueModulus_prime w 0).coprime_iff_not_dvd.mp (wangLow_coprime w 0).symm)

theorem wangBlocks_active {k : ℕ} (w : WangDigitRow k) (j : J) (hj : j ≠ 0) :
    let D := wangBlocks w j hj
    let out : SharedCoordinates.Low (fourValueLayout k) (wangDigitRow w) →
        FourValueShift.Shift (wangValueModulus w) := fun d => match D.decode d with
      | .inl (_,y) => FourValueShift.blockOutput (m := wangValueModulus w) 0 y
      | .inr (_,y) => FourValueShift.blockOutput (m := wangValueModulus w) j y
    ∀ a ≠ 0, (¬ ∃ t, ∀ d, out d a = t) ↔ a = j := by
  dsimp only
  let D := wangBlocks w j hj
  intro a ha
  constructor
  · intro h
    by_contra hne
    apply h
    refine ⟨0,fun d => ?_⟩
    cases he : D.decode d with
    | inl p =>
      have he' : (wangBlocks w j hj).decode d = .inl p := he
      simp only [he',FourValueShift.blockOutput,Function.update_of_ne ha,Pi.zero_apply]
    | inr p =>
      have he' : (wangBlocks w j hj).decode d = .inr p := he
      simp only [he',FourValueShift.blockOutput,Function.update_of_ne hne,Pi.zero_apply]
  · intro he
    subst a
    rintro ⟨t,ht⟩
    let index : Fin (wangValueModulus_representation w j hj).choose_spec.choose :=
      ⟨0,(wangValueModulus_representation w j hj).choose_spec.choose_spec.2.1⟩
    have h₀ := ht (D.decode.symm (.inr (index,0)))
    have h₁ := ht (D.decode.symm (.inr (index,1)))
    have hn : Fact (1 < wangValueModulus w j) := ⟨wangValueModulus_big w j⟩
    apply (zero_ne_one : (0 : ZMod (wangValueModulus w j)) ≠ 1)
    change (match D.decode (D.decode.symm (.inr (index,0))) with
      | .inl (_,y) => FourValueShift.blockOutput (m := wangValueModulus w) 0 y
      | .inr (_,y) => FourValueShift.blockOutput (m := wangValueModulus w) j y) j = t at h₀
    change (match D.decode (D.decode.symm (.inr (index,1))) with
      | .inl (_,y) => FourValueShift.blockOutput (m := wangValueModulus w) 0 y
      | .inr (_,y) => FourValueShift.blockOutput (m := wangValueModulus w) j y) j = t at h₁
    rw [Equiv.apply_symm_apply] at h₀ h₁
    simpa only [FourValueShift.blockOutput,Function.update_self] using h₀.trans h₁.symm


end
end TranslationTiling.FiniteCompiler.Packed
