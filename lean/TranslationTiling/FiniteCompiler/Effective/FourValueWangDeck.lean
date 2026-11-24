import TranslationTiling.FiniteCompiler.Effective.FourValueShiftCodes
import TranslationTiling.FiniteCompiler.Effective.FourValueDependence

namespace TranslationTiling.FiniteCompiler.Packed

open Compiler Compiler.Effective Effective SharedCoordinates
open scoped Classical

noncomputable section

set_option maxRecDepth 1500
set_option maxHeartbeats 3000000

attribute [local irreducible] wangValueModulus fourValueLow wangRecordOffset fourValueLayout fourValueRows

def wangActivationSource {k : ℕ} (w : WangDigitRow k) (x : FourValueBase k)
    (v : WangActivationIndex w) : FourValueBase k :=
  SharedCoordinates.activationSource (fourValueLayout k) (wangDigitRow w)
    (wangRecordHorizontal w v) ((wangRecordHorizontal w v).1 : ℤ) x

private abbrev activationIndexes {k : ℕ} (w : WangDigitRow k) :=
  (Finset.univ : Finset (WangActivationIndex w)).toList

private def activationRecordList {k : ℕ} (w : WangDigitRow k) :=
  (activationIndexes w).map fun v => (wangRecordHorizontal w v,(wangRecord w v).2)

private theorem activationRecordList_eq {k : ℕ} (w : WangDigitRow k) :
    (recordsOfInputs (wangActivationInputs k w)).toFinset = (activationRecordList w).toFinset := by
  ext f
  simp only [activationRecordList,activationIndexes,List.mem_toFinset,
    fourValueActivationRecords_list_mem,List.mem_map,Finset.mem_toList,Finset.mem_univ,true_and]
  have he (v : WangActivationIndex w) : (wangRecordHorizontal w v,(wangRecord w v).2) =
      wangRecord w v := Prod.ext (fourValueRecord_spec w v).1.symm rfl
  simp only [he]

private theorem congruenceBatchDeck_congr (N r : ℕ) {a b : List (Plane × CongruenceList)}
    (he : a.toFinset = b.toFinset) :
    (congruenceBatchDeck N r a).toFinset = (congruenceBatchDeck N r b).toFinset := by
  ext f
  have h (v : Plane × CongruenceList) : v ∈ a ↔ v ∈ b := by
    rw [← List.mem_toFinset,he,List.mem_toFinset]
  simp only [List.mem_toFinset,congruenceBatchDeck,List.mem_flatMap,h]

private theorem activationDeck_eq {k : ℕ} (w : WangDigitRow k) :
    (fourValueWangActivation k w).toFinset =
      (congruenceBatchDeck (SharedCoordinates.order (fourValueLayout k))
        ((fourValueLayout k).lowSize (wangDigitRow w)) (activationRecordList w)).toFinset := by
  rw [fourValueLayout_order,wangDigitRow_low]
  have hN : (activationDeckArgs k w).1.1 = sharedOrder (fourValueRows k) := rfl
  have hr : (activationDeckArgs k w).1.2 = fourValueLow k w := rfl
  have hrecords : (activationDeckArgs k w).2 = recordsOfInputs (wangActivationInputs k w) := rfl
  unfold fourValueWangActivation
  rw [hN,hr,hrecords]
  exact congruenceBatchDeck_congr _ _ (activationRecordList_eq w)

private theorem horizontal_shift_injective {k : ℕ} (w : WangDigitRow k) :
    Function.Injective (fun v : WangActivationIndex w =>
      (wangRecordHorizontal w v,FourValueShift.shift (m := wangValueModulus w) v.2)) := by
  intro a b h
  have he : (wangRecordOffset w a : ℤ) = (wangRecordOffset w b : ℤ) :=
    congrArg (fun p : Plane × WangShift w => p.1.1) h
  have hh : wangRecordOffset w a = wangRecordOffset w b :=
    Int.ofNat_inj.mp he
  have hs : FourValueShift.shift (m := wangValueModulus w) a.2 =
      FourValueShift.shift (m := wangValueModulus w) b.2 :=
    congrArg (fun p : Plane × WangShift w => p.2) h
  exact @wangRecordOffset_injective k w a b (Prod.ext hh hs)

attribute [local irreducible] wangRecordHorizontal wangRecord wangActivationProjection


theorem fourValueWangActivation_iff {k : ℕ} (w : WangDigitRow k) (o : FourValueOutputGraph k) :
    Tiles ((fourValueWangActivation k w).toFinset.image (decodePoint (fourValueLayout k)))
      (Set.range (SharedCoordinates.point (fourValueLayout k) o)) ↔
      ∀ x, Function.Bijective (fun v =>
        (wangActivationProjection w
          (SharedCoordinates.point (fourValueLayout k) o (wangActivationSource w x v)).2 +
            FourValueShift.shift (m := wangValueModulus w) v.2, o.high (wangActivationSource w x v) (wangDigitRow w))) := by
  let L := fourValueLayout k
  let i := wangDigitRow w
  let ψ := wangActivationProjection w
  let js := activationIndexes w
  let e (v : WangActivationIndex w) : WangShift w := FourValueShift.shift (m := wangValueModulus w) v.2
  have hp (v : WangActivationIndex w) (n : ℕ) :
      Congruences (wangRecord w v).2 n ↔ ψ (SharedCoordinates.decode L n) = e v ∧
        ∀ j ≠ i, (n : SharedCoordinates.Low L j) = 0 :=
    (fourValueRecord_spec w v).2 n
  have hmem (v : WangActivationIndex w) : v ∈ js := Finset.mem_toList.mpr (Finset.mem_univ v)
  have h := tiles_congruenceBatchDeck_iff L (J := WangActivationIndex w) (Y := WangShift w)
    (fourValueLayoutCRT k) i ψ js hmem (wangRecordHorizontal w) e
    (horizontal_shift_injective w) (fun v => (wangRecord w v).2) hp o
    (wangActivationProjection_target w)
  have ht := congrArg (fun F : Finset (Plane × ℕ) =>
    Tiles (F.image (decodePoint L)) (Set.range (SharedCoordinates.point L o))) (activationDeck_eq w)
  exact (iff_of_eq ht).trans h

end
end TranslationTiling.FiniteCompiler.Packed
