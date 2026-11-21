import TranslationTiling.FiniteCompiler.Effective.SparseCorrect
import TranslationTiling.FiniteCompiler.Effective.FixedPrimitives
import TranslationTiling.FiniteCompiler.FixedCycleTests

namespace TranslationTiling.FiniteCompiler.Effective
open Compiler.Effective
open scoped Classical
noncomputable section
variable [SeedFrame]
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

variable {T : System} [AlphabetFamily T] {E : EncodingParameters T} {t : ℕ} [NeZero t]
  {cs : Slots T → CycleConfiguration} {cycle : ZMod t ↪ Channel T}
  {labels : ∀ j, Label T (cycle j)}

theorem fixedRows_correct_of_rows (others : ZMod t → List ℕ)
    (hon : ∀ j, cs (channelEquiv T (cycle j)) =
      (E.r (cycle j),others j,E.a (cycle (j-1)),E.b (cycle (j-1)),true))
    (hoff : ∀ i, (∀ j, cycle j ≠ i) →
      (cs (channelEquiv T i)).1 = E.r i ∧ (cs (channelEquiv T i)).2.2.2.2 = false) (qs : List ℕ)
    (hqs : ∀ j, qs.getD ((channelEquiv T) (cycle j)).val 0=E.digitPrime (cycle j) (labels j)) (n : ℕ) :
    CycleTest (List.ofFn fun s => fixedRow (cs s) (qs.getD s.val 0)) n ↔
    q0 E (decodeNumericalPoint E ((0,0),n)) =
      (0,cycleShift cycle (fun j => digitSubgroup E (cycle j) (labels j))
        (fixedCycleMaps E cycle labels) (usefulProjection E (decodeNumericalPoint E ((0,0),n)))) := by
  let d := fixedCycleMaps E cycle labels
  have hrow (i : Channel T) : CycleRowTest (fixedRow (cs (channelEquiv T i))
      (qs.getD ((channelEquiv T) i).val 0)) n ↔
      (n : K E i) = cycleShift cycle (fun j => digitSubgroup E (cycle j) (labels j)) d
        (usefulProjection E (decodeNumericalPoint E ((0,0),n))) i := by
    by_cases hi : ∃ j, cycle j=i
    · obtain ⟨j,rfl⟩ := hi
      rw [hon j,hqs j]
      simp only [fixedRow,ite_true,cycleShift_apply]
      change (n % E.r (cycle j) =
        (triggerTable (E.a (cycle (j-1))) (E.b (cycle (j-1)))
          (E.r (cycle j)/E.digitPrime (cycle j) (labels j))).getD
          (rectangularIndex (E.b (cycle (j-1))) (n % E.a (cycle (j-1)))
            (n % E.b (cycle (j-1)))) 0 % E.r (cycle j)) ↔ _
      have he := triggerTable_apply (E.r (cycle j)/E.digitPrime (cycle j) (labels j))
        ((n : ZMod (E.a (cycle (j-1)))),(n : ZMod (E.b (cycle (j-1)))))
      simp only [ZMod.val_natCast] at he
      rw [he]
      change (n % E.r (cycle j) = (if
        ((n : ZMod (E.a (cycle (j-1)))),(n : ZMod (E.b (cycle (j-1)))))=0 then 0
        else E.r (cycle j)/E.digitPrime (cycle j) (labels j)) % E.r (cycle j)) ↔
        (n : K E (cycle j)) = d j
          ((n : ZMod (E.a (cycle (j-1)))),(n : ZMod (E.b (cycle (j-1)))))
      rw [← (ZMod.val_injective (E.r (cycle j))).eq_iff]
      dsimp only [d,fixedCycleMaps]
      split_ifs <;> simp only [digitGenerator,ZeroMemClass.coe_zero,ZMod.val_natCast,ZMod.val_zero,Nat.zero_mod]
    · have hnone : ∀ j, cycle j≠i := by simpa only [not_exists] using hi
      obtain ⟨hr,hf⟩ := hoff i (by simpa only [not_exists] using hi)
      simp only [fixedRow,hf,Bool.false_eq_true,ite_false,hr,cycleRowTest_zero,
        cycleShift_eq_zero (M:=K E) (N:=P E) cycle _ d _ hnone]
      rw [← (ZMod.val_injective (E.r i)).eq_iff]
      simp only [ZMod.val_natCast,ZMod.val_zero]
  have hrows : CycleTest (List.ofFn fun s => fixedRow (cs s) (qs.getD s.val 0)) n ↔
      ∀ i : Channel T, (n : K E i) = cycleShift cycle
        (fun j => digitSubgroup E (cycle j) (labels j)) d
        (usefulProjection E (decodeNumericalPoint E ((0,0),n))) i := by
    simp only [CycleTest,List.forall_mem_ofFn_iff]
    constructor
    · intro h i; exact (hrow i).mp (h (channelEquiv T i))
    · intro h s
      simpa only [Equiv.apply_symm_apply] using (hrow ((channelEquiv T).symm s)).mpr (h _)
  rw [hrows]
  constructor
  · intro h
    refine Prod.ext (by rfl) ?_
    funext i
    change low E i (n : ZMod (E.r i ^ 2)) = _
    rw [CyclicShear.low_natCast]
    exact h i
  · intro h i
    have hi := congrFun (congrArg Prod.snd h) i
    change low E i (n : ZMod (E.r i ^ 2)) = _ at hi
    rw [CyclicShear.low_natCast] at hi
    exact hi

theorem fixedGadgets_correct_of_rows (others : ZMod t → List ℕ)
    (hon : ∀ j, cs (channelEquiv T (cycle j)) =
      (E.r (cycle j),others j,E.a (cycle (j-1)),E.b (cycle (j-1)),true))
    (hoff : ∀ i, (∀ j, cycle j ≠ i) →
      (cs (channelEquiv T i)).1 = E.r i ∧ (cs (channelEquiv T i)).2.2.2.2 = false) (qs : List ℕ)
    (hqs : ∀ j, qs.getD ((channelEquiv T) (cycle j)).val 0=E.digitPrime (cycle j) (labels j)) :
    ((fixedGadgets E.cyclicOrder (List.ofFn cs) qs).map
      (fun xs => xs.toFinset.image (decodeNumericalPoint E))).toFinset =
      fixedCycleTiles E cycle labels := by
  rw [fixedGadgets,fixedRows_ofFn]
  simp only [List.map_singleton,List.toFinset_cons,List.toFinset_nil,Finset.insert_empty,fixedCycleTiles]
  congr 1
  exact cycleCodes_correct E _ _ (fixedRows_correct_of_rows others hon hoff qs hqs)

theorem fixedGadgets_correct (hs : SparseConfigMatches E cs cycle labels) (qs : List ℕ)
    (hqs : ∀ j, qs.getD ((channelEquiv T) (cycle j)).val 0=E.digitPrime (cycle j) (labels j)) :
    ((fixedGadgets E.cyclicOrder (List.ofFn cs) qs).map
      (fun xs => xs.toFinset.image (decodeNumericalPoint E))).toFinset =
      fixedCycleTiles E cycle labels :=
  fixedGadgets_correct_of_rows hs.other hs.on hs.off qs hqs

end
end TranslationTiling.FiniteCompiler.Effective
