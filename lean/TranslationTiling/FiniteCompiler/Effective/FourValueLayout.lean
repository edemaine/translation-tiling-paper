import TranslationTiling.FiniteCompiler.Effective.FourValueParameters

namespace TranslationTiling.FiniteCompiler.Packed

open Compiler.Size Compiler.Effective Effective SharedCoordinates
open scoped BigOperators

noncomputable section

set_option maxRecDepth 10000
set_option maxHeartbeats 3000000

abbrev FourValueRow (k : ℕ) := Fin (fourValueRows k).length

def fourValueSource {k : ℕ} (i : FourValueRow k) : SharedRowSource k :=
  if h : i.val < 18 then .inl ⟨i.val,h⟩
  else if hj : i.val < 18+2*k then .inr (.inl ⟨i.val-18,by omega⟩)
  else .inr (.inr ⟨i.val-(18+2*k),by
    have hi : i.val < 20+2*k := i.isLt.trans_le (fourValueRows_length k).le
    omega⟩)

private def sourceRowNumber {k : ℕ} : SharedRowSource k → ℕ
  | .inl i => i
  | .inr (.inl j) => 18+j
  | .inr (.inr t) => 18+2*k+t

@[simp] theorem sourceRowNumber_fourValueSource {k : ℕ} (i : FourValueRow k) :
    sourceRowNumber (fourValueSource i) = i.val := by
  unfold fourValueSource
  split_ifs <;> dsimp [sourceRowNumber] <;> omega

theorem fourValueSource_injective (k : ℕ) : Function.Injective (fourValueSource (k := k)) :=
  fun _ _ h => Fin.ext (by simpa using congrArg sourceRowNumber h)

def fourValueSourceData {k : ℕ} : SharedRowSource k → ℕ × ℕ × List ℕ
  | .inl i => sharedArithmeticRow i
  | .inr (.inl j) => fourValueWangRow k j
  | .inr (.inr t) => sharedSeedRows.getD t (0,0,[])

theorem fourValueSource_data {k : ℕ} (i : FourValueRow k) :
    (fourValueRows k).getD i.val (0,0,[]) = fourValueSourceData (fourValueSource i) := by
  unfold fourValueSource
  split_ifs with h hj
  · exact fourValueRows_fixed_at h
  · change _ = fourValueWangRow k (i.val-18)
    have he := fourValueRows_wang_at (by omega : i.val-18 < 2*k)
    rwa [show 18+(i.val-18) = i.val by omega] at he
  · change _ = sharedSeedRows.getD (i.val-(18+2*k)) (0,0,[])
    have he := fourValueRows_seed_at k (i.val-(18+2*k))
    rwa [show 18+2*k+(i.val-(18+2*k)) = i.val by omega] at he

def fourValueFirst {k : ℕ} (src : SharedRowSource k) : ℕ :=
  match src with
  | .inr (.inl _) => 1
  | _ => (fourValueSourceData src).1

theorem fourValueSource_first {k : ℕ} (i : FourValueRow k) :
    sharedObservedA (fourValueRows k) i = fourValueFirst (fourValueSource i) := by
  have hd := congrArg Prod.fst (fourValueSource_data i)
  change rowA (fourValueRows k) i = (fourValueSourceData (fourValueSource i)).1 at hd
  have hlen := fourValueRows_length k
  by_cases hlo : i.val < 18
  · rw [sharedObservedA,ite_eq_right (by omega)]
    simpa only [fourValueSource,dite_eq_left hlo,fourValueFirst] using hd
  · by_cases hhi : i.val < 18+2*k
    · rw [sharedObservedA,ite_eq_left (by omega)]
      simp [fourValueSource,hlo,hhi,fourValueFirst]
    · rw [sharedObservedA,ite_eq_right (by omega)]
      simpa only [fourValueSource,dite_eq_right hlo,dite_eq_right hhi,fourValueFirst] using hd

private theorem wangOutputList_pos {k : ℕ} (i : Fin (2*k)) :
    0 < ((List.range 4).map (fourValueOutput k i)).prod := by
  apply List.prod_pos
  intro p hp
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hp
  exact (fourValueOutput_prime i.isLt (List.mem_range.mp hj)).pos

theorem fourValueModuli_positive {k : ℕ} (i : FourValueRow k) :
    0 < rowR (fourValueRows k) i ∧ 0 < sharedObservedA (fourValueRows k) i ∧
      0 < rowB (fourValueRows k) i := by
  unfold rowR rowDigits rowB
  rw [fourValueSource_first i,fourValueSource_data i]
  generalize fourValueSource i = src
  rcases src with a | (w | t)
  · exact (by decide +kernel : ∀ j : Fin 18,
      0 < (sharedArithmeticRow j).2.2.prod ∧ 0 < (sharedArithmeticRow j).1 ∧
        0 < (sharedArithmeticRow j).2.1) a
  · exact ⟨by simpa [fourValueSourceData,fourValueWangRow] using (fourValueLow_prime w.isLt).pos,
      by change 0 < 1; decide,wangOutputList_pos w⟩
  · exact (by decide +kernel : ∀ j : Fin 2,
      0 < (sharedSeedRows.getD j (0,0,[])).2.2.prod ∧ 0 < (sharedSeedRows.getD j (0,0,[])).1 ∧
        0 < (sharedSeedRows.getD j (0,0,[])).2.1) t

def fourValueLayout (k : ℕ) : SharedCoordinates.Layout (FourValueRow k) where
  lowSize i := rowR (fourValueRows k) i
  firstSize i := sharedObservedA (fourValueRows k) i
  secondSize i := rowB (fourValueRows k) i
  lowSize_pos i := (fourValueModuli_positive i).1

instance (k : ℕ) (i : FourValueRow k) : NeZero ((fourValueLayout k).firstSize i) :=
  ⟨(fourValueModuli_positive i).2.1.ne'⟩

instance (k : ℕ) (i : FourValueRow k) : NeZero ((fourValueLayout k).secondSize i) :=
  ⟨(fourValueModuli_positive i).2.2.ne'⟩

theorem fourValueLayout_order (k : ℕ) : order (fourValueLayout k) = sharedOrder (fourValueRows k) := by
  unfold order sharedOrder
  rw [← Fin.prod_ofFn]
  apply congrArg (fun n => 1225*199*163*n)
  apply congrArg List.prod
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn,rowModulus,fourValueLayout]

theorem fourValueInputOrder_eq (k : ℕ) :
    (guardedModuli (fourValueRows k)).prod = ∏ i, (fourValueLayout k).lowSize i := by
  rw [← Fin.prod_ofFn]
  apply congrArg List.prod
  unfold guardedModuli
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn,fourValueLayout]

theorem fourValueOrder_pos (k : ℕ) : 0 < order (fourValueLayout k) := by
  unfold order
  apply Nat.mul_pos (by decide)
  apply Finset.prod_pos
  intro i _
  obtain ⟨hr,ha,hb⟩ := fourValueModuli_positive i
  exact Nat.mul_pos (Nat.mul_pos (pow_pos hr _) ha) hb

instance (k : ℕ) : NeZero (order (fourValueLayout k)) := ⟨(fourValueOrder_pos k).ne'⟩

theorem fourValueModuli_membership (k r : ℕ) :
    r ∈ guardedModuli (fourValueRows k) ↔ ∃ i : FourValueRow k, (fourValueLayout k).lowSize i = r := by
  simp only [guardedModuli,List.mem_map,List.mem_range,fourValueLayout]
  constructor
  · rintro ⟨i,hi,rfl⟩; exact ⟨⟨i,hi⟩,rfl⟩
  · rintro ⟨i,rfl⟩; exact ⟨i.val,i.isLt,rfl⟩

theorem fourValueOther_membership (k : ℕ) (i : FourValueRow k) (r : ℕ) :
    r ∈ guardedOther (fourValueRows k) i ↔
      ∃ j : FourValueRow k, j ≠ i ∧ (fourValueLayout k).lowSize j = r := by
  simp only [guardedOther,List.mem_map,List.mem_filter,List.mem_range,decide_eq_true_eq,fourValueLayout]
  constructor
  · rintro ⟨j,⟨hj,hne⟩,rfl⟩
    exact ⟨⟨j,hj⟩,fun h => hne (congrArg Fin.val h),rfl⟩
  · rintro ⟨j,hne,rfl⟩
    exact ⟨j.val,⟨j.isLt,fun h => hne (Fin.ext h)⟩,rfl⟩

end
end TranslationTiling.FiniteCompiler.Packed
