import TranslationTiling.FiniteCompiler.Effective.SlotLayout
import TranslationTiling.FiniteCompiler.Effective.SlotPrimeSelection
import TranslationTiling.FiniteCompiler.Effective.SlotKernelGeometry
import Mathlib.Logic.Equiv.Fin.Basic

namespace TranslationTiling.FiniteCompiler.Packed.SlotParameters

open SharedCoordinates Compiler.Size Compiler.Effective FiniteCompiler.Effective
open scoped BigOperators

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

attribute [local irreducible] slotSearchCap slotPrimeAt

private def slotRank (k m : ℕ) : WangSlot k m ≃ Fin (2*k*m) :=
  ((finTwoEquiv.symm.prodCongr finProdFinEquiv).trans finProdFinEquiv).trans
    (finCongr (Nat.mul_assoc 2 k m).symm)

private def fallbackRank (m : ℕ) : SlotFallback m ≃ Fin (4*m) :=
  ((finTwoEquiv.symm.prodCongr ((Equiv.refl _).prodCongr finTwoEquiv.symm |>.trans
    finProdFinEquiv)).trans finProdFinEquiv).trans (finCongr (by ring))

private def markerRank (k m : ℕ) : WangSlot k m × Fin 3 ≃ Fin (6*k*m) :=
  (((slotRank k m).prodCongr (Equiv.refl _)).trans finProdFinEquiv).trans (finCongr (by ring))

private def rankedPrime {I : Type*} {count : ℕ} (threshold : ℕ) (rank : I ≃ Fin count)
    (i : I) : ℕ := slotPrimeAt threshold count (rank i).val

private theorem rankedPrime_injective {I : Type*} {count : ℕ} (threshold : ℕ)
    (rank : I ≃ Fin count) : Function.Injective (rankedPrime threshold rank) :=
  (slotPrimeAt_injective threshold count).comp rank.injective

private theorem rankedPrime_spec {I : Type*} {count : ℕ} (threshold : ℕ)
    (rank : I ≃ Fin count) (i : I) :
    (rankedPrime threshold rank i).Prime ∧ threshold < rankedPrime threshold rank i ∧
      rankedPrime threshold rank i ≤ slotSearchCap threshold count :=
  slotPrimeAt_spec (rank i).isLt

private def baseOrder : ℕ := sharedOrder (fourValueRows 0)

private def fallbackLimit (m : ℕ) : ℕ := fallbackCap m
private def markerLimit (k m : ℕ) : ℕ := markerCap k m

private theorem fallbackLimit_eq (m : ℕ) : fallbackLimit m = fallbackCap m := by
  rfl

private theorem markerLimit_eq (k m : ℕ) : markerLimit k m = markerCap k m := by
  rfl

/-- Sorted bounded prime pools specify all slot moduli without finite choice. -/
def rankedSlotPrime (k m : ℕ) : SlotPrime k m → ℕ
  | .inl (i,none) => rankedPrime (fallbackLimit m*markerLimit k m) (slotRank k m) i
  | .inl (i,some j) => rankedPrime (fallbackLimit m) (markerRank k m) (i,j)
  | .inr i => rankedPrime slotBasePrimeCap (fallbackRank m) i

theorem exists_ranked_parameters (k m : ℕ) :
    ∃ s : SlotParameters k m, s.prime = rankedSlotPrime k m ∧
      (∀ i, s.fallback i ≤ fallbackCap m) ∧
      (∀ i j, s.marker i j ≤ markerCap k m) ∧
      (∀ i, s.low i ≤ lowCap k m) := by
  let N := slotBasePrimeCap
  let A := fallbackLimit m
  let B := markerLimit k m
  let C := slotSearchCap (A*B) (2*k*m)
  have hN : 0 < N := by decide
  have hA : N ≤ A := threshold_le_slotSearchCap ..
  have hAB : A ≤ B := fallbackCap_le_markerCap k m
  have hAP : 0 < A := hN.trans_le hA
  have hBB : B ≤ A*B := by
    simpa using Nat.mul_le_mul_right B hAP
  let a := rankedPrime N (fallbackRank m)
  let b := rankedPrime A (markerRank k m)
  let r := rankedPrime (A*B) (slotRank k m)
  have hia := rankedPrime_injective N (fallbackRank m)
  have hib := rankedPrime_injective A (markerRank k m)
  have hir := rankedPrime_injective (A*B) (slotRank k m)
  have ha := rankedPrime_spec N (fallbackRank m)
  have hb := rankedPrime_spec A (markerRank k m)
  have hr := rankedPrime_spec (A*B) (slotRank k m)
  have ha' (i) : a i ≤ A := (ha i).2.2
  have hb' (i) : b i ≤ B := (hb i).2.2
  have hr' (i) : r i ≤ C := (hr i).2.2
  let p := rankedSlotPrime k m
  have hp (i) : (p i).Prime ∧ N < p i := by
    rcases i with ⟨i,_ | j⟩ | i
    · exact ⟨(hr i).1,((hA.trans hAB).trans hBB).trans_lt (hr i).2.1⟩
    · exact ⟨(hb _).1,hA.trans_lt (hb _).2.1⟩
    · exact ⟨(ha i).1,(ha i).2.1⟩
  have hinj : Function.Injective p := by
    intro i j he
    rcases i with ⟨i,_ | i'⟩ | i <;> rcases j with ⟨j,_ | j'⟩ | j
    · exact congrArg (fun w => Sum.inl (w,none)) (hir he)
    · change r i = b (j,j') at he
      exact ((hb' (j,j')).trans hBB |>.not_gt (he ▸ (hr i).2.1)).elim
    · change r i = a j at he
      exact (((ha' j).trans hAB).trans hBB |>.not_gt (he ▸ (hr i).2.1)).elim
    · change b (i,i') = r j at he
      exact ((hb' (i,i')).trans hBB |>.not_gt (he.symm ▸ (hr j).2.1)).elim
    · have h := hib he
      cases h
      rfl
    · change b (i,i') = a j at he
      exact ((ha' j).not_gt (he ▸ (hb (i,i')).2.1)).elim
    · change a i = r j at he
      exact (((ha' i).trans hAB).trans hBB |>.not_gt (he.symm ▸ (hr j).2.1)).elim
    · change a i = b (j,j') at he
      exact ((ha' i).not_gt (he.symm ▸ (hb (j,j')).2.1)).elim
    · exact congrArg Sum.inr (hia he)
  refine ⟨⟨p,fun i => (hp i).1,hinj,fun i => ?_,?_⟩,rfl,?_,?_,?_⟩
  · exact (coprime_of_primeBound (fourValueOrder_pos 0) slotBasePrimeBound
      (hp i).1 (hp i).2).symm
  · intro i j
    change a (i.1,i.2.2,false) *
      (match j with | none => a (i.1,i.2.2,true) | some j => b (i,j)) < r i
    apply lt_of_le_of_lt _ (hr i).2.1
    refine Nat.mul_le_mul (ha' _) ?_
    cases j with
    | none => exact (ha' _).trans hAB
    | some j => exact hb' _
  · intro i
    exact ha' i
  · intro i j
    exact hb' (i,j)
  · intro i
    exact hr' i

private def selectedProduct (threshold count : ℕ) : ℕ :=
  ((List.range count).map (slotPrimeAt threshold count)).prod

@[fun_prop] private theorem selectedProduct_primrec :
    Primrec (fun z : ℕ × ℕ => selectedProduct z.1 z.2) := by
  unfold selectedProduct
  apply product_primrec.comp
  exact Primrec.list_map (Primrec.list_range.comp Primrec.snd)
    (Primrec.to₂ slotPrimeAt_primrec)

private theorem selectedProduct_eq {I : Type*} [Fintype I] {count : ℕ}
    (threshold : ℕ) (rank : I ≃ Fin count) :
    selectedProduct threshold count = ∏ i, rankedPrime threshold rank i := by
  unfold selectedProduct
  have he : (List.range count).map (slotPrimeAt threshold count) =
      List.ofFn (fun i : Fin count => slotPrimeAt threshold count i.val) := by
    apply List.ext_getElem
    · simp
    · intro i hi hj
      simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn]
  rw [he,Fin.prod_ofFn]
  exact (Fintype.prod_equiv rank _ _ (fun _ => rfl)).symm

/-- Full cyclic order and low period of the numbered layout. -/
def rankedSlotOrders (k m : ℕ) : ℕ × ℕ :=
  let A := fallbackLimit m
  let B := markerLimit k m
  let L := selectedProduct (A*B) (2*k*m)
  let M := selectedProduct A (6*k*m)
  let F := selectedProduct slotBasePrimeCap (4*m)
  (baseOrder * (L^2*M*F), (guardedModuli (fourValueRows 0)).prod * L)

theorem rankedSlotOrders_zero :
    rankedSlotOrders 0 0 = (sharedOrder (fourValueRows 0), (guardedModuli (fourValueRows 0)).prod) := by
  simp only [rankedSlotOrders,selectedProduct,baseOrder,Nat.mul_zero,List.range_zero,
    List.map_nil,List.prod_nil,one_pow,mul_one]

theorem rankedSlotOrders_primrec : Primrec (fun z : ℕ × ℕ => rankedSlotOrders z.1 z.2) := by
  unfold rankedSlotOrders markerLimit fallbackLimit markerCap fallbackCap
  have : Primrec (fun _ : ℕ × ℕ => slotBasePrimeCap) := Primrec.const _
  have : Primrec (fun _ : ℕ × ℕ => baseOrder) := Primrec.const _
  have : Primrec (fun _ : ℕ × ℕ => (guardedModuli (fourValueRows 0)).prod) := Primrec.const _
  fun_prop

open scoped BigOperators in
theorem rankedSlotOrders_eq {k m : ℕ} (s : SlotParameters k m)
    (hs : s.prime = rankedSlotPrime k m) :
    rankedSlotOrders k m = (order s.layout,s.period) := by
  have hlo (i : WangSlot k m) :
      rankedPrime (fallbackLimit m*markerLimit k m) (slotRank k m) i = s.low i := by
    change rankedSlotPrime k m (.inl (i,none)) = s.prime (.inl (i,none))
    rw [hs]
  have hmark (i : WangSlot k m × Fin 3) :
      rankedPrime (fallbackLimit m) (markerRank k m) i = s.marker i.1 i.2 := by
    change rankedSlotPrime k m (.inl (i.1,some i.2)) = s.prime (.inl (i.1,some i.2))
    rw [hs]
  have hfall (i : SlotFallback m) :
      rankedPrime slotBasePrimeCap (fallbackRank m) i = s.fallback i := by
    change rankedSlotPrime k m (.inr i) = s.prime (.inr i)
    rw [hs]
  simp only [rankedSlotOrders,selectedProduct_eq _ (slotRank k m),
    selectedProduct_eq _ (markerRank k m),selectedProduct_eq _ (fallbackRank m),
    hlo,hmark,hfall]
  apply Prod.ext
  · rw [show baseOrder = order (fourValueLayout 0) from (fourValueLayout_order 0).symm]
    rw [s.order_split, Fintype.prod_sum_type]
    simp only [rowModulus,layout,mul_one,one_pow,one_mul]
    have hm : (∏ x : WangSlot k m × Fin 3, s.marker x.1 x.2) =
        ∏ i : WangSlot k m, ∏ j : Fin 3, s.marker i j := Fintype.prod_prod_type _
    rw [hm,Finset.prod_mul_distrib,Finset.prod_pow]
  · rw [fourValueInputOrder_eq]
    simp only [period,Fintype.prod_sum_type,layout,Finset.prod_const,one_pow,mul_one]

end TranslationTiling.FiniteCompiler.Packed.SlotParameters
