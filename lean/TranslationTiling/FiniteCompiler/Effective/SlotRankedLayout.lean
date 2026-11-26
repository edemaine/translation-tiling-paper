import TranslationTiling.FiniteCompiler.Effective.SlotLayout
import TranslationTiling.FiniteCompiler.Effective.SlotPrimeMatching
import TranslationTiling.FiniteCompiler.Effective.SlotKernelGeometry
import Mathlib.Logic.Equiv.Fin.Basic

namespace TranslationTiling.FiniteCompiler.Packed.SlotParameters

open SharedCoordinates Compiler.Size Compiler.Effective FiniteCompiler.Effective
open scoped BigOperators

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

attribute [local irreducible] slotSearchCap slotPrimeAt matchedPrimeAt

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

def rankedLowAt (k m i : ℕ) : ℕ :=
  if 24 ≤ m then matchedPrimeAt k m i 3 else
    slotPrimeAt (fallbackCap m*separateMarkerCap k m) (2*k*m) i

def rankedMarkerAt (k m i j : ℕ) : ℕ :=
  if 24 ≤ m then matchedPrimeAt k m i j else
    slotPrimeAt (fallbackCap m) (6*k*m) (j+3*i)

@[fun_prop] theorem rankedLowAt_primrec :
    Primrec (fun z : ℕ × ℕ × ℕ => rankedLowAt z.1 z.2.1 z.2.2) := by
  have hf : Primrec (fun z : ℕ × ℕ × ℕ =>
      ((fallbackCap z.2.1*separateMarkerCap z.1 z.2.1,2*z.1*z.2.1),z.2.2)) := by
    unfold separateMarkerCap fallbackCap
    fun_prop
  have hm : Primrec (fun z : ℕ × ℕ × ℕ => (z.1,z.2.1,z.2.2,(3 : ℕ))) := by fun_prop
  exact Primrec.ite (by fun_prop) (matchedPrimeAt_primrec.comp hm) (slotPrimeAt_primrec.comp hf)

@[fun_prop] theorem rankedMarkerAt_primrec :
    Primrec (fun z : ℕ × ℕ × ℕ × ℕ => rankedMarkerAt z.1 z.2.1 z.2.2.1 z.2.2.2) := by
  have hf : Primrec (fun z : ℕ × ℕ × ℕ × ℕ =>
      ((fallbackCap z.2.1,6*z.1*z.2.1),z.2.2.2+3*z.2.2.1)) := by unfold fallbackCap; fun_prop
  exact Primrec.ite (by fun_prop) matchedPrimeAt_primrec (slotPrimeAt_primrec.comp hf)

/-- The slot moduli are specified by their numerical ranks. -/
def rankedSlotPrime (k m : ℕ) : SlotPrime k m → ℕ
  | .inl (i,none) => rankedLowAt k m (slotRank k m i)
  | .inl (i,some j) => rankedMarkerAt k m (slotRank k m i) j
  | .inr i => slotFallbackAt m (fallbackRank m i)

private theorem firstFallbackIndex_eq {k m : ℕ} (i : WangSlot k m) :
    slotFirstFallbackIndex k m (slotRank k m i) = fallbackRank m (i.1,i.2.2,false) := by
  rcases i with ⟨g,d,i⟩
  have hdi : i.val + m*d.val < k*m := by
    calc
      _ < m+m*d.val := Nat.add_lt_add_right i.isLt _
      _ = (d.val+1)*m := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ d.isLt
  cases g
  · change 2*((i.val+m*d.val) % m) + (if i.val+m*d.val < k*m then 0 else m*2) =
      0+2*i.val+(m*2)*0
    simp [Nat.add_mod, Nat.mod_eq_of_lt i.isLt,hdi]
  · change 2*((i.val+m*d.val+(k*m)*1) % m) +
      (if i.val+m*d.val+(k*m)*1 < k*m then 0 else m*2) = 0+2*i.val+(m*2)*1
    simp [Nat.add_mod,Nat.mod_eq_of_lt i.isLt,show ¬ i.val+m*d.val+k*m < k*m by omega]

private theorem exists_ranked_separate (k m : ℕ) (hm : ¬ 24 ≤ m) :
    ∃ s : SlotParameters k m, s.prime = rankedSlotPrime k m ∧
      (∀ i, s.fallback i ≤ fallbackCap m) ∧
      (∀ i j, s.marker i j ≤ separateMarkerCap k m) ∧
      (∀ i, s.low i ≤ separateLowCap k m) := by
  let N := slotBasePrimeCap
  let A := fallbackCap m
  let B := separateMarkerCap k m
  let C := slotSearchCap (A*B) (2*k*m)
  have hN : 0 < N := by decide
  have hA : N ≤ A := threshold_le_slotSearchCap ..
  have hAB : A ≤ B := threshold_le_slotSearchCap ..
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
  let p : SlotPrime k m → ℕ
    | .inl (i,none) => r i
    | .inl (i,some j) => b (i,j)
    | .inr i => a i
  have he : p = rankedSlotPrime k m := by
    funext i
    rcases i with ⟨i,_ | j⟩ | i
    · simp [p,r,rankedPrime,rankedSlotPrime,rankedLowAt,hm,A,B]
    · rcases i with ⟨g,d,i⟩
      cases g <;> simp only [p,b,rankedPrime,rankedSlotPrime,rankedMarkerAt,ite_eq_right hm,A] <;> rfl
    · rfl
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
  refine ⟨⟨p,fun i => (hp i).1,hinj,fun i => ?_,?_⟩,he,?_,?_,?_⟩
  · exact (coprime_of_primeBound (fourValueOrder_pos 0) slotBasePrimeBound
      (hp i).1 (hp i).2).symm
  · intro i j
    apply Or.inl
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

theorem exists_ranked_parameters (k m : ℕ) :
    ∃ s : SlotParameters k m, s.prime = rankedSlotPrime k m ∧
      (∀ i, s.fallback i ≤ fallbackCap m) ∧
      (∀ i j, s.marker i j ≤ markerCap k m) ∧
      (∀ i, s.low i ≤ lowCap k m) := by
  by_cases hm : 24 ≤ m
  · let a := rankedPrime slotBasePrimeCap (fallbackRank m)
    let q (i : WangSlot k m) (j : ℕ) := matchedPrimeAt k m (slotRank k m i) j
    let p : SlotPrime k m → ℕ
      | .inl (i,none) => q i 3
      | .inl (i,some j) => q i j
      | .inr i => a i
    have he : p = rankedSlotPrime k m := by
      funext i
      rcases i with ⟨i,_ | j⟩ | i <;>
        simp [p,q,rankedSlotPrime,rankedLowAt,rankedMarkerAt,hm,a,rankedPrime,slotFallbackAt]
    have ha := rankedPrime_spec slotBasePrimeCap (fallbackRank m)
    have hia := rankedPrime_injective slotBasePrimeCap (fallbackRank m)
    have hA : slotBasePrimeCap ≤ fallbackCap m := threshold_le_slotSearchCap ..
    have hAA : fallbackCap m ≤ (fallbackCap m)^2 := by
      rw [pow_two]
      exact Nat.le_mul_of_pos_right _ (fallbackCap_pos m)
    have hq (i : WangSlot k m) {j : ℕ} (hj : j < 4) :=
      matchedPrimeAt_spec (slotRank k m i).isLt hj
    have hp (i : SlotPrime k m) : (p i).Prime ∧ slotBasePrimeCap < p i := by
      rcases i with ⟨i,_ | j⟩ | i
      · exact ⟨(hq i (by decide : 3 < 4)).1,(hA.trans hAA).trans_lt (hq i (by decide : 3 < 4)).2.1⟩
      · exact ⟨(hq i (j.isLt.trans (by decide : 3 < 4))).1,(hA.trans hAA).trans_lt
          (hq i (j.isLt.trans (by decide : 3 < 4))).2.1⟩
      · exact ⟨(ha i).1,(ha i).2.1⟩
    have hinjQ {i i' : WangSlot k m} {j j' : ℕ} (hj : j < 4) (hj' : j' < 4)
        (h : q i j = q i' j') : i = i' ∧ j = j' := by
      obtain ⟨hi,hj⟩ := matchedPrimeAt_injective (slotRank k m i).isLt
        (slotRank k m i').isLt hj hj' h
      exact ⟨(slotRank k m).injective (Fin.ext hi),hj⟩
    have hsep (a' : SlotFallback m) (i : WangSlot k m) {j : ℕ} (hj : j < 4) :
        a a' < q i j := ((ha a').2.2.trans hAA).trans_lt (hq i hj).2.1
    have hinj : Function.Injective p := by
      intro i j h
      rcases i with ⟨i,_ | i'⟩ | i <;> rcases j with ⟨j,_ | j'⟩ | j
      · have := (hinjQ (by decide : 3 < 4) (by decide : 3 < 4) h).1
        subst j; rfl
      · have hh := (hinjQ (by decide : 3 < 4) (j'.isLt.trans (by decide : 3 < 4)) h).2
        have := j'.isLt
        omega
      · exact (hsep j i (by decide : 3 < 4)).ne h.symm |>.elim
      · have hh := (hinjQ (i'.isLt.trans (by decide : 3 < 4)) (by decide : 3 < 4) h).2
        have := i'.isLt
        omega
      · obtain ⟨rfl,hj⟩ := hinjQ (i'.isLt.trans (by decide : 3 < 4)) (j'.isLt.trans (by decide : 3 < 4)) h
        have : i' = j' := Fin.ext hj
        subst j'; rfl
      · exact (hsep j i (i'.isLt.trans (by decide : 3 < 4))).ne h.symm |>.elim
      · exact (hsep i j (by decide : 3 < 4)).ne h |>.elim
      · exact (hsep i j (j'.isLt.trans (by decide : 3 < 4))).ne h |>.elim
      · exact congrArg Sum.inr (hia h)
    refine ⟨⟨p,fun i => (hp i).1,hinj,fun i => ?_,?_⟩,he,?_,?_,?_⟩
    · exact (coprime_of_primeBound (fourValueOrder_pos 0) slotBasePrimeBound
        (hp i).1 (hp i).2).symm
    · intro i j
      cases j with
      | none =>
        apply Or.inl
        have h : a (i.1,i.2.2,false)*a (i.1,i.2.2,true) ≤ (fallbackCap m)^2 := by
          rw [pow_two]
          exact Nat.mul_le_mul (ha _).2.2 (ha _).2.2
        exact h.trans_lt (hq i (by decide : 3 < 4)).2.1
      | some j =>
        apply Or.inr
        have hh := matchedPrimeAt_congruent (slotRank k m i).isLt j.isLt
        rw [firstFallbackIndex_eq i] at hh
        exact hh
    · exact fun i => (ha i).2.2
    · intro i j
      rw [markerCap,ite_eq_left hm]
      exact (hq i (j.isLt.trans (by decide : 3 < 4))).2.2
    · intro i
      rw [lowCap,ite_eq_left hm]
      exact (hq i (by decide : 3 < 4)).2.2
  · simpa [markerCap,lowCap,hm] using exists_ranked_separate k m hm

private theorem indexedProduct_eq {I : Type*} [Fintype I] {count : ℕ}
    (f : ℕ → ℕ) (rank : I ≃ Fin count) :
    ((List.range count).map f).prod = ∏ i, f (rank i).val := by
  have he : (List.range count).map f = List.ofFn (fun i : Fin count => f i.val) := by
    apply List.ext_getElem
    · simp
    · intro i hi hj
      simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn]
  rw [he,Fin.prod_ofFn]
  exact (Fintype.prod_equiv rank _ _ (fun _ => rfl)).symm

/-- Full cyclic order and low period of the numbered layout. -/
def rankedSlotOrders (k m : ℕ) : ℕ × ℕ :=
  let L := ((List.range (2*k*m)).map (rankedLowAt k m)).prod
  let M := ((List.range (2*k*m)).map (fun i =>
    rankedMarkerAt k m i 0 * rankedMarkerAt k m i 1 * rankedMarkerAt k m i 2)).prod
  let F := ((List.range (4*m)).map (slotFallbackAt m)).prod
  (baseOrder * (L^2*M*F), (guardedModuli (fourValueRows 0)).prod * L)

theorem rankedSlotOrders_zero :
    rankedSlotOrders 0 0 = (sharedOrder (fourValueRows 0), (guardedModuli (fourValueRows 0)).prod) := by
  simp only [rankedSlotOrders,baseOrder,Nat.mul_zero,List.range_zero,
    List.map_nil,List.prod_nil,one_pow,mul_one]

attribute [local fun_prop] product_primrec in
theorem rankedSlotOrders_primrec : Primrec (fun z : ℕ × ℕ => rankedSlotOrders z.1 z.2) := by
  unfold rankedSlotOrders
  have : Primrec (fun _ : ℕ × ℕ => slotBasePrimeCap) := Primrec.const _
  have : Primrec (fun _ : ℕ × ℕ => baseOrder) := Primrec.const _
  have : Primrec (fun _ : ℕ × ℕ => (guardedModuli (fourValueRows 0)).prod) := Primrec.const _
  fun_prop

open scoped BigOperators in
theorem rankedSlotOrders_eq {k m : ℕ} (s : SlotParameters k m)
    (hs : s.prime = rankedSlotPrime k m) :
    rankedSlotOrders k m = (order s.layout,s.period) := by
  have hlo (i : WangSlot k m) : rankedLowAt k m (slotRank k m i) = s.low i := by
    change rankedSlotPrime k m (.inl (i,none)) = s.prime (.inl (i,none))
    rw [hs]
  have hmark (i : WangSlot k m) (j : Fin 3) : rankedMarkerAt k m (slotRank k m i) j = s.marker i j := by
    change rankedSlotPrime k m (.inl (i,some j)) = s.prime (.inl (i,some j))
    rw [hs]
  have hfall (i : SlotFallback m) : slotFallbackAt m (fallbackRank m i) = s.fallback i := by
    change rankedSlotPrime k m (.inr i) = s.prime (.inr i)
    rw [hs]
  have hm : (∏ i : WangSlot k m,
      rankedMarkerAt k m (slotRank k m i) 0 * rankedMarkerAt k m (slotRank k m i) 1 *
        rankedMarkerAt k m (slotRank k m i) 2) = ∏ i : WangSlot k m, ∏ j : Fin 3, s.marker i j := by
    apply Finset.prod_congr rfl
    intro i _
    rw [Fin.prod_univ_three,← hmark,← hmark,← hmark]
    rfl
  simp only [rankedSlotOrders,indexedProduct_eq _ (slotRank k m),
    indexedProduct_eq _ (fallbackRank m),hlo,hm,hfall]
  apply Prod.ext
  · rw [show baseOrder = order (fourValueLayout 0) from (fourValueLayout_order 0).symm]
    rw [s.order_split, Fintype.prod_sum_type]
    simp only [rowModulus,layout,mul_one,one_pow,one_mul]
    rw [Finset.prod_mul_distrib,Finset.prod_pow]
  · rw [fourValueInputOrder_eq]
    simp only [period,Fintype.prod_sum_type,layout,Finset.prod_const,one_pow,mul_one]

end TranslationTiling.FiniteCompiler.Packed.SlotParameters
