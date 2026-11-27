import TranslationTiling.FiniteCompiler.Effective.SlotLayout
import TranslationTiling.FiniteCompiler.Effective.SlotPrimeMatching
import TranslationTiling.FiniteCompiler.Effective.SlotSmallPrimeCertificates
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

private def twoDigitLows : List ℕ := [5557,9949,4229,5647]

private def twoDigitMarkers : List ℕ :=
  [691,751,787,757,1523,1879,887,1051,1093,677,823,857]

def rankedLowAt (k m i : ℕ) : ℕ :=
  if k = 1 ∧ m = 1 then [5557,5647].getD i 0 else
  if k = 2 ∧ m = 1 then twoDigitLows.getD i 0 else
  if 24 ≤ m then matchedPrimeAt k m i 3 else
    slotPrimeAt (fallbackCap m*separateMarkerCap k m) (2*k*m) i

def rankedMarkerAt (k m i j : ℕ) : ℕ :=
  if k = 1 ∧ m = 1 then [691,751,787,677,823,857].getD (j+3*i) 0 else
  if k = 2 ∧ m = 1 then twoDigitMarkers.getD (j+3*i) 0 else
  if 24 ≤ m then matchedPrimeAt k m i j else
    slotPrimeAt (fallbackCap m) (6*k*m) (j+3*i)

@[fun_prop] theorem rankedLowAt_primrec :
    Primrec (fun z : ℕ × ℕ × ℕ => rankedLowAt z.1 z.2.1 z.2.2) := by
  have hf : Primrec (fun z : ℕ × ℕ × ℕ =>
      ((fallbackCap z.2.1*separateMarkerCap z.1 z.2.1,2*z.1*z.2.1),z.2.2)) := by
    unfold separateMarkerCap fallbackCap
    fun_prop
  have hm : Primrec (fun z : ℕ × ℕ × ℕ => (z.1,z.2.1,z.2.2,(3 : ℕ))) := by fun_prop
  exact Primrec.ite (by fun_prop) ((Primrec.list_getD 0).comp (Primrec.const _) (by fun_prop))
    (Primrec.ite (by fun_prop) ((Primrec.list_getD 0).comp (Primrec.const _) (by fun_prop))
      (Primrec.ite (by fun_prop) (matchedPrimeAt_primrec.comp hm) (slotPrimeAt_primrec.comp hf)))

@[fun_prop] theorem rankedMarkerAt_primrec :
    Primrec (fun z : ℕ × ℕ × ℕ × ℕ => rankedMarkerAt z.1 z.2.1 z.2.2.1 z.2.2.2) := by
  have hf : Primrec (fun z : ℕ × ℕ × ℕ × ℕ =>
      ((fallbackCap z.2.1,6*z.1*z.2.1),z.2.2.2+3*z.2.2.1)) := by unfold fallbackCap; fun_prop
  exact Primrec.ite (by fun_prop) ((Primrec.list_getD 0).comp (Primrec.const _) (by fun_prop))
    (Primrec.ite (by fun_prop) ((Primrec.list_getD 0).comp (Primrec.const _) (by fun_prop))
      (Primrec.ite (by fun_prop) matchedPrimeAt_primrec (slotPrimeAt_primrec.comp hf)))

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

private theorem exists_ranked_separate (k m : ℕ) (hm : ¬ 24 ≤ m)
    (hsmall : ¬ (k = 1 ∧ m = 1)) (hsmall₂ : ¬ (k = 2 ∧ m = 1)) :
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
  let a (i : SlotFallback m) := slotFallbackAt m (fallbackRank m i)
  let b := rankedPrime A (markerRank k m)
  let r := rankedPrime (A*B) (slotRank k m)
  have hia : Function.Injective a := by
    intro i j h
    apply (fallbackRank m).injective
    by_cases hm₁ : m = 1
    · subst m
      exact (by decide +kernel : ∀ i j : Fin 4,
        slotFallbackAt 1 i = slotFallbackAt 1 j → i = j) _ _ h
    · simp only [a,slotFallbackAt,ite_eq_right hm₁] at h
      exact slotPrimeAt_injective _ _ h
  have hib := rankedPrime_injective A (markerRank k m)
  have hir := rankedPrime_injective (A*B) (slotRank k m)

  have hb := rankedPrime_spec A (markerRank k m)
  have hr := rankedPrime_spec (A*B) (slotRank k m)
  have ha' (i : SlotFallback m) : a i ≤ A := (slotFallbackAt_le (fallbackRank m i).isLt).2
  have hb' (i) : b i ≤ B := (hb i).2.2
  have hr' (i) : r i ≤ C := (hr i).2.2
  let p : SlotPrime k m → ℕ
    | .inl (i,none) => r i
    | .inl (i,some j) => b (i,j)
    | .inr i => a i
  have he : p = rankedSlotPrime k m := by
    funext i
    rcases i with ⟨i,_ | j⟩ | i
    · simp [p,r,rankedPrime,rankedSlotPrime,rankedLowAt,hsmall,hsmall₂,hm,A,B]
    · rcases i with ⟨g,d,i⟩
      cases g <;> simp only [p,b,rankedPrime,rankedSlotPrime,rankedMarkerAt,ite_eq_right hsmall,ite_eq_right hsmall₂,ite_eq_right hm,A] <;> rfl
    · rfl
  have primeCoprime (v : ℕ) (hp : v.Prime) (h : N < v) :
      v.Prime ∧ v.Coprime (order (fourValueLayout 0)) :=
    ⟨hp,(coprime_of_primeBound (fourValueOrder_pos 0) slotBasePrimeBound hp h).symm⟩
  have hp (i) : (p i).Prime ∧ (p i).Coprime (order (fourValueLayout 0)) := by
    rcases i with ⟨i,_ | j⟩ | i
    · exact primeCoprime _ (hr i).1 (((hA.trans hAB).trans hBB).trans_lt (hr i).2.1)
    · exact primeCoprime _ (hb _).1 (hA.trans_lt (hb _).2.1)
    · by_cases hm₁ : m = 1
      · subst m
        rw [fourValueLayout_order]
        have h := (by decide +kernel : ∀ i : Fin 4,
          (2 ≤ slotFallbackAt 1 i ∧ (slotFallbackAt 1 i).minFac = slotFallbackAt 1 i) ∧
            (slotFallbackAt 1 i).Coprime baseOrder) (fallbackRank 1 i)
        exact ⟨Nat.prime_def_minFac.mpr h.1,h.2⟩
      · have h := rankedPrime_spec N (fallbackRank m) i
        simpa only [p,a,slotFallbackAt,ite_eq_right hm₁,rankedPrime] using
          primeCoprime _ h.1 h.2.1
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
  refine ⟨⟨p,fun i => (hp i).1,hinj,fun i => (hp i).2,?_⟩,he,?_,?_,?_⟩
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

private def smallBlockCounts (g : Bool) (j : Option (Fin 3)) : ℕ × ℕ :=
  let i := j.elim 0 (fun j => j.val+1)
  (if g then [(22,1),(4,7),(14,3),(6,5)] else [(4,9),(6,1),(5,2),(2,5)]).getD i (0,0)

private theorem rankedSmall_prime (i : SlotPrime 1 1) :
    (rankedSlotPrime 1 1 i).Prime ∧ (rankedSlotPrime 1 1 i).Coprime baseOrder := by
  have h := (by decide +kernel : ∀ i : SlotPrime 1 1,
    let p := rankedSlotPrime 1 1 i
    (2 ≤ p ∧ p.minFac = p) ∧ p.Coprime baseOrder) i
  exact ⟨Nat.prime_def_minFac.mpr h.1,h.2⟩

private theorem rankedSmall_injective :
    Function.Injective (rankedSlotPrime 1 1) := by
  intro i j
  exact (by decide +kernel : ∀ i j : SlotPrime 1 1,
    rankedSlotPrime 1 1 i = rankedSlotPrime 1 1 j → i = j) i j

private theorem rankedSmall_blocks :
    ∀ (i : WangSlot 1 1) (j : Option (Fin 3)),
      let p := rankedSlotPrime 1 1
      let (u,v) := smallBlockCounts i.1 j
      let a := p (.inr (i.1,i.2.2,false))
      let b := j.elim (p (.inr (i.1,i.2.2,true))) (fun j => p (.inl (i,some j)))
      0 < u ∧ 0 < v ∧ p (.inl (i,none)) = u*a+v*b := by decide +kernel

private theorem exists_ranked_small :
    ∃ s : SlotParameters 1 1, s.prime = rankedSlotPrime 1 1 ∧
      (∀ i, s.fallback i ≤ fallbackCap 1) ∧
      (∀ i j, s.marker i j ≤ markerCap 1 1) ∧
      (∀ i, s.low i ≤ lowCap 1 1) := by
  let s : SlotParameters 1 1 := {
    prime := rankedSlotPrime 1 1
    prime_isPrime := fun i => (rankedSmall_prime i).1
    prime_injective := rankedSmall_injective
    coprime_arithmetic := fun i => by
      rw [fourValueLayout_order]
      exact (rankedSmall_prime i).2
    block_budget := fun i j => by
      right
      right
      refine ⟨(smallBlockCounts i.1 j).1,(smallBlockCounts i.1 j).2,?_⟩
      cases j with
      | none => exact rankedSmall_blocks i none
      | some j => exact rankedSmall_blocks i (some j)
  }
  have ha : slotBasePrimeCap ≤ fallbackCap 1 := threshold_le_slotSearchCap slotBasePrimeCap 4
  have hb := ha.trans (fallbackCap_le_markerCap 1 1)
  have hb' : slotBasePrimeCap ≤ separateMarkerCap 1 1 :=
    ha.trans (threshold_le_slotSearchCap (fallbackCap 1) 6)
  have hc : slotBasePrimeCap^2 ≤ lowCap 1 1 := by
    rw [lowCap,ite_eq_right (by decide : ¬24 ≤ (1 : ℕ)),separateLowCap,pow_two]
    exact (Nat.mul_le_mul ha hb').trans
      (threshold_le_slotSearchCap (fallbackCap 1*separateMarkerCap 1 1) 2)
  refine ⟨s,rfl,?_,?_,?_⟩
  · intro i
    apply Nat.le_trans _ ha
    change rankedSlotPrime 1 1 (.inr i) ≤ slotBasePrimeCap
    exact (by decide +kernel : ∀ i : SlotFallback 1, rankedSlotPrime 1 1 (.inr i) ≤ slotBasePrimeCap) i
  · intro i j
    apply Nat.le_trans _ hb
    change rankedSlotPrime 1 1 (.inl (i,some j)) ≤ slotBasePrimeCap
    exact (by decide +kernel : ∀ (i : WangSlot 1 1) (j : Fin 3),
      rankedSlotPrime 1 1 (.inl (i,some j)) ≤ slotBasePrimeCap) i j
  · intro i
    apply Nat.le_trans _ hc
    change rankedSlotPrime 1 1 (.inl (i,none)) ≤ slotBasePrimeCap^2
    exact (by decide +kernel : ∀ i : WangSlot 1 1,
      rankedSlotPrime 1 1 (.inl (i,none)) ≤ slotBasePrimeCap^2) i

private def twoDigitBlockCounts (i : WangSlot 2 1) (j : Option (Fin 3)) : ℕ × ℕ :=
  let rows := ![![(4,9),(6,1),(5,2),(2,5)], ![(11,4),(2,11),(1,6),(3,4)],
    ![(10,3),(3,4),(14,1),(9,2)], ![(22,1),(4,7),(14,3),(6,5)]]
  rows (slotRank 2 1 i) (j.elim 0 Fin.succ)

private def twoDigitPrimes : List ℕ :=
  [5557,691,751,787,9949,757,1523,1879,4229,887,1051,1093,5647,677,823,857,811,257,227,653]

private def twoDigitPrimeIndex : SlotPrime 2 1 → ℕ
  | .inl (i,j) => 4*(slotRank 2 1 i).val+j.elim 0 (fun x => x.val+1)
  | .inr i => 16+(fallbackRank 1 i).val

private theorem twoDigitPrimeIndex_lt (i : SlotPrime 2 1) :
    twoDigitPrimeIndex i < twoDigitPrimes.length := by
  rcases i with ⟨i,_ | j⟩ | i
  · have h := (slotRank 2 1 i).isLt
    change 4*(slotRank 2 1 i).val < 20
    omega
  · have h := (slotRank 2 1 i).isLt
    have hj := j.isLt
    change 4*(slotRank 2 1 i).val + (j.val+1) < 20
    omega
  · have h := (fallbackRank 1 i).isLt
    change 16+(fallbackRank 1 i).val < 20
    omega

private theorem twoDigitPrimeIndex_injective : Function.Injective twoDigitPrimeIndex := by
  rintro (⟨i,_ | j⟩ | i) (⟨i',_ | j'⟩ | i') h
  all_goals
    simp only [twoDigitPrimeIndex,Option.elim] at h
    try have hr : (slotRank 2 1 i).val<4 := (slotRank 2 1 i).isLt
    try have hr' : (slotRank 2 1 i').val<4 := (slotRank 2 1 i').isLt
    try have hj := j.isLt
    try have hj' := j'.isLt
  · have hi := (slotRank 2 1).injective (Fin.ext (by omega) : slotRank 2 1 i = slotRank 2 1 i')
    subst i'; rfl
  · omega
  · omega
  · omega
  · have hi := (slotRank 2 1).injective (Fin.ext (by omega) : slotRank 2 1 i = slotRank 2 1 i')
    have he : j=j' := Fin.ext (by omega)
    subst i'; subst j'; rfl
  · omega
  · omega
  · omega
  · have hi := (fallbackRank 1).injective (Fin.ext (by omega) : fallbackRank 1 i = fallbackRank 1 i')
    subst i'; rfl

private theorem twoDigitPrime_eq (i : SlotPrime 2 1) :
    rankedSlotPrime 2 1 i = twoDigitPrimes.getD (twoDigitPrimeIndex i) 0 := by
  rcases i with ⟨i,_ | j⟩ | i
  · simp only [rankedSlotPrime,rankedLowAt,twoDigitPrimeIndex,Option.elim]
    have h : (slotRank 2 1 i).val<4 := (slotRank 2 1 i).isLt
    generalize (slotRank 2 1 i).val = r at *
    interval_cases r <;> decide
  · simp only [rankedSlotPrime,rankedMarkerAt,twoDigitPrimeIndex,Option.elim]
    have h : (slotRank 2 1 i).val<4 := (slotRank 2 1 i).isLt
    have hj := j.isLt
    generalize (slotRank 2 1 i).val = r at *
    generalize j.val = t at *
    interval_cases r <;> interval_cases t <;> decide
  · simp only [rankedSlotPrime,slotFallbackAt,twoDigitPrimeIndex]
    have h : (fallbackRank 1 i).val<4 := (fallbackRank 1 i).isLt
    generalize (fallbackRank 1 i).val = r at *
    interval_cases r <;> decide

private theorem rankedTwo_prime (i : SlotPrime 2 1) :
    (rankedSlotPrime 2 1 i).Prime ∧ (rankedSlotPrime 2 1 i).Coprime baseOrder := by
  have hp : ∀ p ∈ twoDigitPrimes, p.Prime := by
    unfold twoDigitPrimes
    simp only [List.forall_mem_cons,List.not_mem_nil,IsEmpty.forall_iff,implies_true]
    norm_num
  have hco : twoDigitPrimes.prod.Coprime baseOrder := by decide +kernel
  rw [twoDigitPrime_eq, List.getD_eq_getElem _ _ (twoDigitPrimeIndex_lt i)]
  have h := List.getElem_mem (l := twoDigitPrimes) (twoDigitPrimeIndex_lt i)
  exact ⟨hp _ h,hco.coprime_dvd_left (List.dvd_prod h)⟩

private theorem rankedTwo_injective :
    Function.Injective (rankedSlotPrime 2 1) := by
  intro i j h
  rw [twoDigitPrime_eq i, twoDigitPrime_eq j, List.getD_eq_getElem _ _ (twoDigitPrimeIndex_lt i),
    List.getD_eq_getElem _ _ (twoDigitPrimeIndex_lt j)] at h
  exact twoDigitPrimeIndex_injective ((List.Nodup.getElem_inj_iff (by decide)).mp h)

private theorem rankedTwo_blocks (i : WangSlot 2 1) (j : Option (Fin 3)) :
    let p := rankedSlotPrime 2 1
    let counts := twoDigitBlockCounts i j
    let a := p (.inr (i.1,i.2.2,false))
    let b := match j with
      | none => p (.inr (i.1,i.2.2,true))
      | some j => p (.inl (i,some j))
    0 < counts.1 ∧ 0 < counts.2 ∧ p (.inl (i,none)) = counts.1*a+counts.2*b := by
  rcases i with ⟨g,i,t⟩
  have ht : t=0 := Subsingleton.elim ..
  subst t
  cases g <;> fin_cases i <;> rcases j with _ | j
  all_goals first | decide +kernel | (fin_cases j <;> decide +kernel)

private def twoDigitParameters : SlotParameters 2 1 where
  prime := rankedSlotPrime 2 1
  prime_isPrime := fun i => (rankedTwo_prime i).1
  prime_injective := rankedTwo_injective
  coprime_arithmetic := fun i => by
    rw [fourValueLayout_order]
    exact (rankedTwo_prime i).2
  block_budget := fun i j => Or.inr (Or.inr
    ⟨(twoDigitBlockCounts i j).1,(twoDigitBlockCounts i j).2,rankedTwo_blocks i j⟩)

private theorem getD_zero_le {L : List ℕ} {c : ℕ}
    (h : ∀ x ∈ L, x ≤ c) (i : ℕ) : L.getD i 0 ≤ c := by
  by_cases hi : i<L.length
  · rw [List.getD_eq_getElem _ _ hi]
    exact h _ (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ (by omega : L.length ≤ i)]
    exact Nat.zero_le _

private theorem twoDigitFallback_le (i : SlotFallback 1) : twoDigitParameters.fallback i ≤ fallbackCap 1 := by
  change slotFallbackAt 1 (fallbackRank 1 i).val ≤ fallbackCap 1
  exact (slotFallbackAt_le (m := 1) (fallbackRank 1 i).isLt).2

private theorem twoDigitMarker_le (i : WangSlot 2 1) (j : Fin 3) :
    twoDigitParameters.marker i j ≤ markerCap 2 1 := by
  have hA : fallbackCap 1 = 2208 := slotSearchCap_2048_4
  have hB : markerCap 2 1 = 2624 := by
    rw [markerCap,ite_eq_right (by decide : ¬24≤(1:ℕ)),separateMarkerCap,hA]
    exact slotSearchCap_2208_12
  rw [hB]
  change twoDigitMarkers.getD (j.val+3*(slotRank 2 1 i).val) 0 ≤ 2624
  apply getD_zero_le
  unfold twoDigitMarkers
  simp only [List.forall_mem_cons,List.not_mem_nil,IsEmpty.forall_iff,implies_true]
  decide +kernel

private theorem twoDigitLow_le (i : WangSlot 2 1) :
    twoDigitParameters.low i ≤ lowCap 2 1 := by
  have hA : fallbackCap 1 = 2208 := slotSearchCap_2048_4
  have hB : separateMarkerCap 2 1 = 2624 := by
    rw [separateMarkerCap,hA]
    exact slotSearchCap_2208_12
  have hc : lowCap 2 1 = 5793952 := by
    rw [lowCap,ite_eq_right (by decide : ¬24≤(1:ℕ)),separateLowCap,hA,hB]
    exact slotSearchCap_5793792_4
  rw [hc]
  change twoDigitLows.getD (slotRank 2 1 i).val 0 ≤ 5793952
  apply getD_zero_le
  unfold twoDigitLows
  simp only [List.forall_mem_cons,List.not_mem_nil,IsEmpty.forall_iff,implies_true]
  decide +kernel

private theorem exists_ranked_two :
    ∃ s : SlotParameters 2 1, s.prime = rankedSlotPrime 2 1 ∧
      (∀ i, s.fallback i ≤ fallbackCap 1) ∧
      (∀ i j, s.marker i j ≤ markerCap 2 1) ∧
      (∀ i, s.low i ≤ lowCap 2 1) :=
  ⟨twoDigitParameters,rfl,twoDigitFallback_le,twoDigitMarker_le,twoDigitLow_le⟩

theorem exists_ranked_parameters (k m : ℕ) :
    ∃ s : SlotParameters k m, s.prime = rankedSlotPrime k m ∧
      (∀ i, s.fallback i ≤ fallbackCap m) ∧
      (∀ i j, s.marker i j ≤ markerCap k m) ∧
      (∀ i, s.low i ≤ lowCap k m) := by
  by_cases hsmall : k = 1 ∧ m = 1
  · obtain ⟨rfl,rfl⟩ := hsmall
    exact exists_ranked_small
  by_cases hsmall₂ : k = 2 ∧ m = 1
  · obtain ⟨rfl,rfl⟩ := hsmall₂
    exact exists_ranked_two
  by_cases hm : 24 ≤ m
  · have hm₁ : m ≠ 1 := by omega
    let a := rankedPrime slotBasePrimeCap (fallbackRank m)
    let q (i : WangSlot k m) (j : ℕ) := matchedPrimeAt k m (slotRank k m i) j
    let p : SlotPrime k m → ℕ
      | .inl (i,none) => q i 3
      | .inl (i,some j) => q i j
      | .inr i => a i
    have he : p = rankedSlotPrime k m := by
      funext i
      rcases i with ⟨i,_ | j⟩ | i
      · simp only [p,q,rankedSlotPrime,rankedLowAt,ite_eq_right hsmall,ite_eq_right hsmall₂,ite_eq_left hm]
      · simp only [p,q,rankedSlotPrime,rankedMarkerAt,ite_eq_right hsmall,ite_eq_right hsmall₂,ite_eq_left hm]
      · simp only [p,rankedSlotPrime,slotFallbackAt,ite_eq_right hm₁,a,rankedPrime]
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
        right
        left
        have hh := matchedPrimeAt_congruent (slotRank k m i).isLt j.isLt
        rw [firstFallbackIndex_eq i,slotFallbackAt,ite_eq_right hm₁] at hh
        exact hh
    · exact fun i => (ha i).2.2
    · intro i j
      rw [markerCap,ite_eq_left hm]
      exact (hq i (j.isLt.trans (by decide : 3 < 4))).2.2
    · intro i
      rw [lowCap,ite_eq_left hm]
      exact (hq i (by decide : 3 < 4)).2.2
  · simpa [markerCap,lowCap,hm] using exists_ranked_separate k m hm hsmall hsmall₂

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
