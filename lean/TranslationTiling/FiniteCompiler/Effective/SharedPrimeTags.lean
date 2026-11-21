import TranslationTiling.FiniteCompiler.Effective.SharedParameterData

namespace TranslationTiling.FiniteCompiler.Packed

open Compiler.Size Compiler.Effective Effective

/-- Each prime in the cyclic group is selected once. The Wang slope
primes are selected in the fixed part, independently of the trit count. -/
abbrev SharedPrimeTag (k : ℕ) :=
  Fin sharedReservedPrimes.length ⊕ (Fin (2*k) ⊕ Fin (6*k))

def sharedPrimeAt (k : ℕ) : SharedPrimeTag k → ℕ
  | .inl i => sharedReservedPrimes.getD i.val 0
  | .inr (.inl i) => (sharedUsefulPool k).getD i.val 0
  | .inr (.inr i) => (sharedDigitPool k).getD i.val 0

private theorem fixedPrimes_bounded :
    ∀ p ∈ sharedReservedPrimes, p.Prime ∧ p ≤ 1619 := by decide +kernel

private theorem sharedUsefulPool_nodup (k : ℕ) : (sharedUsefulPool k).Nodup :=
  List.nodup_range.filter _

private theorem sharedDigitPool_nodup (k : ℕ) : (sharedDigitPool k).Nodup :=
  List.nodup_range.filter _

private theorem pool_index_injective {ps : List ℕ} {i j : ℕ} (h : ps.Nodup)
    (hi : i < ps.length) (hj : j < ps.length) (he : ps.getD i 0 = ps.getD j 0) :
    i = j := by
  rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj] at he
  exact h.getElem_inj_iff.mp he

private theorem usefulPrime_properties {k : ℕ} (i : Fin (2*k)) :
    let p := (sharedUsefulPool k).getD i.val 0
    p.Prime ∧ p ∉ sharedReservedPrimes ∧ p ≤ guardedPrimeCap (2*k+136) :=
  sharedUsefulPool_facts
    (getD_mem_of_lt _ _ _ (i.isLt.trans_le (sharedUsefulPool_length k)))

private theorem digitPrime_properties {k : ℕ} (i : Fin (6*k)) :
    let p := (sharedDigitPool k).getD i.val 0
    p.Prime ∧ 200*guardedPrimeCap (2*k+136) < p ∧ p ≤ 1600*guardedPrimeCap (2*k+136) :=
  sharedDigitPool_facts
    (getD_mem_of_lt _ _ _ (i.isLt.trans_le (sharedDigitPool_length k)))

theorem sharedPrimeAt_prime (k : ℕ) (i : SharedPrimeTag k) : (sharedPrimeAt k i).Prime := by
  rcases i with i | (i | i)
  · exact (fixedPrimes_bounded _ (getD_mem_of_lt sharedReservedPrimes i.val 0 i.isLt)).1
  · exact (usefulPrime_properties i).1
  · exact (digitPrime_properties i).1

private theorem digitThreshold_large (k : ℕ) :
    1619 < 200*guardedPrimeCap (2*k+136) := by
  have h : 4*(2*k+136) ≤ guardedPrimeCap (2*k+136) := by
    unfold guardedPrimeCap
    exact Nat.le_mul_of_pos_right _ (by omega)
  omega

private theorem fixed_ne_useful {k : ℕ} (i : Fin sharedReservedPrimes.length) (j : Fin (2*k)) :
    sharedReservedPrimes.getD i.val 0 ≠ (sharedUsefulPool k).getD j.val 0 := by
  intro he
  apply (usefulPrime_properties j).2.1
  rw [← he]
  exact getD_mem_of_lt _ _ _ i.isLt

private theorem fixed_ne_digit {k : ℕ} (i : Fin sharedReservedPrimes.length) (j : Fin (6*k)) :
    sharedReservedPrimes.getD i.val 0 ≠ (sharedDigitPool k).getD j.val 0 := by
  have hlo := (digitPrime_properties j).2.1
  have hhi := (fixedPrimes_bounded _ (getD_mem_of_lt sharedReservedPrimes i.val 0 i.isLt)).2
  have h := digitThreshold_large k
  omega

private theorem useful_ne_digit {k : ℕ} (i : Fin (2*k)) (j : Fin (6*k)) :
    (sharedUsefulPool k).getD i.val 0 ≠ (sharedDigitPool k).getD j.val 0 := by
  have hlo := (digitPrime_properties j).2.1
  have hhi := (usefulPrime_properties i).2.2
  omega

theorem sharedPrimeAt_injective (k : ℕ) : Function.Injective (sharedPrimeAt k) := by
  intro i j he
  rcases i with i | (i | i) <;> rcases j with j | (j | j)
  all_goals simp only [sharedPrimeAt] at he
  · exact congrArg Sum.inl (Fin.ext (pool_index_injective sharedReservedPrimes_nodup i.isLt j.isLt he))
  · exact (fixed_ne_useful i j he).elim
  · exact (fixed_ne_digit i j he).elim
  · exact (fixed_ne_useful j i he.symm).elim
  · apply congrArg (Sum.inr ∘ Sum.inl)
    exact Fin.ext (pool_index_injective (sharedUsefulPool_nodup k)
      (i.isLt.trans_le (sharedUsefulPool_length k)) (j.isLt.trans_le (sharedUsefulPool_length k)) he)
  · exact (useful_ne_digit i j he).elim
  · exact (fixed_ne_digit j i he.symm).elim
  · exact (useful_ne_digit j i he.symm).elim
  · apply congrArg (Sum.inr ∘ Sum.inr)
    exact Fin.ext (pool_index_injective (sharedDigitPool_nodup k)
      (i.isLt.trans_le (sharedDigitPool_length k)) (j.isLt.trans_le (sharedDigitPool_length k)) he)

theorem sharedPrimeAt_le (k : ℕ) (i : SharedPrimeTag k) :
    sharedPrimeAt k i ≤ 1600*guardedPrimeCap (2*k+136) := by
  rcases i with i | (i | i)
  · have hi := (fixedPrimes_bounded _ (getD_mem_of_lt sharedReservedPrimes i.val 0 i.isLt)).2
    change sharedReservedPrimes.getD i.val 0 ≤ _
    have h := digitThreshold_large k
    omega
  · have hi := (usefulPrime_properties i).2.2
    change (sharedUsefulPool k).getD i.val 0 ≤ _
    omega
  · exact (digitPrime_properties i).2.2

private def wangDigitTag {k : ℕ} (i : Fin (2*k)) (j : Fin 3) : SharedPrimeTag k :=
  .inr (.inr ⟨3*i.val+j.val,by have := i.isLt; have := j.isLt; omega⟩)

private theorem wangDigitTag_inj {k : ℕ} {i i' : Fin (2*k)} {j j' : Fin 3}
    (h : wangDigitTag i j = wangDigitTag i' j') : i = i' ∧ j = j' := by
  have he := congrArg Fin.val (Sum.inr.inj (Sum.inr.inj h))
  change 3*i.val+j.val = 3*i'.val+j'.val at he
  have hj := j.isLt
  have hj' := j'.isLt
  exact ⟨Fin.ext (by omega),Fin.ext (by omega)⟩

private def wangRowTags {k : ℕ} (i : Fin (2*k)) : List (SharedPrimeTag k) :=
  .inr (.inl i) :: (List.finRange 3).map (wangDigitTag i)

/-- The useful and digit primes in a Wang row each have an individual tag. -/
def wangPrivatePrimes {k : ℕ} (i : Fin (2*k)) : List ℕ :=
  (sharedWangRow k i).2.1 :: (sharedWangRow k i).2.2

theorem wangRowTags_map {k : ℕ} (i : Fin (2*k)) :
    (wangRowTags i).map (sharedPrimeAt k) = wangPrivatePrimes i := by
  apply congrArg₂ List.cons rfl
  change ((List.finRange 3).map (wangDigitTag i)).map (sharedPrimeAt k) =
    (List.range 3).map (fun j => (sharedDigitPool k).getD (3*i.val+j) 0)
  rw [show List.range 3 = (List.finRange 3).map Fin.val by decide]
  simp only [List.map_map]
  rfl

private theorem wangRowTags_nodup {k : ℕ} (i : Fin (2*k)) : (wangRowTags i).Nodup := by
  unfold wangRowTags
  apply List.nodup_cons.mpr
  constructor
  · intro hi
    obtain ⟨j,_,he⟩ := List.mem_map.mp hi
    unfold wangDigitTag at he
    cases he
  · exact (List.nodup_finRange _).map fun _ _ h => (wangDigitTag_inj h).2

private theorem wangRowTags_disjoint {k : ℕ} {i j : Fin (2*k)} (h : i ≠ j) :
    List.Disjoint (wangRowTags i) (wangRowTags j) := by
  intro tag hi hj
  simp only [wangRowTags,List.mem_cons,List.mem_map] at hi hj
  rcases hi with rfl | ⟨a,_,rfl⟩
  · rcases hj with he | ⟨a,_,ha⟩
    · exact h (Sum.inl.inj (Sum.inr.inj he))
    · unfold wangDigitTag at ha
      cases ha
  · rcases hj with he | ⟨b,_,hb⟩
    · unfold wangDigitTag at he
      cases he
    · exact h (wangDigitTag_inj hb.symm).1

theorem wangPrivatePrimes_pairwise {k : ℕ} {i j : Fin (2*k)} (h : i ≠ j) :
    List.Disjoint (wangPrivatePrimes i) (wangPrivatePrimes j) := by
  rw [← wangRowTags_map i,← wangRowTags_map j]
  intro p hi hj
  obtain ⟨a,ha,ea⟩ := List.mem_map.mp hi
  obtain ⟨b,hb,eb⟩ := List.mem_map.mp hj
  have e := sharedPrimeAt_injective k (ea.trans eb.symm)
  exact wangRowTags_disjoint h ha (e.symm ▸ hb)

theorem wangPrivatePrimes_nodup (k : ℕ) :
    ((List.finRange (2*k)).flatMap wangPrivatePrimes).Nodup := by
  have ht : ((List.finRange (2*k)).flatMap wangRowTags).Nodup := by
    apply List.nodup_flatMap.mpr
    exact ⟨fun i _ => wangRowTags_nodup i,
      (List.nodup_finRange _).imp (fun h => wangRowTags_disjoint h)⟩
  have h := ht.map (sharedPrimeAt_injective k)
  simpa only [List.map_flatMap,Function.comp_apply,wangRowTags_map] using h

theorem wangPrivatePrimes_disjoint (k : ℕ) :
    List.Disjoint sharedReservedPrimes ((List.finRange (2*k)).flatMap wangPrivatePrimes) := by
  intro p hfix hw
  obtain ⟨i,_,hi⟩ := List.mem_flatMap.mp hw
  rw [← wangRowTags_map i] at hi
  obtain ⟨tag,ht,rfl⟩ := List.mem_map.mp hi
  simp only [wangRowTags,List.mem_cons,List.mem_map] at ht
  rcases ht with rfl | ⟨j,_,rfl⟩
  · exact (usefulPrime_properties i).2.1 hfix
  · have hlow := (digitPrime_properties (⟨3*i.val+j.val,by
      have := i.isLt
      have := j.isLt
      omega⟩ : Fin (6*k))).2.1
    change 200*guardedPrimeCap (2*k+136) < (sharedDigitPool k).getD (3*i.val+j.val) 0 at hlow
    change (sharedDigitPool k).getD (3*i.val+j.val) 0 ∈ sharedReservedPrimes at hfix
    have hhigh := (fixedPrimes_bounded _ hfix).2
    have h := digitThreshold_large k
    omega

end TranslationTiling.FiniteCompiler.Packed
