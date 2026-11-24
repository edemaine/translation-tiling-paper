import TranslationTiling.FiniteCompiler.Effective.FourValueLayout

namespace TranslationTiling.FiniteCompiler.Packed

open Compiler.Size Effective SharedCoordinates
open scoped BigOperators

noncomputable section
set_option maxRecDepth 10000

private def fixedFactors (row : ℕ × ℕ × List ℕ) : List ℕ :=
  row.1 :: row.2.1 :: row.2.2

private def arithmeticFactors (i : Fin 18) : List ℕ := fixedFactors (sharedArithmeticRow i)
private def seedFactors (t : Fin 2) : List ℕ := fixedFactors (sharedSeedRows.getD t (0,0,[]))

private def outputFactors {k : ℕ} (i : Fin (2*k)) : List ℕ :=
  (List.range 4).map (fourValueOutput k i)

private def wangFactors {k : ℕ} (i : Fin (2*k)) : List ℕ :=
  fourValueLow k i :: outputFactors i

private theorem wangFactors_prime {k : ℕ} (i : Fin (2*k)) :
    ∀ p ∈ wangFactors i, p.Prime := by
  intro p hp
  rcases List.mem_cons.mp hp with he|hp
  · exact he.symm ▸ fourValueLow_prime i.isLt
  · obtain ⟨j,hj,hjval⟩ := List.mem_map.mp hp
    exact hjval ▸ fourValueOutput_prime i.isLt (List.mem_range.mp hj)

private theorem wangFactors_nodup {k : ℕ} (i : Fin (2*k)) : (wangFactors i).Nodup := by
  apply List.nodup_cons.mpr
  constructor
  · intro h
    obtain ⟨j,hj,he⟩ := List.mem_map.mp h
    exact fourValueLow_ne_output i.isLt i.isLt (List.mem_range.mp hj) he.symm
  · unfold outputFactors
    apply List.Nodup.map_on (l := List.range 4) _ List.nodup_range
    intro a ha b hb he
    have h := (fourValueOutput_inj (i := i) (i' := i)
      (j := ⟨a,List.mem_range.mp ha⟩) (j' := ⟨b,List.mem_range.mp hb⟩) he).2
    exact congrArg Fin.val h

private theorem wangFactors_disjoint {k : ℕ} (i j : Fin (2*k)) (hne : i ≠ j) :
    List.Disjoint (wangFactors i) (wangFactors j) := by
  intro p hp hq
  rcases List.mem_cons.mp hp with he|hp <;> rcases List.mem_cons.mp hq with hq|hq
  · exact hne (Fin.ext (fourValueLow_inj i.isLt j.isLt (he.symm.trans hq)))
  · obtain ⟨t,ht,hm⟩ := List.mem_map.mp hq
    exact fourValueLow_ne_output i.isLt j.isLt (List.mem_range.mp ht) (he.symm.trans hm.symm)
  · obtain ⟨t,ht,he⟩ := List.mem_map.mp hp
    exact fourValueLow_ne_output j.isLt i.isLt (List.mem_range.mp ht) (hq.symm.trans he.symm)
  · obtain ⟨a,ha,he⟩ := List.mem_map.mp hp
    obtain ⟨b,hb,hf⟩ := List.mem_map.mp hq
    exact hne (fourValueOutput_inj (i := i) (i' := j)
      (j := ⟨a,List.mem_range.mp ha⟩) (j' := ⟨b,List.mem_range.mp hb⟩) (he.trans hf.symm)).1

private def fourValueFactors {k : ℕ} : SharedRowSource k → List ℕ
  | .inl i => arithmeticFactors i
  | .inr (.inl j) => wangFactors j
  | .inr (.inr t) => seedFactors t

private theorem reserved_arithmetic (i : Fin 18) : ∀ p ∈ arithmeticFactors i, p ∈ sharedReservedPrimes :=
  (by decide +kernel : ∀ i : Fin 18, ∀ p ∈ arithmeticFactors i, p ∈ sharedReservedPrimes) i

private theorem reserved_seed (t : Fin 2) : ∀ p ∈ seedFactors t, p ∈ sharedReservedPrimes :=
  (by decide +kernel : ∀ t : Fin 2, ∀ p ∈ seedFactors t, p ∈ sharedReservedPrimes) t

private theorem fourValueFactors_prime {k : ℕ} (s : SharedRowSource k) :
    ∀ p ∈ fourValueFactors s, p.Prime := by
  rcases s with i | (i | t)
  · exact (by decide +kernel : ∀ i : Fin 18, ∀ p ∈ arithmeticFactors i, p.Prime) i
  · exact wangFactors_prime i
  · exact (by decide +kernel : ∀ t : Fin 2, ∀ p ∈ seedFactors t, p.Prime) t

private theorem fourValueFactors_nodup {k : ℕ} (s : SharedRowSource k) : (fourValueFactors s).Nodup := by
  rcases s with i | (i | t)
  · exact (by decide +kernel : ∀ i : Fin 18, (arithmeticFactors i).Nodup) i
  · exact wangFactors_nodup i
  · exact (by decide +kernel : ∀ t : Fin 2, (seedFactors t).Nodup) t

private theorem wangDisjoint {k : ℕ} (i : Fin (2*k)) :
    List.Disjoint sharedReservedPrimes (wangFactors i) := by
  intro p hp hi
  rcases List.mem_cons.mp hi with he|hi
  · exact fourValueLow_not_reserved i.isLt (he ▸ hp)
  · obtain ⟨j,hj,hjval⟩ := List.mem_map.mp hi
    exact fourValueOutput_not_reserved i.isLt (List.mem_range.mp hj) (hjval.symm ▸ hp)

private theorem arithmetic_disjoint : ∀ i j : Fin 18, i ≠ j →
    ∀ p ∈ arithmeticFactors i, p ∉ arithmeticFactors j := by decide +kernel

private theorem seeds_disjoint : ∀ i j : Fin 2, i ≠ j →
    ∀ p ∈ seedFactors i, p ∉ seedFactors j := by decide +kernel

private theorem arithmetic_seed_disjoint : ∀ i : Fin 18, ∀ j : Fin 2,
    ∀ p ∈ arithmeticFactors i, p ∉ seedFactors j := by decide +kernel

private theorem sources_disjoint {k : ℕ} (s t : SharedRowSource k) (hne : s ≠ t) :
    List.Disjoint (fourValueFactors s) (fourValueFactors t) := by
  rcases s with i | (i | i) <;> rcases t with j | (j | j)
  · intro p hp hq
    exact arithmetic_disjoint i j (fun h => hne (congrArg Sum.inl h)) p hp hq
  · intro p hp hq
    exact wangDisjoint j (reserved_arithmetic i p hp) hq
  · intro p hp hq
    exact arithmetic_seed_disjoint i j p hp hq
  · intro p hp hq
    exact wangDisjoint i (reserved_arithmetic j p hq) hp
  · exact wangFactors_disjoint i j (fun h => hne (congrArg (Sum.inr ∘ Sum.inl) h))
  · intro p hp hq
    exact wangDisjoint i (reserved_seed j p hq) hp
  · intro p hp hq
    exact arithmetic_seed_disjoint j i p hq hp
  · intro p hp hq
    exact wangDisjoint j (reserved_seed i p hp) hq
  · intro p hp hq
    exact seeds_disjoint i j (fun h => hne (congrArg (Sum.inr ∘ Sum.inr) h)) p hp hq

private theorem fixedFactors_disjoint {k : ℕ} (s : SharedRowSource k) :
    List.Disjoint ([5,7,199,163] : List ℕ) (fourValueFactors s) := by
  rcases s with i | (i | t)
  · intro p hp hq
    exact (by decide +kernel : ∀ i : Fin 18, ∀ p ∈ ([5,7,199,163] : List ℕ),
      p ∉ arithmeticFactors i) i p hp hq
  · intro p hp hq
    have hr : p ∈ ([5,7,199,163] : List ℕ) ++
        (sharedFixedRows ++ sharedSeedRows).flatMap fixedFactors := List.mem_append_left _ hp
    exact wangDisjoint i (show p ∈ sharedReservedPrimes from hr) hq
  · intro p hp hq
    exact (by decide +kernel : ∀ t : Fin 2, ∀ p ∈ ([5,7,199,163] : List ℕ),
      p ∉ seedFactors t) t p hp hq

private theorem fixedFactors_perm (r : ℕ × ℕ × List ℕ) (ha : r.1 ≠ 1) :
    (r.2.2 ++ firstFactors r.1 ++ [r.2.1]).Perm (fixedFactors r) := by
  rw [firstFactors,ite_eq_right ha,List.append_assoc]
  exact List.perm_append_comm (l₁ := r.2.2) (l₂ := [r.1,r.2.1])

def sourceSecondFactors {k : ℕ} (s : SharedRowSource k) : List ℕ :=
  match s with
  | .inr (.inl w) => outputFactors w
  | _ => [(fourValueSourceData s).2.1]

def fourValueSecondFactors (k : ℕ) (i : FourValueRow k) : List ℕ :=
  sourceSecondFactors (fourValueSource i)

theorem fourValueSecondFactors_prod (k : ℕ) (i : FourValueRow k) :
    (fourValueSecondFactors k i).prod = (fourValueLayout k).secondSize i := by
  change _ = ((fourValueRows k).getD i.val (0,0,[])).2.1
  rw [fourValueSource_data]
  unfold fourValueSecondFactors
  generalize fourValueSource i = s
  rcases s with a | (w | t) <;> simp [sourceSecondFactors,outputFactors,fourValueSourceData,fourValueWangRow]

private theorem sourceFactors_perm {k : ℕ} (s : SharedRowSource k) :
    ((fourValueSourceData s).2.2 ++ firstFactors (fourValueFirst s) ++ sourceSecondFactors s).Perm
      (fourValueFactors s) := by
  rcases s with i | (i | t)
  · exact fixedFactors_perm (sharedArithmeticRow i)
      ((by decide +kernel : ∀ i : Fin 18, (sharedArithmeticRow i).1 ≠ 1) i)
  · simp [sourceSecondFactors,fourValueSourceData,fourValueFirst,firstFactors,fourValueFactors,wangFactors,fourValueWangRow]
  · exact fixedFactors_perm (sharedSeedRows.getD t (0,0,[]))
      ((by decide +kernel : ∀ t : Fin 2, (sharedSeedRows.getD t (0,0,[])).1 ≠ 1) t)

private theorem fourValueFactors_perm (k : ℕ) (i : Fin (fourValueRows k).length) :
    (rowFactorsWith (fourValueLayout k) (fun j => rowDigits (fourValueRows k) j) (fourValueSecondFactors k) i).Perm
      (fourValueFactors (fourValueSource i)) := by
  change (((fourValueRows k).getD i.val (0,0,[])).2.2 ++
    firstFactors (sharedObservedA (fourValueRows k) i) ++
    fourValueSecondFactors k i).Perm _
  rw [fourValueSource_first, fourValueSource_data]
  exact sourceFactors_perm (fourValueSource i)

theorem fourValueRowFactors_prime {k : ℕ} (i : Fin (fourValueRows k).length) :
    ∀ p ∈ rowFactorsWith (fourValueLayout k) (fun j => rowDigits (fourValueRows k) j) (fourValueSecondFactors k) i, p.Prime :=
  fun p hp => fourValueFactors_prime _ p ((fourValueFactors_perm k i).mem_iff.mp hp)

theorem fourValueRowFactors_nodup {k : ℕ} (i : Fin (fourValueRows k).length) :
    (rowFactorsWith (fourValueLayout k) (fun j => rowDigits (fourValueRows k) j) (fourValueSecondFactors k) i).Nodup :=
  (fourValueFactors_perm k i).nodup_iff.mpr (fourValueFactors_nodup _)

theorem fourValueRowFactors_disjoint {k : ℕ} (i : Fin (fourValueRows k).length) :
    List.Disjoint ([5,7,199,163] : List ℕ)
      (rowFactorsWith (fourValueLayout k) (fun j => rowDigits (fourValueRows k) j) (fourValueSecondFactors k) i) :=
  fun {p} hp hq => fixedFactors_disjoint _ hp ((fourValueFactors_perm k i).mem_iff.mp hq)

def fourValueRowsCRT (k : ℕ) : ZMod (sharedOrder (fourValueRows k)) ≃+* Factor (fourValueLayout k) := by
  rw [← fourValueLayout_order]
  apply finiteCRT_of_rowFactorsWith (fourValueLayout k) (fun j => rowDigits (fourValueRows k) j)
    (fourValueSecondFactors k)
  · intro i; rfl
  · exact fourValueSecondFactors_prod k
  · intro i p hp
    exact fourValueFactors_prime _ p ((fourValueFactors_perm k i).mem_iff.mp hp)
  · intro i
    exact (fourValueFactors_perm k i).nodup_iff.mpr (fourValueFactors_nodup _)
  · intro i j hij p hp hq
    exact sources_disjoint _ _ (fun he => hij (fourValueSource_injective k he))
      ((fourValueFactors_perm k i).mem_iff.mp hp) ((fourValueFactors_perm k j).mem_iff.mp hq)
  · intro i p hp hq
    exact fixedFactors_disjoint _ hp ((fourValueFactors_perm k i).mem_iff.mp hq)

private theorem reservedFactor_le {p : ℕ} (k : ℕ) (hp : p ∈ sharedReservedPrimes) :
    p ≤ sharedPrimeCap (4*k) := by
  obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp hp
  have h := sharedPrimeAt_le (4*k) (.inl ⟨i,hi⟩)
  change sharedReservedPrimes.getD i 0 ≤ _ at h
  rw [List.getD_eq_getElem _ _ hi,he] at h
  exact h

private theorem fourValueFactors_le {k p : ℕ} (s : SharedRowSource k)
    (hp : p ∈ fourValueFactors s) : p ≤ sharedPrimeCap (4*k) := by
  rcases s with i | (i | t)
  · exact reservedFactor_le k (reserved_arithmetic i p hp)
  · rcases List.mem_cons.mp hp with he|hp
    · exact he.symm ▸ fourValueLow_le i.isLt
    · obtain ⟨j,hj,hjval⟩ := List.mem_map.mp hp
      rw [← hjval]
      exact (fourValueOutput_le i.isLt (List.mem_range.mp hj)).trans (by
        unfold sharedPrimeCap sharedPairCap
        omega)
  · exact reservedFactor_le k (reserved_seed t p hp)

/-- Every prime in the concrete shared modulus fits the stacking cap. -/
theorem fourValueOrder_primeBound (k : ℕ) :
    PrimeBound (sharedOrder (fourValueRows k)) (sharedPrimeCap (4*k)) := by
  intro p _
  by_cases hp : p.Prime
  · right
    by_cases hd : p ∣ sharedOrder (fourValueRows k)
    · right
      rw [← fourValueLayout_order] at hd
      let L := fourValueLayout k
      change p ∣ (1225*199*163) * ∏ i, rowModulus L i at hd
      rcases hp.dvd_mul.mp hd with hf|hr
      · rw [show 1225*199*163 = ([5,5,7,7,199,163] : List ℕ).prod by decide] at hf
        obtain ⟨q,hq,hpq⟩ := hp.prime.dvd_prod_iff.mp hf
        have hl : q ∈ ([5,7,199,163] : List ℕ) := by
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hq ⊢
          tauto
        have hprime := (by decide : ∀ q ∈ ([5,7,199,163] : List ℕ), q.Prime) q hl
        have he := (Nat.dvd_prime_two_le hprime hp.two_le).mp hpq
        rw [he]
        apply reservedFactor_le k
        exact List.mem_append_left
          ((sharedFixedRows ++ sharedSeedRows).flatMap fixedFactors) hl
      · rw [← Fin.prod_ofFn] at hr
        obtain ⟨q,hq,hpq⟩ := hp.prime.dvd_prod_iff.mp hr
        obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hq
        let ds := rowDigits (fourValueRows k) i
        let fs := rowFactorsWith L (fun j => rowDigits (fourValueRows k) j) (fourValueSecondFactors k) i
        have hm : (ds ++ fs).prod = rowModulus L i := by
          change (rowDigits (fourValueRows k) i ++
            rowFactorsWith L (fun j => rowDigits (fourValueRows k) j) (fourValueSecondFactors k) i).prod = _
          simp only [rowFactorsWith,List.prod_append,firstFactors_prod,fourValueSecondFactors_prod,
            rowModulus,pow_two]
          change _ = ds.prod*ds.prod * L.firstSize i * L.secondSize i
          ac_rfl
        rw [← hm] at hpq
        obtain ⟨q,hq,hpq⟩ := hp.prime.dvd_prod_iff.mp hpq
        have hm : q ∈ fs := by
          rcases List.mem_append.mp hq with hl|hl
          · unfold fs rowFactorsWith
            exact List.mem_append_left _ (List.mem_append_left _ hl)
          · exact hl
        have hsource := (fourValueFactors_perm k i).mem_iff.mp hm
        have hprime := fourValueFactors_prime _ q hsource
        have he := (Nat.dvd_prime_two_le hprime hp.two_le).mp hpq
        rw [he]
        exact fourValueFactors_le _ hsource
    · exact Or.inl hd
  · exact Or.inl hp

end
end TranslationTiling.FiniteCompiler.Packed
