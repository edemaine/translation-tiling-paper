import TranslationTiling.FiniteCompiler.Effective.SharedRowSources
import TranslationTiling.FiniteCompiler.SharedCRT
import TranslationTiling.Compiler.SharedUsefulBound
import Mathlib.Data.List.Prime

namespace TranslationTiling.FiniteCompiler.Packed

open Compiler.Size Effective SharedCoordinates
open scoped BigOperators

noncomputable section
set_option maxRecDepth 10000

private def fixedFactors (row : ℕ × ℕ × List ℕ) : List ℕ :=
  row.1 :: row.2.1 :: row.2.2

private def arithmeticFactors (i : Fin 18) : List ℕ := fixedFactors (sharedArithmeticRow i)
private def seedFactors (t : Fin 2) : List ℕ := fixedFactors (sharedSeedRows.getD t (0,0,[]))

private def sourceFactors {k : ℕ} : SharedRowSource k → List ℕ
  | .inl i => arithmeticFactors i
  | .inr (.inl j) => wangPrivatePrimes j
  | .inr (.inr t) => seedFactors t

private theorem reserved_arithmetic (i : Fin 18) : ∀ p ∈ arithmeticFactors i, p ∈ sharedReservedPrimes :=
  (by decide +kernel : ∀ i : Fin 18, ∀ p ∈ arithmeticFactors i, p ∈ sharedReservedPrimes) i

private theorem reserved_seed (t : Fin 2) : ∀ p ∈ seedFactors t, p ∈ sharedReservedPrimes :=
  (by decide +kernel : ∀ t : Fin 2, ∀ p ∈ seedFactors t, p ∈ sharedReservedPrimes) t

private theorem sourceFactors_prime {k : ℕ} (s : SharedRowSource k) :
    ∀ p ∈ sourceFactors s, p.Prime := by
  rcases s with i | (i | t)
  · exact (by decide +kernel : ∀ i : Fin 18, ∀ p ∈ arithmeticFactors i, p.Prime) i
  · obtain ⟨_,hb,_,_,_,hd⟩ := sharedWangRow_facts i.isLt
    intro p hp
    rcases List.mem_cons.mp hp with h|h
    · exact h.symm ▸ hb
    · exact (hd p h).1
  · exact (by decide +kernel : ∀ t : Fin 2, ∀ p ∈ seedFactors t, p.Prime) t

private theorem sourceFactors_nodup {k : ℕ} (s : SharedRowSource k) : (sourceFactors s).Nodup := by
  rcases s with i | (i | t)
  · exact (by decide +kernel : ∀ i : Fin 18, (arithmeticFactors i).Nodup) i
  · exact ((List.nodup_flatMap.mp (wangPrivatePrimes_nodup k)).1 i (List.mem_finRange i))
  · exact (by decide +kernel : ∀ t : Fin 2, (seedFactors t).Nodup) t

private theorem wangDisjoint {k : ℕ} (i : Fin (2*k)) :
    List.Disjoint sharedReservedPrimes (wangPrivatePrimes i) := by
  intro p hp hi
  exact wangPrivatePrimes_disjoint k hp (List.mem_flatMap.mpr ⟨i,List.mem_finRange i,hi⟩)

private theorem arithmetic_disjoint : ∀ i j : Fin 18, i ≠ j →
    ∀ p ∈ arithmeticFactors i, p ∉ arithmeticFactors j := by decide +kernel

private theorem seeds_disjoint : ∀ i j : Fin 2, i ≠ j →
    ∀ p ∈ seedFactors i, p ∉ seedFactors j := by decide +kernel

private theorem arithmetic_seed_disjoint : ∀ i : Fin 18, ∀ j : Fin 2,
    ∀ p ∈ arithmeticFactors i, p ∉ seedFactors j := by decide +kernel

private theorem sources_disjoint {k : ℕ} (s t : SharedRowSource k) (hne : s ≠ t) :
    List.Disjoint (sourceFactors s) (sourceFactors t) := by
  rcases s with i | (i | i) <;> rcases t with j | (j | j)
  · intro p hp hq
    exact arithmetic_disjoint i j (fun h => hne (congrArg Sum.inl h)) p hp hq
  · intro p hp hq
    exact wangDisjoint j (reserved_arithmetic i p hp) hq
  · intro p hp hq
    exact arithmetic_seed_disjoint i j p hp hq
  · intro p hp hq
    exact wangDisjoint i (reserved_arithmetic j p hq) hp
  · exact wangPrivatePrimes_pairwise (fun h => hne (congrArg (Sum.inr ∘ Sum.inl) h))
  · intro p hp hq
    exact wangDisjoint i (reserved_seed j p hq) hp
  · intro p hp hq
    exact arithmetic_seed_disjoint j i p hq hp
  · intro p hp hq
    exact wangDisjoint j (reserved_seed i p hp) hq
  · intro p hp hq
    exact seeds_disjoint i j (fun h => hne (congrArg (Sum.inr ∘ Sum.inr) h)) p hp hq

private theorem fixedFactors_disjoint {k : ℕ} (s : SharedRowSource k) :
    List.Disjoint ([5,7,199,163] : List ℕ) (sourceFactors s) := by
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

private theorem sourceFactors_perm {k : ℕ} (s : SharedRowSource k) :
    ((sourceData s).2.2 ++ firstFactors (sourceFirst s) ++ [(sourceData s).2.1]).Perm
      (sourceFactors s) := by
  rcases s with i | (i | t)
  · exact fixedFactors_perm (sharedArithmeticRow i)
      ((by decide +kernel : ∀ i : Fin 18, (sharedArithmeticRow i).1 ≠ 1) i)
  · exact List.perm_append_comm (l₁ := (sharedWangRow k i).2.2) (l₂ := [(sharedWangRow k i).2.1])
  · exact fixedFactors_perm (sharedSeedRows.getD t (0,0,[]))
      ((by decide +kernel : ∀ t : Fin 2, (sharedSeedRows.getD t (0,0,[])).1 ≠ 1) t)

private theorem sharedFactors_perm (k : ℕ) (i : Fin (sharedRows k).length) :
    (rowFactors (sharedLayout k) (fun j => rowDigits (sharedRows k) j) i).Perm
      (sourceFactors (sharedRowSource i)) := by
  change (((sharedRows k).getD i.val (0,0,[])).2.2 ++
    firstFactors (sharedObservedA (sharedRows k) i) ++
    [((sharedRows k).getD i.val (0,0,[])).2.1]).Perm _
  rw [sharedRowSource_first, sharedRowSource_data]
  exact sourceFactors_perm (sharedRowSource i)

theorem sharedRowFactors_prime {k : ℕ} (i : Fin (sharedRows k).length) :
    ∀ p ∈ rowFactors (sharedLayout k) (fun j => rowDigits (sharedRows k) j) i, p.Prime :=
  fun p hp => sourceFactors_prime _ p ((sharedFactors_perm k i).mem_iff.mp hp)

theorem sharedRowFactors_nodup {k : ℕ} (i : Fin (sharedRows k).length) :
    (rowFactors (sharedLayout k) (fun j => rowDigits (sharedRows k) j) i).Nodup :=
  (sharedFactors_perm k i).nodup_iff.mpr (sourceFactors_nodup _)

theorem sharedRowFactors_disjoint {k : ℕ} (i : Fin (sharedRows k).length) :
    List.Disjoint ([5,7,199,163] : List ℕ)
      (rowFactors (sharedLayout k) (fun j => rowDigits (sharedRows k) j) i) :=
  fun {p} hp hq => fixedFactors_disjoint _ hp ((sharedFactors_perm k i).mem_iff.mp hq)

def sharedRowsCRT (k : ℕ) : ZMod (sharedOrder (sharedRows k)) ≃+* Factor (sharedLayout k) := by
  rw [← sharedLayout_order]
  apply finiteCRT_of_rowFactors (sharedLayout k) (fun j => rowDigits (sharedRows k) j)
  · intro i; rfl
  · intro i p hp
    exact sourceFactors_prime _ p ((sharedFactors_perm k i).mem_iff.mp hp)
  · intro i
    exact (sharedFactors_perm k i).nodup_iff.mpr (sourceFactors_nodup _)
  · intro i j hij p hp hq
    exact sources_disjoint _ _ (fun he => hij (sharedRowSource_injective k he))
      ((sharedFactors_perm k i).mem_iff.mp hp) ((sharedFactors_perm k j).mem_iff.mp hq)
  · intro i p hp hq
    exact fixedFactors_disjoint _ hp ((sharedFactors_perm k i).mem_iff.mp hq)

private theorem reservedFactor_le {p : ℕ} (k : ℕ) (hp : p ∈ sharedReservedPrimes) :
    p ≤ sharedPrimeCap k := by
  obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp hp
  have h := sharedPrimeAt_le k (.inl ⟨i,hi⟩)
  change sharedReservedPrimes.getD i 0 ≤ _ at h
  rw [List.getD_eq_getElem _ _ hi,he] at h
  exact h

private theorem sourceFactors_le {k p : ℕ} (s : SharedRowSource k)
    (hp : p ∈ sourceFactors s) : p ≤ sharedPrimeCap k := by
  rcases s with i | (i | t)
  · exact reservedFactor_le k (reserved_arithmetic i p hp)
  · obtain ⟨_,_,_,hb,_,hd⟩ := sharedWangRow_facts i.isLt
    rcases List.mem_cons.mp hp with h|h
    · rw [h]
      exact hb.trans (by unfold sharedPrimeCap sharedPairCap; omega)
    · exact (hd p h).2.2
  · exact reservedFactor_le k (reserved_seed t p hp)

/-- Every prime in the concrete shared modulus fits the stacking cap. -/
theorem sharedOrder_primeBound (k : ℕ) :
    PrimeBound (sharedOrder (sharedRows k)) (sharedPrimeCap k) := by
  intro p _
  by_cases hp : p.Prime
  · right
    by_cases hd : p ∣ sharedOrder (sharedRows k)
    · right
      rw [← sharedLayout_order] at hd
      let L := sharedLayout k
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
        let ds := rowDigits (sharedRows k) i
        let fs := rowFactors L (fun j => rowDigits (sharedRows k) j) i
        have hm : (ds ++ fs).prod = rowModulus L i := by
          change (rowDigits (sharedRows k) i ++
            rowFactors L (fun j => rowDigits (sharedRows k) j) i).prod = _
          simp only [rowFactors,List.prod_append,firstFactors_prod,List.prod_cons,List.prod_nil,
            Nat.mul_one,rowModulus,pow_two]
          change _ = ds.prod*ds.prod * L.firstSize i * L.secondSize i
          ac_rfl
        rw [← hm] at hpq
        obtain ⟨q,hq,hpq⟩ := hp.prime.dvd_prod_iff.mp hpq
        have hm : q ∈ fs := by
          rcases List.mem_append.mp hq with hl|hl
          · unfold fs rowFactors
            exact List.mem_append_left _ (List.mem_append_left _ hl)
          · exact hl
        have hsource := (sharedFactors_perm k i).mem_iff.mp hm
        have hprime := sourceFactors_prime _ q hsource
        have he := (Nat.dvd_prime_two_le hprime hp.two_le).mp hpq
        rw [he]
        exact sourceFactors_le _ hsource
    · exact Or.inl hd
  · exact Or.inl hp

end
end TranslationTiling.FiniteCompiler.Packed
