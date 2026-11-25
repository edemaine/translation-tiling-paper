import TranslationTiling.FiniteCompiler.Effective.SharedStrip
import TranslationTiling.FiniteCompiler.Effective.FourValueTailCore

namespace TranslationTiling.FiniteCompiler.Packed

open Compiler Compiler.Size Compiler.Effective Compiler.StripLift Effective Rails.Strips SharedCoordinates

set_option maxRecDepth 10000
set_option exponentiation.threshold 2000

private theorem fourValue_fixed_radius (k i : ℕ) (hi : i < 18) :
    2*(rowR (fourValueRows k) i*rowA (fourValueRows k) i*rowB (fourValueRows k) i) ≤
      fourValueRadius k := by
  unfold rowR rowA rowB rowDigits
  rw [fourValueRows_fixed_at hi]
  have h := (by decide +kernel : ∀ j : Fin 18,
    2*((sharedArithmeticRow j).2.2.prod*(sharedArithmeticRow j).1*(sharedArithmeticRow j).2.1) ≤
      2^68) ⟨i,hi⟩
  exact h.trans (Nat.le_add_right _ _)

private theorem fourValue_wang_strip (k i : ℕ) (hi : i < 2*k) (f : NumericalPoint)
    (hf : f ∈ fourValueWangActivation k i) :
    TestSupportAt 35 (fun _ => fourValueRadius k) f.1 := by
  unfold fourValueWangActivation congruenceBatchDeck at hf
  obtain ⟨record,hrecord,hf⟩ := List.mem_flatMap.mp hf
  obtain ⟨a,_,ha⟩ := List.mem_map.mp hf
  have hh : f.1 = record.1 := (congrArg Prod.fst ha).symm
  rw [hh]
  simp only [activationDeckArgs,recordsOfInputs,wangActivationInputs,fourValueActivationRecords,
    List.mem_flatMap,List.mem_map] at hrecord
  obtain ⟨l,_,z,_,rfl⟩ := hrecord
  let ms := fourValueModuli k i
  let P := sharedPrimeCap (4*k)
  have hp : sharedPairCap (4*k) ≤ P := by unfold P sharedPrimeCap; omega
  have ha : (fourValueWangRow k i).1 ≤ 200 := by
    unfold fourValueWangRow
    split <;> simp
  have hm : ms.prod ≤ 200*P^4 := by
    change (fourValueWangRow k i).1 * (fourValueWangRow k i).2.1 ≤ _
    exact Nat.mul_le_mul ha ((fourValueOutputProduct_le hi).trans (Nat.pow_le_pow_left hp 4))
  have hM : fourValueLow k i*ms.prod ≤ 200*P^5 := by
    calc
      _ ≤ P*(200*P^4) := Nat.mul_le_mul (fourValueLow_le hi) hm
      _ = _ := by ring
  refine Or.inr ⟨if i < k then 0 else 2,by split <;> decide,?_,rfl⟩
  simp only [fourValueRecord,Int.natAbs_natCast]
  apply (residueSearch_le _ _).trans
  exact hM.trans ((Nat.mul_le_mul_right (P^5) (by decide : 200 ≤ 256)).trans
    (by
      unfold fourValueRadius
      rw [min_eq_left (by omega : 1 ≤ k),one_mul]
      exact Nat.le_add_left _ _))

/-- All concrete shared tests lie in the strips used by the slot assembly. -/
theorem fourValueRawDeck_strip (T : LeanWang.TileSet) (k : ℕ) :
    ∀ F ∈ fourValueRawDeck T k, ∀ f ∈ F,
      TestSupportAt 35 (fun _ => fourValueRadius k) f.1 := by
  let rs := fourValueRows k
  let H := fourValueRadius k
  have hH : 35 ≤ H := by unfold H fourValueRadius; omega
  have hinv (a b : ℕ) (h : Plane) (g : Option ℕ)
      (hh : TestSupportAt 35 (fun _ => H) h) (f : NumericalPoint)
      (hf : f ∈ sharedInvariance rs a b h g) : TestSupportAt 35 (fun _ => H) f.1 := by
    unfold sharedInvariance invarianceCodes at hf
    rcases List.mem_append.mp hf with hf|hf
    · obtain ⟨_,_,rfl⟩ := List.mem_map.mp hf
      exact zero_strip H
    · obtain ⟨_,_,rfl⟩ := List.mem_map.mp hf
      exact hh
  intro F hF f hf
  simp only [fourValueRawDeck,List.mem_cons,List.mem_append] at hF
  rcases hF with rfl | ((hd | ha) | hc)
  · obtain ⟨_,_,rfl⟩ := List.mem_map.mp hf
    exact zero_strip H
  · simp only [sharedDependence,List.mem_append,List.mem_flatMap,List.mem_map] at hd
    rcases hd with ((⟨i,_,j,_,rfl⟩ | ⟨i,_,rfl⟩) | ⟨t,_,ht⟩) | ht
    · exact hinv _ _ _ _ (zero_strip H) _ hf
    · apply hinv _ _ _ _ _ _ hf
      exact Or.inl ⟨(by decide : 1 ≤ 35).trans hH,by
        simpa using (getD_tailSlopes_le k i).trans (by decide : 16 ≤ 35)⟩
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
      rcases ht with rfl|rfl
      · exact hinv _ _ (35,0) _ (Or.inl ⟨hH,by decide⟩) _ hf
      · exact hinv _ _ (0,35) _ (Or.inl ⟨Nat.zero_le _,by decide⟩) _ hf
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
      rcases ht with rfl|rfl
      · exact hinv _ _ (1,0) _ (Or.inl ⟨(by decide : 1 ≤ 35).trans hH,by decide⟩) _ hf
      · exact hinv _ _ (1,-2) _ (Or.inl ⟨(by decide : 1 ≤ 35).trans hH,by decide⟩) _ hf
  · simp only [fourValueActivation,List.mem_append,List.mem_map,List.mem_range] at ha
    rcases ha with (⟨i,hi,rfl⟩ | ⟨i,hi,rfl⟩) | ⟨t,ht,rfl⟩
    · exact compactCodes_strip _ _ H ((getD_tailSlopes_le k i).trans_lt (by decide))
        (fourValue_fixed_radius k i hi) f hf
    · exact fourValue_wang_strip k i hi f hf
    · obtain ⟨j,hj,hf⟩ := List.mem_flatMap.mp hf
      have hh := activationBatch_horizontal _ hf
      let i := (fourValueRows k).length-2+t
      let o := (fourValueRows k).length-2+(1-t)
      have hget (v : ℕ) : (fourValueRows k).getD ((fourValueRows k).length-2+v) (0,0,[]) =
          sharedSeedRows.getD v (0,0,[]) := by
        rw [fourValueRows_length,show 20+2*k-2+v=18+2*k+v by omega,fourValueRows_seed_at]
      have ha (v : ℕ) (hv : v < 2) : rowA (fourValueRows k) ((fourValueRows k).length-2+v) ≤ 3 := by
        unfold rowA
        rw [hget]
        exact (by decide : ∀ v : Fin 2, (sharedSeedRows.getD v.val (0,0,[])).1 ≤ 3) ⟨v,hv⟩
      have hb : rowB (fourValueRows k) i ≤ 1229 := by
        unfold i rowB
        rw [hget]
        exact (by decide : ∀ v : Fin 2, (sharedSeedRows.getD v.val (0,0,[])).2.1 ≤ 1229) ⟨t,ht⟩
      have hr : rowR (fourValueRows k) i ≤ 1231 := by
        unfold i rowR rowDigits
        rw [hget]
        exact (by decide : ∀ v : Fin 2, (sharedSeedRows.getD v.val (0,0,[])).2.2.prod ≤ 1231) ⟨t,ht⟩
      have hs := seedFirst_bound _ _ _ _ j (ha t ht) hb hr (ha (1-t) (by omega)) hj
      rw [hh]
      exact Or.inl ⟨hs.1.trans (Nat.le_add_right _ _),by simpa using hs.2.le⟩
  · obtain ⟨xs,_,hc⟩ := List.mem_flatMap.mp hc
    unfold fourValueCycle at hc
    split at hc
    · simp at hc
    · simp only [List.mem_singleton] at hc
      subst F
      obtain ⟨_,_,rfl⟩ := List.mem_map.mp hf
      exact zero_strip H

end TranslationTiling.FiniteCompiler.Packed
