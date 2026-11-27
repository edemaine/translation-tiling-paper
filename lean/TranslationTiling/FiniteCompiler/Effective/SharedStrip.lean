import TranslationTiling.FiniteCompiler.Effective.SharedTailCore

namespace TranslationTiling.FiniteCompiler.Packed

open Compiler Compiler.Size Compiler.Effective Compiler.StripLift Effective Rails.Strips

set_option maxRecDepth 10000
set_option exponentiation.threshold 2000

theorem residueSearch_le (m : ℕ) (cs : CongruenceList) :
    residueSearch m cs ≤ m := by
  unfold residueSearch
  generalize ht : ((List.range m).filter fun n => decide (Congruences cs n)) = l
  cases l with
  | nil => simp
  | cons a as =>
    have ha : a ∈ (List.range m).filter (fun n => decide (Congruences cs n)) := by rw [ht]; simp
    exact (List.mem_range.mp (List.mem_filter.mp ha).1).le

private theorem compactFirst_bound (z : ActivationNumbers) :
    (compactFirst z).natAbs ≤ 2*(z.1.2.2*z.1.1*z.1.2.1) := by
  unfold compactFirst
  dsimp only
  split
  · simp only [mul_zero,add_zero,Int.natAbs_natCast]
    exact (residueSearch_le _ _).trans (by omega)
  · simp only [mul_one,← Nat.cast_add,Int.natAbs_natCast]
    have h := residueSearch_le
      (z.1.2.2*z.1.1*z.1.2.1)
      [(z.1.2.2,z.2.1),
       (z.1.1,differenceResidue z.1.1 (2*Compiler.numericalRank z.2.2.1 z.2.2.2.1 z.2.2.2.2) z.2.2.1),
       (z.1.2.1,differenceResidue z.1.2.1 (2*Compiler.numericalRank z.2.2.2.1 z.2.2.1 z.2.2.2.2) z.2.2.2.1)]
    omega

theorem activationBatch_horizontal (z : ActivationBatchData) {f : NumericalPoint}
    (hf : f ∈ activationBatchCodes z) : f.1 = z.2.2.1 := by
  obtain ⟨_,_,rfl⟩ := List.mem_map.mp hf
  rfl

theorem compactCodes_stripAt (env : ActivationEnvironment) (s : ℕ) (H : ℕ → ℕ)
    (hs : s < 17) (hH : 2*(env.2.1*env.2.2.1*env.2.2.2.1) ≤ H s)
    (f : NumericalPoint) (hf : f ∈ compactCodes env s) :
    TestSupportAt 35 H f.1 := by
  obtain ⟨j,_,hj⟩ := List.mem_flatMap.mp hf
  simp only [compactBatch] at hj
  rw [activationBatch_horizontal _ hj]
  exact Or.inr ⟨s,hs,(compactFirst_bound _).trans hH,rfl⟩

theorem compactFirst_centered (z : ActivationNumbers) :
    (compactFirst z - (z.1.2.2*z.1.1*z.1.2.1 : ℕ)).natAbs ≤ z.1.2.2*z.1.1*z.1.2.1 := by
  let M := z.1.2.2*z.1.1*z.1.2.1
  have h := compactFirst_bound z
  have hp : 0 ≤ compactFirst z := by unfold compactFirst; positivity
  have hle : compactFirst z ≤ 2*(M : ℤ) := by
    have hcast : ((compactFirst z).natAbs : ℤ) ≤ 2*(M : ℤ) := by
      exact_mod_cast (show (compactFirst z).natAbs ≤ 2*M from h)
    rwa [Int.natAbs_of_nonneg hp] at hcast
  change (compactFirst z - (M : ℤ)).natAbs ≤ M
  omega

theorem compactCodes_centered_stripAt (env : ActivationEnvironment) (s : ℕ) (H : ℕ → ℕ)
    (hs : s < 17) (hH : env.2.1*env.2.2.1*env.2.2.2.1 ≤ H s)
    (f : NumericalPoint) (hf : f ∈ compactCodes env s) :
    let M : ℤ := (env.2.1*env.2.2.1*env.2.2.2.1 : ℕ)
    TestSupportAt 35 H (f.1+(-M,(s : ℤ)*M)) := by
  obtain ⟨j,_,hj⟩ := List.mem_flatMap.mp hf
  simp only [compactBatch] at hj
  rw [activationBatch_horizontal _ hj]
  refine Or.inr ⟨s,hs,?_,?_⟩
  · change (_ + -_).natAbs ≤ H s
    rw [← sub_eq_add_neg]
    exact (compactFirst_centered _).trans hH
  · change -_ * _ + _ * _ = -_ * (_ + -_)
    ring

theorem compactCodes_strip (env : ActivationEnvironment) (s H : ℕ)
    (hs : s < 17) (hH : 2*(env.2.1*env.2.2.1*env.2.2.2.1) ≤ H)
    (f : NumericalPoint) (hf : f ∈ compactCodes env s) :
    TestSupportAt 35 (fun _ => H) f.1 :=
  compactCodes_stripAt env s (fun _ => H) hs hH f hf

private theorem numericalMultiplicity_le_two (a b : ℕ) :
    Compiler.numericalMultiplicity a b ≤ 2 := by
  unfold Compiler.numericalMultiplicity
  repeat
    first | decide | split

theorem seedFirst_bound (a b r o : ℕ) (j : SeedCode)
    (ha : a ≤ 3) (hb : b ≤ 1229) (hr : r ≤ 1231) (ho : o ≤ 3)
    (hj : j ∈ seedIndices a b r 35) :
    (numericalSeedFirst (((a,b,r),j.1),(35,o,j.2.1,j.2.2))).natAbs ≤ 2^53 ∧ j.2.2 < 35 := by
  rcases j with ⟨j,x,y⟩
  simp only [seedIndices,List.mem_flatMap,List.mem_map,List.mem_range,Prod.mk.injEq] at hj
  obtain ⟨jj,hj,xx,hx,yy,hy,he₁,he₂,he₃⟩ := hj
  subst jj xx yy
  obtain ⟨_,ha',hb',hd⟩ := (mem_activationIndices _ _ _ _).mp hj
  have hd' : j.2.2.2 < 2 := hd.trans_le (numericalMultiplicity_le_two _ _)
  have hα : j.2.1 ≤ 3 := ha'.le.trans ha
  have hξ : j.2.2.1 ≤ 1229 := hb'.le.trans hb
  let code := CompactIndex.pack 35 (CompactIndex.pack 35 (numericalActivationCode a b j) x) y
  have hcode : code ≤ 13000000 := by
    have hmul := Nat.mul_le_mul hb hα
    unfold code numericalActivationCode CompactIndex.pack
    omega
  let m := (r*a*b*35)*o
  have hm : m ≤ 500000000 :=
    (Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul hr ha) hb) (Nat.le_refl 35)) ho).trans (by decide)
  refine ⟨?_,hy⟩
  unfold numericalSeedFirst
  dsimp only
  rw [← Nat.cast_mul,← Nat.cast_add,Int.natAbs_natCast]
  exact (Nat.add_le_add ((residueSearch_le m _).trans hm) (Nat.mul_le_mul hm hcode)).trans (by decide : 500000000+500000000*13000000 ≤ 2^53)

theorem getD_tailSlopes_le (k i : ℕ) : (tailSlopes k).getD i 0 ≤ 16 := by
  by_cases h : i < (tailSlopes k).length
  · have hi : i < 18+2*k := by simpa [tailSlopes] using h
    rw [List.getD_eq_getElem _ _ h]
    simp only [tailSlopes,List.getElem_map,List.getElem_range]
    unfold Profile.slope
    split_ifs with hs _
    · have hs' : i < ([0,1,2,3,4,5,6,7,10,0,1,2,3,4,7,8,9,14] : List ℕ).length := hs
      exact (by decide : ∀ v ∈ ([0,1,2,3,4,5,6,7,10,0,1,2,3,4,7,8,9,14] : List ℕ), v ≤ 16) _
        (getD_mem_of_lt _ _ 0 hs')
    · decide
    · decide
  · simp only [List.getD_eq_getElem?_getD,List.getElem?_eq_none (Nat.le_of_not_gt h),Option.getD_none]
    decide

private theorem ordinary_radius (k i : ℕ) (hi : i < (sharedRows k).length-2) :
    2*(rowR (sharedRows k) i*rowA (sharedRows k) i*rowB (sharedRows k) i) ≤ sharedRadius k := by
  unfold rowR rowA rowB rowDigits
  by_cases h : i < 18
  · rw [sharedRows_fixed_at h]
    have hsmall := (by decide +kernel : ∀ j : Fin 18,
      2*((sharedArithmeticRow j).2.2.prod*(sharedArithmeticRow j).1*(sharedArithmeticRow j).2.1) ≤ 2^70) ⟨i,h⟩
    exact hsmall.trans (Nat.le_add_right _ _)
  · have hi' : i-18 < 2*k := by rw [sharedRows_length] at hi; omega
    have he := sharedRows_wang_at hi'
    rw [show 18+(i-18)=i by omega] at he
    rw [he]
    obtain ⟨ha,_,_,hb,hlen,hd⟩ := sharedWangRow_facts hi'
    change (sharedWangRow k (i-18)).1 = 199 ∨ (sharedWangRow k (i-18)).1 = 163 at ha
    change (sharedWangRow k (i-18)).2.2.length = 3 at hlen
    have hab : (sharedWangRow k (i-18)).1 ≤ 200 := by omega
    let P := sharedPrimeCap k
    have hr (l : List ℕ) (h : ∀ d ∈ l, d ≤ P) : l.prod ≤ P^l.length := by
      induction l with
      | nil => simp
      | cons d ds ih =>
        simp only [List.prod_cons,List.length_cons,pow_succ']
        exact Nat.mul_le_mul (h d (by simp)) (ih (fun d hd => h d (by simp [hd])))
    have hp := hr (sharedWangRow k (i-18)).2.2 (fun d h => (hd d h).2.2)
    rw [hlen] at hp
    calc
      _ ≤ 2*(P^3*200*sharedPairCap k) := Nat.mul_le_mul_left _ (Nat.mul_le_mul (Nat.mul_le_mul hp hab) hb)
      _ = 400*P^3*sharedPairCap k := by ring
      _ ≤ _ := Nat.le_add_left _ _

theorem zero_strip (H : ℕ) : TestSupportAt 35 (fun _ => H) 0 := by
  exact Or.inl ⟨Nat.zero_le _,by decide⟩

/-- All concrete shared tests lie in the strips used by the slot assembly. -/
theorem sharedRawDeck_strip (k : ℕ) (tests : List GuardedAssignments) :
    ∀ F ∈ sharedRawDeck (sharedRows k) (tailSlopes k) tests, ∀ f ∈ F,
      TestSupportAt 35 (fun _ => sharedRadius k) f.1 := by
  let rs := sharedRows k
  let H := sharedRadius k
  have hH : 35 ≤ H := by unfold H sharedRadius; omega
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
  simp only [sharedRawDeck,List.mem_cons,List.mem_append] at hF
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
  · simp only [sharedActivationCodes,List.mem_append,List.mem_map,List.mem_range] at ha
    rcases ha with ⟨i,hi,rfl⟩ | ⟨t,ht,rfl⟩
    · exact compactCodes_strip _ _ H ((getD_tailSlopes_le k i).trans_lt (by decide))
        (ordinary_radius k i hi) f hf
    · obtain ⟨j,hj,hf⟩ := List.mem_flatMap.mp hf
      have hh := activationBatch_horizontal _ hf
      let i := (sharedRows k).length-2+t
      let o := (sharedRows k).length-2+(1-t)
      have hget (v : ℕ) : (sharedRows k).getD ((sharedRows k).length-2+v) (0,0,[]) =
          sharedSeedRows.getD v (0,0,[]) := by
        rw [sharedRows_length,show 20+2*k-2+v=18+2*k+v by omega,sharedRows_seed_at]
      have ha (v : ℕ) (hv : v < 2) : rowA (sharedRows k) ((sharedRows k).length-2+v) ≤ 3 := by
        unfold rowA
        rw [hget]
        exact (by decide : ∀ v : Fin 2, (sharedSeedRows.getD v.val (0,0,[])).1 ≤ 3) ⟨v,hv⟩
      have hb : rowB (sharedRows k) i ≤ 1229 := by
        unfold i rowB
        rw [hget]
        exact (by decide : ∀ v : Fin 2, (sharedSeedRows.getD v.val (0,0,[])).2.1 ≤ 1229) ⟨t,ht⟩
      have hr : rowR (sharedRows k) i ≤ 1231 := by
        unfold i rowR rowDigits
        rw [hget]
        exact (by decide : ∀ v : Fin 2, (sharedSeedRows.getD v.val (0,0,[])).2.2.prod ≤ 1231) ⟨t,ht⟩
      have hs := seedFirst_bound _ _ _ _ j (ha t ht) hb hr (ha (1-t) (by omega)) hj
      rw [hh]
      exact Or.inl ⟨hs.1.trans ((by decide : (2 : ℕ)^53 ≤ 2^70).trans (Nat.le_add_right _ _)),by simpa using hs.2.le⟩
  · obtain ⟨xs,_,hc⟩ := List.mem_flatMap.mp hc
    unfold sharedCycle at hc
    split at hc
    · simp at hc
    · simp only [fixedGadgets,List.mem_singleton] at hc
      subst F
      obtain ⟨_,_,rfl⟩ := List.mem_map.mp hf
      exact zero_strip H

end TranslationTiling.FiniteCompiler.Packed
