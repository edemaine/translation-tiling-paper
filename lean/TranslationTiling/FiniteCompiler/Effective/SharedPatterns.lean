import TranslationTiling.FiniteCompiler.Effective.SharedConcreteCycle
import TranslationTiling.FiniteCompiler.Effective.SharedSeedCorrect
import TranslationTiling.FiniteCompiler.Effective.PackedPatternCorrect

namespace TranslationTiling.FiniteCompiler.Packed

open Effective PairSmall GuardedCompiler
open scoped Classical

noncomputable section

local instance sharedPatternsFrame : SeedFrame := compactSeedFrame
attribute [local instance] ColumnRefinement.family
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000

variable {T : LeanWang.TileSet} {k : ℕ} (hk : 0 < k)
  (c : Code T (radixLayoutProfile 3 k).radices.prod)

local instance sharedPatternAlphabet : AlphabetFamily (system c) := GuardedCompiler.alphabet c

abbrev sharedRefinement := tailRefinement hk (by decide : 0 < 3) c

local notation "S" => sharedRefinement hk c

include hk in
theorem sharedRows_arity (i : ℕ) (hi : i < 18+2*k) :
    (rowDigits (sharedRows k) i).length = (radixLayoutProfile 3 k).arity i := by
  rw [radixLayout_arity hk (by simpa using hi)]
  unfold rowDigits
  by_cases h : i < 18
  · rw [sharedRows_fixed_at h]
    exact (by decide +kernel : ∀ j : Fin 18, (sharedArithmeticRow j).2.2.length =
      if j.val < 9 then 4 else if j.val < 18 then 6 else 3) ⟨i,h⟩
  · let j := i-18
    have hj : j < 2*k := by dsimp [j]; omega
    have he := sharedRows_wang_at hj
    rw [show 18+j=i by dsimp [j]; omega] at he
    rw [he,if_neg (by omega),if_neg h]
    exact (sharedWangRow_facts hj).2.2.2.2.1

def sharedColumnRow : Column (S).system ↪ SharedRow k where
  toFun i := ⟨i.val,by
    have h : i.val < (S).width := i.isLt
    rw [tailRefinement_width] at h
    rw [sharedRows_length]
    omega⟩
  inj' _ _ h := Fin.ext (congrArg (fun j : SharedRow k => j.val) h)

@[simp] theorem sharedColumnRow_val (i : Column (S).system) :
    (sharedColumnRow hk c i).val = i.val := rfl

theorem sharedColumnRow_lt (i : Column (S).system) :
    (sharedColumnRow hk c i).val < (sharedRows k).length-2 := by
  have h : i.val < (S).width := i.isLt
  rw [tailRefinement_width] at h
  simp only [sharedColumnRow_val,sharedRows_length]
  omega

def sharedColumnOfRow (i : SharedRow k) (hi : i.val < (sharedRows k).length-2) : Column (S).system :=
  ⟨i.val,by change i.val < (S).width; rw [tailRefinement_width]; have := sharedRows_length k; omega⟩

@[simp] theorem sharedColumnOfRow_val (i : SharedRow k) (hi : i.val < (sharedRows k).length-2) :
    (sharedColumnOfRow hk c i hi).val = i.val := rfl

theorem sharedColumn_slope (i : Column (S).system) :
    (S).system.slope i = (tailSlopes k).getD i.val 0 := by
  rw [show (S).system.slope i = ((radixLayoutProfile 3 k).slope i.val : ℤ) from
    (packedRadix_layout _ hk (by decide) rfl).slope i]
  have hi : i.val < 18+2*k := by
    have h : i.val < (S).width := i.isLt
    rwa [tailRefinement_width] at h
  simp only [tailSlopes,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_range hi,
    Option.map_some,Option.getD_some,ternaryLayoutProfile]

def sharedColumnLabel (i : Column (S).system) : Letter (S).system i ≃ SharedLabel (sharedColumnRow hk c i) :=
  finCongr (by
    have h : i.val < (S).width := i.isLt
    rw [tailRefinement_width] at h
    exact (sharedRows_arity hk i.val h).symm)

@[simp] theorem sharedColumnLabel_val (i : Column (S).system) (v : Letter (S).system i) :
    (sharedColumnLabel hk c i v).val = v.val := rfl

def sharedPatternCycle (q : PartialTest (S).system) [NeZero q.columns.card] :
    ZMod q.columns.card ↪ SharedRow k :=
  ((ZMod.finEquiv q.columns.card).symm.toEmbedding.trans (testEmbedding q)).trans (sharedColumnRow hk c)

def sharedPatternLabel (q : PartialTest (S).system) [NeZero q.columns.card] (j : ZMod q.columns.card) :
    SharedLabel (sharedPatternCycle hk c q j) :=
  sharedColumnLabel hk c (testEquiv q ((ZMod.finEquiv q.columns.card).symm j)).val
    (q.label (testEquiv q ((ZMod.finEquiv q.columns.card).symm j)))

theorem sharedPattern_indices (b : PartialTest (system c)) :
    let q := (S).expand b
    expandMask 3 k (testMask c b) = if h : q.columns.Nonempty then
      letI : NeZero q.columns.card := ⟨(Finset.card_pos.mpr h).ne'⟩
      sharedAssignments (sharedPatternCycle hk c q) (sharedPatternLabel hk c q)
    else [] := by
  let q := (S).expand b
  dsimp only
  rw [numericalExpandedPattern_indices hk (by decide : 0 < 3) c b]
  change _ = dite (q.columns.Nonempty) _ _
  by_cases h : q.columns.Nonempty
  · rw [if_pos h,dif_pos h]
    letI : NeZero q.columns.card := ⟨(Finset.card_pos.mpr h).ne'⟩
    apply List.ofFn_inj.mpr
    funext j
    let f (j : Fin q.columns.card) := ((testEquiv q j).val.val,(q.label (testEquiv q j)).val)
    change f j = f ((ZMod.finEquiv q.columns.card).symm ((ZMod.finEquiv q.columns.card) j))
    exact congrArg f ((ZMod.finEquiv q.columns.card).symm_apply_apply j).symm
  · rw [if_neg h,dif_neg h]

def sharedSeedCycle (t : Fin 2) (i : Column (S).system) : ZMod 2 ↪ SharedRow k where
  toFun j := if j = 0 then sharedSeedRow k t else sharedColumnRow hk c i
  inj' := by
    intro u v huv
    have hne : sharedSeedRow k t ≠ sharedColumnRow hk c i := by
      have hi := sharedColumnRow_lt hk c i
      intro h
      rw [← h] at hi
      change (sharedRows k).length-2+t.val < _ at hi
      omega
    have hz : (0 : ZMod 2) = 0 := rfl
    have ho : (1 : ZMod 2) ≠ 0 := by decide
    fin_cases u <;> fin_cases v
    · rfl
    · change (if (0 : ZMod 2) = 0 then _ else _) =
          (if (1 : ZMod 2) = 0 then _ else _) at huv
      exact (hne (by simpa only [ite_eq_left hz,ite_eq_right ho,if_true] using huv)).elim
    · change (if (1 : ZMod 2) = 0 then _ else _) =
          (if (0 : ZMod 2) = 0 then _ else _) at huv
      exact (hne (by simpa only [ite_eq_left hz,ite_eq_right ho,if_true] using huv.symm)).elim
    · rfl

def sharedSeedCycleLabel (t : Fin 2) (i : Column (S).system)
    (v : Letter (S).system i) (j : ZMod 2) : SharedLabel (sharedSeedCycle hk c t i j) := by
  by_cases h : j = 0
  · change SharedLabel (if j = 0 then sharedSeedRow k t else sharedColumnRow hk c i)
    rw [if_pos h]
    exact sharedSeedLabel k t
  · change SharedLabel (if j = 0 then sharedSeedRow k t else sharedColumnRow hk c i)
    rw [if_neg h]
    exact sharedColumnLabel hk c i v

theorem sharedSeed_indices (t : Fin 2) (i : Column (S).system) (v : Letter (S).system i) :
    sharedAssignments (sharedSeedCycle hk c t i) (sharedSeedCycleLabel hk c t i v) =
      [(18+2*k+t.val,0),(i.val,v.val)] := by
  unfold sharedAssignments
  rw [List.ofFn_succ,List.ofFn_succ,List.ofFn_zero]
  change [((sharedSeedRow k t).val,0),(i.val,v.val)] = _
  rw [sharedSeedRow_val]

theorem tailSeedTests_iff (xs : GuardedAssignments) :
    xs ∈ tailSeedTests k ↔ ∃ (t : Fin 2) (i : Column (S).system) (v : Letter (S).system i),
      ¬ LetterSeedSet (S).system t i v ∧
        sharedAssignments (sharedSeedCycle hk c t i) (sharedSeedCycleLabel hk c t i v) = xs := by
  constructor
  · intro h
    obtain ⟨⟨t,i,v⟩,htemp,hx⟩ := List.mem_map.mp h
    have ht : t < 2 := by
      simp only [seedTestTemplates,List.mem_flatMap,List.mem_append,List.mem_map,
        Prod.mk.injEq] at htemp
      rcases htemp with ⟨⟨u,b⟩,_,⟨a,_,h,_⟩ | ⟨a,_,h,_⟩⟩ <;> omega
    have hi : i < 18+2*k := by
      simp only [seedTestTemplates,List.mem_flatMap,List.mem_append,List.mem_map,
        Prod.mk.injEq] at htemp
      rcases htemp with ⟨⟨u,b⟩,_,⟨a,_,_,h,_⟩ | ⟨a,_,_,h,_⟩⟩ <;> omega
    have hv : v < (radixLayoutProfile 3 k).arity i := by
      rw [radixLayout_arity hk (by simpa using hi)]
      simp only [seedTestTemplates,List.mem_flatMap,List.mem_append,List.mem_map,
        Prod.mk.injEq] at htemp
      rcases htemp with ⟨⟨u,b⟩,_,⟨a,_,_,rfl,rfl⟩ | ⟨a,_,_,rfl,rfl⟩⟩
      · rw [if_pos b.isLt]; exact (pEquiv a).isLt
      · rw [if_neg (by omega),if_pos (by omega)]; exact (qEquiv a).isLt
    let t' : Fin 2 := ⟨t,ht⟩
    let i' : Column (S).system := ⟨i,by change i < (S).width; rwa [tailRefinement_width]⟩
    let v' : Letter (S).system i' := ⟨v,hv⟩
    refine ⟨t',i',v',?_,?_⟩
    · rw [tailSeedTest_matches hk (by decide : 0 < 3) c]
      exact (seedTest_template hk t' hi hv).mp htemp
    · rw [sharedSeed_indices]
      exact hx
  · rintro ⟨t,i,v,h,hx⟩
    have hi : i.val < 18+2*k := by
      have h : i.val < (S).width := i.isLt
      rwa [tailRefinement_width] at h
    have hv : v.val < (radixLayoutProfile 3 k).arity i.val := v.isLt
    have htemp := (seedTest_template hk t hi hv).mpr
      (fun hp => h ((tailSeedTest_matches hk (by decide : 0 < 3) c t i v).mpr hp))
    exact List.mem_map.mpr ⟨(t.val,i.val,v.val),htemp,(sharedSeed_indices hk c t i v).symm.trans hx⟩

end
end TranslationTiling.FiniteCompiler.Packed
