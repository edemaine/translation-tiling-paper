import TranslationTiling.FiniteCompiler.Effective.FourValueCycleCorrect
import TranslationTiling.FiniteCompiler.Effective.FourValueSeeds
import TranslationTiling.FiniteCompiler.Effective.PackedPatternCorrect

namespace TranslationTiling.FiniteCompiler.Packed

open Effective PairSmall GuardedCompiler
open scoped Classical

noncomputable section

local instance fourValuePatternsFrame : SeedFrame := compactSeedFrame
attribute [local instance] ColumnRefinement.family
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000

variable {T : LeanWang.TileSet} {k : ℕ} (hk : 0 < k)
  (c : Code T (radixLayoutProfile 4 k).radices.prod)

local instance fourValuePatternAlphabet : AlphabetFamily (system c) := GuardedCompiler.alphabet c

abbrev fourValueRefinement := tailRefinement hk (by decide : 0 < 4) c

local notation "S" => fourValueRefinement hk c

include hk in
theorem fourValueRows_arity (i : ℕ) (hi : i < 18) :
    (rowDigits (fourValueRows k) i).length = (radixLayoutProfile 4 k).arity i := by
  rw [radixLayout_arity hk (by simpa using (show i < 18+2*k by omega))]
  unfold rowDigits
  rw [fourValueRows_fixed_at hi]
  exact (by decide +kernel : ∀ j : Fin 18, (sharedArithmeticRow j).2.2.length =
    if j.val < 9 then 4 else if j.val < 18 then 6 else 4) ⟨i,hi⟩

def fourValueColumnRow : Column (S).system ↪ FourValueRow k where
  toFun i := ⟨i.val,by
    have h : i.val < (S).width := i.isLt
    rw [tailRefinement_width] at h
    rw [fourValueRows_length]
    omega⟩
  inj' _ _ h := Fin.ext (congrArg (fun j : FourValueRow k => j.val) h)

@[simp] theorem fourValueColumnRow_val (i : Column (S).system) :
    (fourValueColumnRow hk c i).val = i.val := rfl

theorem fourValueColumnRow_lt (i : Column (S).system) :
    (fourValueColumnRow hk c i).val < (fourValueRows k).length-2 := by
  have h : i.val < (S).width := i.isLt
  rw [tailRefinement_width] at h
  simp only [fourValueColumnRow_val,fourValueRows_length]
  omega

def fourValueColumnOfRow (i : FourValueRow k) (hi : i.val < (fourValueRows k).length-2) : Column (S).system :=
  ⟨i.val,by change i.val < (S).width; rw [tailRefinement_width]; have := fourValueRows_length k; omega⟩

@[simp] theorem fourValueColumnOfRow_val (i : FourValueRow k) (hi : i.val < (fourValueRows k).length-2) :
    (fourValueColumnOfRow hk c i hi).val = i.val := rfl

theorem fourValueColumn_slope (i : Column (S).system) :
    (S).system.slope i = (tailSlopes k).getD i.val 0 := by
  rw [show (S).system.slope i = ((radixLayoutProfile 4 k).slope i.val : ℤ) from
    (packedRadix_layout _ hk (by decide) rfl).slope i]
  have hi : i.val < 18+2*k := by
    have h : i.val < (S).width := i.isLt
    rwa [tailRefinement_width] at h
  simp only [tailSlopes,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_range hi,
    Option.map_some,Option.getD_some,ternaryLayoutProfile]
  simp only [Profile.slope,radixLayoutProfile,List.length_replicate]

def fourValuePatternCycle (q : PartialTest (S).system) [NeZero q.columns.card] :
    ZMod q.columns.card ↪ FourValueRow k :=
  ((ZMod.finEquiv q.columns.card).symm.toEmbedding.trans (testEmbedding q)).trans (fourValueColumnRow hk c)

def fourValuePatternLabel (q : PartialTest (S).system) [NeZero q.columns.card] (j : ZMod q.columns.card) : ℕ :=
  (q.label (testEquiv q ((ZMod.finEquiv q.columns.card).symm j))).val

theorem fourValuePattern_indices (b : PartialTest (system c)) :
    let q := (S).expand b
    expandMask 4 k (testMask c b) = if h : q.columns.Nonempty then
      letI : NeZero q.columns.card := ⟨(Finset.card_pos.mpr h).ne'⟩
      fourValueAssignments (fourValuePatternCycle hk c q) (fourValuePatternLabel hk c q)
    else [] := by
  let q := (S).expand b
  dsimp only
  rw [numericalExpandedPattern_indices hk (by decide : 0 < 4) c b]
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

def fourValueSeedCycle (t : Fin 2) (i : Column (S).system) : ZMod 2 ↪ FourValueRow k where
  toFun j := if j = 0 then fourValueSeedRow k t else fourValueColumnRow hk c i
  inj' := by
    intro u v huv
    have hne : fourValueSeedRow k t ≠ fourValueColumnRow hk c i := by
      have hi := fourValueColumnRow_lt hk c i
      intro h
      rw [← h] at hi
      change (fourValueRows k).length-2+t.val < _ at hi
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

def fourValueSeedCycleLabel (t : Fin 2) (i : Column (S).system)
    (v : Letter (S).system i) (j : ZMod 2) : ℕ :=
  if j = 0 then 0 else v.val

theorem fourValueSeed_indices (t : Fin 2) (i : Column (S).system) (v : Letter (S).system i) :
    fourValueAssignments (fourValueSeedCycle hk c t i) (fourValueSeedCycleLabel hk c t i v) =
      [(18+2*k+t.val,0),(i.val,v.val)] := by
  unfold fourValueAssignments
  rw [List.ofFn_succ,List.ofFn_succ,List.ofFn_zero]
  change [((fourValueSeedRow k t).val,0),(i.val,v.val)] = _
  rw [fourValueSeedRow_val]

theorem fourValueTailSeedTests_iff (xs : GuardedAssignments) :
    xs ∈ tailSeedTests k ↔ ∃ (t : Fin 2) (i : Column (S).system) (v : Letter (S).system i),
      ¬ LetterSeedSet (S).system t i v ∧
        fourValueAssignments (fourValueSeedCycle hk c t i) (fourValueSeedCycleLabel hk c t i v) = xs := by
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
    have hv : v < (radixLayoutProfile 4 k).arity i := by
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
    · rw [tailSeedTest_matches hk (by decide : 0 < 4) c]
      exact (seedTest_template hk t' hi hv).mp htemp
    · rw [fourValueSeed_indices]
      exact hx
  · rintro ⟨t,i,v,h,hx⟩
    have hi : i.val < 18+2*k := by
      have h : i.val < (S).width := i.isLt
      rwa [tailRefinement_width] at h
    have hv : v.val < (radixLayoutProfile 4 k).arity i.val := v.isLt
    have htemp := (seedTest_template hk t hi hv).mpr
      (fun hp => h ((tailSeedTest_matches hk (by decide : 0 < 4) c t i v).mpr hp))
    exact List.mem_map.mpr ⟨(t.val,i.val,v.val),htemp,(fourValueSeed_indices hk c t i v).symm.trans hx⟩

end
end TranslationTiling.FiniteCompiler.Packed
