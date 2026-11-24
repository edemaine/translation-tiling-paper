import TranslationTiling.FiniteCompiler.Effective.FourValueExclusions
import TranslationTiling.FiniteCompiler.Effective.FourValueModel
import TranslationTiling.FiniteCompiler.Effective.FourValueWangSound

namespace TranslationTiling.FiniteCompiler.Packed

open Compiler Compiler.Effective Effective SharedCoordinates PairSmall GuardedCompiler
open scoped Classical

noncomputable section

local instance fourValueSelectionFrame : SeedFrame := compactSeedFrame
attribute [local instance] ColumnRefinement.family
set_option maxRecDepth 2500
set_option maxHeartbeats 3000000

attribute [local irreducible] wangValueModulus fourValueLow fourValueOutput

theorem fourValueActivation_members (k : ℕ) (F : CyclicTile) :
    F ∈ fourValueActivation k ↔
      ((∃ (i : FourValueRow k), i.val < 18 ∧
        compactCodes (sharedEnvironment (fourValueRows k) i) ((tailSlopes k).getD i 0) = F) ∨
      (∃ w : WangDigitRow k, fourValueWangActivation k w = F)) ∨
      (∃ t : Fin 2, fourValueSeedRaw k t = F) := by
  simp only [fourValueActivation,List.mem_append,List.mem_map,List.mem_range]
  apply or_congr (or_congr ?_ ?_) ?_
  · constructor
    · rintro ⟨i,hi,rfl⟩
      exact ⟨⟨i,by have := fourValueRows_length k; omega⟩,hi,rfl⟩
    · rintro ⟨i,hi,rfl⟩
      exact ⟨i.val,hi,rfl⟩
  · exact ⟨fun ⟨i,hi,e⟩ => ⟨⟨i,hi⟩,e⟩,fun ⟨i,e⟩ => ⟨i.val,i.isLt,e⟩⟩
  · constructor
    · rintro ⟨t,ht,rfl⟩
      exact ⟨⟨t,ht⟩,by rw [fourValueSeedRaw,fourValueSeedRow_other]; rfl⟩
    · rintro ⟨t,rfl⟩
      exact ⟨t.val,t.isLt,by rw [fourValueSeedRaw,fourValueSeedRow_other]; rfl⟩

variable {T : LeanWang.TileSet} {k : ℕ} (hk : 0 < k)
  (c : Code T (radixLayoutProfile 4 k).radices.prod)

local instance fourValueSelectionAlphabet : AlphabetFamily (system c) := GuardedCompiler.alphabet c
local notation "S" => fourValueRefinement hk c

theorem fourValueColumn_coverage (o : FourValueOutputGraph k)
    (h : ∀ F ∈ fourValueActivation k, fourValueHolds k o F)
    (hd : HasFourValueDependence k (tailSlopes k) o) (i : Column (S).system) (x : Plane) :
    ∃ v : Letter (S).system i, fourValueColumnActive hk c o i v x := by
  let j := fourValueColumnRow hk c i
  by_cases hf : i.val < 18
  · obtain ⟨a,ha⟩ := fourValue_fixed_active j hf hd
      (h _ ((fourValueActivation_members k _).mpr (Or.inl (Or.inl ⟨j,hf,rfl⟩)))) x
    have hav := a.isLt
    change a.val < (rowDigits (fourValueRows k) i.val).length at hav
    rw [fourValueRows_arity hk i.val hf] at hav
    let v : Letter (S).system i := ⟨a.val,hav⟩
    exact ⟨v,(fourValueColumn_fixed_activity hk c o i v x hf).mpr ha⟩
  · have hw : IsWangRow j := ⟨Nat.le_of_not_gt hf,fourValueColumnRow_lt hk c i⟩
    let w := wangRowOf j hw
    obtain ⟨a,ha,hn⟩ := fourValue_wang_active w o hd
      (h _ ((fourValueActivation_members k _).mpr (Or.inl (Or.inr ⟨w,rfl⟩)))) x
    let u : Fin 4 := ⟨a.val-1,by have := ZMod.val_lt a; omega⟩
    have hv : (radixLayoutProfile 4 k).arity i.val = 4 := by
      rw [fourValueColumn_arity hk c i,if_neg (show ¬i.val < 9 by omega),if_neg hf]
    let v : Letter (S).system i := ⟨u.val,by
      change u.val < (radixLayoutProfile 4 k).arity i.val
      rw [hv]
      exact u.isLt⟩
    refine ⟨v,(fourValueColumn_wang_activity hk c o i v x (Nat.le_of_not_gt hf)).mpr ?_⟩
    change ¬ ∃ t, ∀ d, joinWangUseful w (0,(fourValuePrivateAt o x (wangDigitRow w) d).2) (labelIndex u) = t
    rw [labelIndex_inverse a ha]
    exact hn

private def wangColumn (w : WangDigitRow k) : Column (S).system :=
  fourValueColumnOfRow hk c (wangDigitRow w) (isWangRow_digit w).2

def fourValuePickerOfWord (W : WordArray (S).system) : FourValuePicker k where
  fixed i h z :=
    let col := fourValueColumnOfRow hk c i (by have := fourValueRows_length k; omega)
    ⟨(W col z).val,by
      rw [fourValueRows_arity hk i.val h]
      exact (W col z).isLt⟩
  wang w z :=
    let col := wangColumn hk c w
    have hw : 18 ≤ col.val := (isWangRow_digit w).1
    have hv := (W col z).isLt
    have ho : (W col z).val < 4 := by
      change _ < (radixLayoutProfile 4 k).arity col.val at hv
      rwa [fourValueColumn_arity hk c col,if_neg (by omega),if_neg (by omega)] at hv
    ⟨labelIndex ⟨(W col z).val,ho⟩,labelIndex_ne _⟩

theorem fourValueModel_column_activity (W : WordArray (S).system) (x : Plane)
    (i : Column (S).system) (v : Letter (S).system i) :
    fourValueColumnActive hk c (fourValueModel (fourValuePickerOfWord hk c W)) i v x ↔
      v = W i (lineValue (S).system i x) := by
  let pick := fourValuePickerOfWord hk c W
  let o := fourValueModel pick
  let j := fourValueColumnRow hk c i
  by_cases hf : i.val < 18
  · have hj : j.val < 18 := hf
    rw [fourValueColumn_fixed_activity hk c o i v x hf,fourValueModel_fixed_active pick j hj]
    have he : fourValueLineValue j x = lineValue (S).system i x := fourValueColumn_at hk c i x
    rw [he]
    constructor
    · intro h
      have he := congrArg (fun p : FourValueLabel j => p.val) h
      exact Fin.ext he
    · intro h
      have he := congrArg (fun p : Letter (S).system i => p.val) h
      exact Fin.ext he
  · let hw : IsWangRow j := ⟨Nat.le_of_not_gt hf,fourValueColumnRow_lt hk c i⟩
    let w := wangRowOf j hw
    let u : Fin 4 := ⟨v.val,fourValueColumn_valid_wang hk c i v hw⟩
    have hact := fourValueColumn_wang_activity hk c o i v x (Nat.le_of_not_gt hf)
    dsimp only at hact
    rw [hact]
    have hcol : wangColumn hk c w = i := Fin.ext (by
      have he := congrArg Fin.val (wangRowOf_eq j hw)
      exact he)
    have hs : wangLineValue w x = lineValue (S).system i x := by
      rw [← fourValueColumn_at hk c i x]
      change wangLineValue w x = fourValueLineValue j x
      rw [← wangRowOf_eq j hw]
      unfold fourValueLineValue wangLineValue
      rw [wangDigitRow_slope]
      split <;> rfl
    let a : WangChoice := ⟨labelIndex u,labelIndex_ne u⟩
    let b := pick.wang w (wangLineValue w x)
    have he (d : FourValueLow (wangDigitRow w)) :
        joinWangUseful w (0,(fourValuePrivateAt o x (wangDigitRow w) d).2) a.val =
          wangBlockOutput w b d a.val := by
      unfold fourValuePrivateAt
      rw [fourValueModel_wangPair]
      change joinWangUseful w (0,(wangModelPair pick w (x,Function.update 0 (wangDigitRow w) d)).2) a.val = _
      rw [← joinWangUseful_nonzero w a.val a.property (wangModelPair pick w _).1]
      rw [Prod.eta]
      unfold wangModelPair
      rw [AddEquiv.apply_symm_apply]
      change wangBlockOutput w b (Function.update
        (0 : ∀ j : FourValueRow k, FourValueLow j) (wangDigitRow w) d (wangDigitRow w)) a.val = _
      rw [Function.update_self]
    change (¬ ∃ t, ∀ d, joinWangUseful w (0,(fourValuePrivateAt o x (wangDigitRow w) d).2) a.val = t) ↔ _
    simp only [he,wang_block_active]
    have hb : b.val.val = (W i (lineValue (S).system i x)).val+1 := by
      change (labelIndex _).val = _
      rw [labelIndex_val,hs]
      have hcolval (z : ℤ) : (W (wangColumn hk c w) z).val = (W i z).val := by
        rw [hcol]
      rw [hcolval]
    constructor
    · intro h
      have heq := congrArg (fun e : WangChoice => e.val.val) h
      change (labelIndex u).val = _ at heq
      rw [labelIndex_val,hb] at heq
      exact Fin.ext (Nat.add_right_cancel heq)
    · intro h
      apply Subtype.ext
      apply ZMod.val_injective 5
      change (labelIndex u).val = b.val.val
      rw [labelIndex_val,hb]
      exact congrArg (·+1) (congrArg Fin.val h)

end
end TranslationTiling.FiniteCompiler.Packed
