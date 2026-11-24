import TranslationTiling.FiniteCompiler.Effective.FourValueColumn

namespace TranslationTiling.FiniteCompiler.Packed

open Compiler Compiler.Effective Effective SharedCoordinates PairSmall GuardedCompiler
open scoped Classical

noncomputable section

local instance fourValueExclusionsFrame : SeedFrame := compactSeedFrame
attribute [local instance] ColumnRefinement.family
set_option maxRecDepth 2500
set_option maxHeartbeats 3000000

def fourValueHolds (k : ℕ) (o : FourValueOutputGraph k) (F : CyclicTile) : Prop :=
  FiniteCompiler.Tiles (F.toFinset.image (decodePoint (fourValueLayout k)))
    (Set.range (SharedCoordinates.point (fourValueLayout k) o))

variable {T : LeanWang.TileSet} {k : ℕ} (hk : 0 < k)
  (c : Code T (radixLayoutProfile 4 k).radices.prod)

local instance fourValueExclusionsAlphabet : AlphabetFamily (system c) := GuardedCompiler.alphabet c
local notation "S" => fourValueRefinement hk c

theorem fourValuePatternActivity (o : FourValueOutputGraph k)
    (hd : HasFourValueDependence k (tailSlopes k) o)
    (q : PartialTest (S).system) (hne : q.columns.Nonempty) :
    letI : NeZero q.columns.card := ⟨(Finset.card_pos.mpr hne).ne'⟩
    (∀ F ∈ fourValueCycle k
      (fourValueAssignments (fourValuePatternCycle hk c q) (fourValuePatternLabel hk c q)),
      fourValueHolds k o F) ↔
      ∀ x, ∃ i : q.columns, ¬ fourValueColumnActive hk c o i.val (q.label i) x := by
  letI : NeZero q.columns.card := ⟨(Finset.card_pos.mpr hne).ne'⟩
  let p (j : ZMod q.columns.card) := testEquiv q ((ZMod.finEquiv q.columns.card).symm j)
  have hr (j : ZMod q.columns.card) : fourValuePatternCycle hk c q j =
      fourValueColumnRow hk c (p j).val := rfl
  have hv (j : ZMod q.columns.card) : fourValuePatternLabel hk c q j = (q.label (p j)).val := rfl
  dsimp only [fourValueHolds]
  rw [fourValueCycle_iff _ _
    (fun j => fourValueColumn_valid_wang hk c (p j).val (q.label (p j)))
    (fun j => fourValueColumn_valid_fixed hk c (p j).val (q.label (p j))) o hd]
  constructor
  · intro h x
    obtain ⟨j,hj⟩ := h x
    exact ⟨p j,hj⟩
  · intro h x
    obtain ⟨i,hi⟩ := h x
    refine ⟨(ZMod.finEquiv _ ) ((testEquiv q).symm i),?_⟩
    let inactive (j : q.columns) := ¬ fourValueColumnActive hk c o j.val (q.label j) x
    change inactive (testEquiv q ((ZMod.finEquiv q.columns.card).symm
      ((ZMod.finEquiv q.columns.card) ((testEquiv q).symm i))))
    rw [(ZMod.finEquiv q.columns.card).symm_apply_apply,(testEquiv q).apply_symm_apply]
    exact hi

theorem seedRow_digits (t : Fin 2) : (rowDigits (fourValueRows k) (fourValueSeedRow k t)).length = 1 := by
  unfold rowDigits
  rw [fourValueSeedRow_val,fourValueRows_seed_at]
  fin_cases t <;> rfl

theorem seedRow_is_not_wang (t : Fin 2) : ¬ IsWangRow (fourValueSeedRow k t) := by
  intro h
  have he : (fourValueRows k).length-2+t.val < (fourValueRows k).length-2 := h.2
  omega

private theorem seedCycle_zero (t : Fin 2) (i : Column (S).system) :
    fourValueSeedCycle hk c t i 0 = fourValueSeedRow k t := rfl

private theorem seedCycle_one (t : Fin 2) (i : Column (S).system) :
    fourValueSeedCycle hk c t i 1 = fourValueColumnRow hk c i := rfl

private theorem seed_subgroup_top (t : Fin 2) (hv : 0 < (rowDigits (fourValueRows k) (fourValueSeedRow k t)).length) :
    fourValueDigitSubgroup (fourValueSeedRow k t) ⟨0,hv⟩ = ⊤ := by
  ext z
  simp only [fourValueDigitSubgroup_iff,AddSubgroup.mem_top,iff_true]
  intro q hq
  apply False.elim
  apply hq
  apply Fin.ext
  have ho := q.isLt
  have hl := seedRow_digits (k := k) t
  dsimp only
  omega

theorem fourValueSeedActivity (o : FourValueOutputGraph k)
    (hd : HasFourValueDependence k (tailSlopes k) o)
    (t : Fin 2) (i : Column (S).system) (v : Letter (S).system i) :
    (∀ F ∈ fourValueCycle k
      (fourValueAssignments (fourValueSeedCycle hk c t i) (fourValueSeedCycleLabel hk c t i v)),
      fourValueHolds k o F) ↔
      ∀ x, ¬ (DigitActive (fourValuePrivateAt o x (fourValueSeedRow k t)) ⊤ ∧
        fourValueColumnActive hk c o i v x) := by
  let cy := fourValueSeedCycle hk c t i
  let lab := fourValueSeedCycleLabel hk c t i v
  have hf : ¬ IsWangRow (fourValueSeedRow k t) := seedRow_is_not_wang t
  have hl : 0 < (rowDigits (fourValueRows k) (fourValueSeedRow k t)).length := by
    rw [seedRow_digits]
    decide
  have hw (j : ZMod 2) : IsWangRow (cy j) → lab j < 4 := by
    fin_cases j
    · exact fun h => (hf h).elim
    · exact fourValueColumn_valid_wang hk c i v
  have ha (j : ZMod 2) : ¬ IsWangRow (cy j) → lab j < (rowDigits (fourValueRows k) (cy j)).length := by
    fin_cases j
    · exact fun _ => hl
    · exact fourValueColumn_valid_fixed hk c i v
  dsimp only [fourValueHolds]
  rw [fourValueCycle_iff cy lab hw ha o hd]
  have h0 (x : Plane) : DigitActive (fun d => fourValueCycleRead (cy 0) (lab 0) (hw 0)
        (fourValuePrivateAt o x (cy 0) d)) (fourValueCycleSubgroup (cy 0) (lab 0) (ha 0)) ↔
      DigitActive (fourValuePrivateAt o x (fourValueSeedRow k t)) ⊤ := by
    change DigitActive (fun d => fourValueCycleRead (fourValueSeedRow k t) 0 _
        (fourValuePrivateAt o x (fourValueSeedRow k t) d)) (fourValueCycleSubgroup _ 0 _) ↔ _
    rw [cycle_active_fixed_iff (fourValueSeedRow k t) ⟨0,hl⟩ hf,seed_subgroup_top]
  constructor
  · intro h x hab
    obtain ⟨j,hj⟩ := h x
    fin_cases j
    · exact hj ((h0 x).mpr hab.1)
    · exact hj hab.2
  · intro h x
    by_cases ht : DigitActive (fourValuePrivateAt o x (fourValueSeedRow k t)) ⊤
    · exact ⟨1,fun hi => h x ⟨ht,hi⟩⟩
    · exact ⟨0,fun h' => ht ((h0 x).mp h')⟩

end
end TranslationTiling.FiniteCompiler.Packed
