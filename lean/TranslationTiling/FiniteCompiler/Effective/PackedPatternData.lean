import TranslationTiling.FiniteCompiler.PackedTernaryDigits
import TranslationTiling.FiniteCompiler.PackedCompiler
import TranslationTiling.FiniteCompiler.Effective.GuardedNumericalCorrect
import TranslationTiling.FiniteCompiler.Effective.BitCode

namespace TranslationTiling.FiniteCompiler.Packed

open Compiler.Effective
open Effective
open GuardedCompiler (rawSelection digits queryLabels Units5 Units7)
open scoped Classical

attribute [local fun_prop] LeanWang.WangTile.n_primrec LeanWang.WangTile.s_primrec
  LeanWang.WangTile.e_primrec LeanWang.WangTile.w_primrec

noncomputable section

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

local instance packedPatternDataPrimeFive : Fact (Nat.Prime 5) := ⟨by decide⟩
local instance packedPatternDataPrimeSeven : Fact (Nat.Prime 7) := ⟨by decide⟩

abbrev RawMask := List (Option ℕ)

/-- The arithmetic-only patterns do not depend on Wang tiles. -/
def arithmeticMasks : List RawMask :=
  (Sudoku.PartialWord.codes5.map (fun m =>
    List.ofFn (rawSelection (d:=1) (digits 5 m) (fun _ => none) (fun _ => none)))) ++
  (Sudoku.PartialWord.codes7.map (fun m =>
    List.ofFn (rawSelection (d:=1) (fun _ => none) (digits 7 m) (fun _ => none))))

abbrev QueryPhase := Fin 3 × Units5 × Units7

/-- Each mask starts with the arithmetic symbols that identify its query type. -/
def guardTemplates : List (ℕ × RawMask) :=
  (Finset.univ : Finset QueryPhase).toList.map fun z =>
    (z.1.val, (List.ofFn (rawSelection (d:=1) (queryLabels 5 z.1 z.2.1)
      (queryLabels 7 z.1 z.2.2) (fun _ => none))).take 18)

def rawBadQuery (j : ℕ) (u v : LeanWang.WangTile) : Prop :=
  ¬ if j = 0 then u=v else if j=1 then u.HMatches v else u.VMatches v

instance (j : ℕ) (u v : LeanWang.WangTile) : Decidable (rawBadQuery j u v) := by
  unfold rawBadQuery
  split_ifs <;> infer_instance

theorem rawBadQuery_primrec : PrimrecPred
    (fun z : ℕ × LeanWang.WangTile × LeanWang.WangTile => rawBadQuery z.1 z.2.1 z.2.2) := by
  let p (z : ℕ × LeanWang.WangTile × LeanWang.WangTile) :=
    (z.1 = 0 ∧ z.2.1 = z.2.2) ∨
    (z.1 = 1 ∧ z.2.1.e = z.2.2.w) ∨
    (z.1 ≠ 0 ∧ z.1 ≠ 1 ∧ z.2.1.n = z.2.2.s)
  have hp : PrimrecPred p := by unfold p; fun_prop
  apply hp.not.of_eq
  intro z
  unfold p rawBadQuery LeanWang.WangTile.HMatches LeanWang.WangTile.VMatches
  split_ifs with h0 h1 <;> simp_all

def rawGuardedMasks (T : LeanWang.TileSet) (D : ℕ) : List RawMask :=
  let fill := T.getD 0 ⟨0,0,0,0⟩
  arithmeticMasks ++ guardTemplates.flatMap fun (j,s) =>
    (List.range D).flatMap fun a =>
      ((List.range D).filter (fun b => decide (rawBadQuery j (T.getD a fill) (T.getD b fill)))).map
        fun b => s ++ [some a,some b]

@[local fun_prop] private theorem variableListDefault {α β : Type*} [Primcodable α] [Primcodable β]
    {f : α → List β} {g : α → ℕ} {d : α → β}
    (hf : Primrec f) (hg : Primrec g) (hd : Primrec d) :
    Primrec (fun z => (f z).getD (g z) (d z)) :=
  (Primrec.option_getD.comp (Primrec.list_getElem?.comp hf hg) hd).of_eq
    (fun _ => List.getD_eq_getElem?_getD.symm)

private abbrev MaskContext := (LeanWang.TileSet × ℕ) × (ℕ × RawMask)
private abbrev MaskRow := MaskContext × ℕ

theorem rawGuardedMasks_primrec :
    Primrec (fun z : LeanWang.TileSet × ℕ => rawGuardedMasks z.1 z.2) := by
  unfold rawGuardedMasks
  apply appendList (Primrec.const arithmeticMasks)
  apply flatMapList (Primrec.const guardTemplates)
  change Primrec (fun z : MaskContext =>
    (List.range z.1.2).flatMap fun a =>
      ((List.range z.1.2).filter (fun b =>
        decide (rawBadQuery z.2.1 (z.1.1.getD a (z.1.1.getD 0 ⟨0,0,0,0⟩))
          (z.1.1.getD b (z.1.1.getD 0 ⟨0,0,0,0⟩))))).map
            fun b => z.2.2 ++ [some a,some b])
  apply flatMapList (show Primrec (fun z : MaskContext => List.range z.1.2) by fun_prop)
  have htest : PrimrecPred (fun z : MaskRow × ℕ =>
      rawBadQuery z.1.1.2.1 (z.1.1.1.1.getD z.1.2 (z.1.1.1.1.getD 0 ⟨0,0,0,0⟩))
        (z.1.1.1.1.getD z.2 (z.1.1.1.1.getD 0 ⟨0,0,0,0⟩))) :=
    rawBadQuery_primrec.comp (show Primrec (fun z : MaskRow × ℕ =>
      (z.1.1.2.1,z.1.1.1.1.getD z.1.2 (z.1.1.1.1.getD 0 ⟨0,0,0,0⟩),
        z.1.1.1.1.getD z.2 (z.1.1.1.1.getD 0 ⟨0,0,0,0⟩))) by fun_prop)
  apply mapList (filterList (show Primrec (fun z : MaskRow => List.range z.1.1.2) by fun_prop) htest)
  fun_prop

def rawOrigin (k i : ℕ) : ℕ :=
  if i < 18 then i else if i < 18+k then 18 else 19

def expandMask (r k : ℕ) (m : RawMask) : GuardedAssignments :=
  ((List.range (18+2*k)).filter (fun i => (m.getD (rawOrigin k i) none).isSome)).map
    fun i => (i,radixDigit r k i ((m.getD (rawOrigin k i) none).getD 0))

@[fun_prop] theorem rawOrigin_primrec : Primrec (fun z : ℕ × ℕ => rawOrigin z.1 z.2) := by
  unfold rawOrigin
  fun_prop

@[fun_prop] theorem radixDigit_primrec :
    Primrec (fun z : ℕ × ℕ × ℕ × ℕ => radixDigit z.1 z.2.1 z.2.2.1 z.2.2.2) := by
  unfold radixDigit
  fun_prop

@[fun_prop] theorem expandMask_primrec : Primrec (fun z : ℕ × ℕ × RawMask => expandMask z.1 z.2.1 z.2.2) := by
  unfold expandMask
  have hm : Primrec (fun z : (ℕ × ℕ × RawMask) × ℕ => z.1.2.2.getD (rawOrigin z.1.2.1 z.2) none) := by fun_prop
  have hb : Primrec (fun z : (ℕ × ℕ × RawMask) × ℕ => (z.1.2.2.getD (rawOrigin z.1.2.1 z.2) none).isSome) :=
    Primrec.option_isSome.comp hm
  have hv : Primrec (fun z : (ℕ × ℕ × RawMask) × ℕ => (z.1.2.2.getD (rawOrigin z.1.2.1 z.2) none).getD 0) :=
    Primrec.option_getD.comp hm (Primrec.const 0)
  have htest : PrimrecPred (fun z : (ℕ × ℕ × RawMask) × ℕ =>
      (z.1.2.2.getD (rawOrigin z.1.2.1 z.2) none).isSome = true) :=
    (hb.of_eq (fun z => by cases h : (z.1.2.2.getD (rawOrigin z.1.2.1 z.2) none).isSome <;> simp [h])).primrecPred
  have hf := filterList (p := fun (z : ℕ × ℕ × RawMask) i => (z.2.2.getD (rawOrigin z.2.1 i) none).isSome = true)
    (show Primrec (fun z : ℕ × ℕ × RawMask => List.range (18+2*z.2.1)) by fun_prop) htest
  have hf' : Primrec (fun z : ℕ × ℕ × RawMask =>
      (List.range (18+2*z.2.1)).filter (fun i => (z.2.2.getD (rawOrigin z.2.1 i) none).isSome)) :=
    hf.of_eq (fun z => by simp only [Bool.decide_coe])
  apply mapList hf'
  fun_prop

/-- The excluded seed letters in the eighteen arithmetic columns. -/
def seedTestTemplates : List (ℕ × ℕ × ℕ) :=
  (Finset.univ : Finset (Fin 2 × Fin 9)).toList.flatMap fun (t,b) =>
    (((Finset.univ : Finset Units5).filter
      (fun u => ¬ GuardedCompiler.seedDigit 5 t u.val)).toList.map
        (fun u => (t.val,b.val,(PairSmall.pEquiv u).val))) ++
    (((Finset.univ : Finset Units7).filter
      (fun u => ¬ GuardedCompiler.seedDigit 7 t u.val)).toList.map
        (fun u => (t.val,9+b.val,(PairSmall.qEquiv u).val)))

def tailSeedTests (k : ℕ) : List GuardedAssignments :=
  seedTestTemplates.map fun (t,i,v) => [(18+2*k+t,0),(i,v)]

@[fun_prop] theorem tailSeedTests_primrec : Primrec tailSeedTests := by
  unfold tailSeedTests
  fun_prop

theorem tailSeedTests_length (k : ℕ) : (tailSeedTests k).length ≤ 180 := by
  rw [tailSeedTests,List.length_map]
  unfold seedTestTemplates
  rw [List.length_flatMap]
  calc
    _ ≤ ((Finset.univ : Finset (Fin 2 × Fin 9)).toList.map (fun _ => 10)).sum := by
      apply listSumMap_le
      rintro ⟨t,i⟩ _
      simp only [List.length_append,List.length_map,Finset.length_toList]
      have h5 := Finset.card_filter_le (s := (Finset.univ : Finset Units5)) (fun u => ¬ GuardedCompiler.seedDigit 5 t u.val)
      have h7 := Finset.card_filter_le (s := (Finset.univ : Finset Units7)) (fun u => ¬ GuardedCompiler.seedDigit 7 t u.val)
      rw [Finset.card_univ,Fintype.card_congr PairSmall.pEquiv,Fintype.card_fin] at h5
      rw [Finset.card_univ,Fintype.card_congr PairSmall.qEquiv,Fintype.card_fin] at h7
      omega
    _ = 180 := by simp

end
end TranslationTiling.FiniteCompiler.Packed
