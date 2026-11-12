import TranslationTiling.FiniteCompiler.Effective.BitCode
import TranslationTiling.FiniteCompiler.Effective.ParameterSelection
import TranslationTiling.FiniteCompiler.BitSystem
import Mathlib.Data.List.OfFn

namespace TranslationTiling.FiniteCompiler.Effective

open Compiler.Effective
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
noncomputable section
local instance : Fact Sudoku.p.Prime := ⟨by decide⟩
local instance : Fact Sudoku.q.Prime := ⟨by decide⟩

/-- Slopes, allowed numerical words, and the two seed alphabets. -/
abbrev Payload := List ℤ × List (List ℕ) × (List ℕ × List ℕ)

private def unitOfFin {p : ℕ} [Fact p.Prime] (a : Fin p) (ha : a.val ≠ 0) : (ZMod p)ˣ :=
  Units.mk0 (a.val : ZMod p) (by
    intro he
    apply ha
    have h := congrArg ZMod.val he
    simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt a.isLt, ZMod.val_zero] using h)

/-- This lookup table is fixed, independent of the input Wang set and bit width. -/
def gammaLookup (z : Fin Sudoku.p × Fin Sudoku.q × Bool) : ℕ :=
  if ha : z.1.val = 0 then 0 else
    if hb : z.2.1.val = 0 then 0 else
      (BitSystem.gammaEquiv (unitOfFin z.1 ha, unitOfFin z.2.1 hb, z.2.2)).val

def gammaCode (a b : ℕ) (bit : Bool) : ℕ :=
  gammaLookup (⟨a % Sudoku.p,Nat.mod_lt _ (by decide)⟩,
    ⟨b % Sudoku.q,Nat.mod_lt _ (by decide)⟩,bit)

@[fun_prop] theorem gammaCode_primrec : Primrec (fun z : ℕ × ℕ × Bool =>
    gammaCode z.1 z.2.1 z.2.2) := by
  have ha : Primrec (fun z : ℕ × ℕ × Bool =>
      (⟨z.1 % Sudoku.p,Nat.mod_lt _ (by decide)⟩ : Fin Sudoku.p)) :=
    Primrec.fin_val_iff.mp (by fun_prop)
  have hb : Primrec (fun z : ℕ × ℕ × Bool =>
      (⟨z.2.1 % Sudoku.q,Nat.mod_lt _ (by decide)⟩ : Fin Sudoku.q)) :=
    Primrec.fin_val_iff.mp (by fun_prop)
  exact (finiteFunction_primrec gammaLookup).comp (ha.pair (hb.pair (by fun_prop)))

theorem gammaCode_eq {T : LeanWang.TileSet} (s : Sudoku.Symbol T) (bit : Bool) :
    gammaCode (rawSymbol s).1 (rawSymbol s).2.1 bit =
      (BitSystem.gammaEquiv (s.1,s.2.1,bit)).val := by
  have ha : s.1.val.val ≠ 0 := fun h => Units.ne_zero s.1 ((ZMod.val_eq_zero _).mp h)
  have hb : s.2.1.val.val ≠ 0 := fun h => Units.ne_zero s.2.1 ((ZMod.val_eq_zero _).mp h)
  simp only [gammaCode, rawSymbol, Nat.mod_eq_of_lt (ZMod.val_lt s.1.val),
    Nat.mod_eq_of_lt (ZMod.val_lt s.2.1.val), gammaLookup, ha, hb, ↓reduceDIte]
  have hua : unitOfFin (p := Sudoku.p) ⟨s.1.val.val,ZMod.val_lt s.1.val⟩ ha = s.1 := by
    apply Units.ext
    simp only [unitOfFin, Units.val_mk0]
    exact ZMod.natCast_zmod_val _
  have hub : unitOfFin (p := Sudoku.q) ⟨s.2.1.val.val,ZMod.val_lt s.2.1.val⟩ hb = s.2.1 := by
    apply Units.ext
    simp only [unitOfFin, Units.val_mk0]
    exact ZMod.natCast_zmod_val _
  rw [hua,hub]

def rawWordAt (w : RawWord) (k : ℕ) : RawSymbol :=
  w ⟨k % Sudoku.Width,Nat.mod_lt _ (by decide)⟩

@[fun_prop] theorem rawWordAt_primrec : Primrec (fun z : RawWord × ℕ => rawWordAt z.1 z.2) := by
  have hi : Primrec (fun z : RawWord × ℕ =>
      (⟨z.2 % Sudoku.Width,Nat.mod_lt _ (by decide)⟩ : Sudoku.Column)) :=
    Primrec.fin_val_iff.mp (by fun_prop)
  exact Primrec.fin_app.comp Primrec.fst hi

@[fun_prop] theorem idxOfRule {α β : Type*} [Primcodable α] [Primcodable β] [DecidableEq β]
    {x : α → β} {xs : α → List β} (hx : Primrec x) (hxs : Primrec xs) :
    Primrec (fun a => (xs a).idxOf (x a)) := Primrec.list_idxOf.comp hx hxs

attribute [local fun_prop] bitWidth_primrec indexedBit_primrec

def encodedWord (T : LeanWang.TileSet) (w : RawWord) : List ℕ :=
  (List.range (Sudoku.Width * bitWidth T)).map fun k =>
    let s := rawWordAt w (k / bitWidth T)
    gammaCode s.1 s.2.1 ((T.idxOf s.2.2).testBit (k % bitWidth T))

@[fun_prop] theorem encodedWord_primrec : Primrec (fun z : LeanWang.TileSet × RawWord =>
    encodedWord z.1 z.2) := by
  unfold encodedWord
  apply mapList (by fun_prop)
  fun_prop

def bitSystem (T : LeanWang.TileSet) : System := BitSystem.system (bitCode T) (by
  unfold bitWidth
  omega)

def goodRawWords (T : LeanWang.TileSet) : List RawWord :=
  (words T).filter fun w => decide (WordTest T w)

@[fun_prop] theorem goodRawWords_primrec : Primrec goodRawWords :=
  filterList words_primrec wordTest_primrec

theorem mem_goodRawWords (T : LeanWang.TileSet) (w : RawWord) :
    w ∈ goodRawWords T ↔ ∃ v : Compiler.Word T, rawWord v = w ∧ Compiler.Allowed T v := by
  simp only [goodRawWords, List.mem_filter, decide_eq_true_eq, mem_words]
  constructor
  · rintro ⟨⟨v,rfl⟩,hv⟩
    exact ⟨v,rfl,(wordTest_iff v).mp hv⟩
  · rintro ⟨v,rfl,hv⟩
    exact ⟨⟨v,rfl⟩,(wordTest_iff v).mpr hv⟩

/-- The seed tables have fixed finite domains and are input-independent. -/
def seedAlphabet (t : Fin 2) : List ℕ :=
  ((Finset.univ : Finset (Fin BitSystem.alphabet)).filter fun j =>
    (BitSystem.gammaEquiv.symm j).1.val = (t.val + 1 : ℕ) ∧
    (BitSystem.gammaEquiv.symm j).2.1.val = (t.val + 1 : ℕ)).toList.map Fin.val

def bitPayload (T : LeanWang.TileSet) : Payload :=
  ((List.range (Sudoku.Width * bitWidth T)).map (fun k => ((k / bitWidth T : ℕ) : ℤ)),
    (goodRawWords T).map (encodedWord T), (seedAlphabet 0,seedAlphabet 1))

theorem bitPayload_primrec : Primrec bitPayload := by
  unfold bitPayload
  have hslopes : Primrec (fun T : LeanWang.TileSet =>
      (List.range (Sudoku.Width * bitWidth T)).map fun k => ((k / bitWidth T : ℕ) : ℤ)) := by
    fun_prop
  have hwords : Primrec (fun T : LeanWang.TileSet => (goodRawWords T).map (encodedWord T)) := by
    fun_prop
  exact hslopes.pair (hwords.pair (Primrec.const _))

/-- The raw word uses the same fixed alphabet and column order as the checked
bit-channel construction. -/
theorem encodedWord_eq (T : LeanWang.TileSet) (w : Compiler.Word T) :
    encodedWord T (rawWord w) = List.ofFn (fun k : Column (bitSystem T) =>
      (BitSystem.symbolBit (bitCode T) (w (finProdFinEquiv.symm k).1)
        (finProdFinEquiv.symm k).2).val) := by
  apply List.ext_getElem
  · simp [encodedWord, bitSystem, BitSystem.system]
  · intro k hk hk'
    simp only [encodedWord, List.getElem_map, List.getElem_range, List.getElem_ofFn]
    have hk0 : k < Sudoku.Width * bitWidth T := by simpa [encodedWord] using hk
    have hl : 0 < bitWidth T := by unfold bitWidth; omega
    have hi : k / bitWidth T < Sudoku.Width := (Nat.div_lt_iff_lt_mul hl).mpr hk0
    simp only [rawWordAt, Nat.mod_eq_of_lt hi, rawWord]
    rw [gammaCode_eq]
    rfl

end
end TranslationTiling.FiniteCompiler.Effective
