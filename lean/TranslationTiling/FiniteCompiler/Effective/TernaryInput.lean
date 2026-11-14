import TranslationTiling.FiniteCompiler.Effective.BitInputCorrect
import TranslationTiling.FiniteCompiler.TernarySystem

namespace TranslationTiling.FiniteCompiler.Effective
open Compiler.Effective
open scoped Classical
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def arithmeticIndex {T : LeanWang.TileSet} (s : Sudoku.Symbol T) : ℕ :=
  s.1.val.val * Sudoku.q + s.2.1.val.val

theorem arithmeticIndex_lt {T : LeanWang.TileSet} (s : Sudoku.Symbol T) :
    arithmeticIndex s < 2 ^ 16 := by
  have ha := ZMod.val_lt s.1.val
  have hb := ZMod.val_lt s.2.1.val
  unfold arithmeticIndex
  norm_num [Sudoku.p, Sudoku.q] at *
  omega

def fullCode (T : LeanWang.TileSet) (s : Sudoku.Symbol T) (j : Fin (bitWidth T + 16)) : Bool :=
  if h : j.val < 16 then (arithmeticIndex s).testBit j.val
  else bitCode T s.2.2 ⟨j.val - 16, by omega⟩

theorem fullCode_injective (T : LeanWang.TileSet) : Function.Injective (fullCode T) := by
  intro s u h
  have hi : arithmeticIndex s = arithmeticIndex u := by
    apply Nat.eq_of_testBit_eq
    intro j
    by_cases hj : j < 16
    · simpa only [fullCode, hj, ↓reduceDIte] using congrFun h ⟨j, by omega⟩
    · have hp : 2 ^ 16 ≤ 2 ^ j := Nat.pow_le_pow_right (by decide) (by omega)
      rw [Nat.testBit_eq_false_of_lt ((arithmeticIndex_lt s).trans_le hp),
        Nat.testBit_eq_false_of_lt ((arithmeticIndex_lt u).trans_le hp)]
  have ht : s.2.2 = u.2.2 := by
    apply bitCode_injective T
    funext j
    have he := congrFun h ⟨j.val + 16, by omega⟩
    simpa only [fullCode, show ¬ j.val + 16 < 16 by omega, ↓reduceDIte,
      Nat.add_sub_cancel, Fin.eta] using he
  have hb := ZMod.val_lt s.2.1.val
  have hb' := ZMod.val_lt u.2.1.val
  have haeq : s.1.val.val = u.1.val.val := by
    unfold arithmeticIndex at hi
    norm_num [Sudoku.q] at hi hb hb'
    omega
  have hbeq : s.2.1.val.val = u.2.1.val.val := by
    unfold arithmeticIndex at hi
    rw [haeq] at hi
    omega
  exact Prod.ext (Units.ext (ZMod.val_injective _ haeq))
    (Prod.ext (Units.ext (ZMod.val_injective _ hbeq)) ht)

def ternaryWidth (T : LeanWang.TileSet) : ℕ := bitWidth T + 16 + 2

@[fun_prop] theorem ternaryWidth_primrec : Primrec ternaryWidth :=
  natAdd (natAdd bitWidth_primrec (Primrec.const 16)) (Primrec.const 2)

def ternarySystem (T : LeanWang.TileSet) : System := TernarySystem.system (fullCode T)

def rawTag (a b : ℕ) : ℕ := if a = 1 ∧ b = 1 then 0 else if a = 2 ∧ b = 2 then 1 else 2

@[fun_prop] theorem rawTag_primrec : Primrec (fun z : ℕ × ℕ => rawTag z.1 z.2) := by
  unfold rawTag
  fun_prop

theorem tag_eq_raw {T : LeanWang.TileSet} (s : Sudoku.Symbol T) :
    (TernarySystem.tag s).val = rawTag (rawSymbol s).1 (rawSymbol s).2.1 := by
  have hs (t : Fin 2) : Compiler.SeedSet t s ↔
      s.1.val.val = t.val + 1 ∧ s.2.1.val.val = t.val + 1 := by
    fin_cases t <;> unfold Compiler.SeedSet
    all_goals
      constructor
      · rintro ⟨ha,hb⟩
        exact ⟨congrArg ZMod.val ha,congrArg ZMod.val hb⟩
      · rintro ⟨ha,hb⟩
        exact ⟨ZMod.val_injective _ ha,ZMod.val_injective _ hb⟩
  have h0 := hs 0
  have h1 := hs 1
  norm_num only [Fin.val_zero,Fin.val_one,Nat.reduceAdd] at h0 h1
  by_cases ha : s.1.val.val = 1 ∧ s.2.1.val.val = 1
  · simp [TernarySystem.tag,h0,h1,ha,rawTag,rawSymbol]
  · by_cases hb : s.1.val.val = 2 ∧ s.2.1.val.val = 2
    · simp [TernarySystem.tag,h0,h1,ha,hb,rawTag,rawSymbol]
    · simp [TernarySystem.tag,h0,h1,ha,hb,rawTag,rawSymbol]

/-- Numerical version of the checked prefix and payload encoder. -/
def rawTernaryCode (T : LeanWang.TileSet) (s : RawSymbol) (k : ℕ) : ℕ :=
  let c := rawTag s.1 s.2.1
  if k < 2 then if c = 2 then k else c
  else
    let bit := if k - 2 < 16 then (s.1 * Sudoku.q + s.2.1).testBit (k - 2)
      else (T.idxOf s.2.2).testBit (k - 2 - 16)
    if bit then 2 else if c = 1 then 1 else 0

@[fun_prop] theorem rawTernaryCode_primrec :
    Primrec (fun z : LeanWang.TileSet × RawSymbol × ℕ => rawTernaryCode z.1 z.2.1 z.2.2) := by
  unfold rawTernaryCode
  fun_prop

theorem rawTernaryCode_eq (T : LeanWang.TileSet) (s : Sudoku.Symbol T)
    (k : Fin (bitWidth T + 16 + 2)) :
    rawTernaryCode T (rawSymbol s) k.val = (TernarySystem.symbolBit (fullCode T) s k).val := by
  have htag := tag_eq_raw s
  generalize hc : TernarySystem.tag s = c at *
  fin_cases c
  all_goals
    have ht := htag.symm
    clear htag
    simp only [Fin.val_zero,Fin.val_one,Fin.val_ofNat,rawSymbol] at ht
    simp [rawTernaryCode,TernarySystem.symbolBit,TernarySystem.encode,hc,ht,
      fullCode,bitCode,arithmeticIndex,rawSymbol]
  all_goals split_ifs <;> rfl

def ternaryEncodedWord (T : LeanWang.TileSet) (w : RawWord) : List ℕ :=
  (List.range (Sudoku.Width * ternaryWidth T)).map fun k =>
    rawTernaryCode T (rawWordAt w (k / ternaryWidth T)) (k % ternaryWidth T)

@[fun_prop] theorem ternaryEncodedWord_primrec :
    Primrec (fun z : LeanWang.TileSet × RawWord => ternaryEncodedWord z.1 z.2) := by
  unfold ternaryEncodedWord
  apply mapList (by fun_prop)
  fun_prop

def ternaryPayload (T : LeanWang.TileSet) : Payload :=
  ((List.range (Sudoku.Width * ternaryWidth T)).map (fun k => ((k / ternaryWidth T : ℕ) : ℤ)),
    (goodRawWords T).map (ternaryEncodedWord T), ([0,2],[1,2]))

theorem ternaryPayload_primrec : Primrec ternaryPayload := by
  unfold ternaryPayload
  have hslopes : Primrec (fun T : LeanWang.TileSet =>
      (List.range (Sudoku.Width * ternaryWidth T)).map fun k => ((k / ternaryWidth T : ℕ) : ℤ)) := by
    fun_prop
  have hwords : Primrec (fun T : LeanWang.TileSet => (goodRawWords T).map (ternaryEncodedWord T)) := by
    fun_prop
  exact hslopes.pair (hwords.pair (Primrec.const _))

theorem ternaryEncodedWord_eq (T : LeanWang.TileSet) (w : Compiler.Word T) :
    ternaryEncodedWord T (rawWord w) = List.ofFn (fun k : Column (ternarySystem T) =>
      (TernarySystem.symbolBit (fullCode T) (w (finProdFinEquiv.symm k).1)
        (finProdFinEquiv.symm k).2).val) := by
  apply List.ext_getElem
  · simp only [ternaryEncodedWord,List.length_map,List.length_range,List.length_ofFn]; rfl
  · intro k hk hk'
    simp only [ternaryEncodedWord, List.getElem_map, List.getElem_range, List.getElem_ofFn]
    have hk0 : k < Sudoku.Width * ternaryWidth T := by simpa [ternaryEncodedWord] using hk
    have hl : 0 < ternaryWidth T := by unfold ternaryWidth; omega
    have hi : k / ternaryWidth T < Sudoku.Width := (Nat.div_lt_iff_lt_mul hl).mpr hk0
    simp only [rawWordAt, Nat.mod_eq_of_lt hi, rawWord]
    rw [rawTernaryCode_eq T _ ⟨k % ternaryWidth T, Nat.mod_lt _ hl⟩]
    rfl

private theorem ternaryEncodedWord_match (T : LeanWang.TileSet) (w : Compiler.Word T)
    (v : Word (ternarySystem T)) :
    ternaryEncodedWord T (Compiler.Effective.rawWord w) = wordList v ↔
      ∀ i b, v (TernarySystem.flat i b) = TernarySystem.symbolBit (fullCode T) (w i) b := by
  rw [ternaryEncodedWord_eq,wordList,List.ofFn_inj]
  constructor
  · intro h i b
    apply Fin.ext
    have hi := congrFun h (TernarySystem.flat i b)
    simpa only [TernarySystem.flat,Equiv.symm_apply_apply] using hi.symm
  · intro h
    funext k
    have hk : TernarySystem.flat (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2 = k :=
      finProdFinEquiv.apply_symm_apply k
    simpa only [hk] using congrArg Fin.val (h (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2).symm

theorem ternaryPayload_correct (T : LeanWang.TileSet) :
    PayloadCorrect (ternarySystem T) (ternaryPayload T) := by
  constructor
  · intro n
    have hn : n.val < ((ternaryPayload T).1).length := by
      simpa only [ternaryPayload,List.length_map,List.length_range,ternarySystem,
        TernarySystem.system,ternaryWidth] using n.isLt
    rw [List.getD_eq_getElem _ _ hn]
    simp only [ternaryPayload,List.getElem_map,List.getElem_range,ternarySystem,TernarySystem.system]
    rfl
  constructor
  · intro v
    change wordList v ∈ (goodRawWords T).map (ternaryEncodedWord T) ↔ _
    simp only [List.mem_map,mem_goodRawWords]
    constructor
    · rintro ⟨w,⟨v',rfl,hv'⟩,he⟩
      exact ⟨v',hv',(ternaryEncodedWord_match T v' v).mp he⟩
    · rintro ⟨v',hv',he⟩
      exact ⟨Compiler.Effective.rawWord v',⟨v',rfl,hv'⟩,(ternaryEncodedWord_match T v' v).mpr he⟩
  · intro t j
    change Fin 3 at j
    fin_cases t
    · change (j.val ∈ ([0,2] : List ℕ)) ↔ j = 0 ∨ j = 2
      fin_cases j <;> decide
    · change (j.val ∈ ([1,2] : List ℕ)) ↔ j = 1 ∨ j = 2
      fin_cases j <;> decide

end
end TranslationTiling.FiniteCompiler.Effective
