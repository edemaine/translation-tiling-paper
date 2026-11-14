import TranslationTiling.FiniteCompiler.Effective.MixedCode

namespace TranslationTiling.FiniteCompiler.Effective
open Compiler.Effective
open scoped Classical
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem natLog_primrec (b : ℕ) (hb : 1 < b) : Primrec (Nat.log b) := by
  apply Primrec.of_graph (f := Nat.log b)
    ⟨fun n => n+1, by fun_prop, fun n => (Nat.log_le_self b n).trans (Nat.le_succ n)⟩
  have h : PrimrecPred (fun z : ℕ × ℕ =>
      (z.1 = 0 ∧ z.2 = 0) ∨ (z.1 ≠ 0 ∧ b ^ z.2 ≤ z.1 ∧ z.1 < b ^ (z.2+1))) := by fun_prop
  apply h.of_eq
  intro z
  by_cases hz : z.1 = 0
  · simp [hz,eq_comm]
  · simp only [hz,false_and,false_or,not_false_eq_true,true_and]
    exact (and_iff_right hz).trans (Nat.log_eq_iff (Or.inr ⟨hb,hz⟩)).symm

@[fun_prop] theorem mixedPayloadWidth_primrec : Primrec mixedPayloadWidth := by
  unfold mixedPayloadWidth
  have h2 := natLog_primrec 2 (by decide)
  have h3 := natLog_primrec 3 (by decide)
  fun_prop

@[fun_prop] theorem mixedWidth_primrec : Primrec mixedWidth := by unfold mixedWidth; fun_prop

/-- Numerical mixed-radix code, including its two-position seed prefix. -/
def rawMixedCode (T : LeanWang.TileSet) (s : RawSymbol) (k : ℕ) : ℕ :=
  let c := rawTag s.1 s.2.1
  if k < 2 then if c = 2 then k else c
  else if c = 2 then
    ((s.1 * Sudoku.q + s.2.1) * T.length + T.idxOf s.2.2) / 3 ^ (k-2) % 3
  else if (T.idxOf s.2.2).testBit (k-2) then 2 else c

@[fun_prop] theorem rawMixedCode_primrec :
    Primrec (fun z : LeanWang.TileSet × RawSymbol × ℕ => rawMixedCode z.1 z.2.1 z.2.2) := by
  unfold rawMixedCode
  fun_prop

theorem rawMixedCode_eq (T : LeanWang.TileSet) (s : Sudoku.Symbol T)
    (k : Fin (mixedWidth T.length)) :
    rawMixedCode T (rawSymbol s) k.val = (mixedWord T s k).val := by
  have htag := tag_eq_raw s
  generalize hc : TernarySystem.tag s = c at *
  fin_cases c
  all_goals
    have ht := htag.symm
    clear htag
    simp only [Fin.val_zero,Fin.val_one,Fin.val_ofNat,rawSymbol] at ht
    simp [rawMixedCode,mixedWord,mixedPrefix,hc,ht,mixedIndex,arithmeticIndex,rawSymbol]
  all_goals split_ifs <;> rfl

def mixedEncodedWord (T : LeanWang.TileSet) (w : RawWord) : List ℕ :=
  (List.range (Sudoku.Width * mixedWidth T.length)).map fun k =>
    rawMixedCode T (rawWordAt w (k / mixedWidth T.length)) (k % mixedWidth T.length)

@[fun_prop] theorem mixedEncodedWord_primrec :
    Primrec (fun z : LeanWang.TileSet × RawWord => mixedEncodedWord z.1 z.2) := by
  unfold mixedEncodedWord
  apply mapList (by fun_prop)
  fun_prop

def mixedPayload (T : LeanWang.TileSet) : Payload :=
  ((List.range (Sudoku.Width * mixedWidth T.length)).map (fun k => ((k / mixedWidth T.length : ℕ) : ℤ)),
    (goodRawWords T).map (mixedEncodedWord T), ([0,2],[1,2]))

theorem mixedPayload_primrec : Primrec mixedPayload := by
  unfold mixedPayload
  have hslopes : Primrec (fun T : LeanWang.TileSet =>
      (List.range (Sudoku.Width * mixedWidth T.length)).map fun k => ((k / mixedWidth T.length : ℕ) : ℤ)) := by
    fun_prop
  have hwords : Primrec (fun T : LeanWang.TileSet => (goodRawWords T).map (mixedEncodedWord T)) := by
    fun_prop
  exact hslopes.pair (hwords.pair (Primrec.const _))

theorem mixedEncodedWord_eq (T : LeanWang.TileSet) (w : Compiler.Word T) :
    mixedEncodedWord T (rawWord w) = List.ofFn (fun k : Column (mixedSystem T) =>
      ((mixedCode T).word (w (finProdFinEquiv.symm k).1)
        (finProdFinEquiv.symm k).2).val) := by
  apply List.ext_getElem
  · simp only [mixedEncodedWord,List.length_map,List.length_range,List.length_ofFn]; rfl
  · intro k hk hk'
    simp only [mixedEncodedWord, List.getElem_map, List.getElem_range, List.getElem_ofFn]
    have hk0 : k < Sudoku.Width * mixedWidth T.length := by simpa [mixedEncodedWord] using hk
    have hl : 0 < mixedWidth T.length := by unfold mixedWidth; omega
    have hi : k / mixedWidth T.length < Sudoku.Width := (Nat.div_lt_iff_lt_mul hl).mpr hk0
    simp only [rawWordAt, Nat.mod_eq_of_lt hi, rawWord]
    rw [rawMixedCode_eq T _ ⟨k % mixedWidth T.length, Nat.mod_lt _ hl⟩]
    rfl

private theorem mixedEncodedWord_match (T : LeanWang.TileSet) (w : Compiler.Word T)
    (v : Word (mixedSystem T)) :
    mixedEncodedWord T (Compiler.Effective.rawWord w) = wordList v ↔
      ∀ i b, v (TaggedSystem.flat i b) = (mixedCode T).word (w i) b := by
  rw [mixedEncodedWord_eq,wordList,List.ofFn_inj]
  constructor
  · intro h i b
    apply Fin.ext
    have hi := congrFun h (TaggedSystem.flat i b)
    simpa only [TaggedSystem.flat,Equiv.symm_apply_apply] using hi.symm
  · intro h
    funext k
    have hk : TaggedSystem.flat (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2 = k :=
      finProdFinEquiv.apply_symm_apply k
    simpa only [hk] using congrArg Fin.val (h (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2).symm

theorem mixedPayload_correct (T : LeanWang.TileSet) :
    PayloadCorrect (mixedSystem T) (mixedPayload T) := by
  constructor
  · intro n
    have hn : n.val < ((mixedPayload T).1).length := by
      simpa only [mixedPayload,List.length_map,List.length_range,mixedSystem,
        TaggedSystem.system,mixedWidth] using n.isLt
    rw [List.getD_eq_getElem _ _ hn]
    simp only [mixedPayload,List.getElem_map,List.getElem_range,mixedSystem,TaggedSystem.system]
    rfl
  constructor
  · intro v
    change wordList v ∈ (goodRawWords T).map (mixedEncodedWord T) ↔ _
    simp only [List.mem_map,mem_goodRawWords]
    constructor
    · rintro ⟨w,⟨v',rfl,hv'⟩,he⟩
      exact ⟨v',hv',(mixedEncodedWord_match T v' v).mp he⟩
    · rintro ⟨v',hv',he⟩
      exact ⟨Compiler.Effective.rawWord v',⟨v',rfl,hv'⟩,(mixedEncodedWord_match T v' v).mpr he⟩
  · intro t j
    change Fin 3 at j
    fin_cases t
    · change (j.val ∈ ([0,2] : List ℕ)) ↔ j = 0 ∨ j = 2
      fin_cases j <;> decide
    · change (j.val ∈ ([1,2] : List ℕ)) ↔ j = 1 ∨ j = 2
      fin_cases j <;> decide

end
end TranslationTiling.FiniteCompiler.Effective
