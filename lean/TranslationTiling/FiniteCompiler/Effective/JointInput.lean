import TranslationTiling.FiniteCompiler.Effective.JointCode

namespace TranslationTiling.FiniteCompiler.Effective
open Compiler.Effective
open scoped Classical
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def jointEncodedWord (T : LeanWang.TileSet) (w : RawWord) : List ℕ :=
  (List.range (Sudoku.Width * jointWidth T.length)).map fun k =>
    rawJointCode T (rawWordAt w (k / jointWidth T.length)) (k % jointWidth T.length)

@[fun_prop] theorem jointEncodedWord_primrec :
    Primrec (fun z : LeanWang.TileSet × RawWord => jointEncodedWord z.1 z.2) := by
  unfold jointEncodedWord
  apply mapList (by fun_prop)
  fun_prop

def jointPayload (T : LeanWang.TileSet) : Payload :=
  ((List.range (Sudoku.Width * jointWidth T.length)).map (fun k => ((k / jointWidth T.length : ℕ) : ℤ)),
    (goodRawWords T).map (jointEncodedWord T), ([0,1,2],[0,1,2]))

theorem jointPayload_primrec : Primrec jointPayload := by
  unfold jointPayload
  have hslopes : Primrec (fun T : LeanWang.TileSet =>
      (List.range (Sudoku.Width * jointWidth T.length)).map fun k => ((k / jointWidth T.length : ℕ) : ℤ)) := by
    fun_prop
  have hwords : Primrec (fun T : LeanWang.TileSet => (goodRawWords T).map (jointEncodedWord T)) := by
    fun_prop
  exact hslopes.pair (hwords.pair (Primrec.const _))

theorem jointEncodedWord_eq (T : LeanWang.TileSet) (w : Compiler.Word T) :
    jointEncodedWord T (rawWord w) = List.ofFn (fun k : Column (jointSystem T) =>
      ((jointCode T).word (w (finProdFinEquiv.symm k).1)
        (finProdFinEquiv.symm k).2).val) := by
  apply List.ext_getElem
  · simp only [jointEncodedWord,List.length_map,List.length_range,List.length_ofFn]; rfl
  · intro k hk hk'
    simp only [jointEncodedWord, List.getElem_map, List.getElem_range, List.getElem_ofFn]
    have hk0 : k < Sudoku.Width * jointWidth T.length := by simpa [jointEncodedWord] using hk
    have hl : 0 < jointWidth T.length := jointWidth_pos _
    have hi : k / jointWidth T.length < Sudoku.Width := (Nat.div_lt_iff_lt_mul hl).mpr hk0
    simp only [rawWordAt, Nat.mod_eq_of_lt hi, rawWord]
    rw [rawJointCode_eq T _ ⟨k % jointWidth T.length, Nat.mod_lt _ hl⟩]
    rfl

private theorem jointEncodedWord_match (T : LeanWang.TileSet) (w : Compiler.Word T)
    (v : Word (jointSystem T)) :
    jointEncodedWord T (Compiler.Effective.rawWord w) = wordList v ↔
      ∀ i b, v (JointSystem.flat i b) = (jointCode T).word (w i) b := by
  rw [jointEncodedWord_eq,wordList,List.ofFn_inj]
  constructor
  · intro h i b
    apply Fin.ext
    have hi := congrFun h (JointSystem.flat i b)
    simpa only [JointSystem.flat,TaggedSystem.flat,Equiv.symm_apply_apply] using hi.symm
  · intro h
    funext k
    have hk : JointSystem.flat (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2 = k :=
      finProdFinEquiv.apply_symm_apply k
    have he := h (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2
    rw [hk] at he
    exact congrArg Fin.val he.symm

theorem jointPayload_correct (T : LeanWang.TileSet) :
    PayloadCorrect (jointSystem T) (jointPayload T) := by
  constructor
  · intro n
    have hn : n.val < ((jointPayload T).1).length := by
      simpa only [jointPayload,List.length_map,List.length_range,jointSystem,
        JointSystem.system,jointWidth] using n.isLt
    rw [List.getD_eq_getElem _ _ hn]
    simp only [jointPayload,List.getElem_map,List.getElem_range,jointSystem,JointSystem.system]
    rfl
  constructor
  · intro v
    change wordList v ∈ (goodRawWords T).map (jointEncodedWord T) ↔ _
    simp only [List.mem_map,mem_goodRawWords]
    constructor
    · rintro ⟨w,⟨v',rfl,hv'⟩,he⟩
      exact ⟨v',hv',(jointEncodedWord_match T v' v).mp he⟩
    · rintro ⟨v',hv',he⟩
      exact ⟨Compiler.Effective.rawWord v',⟨v',rfl,hv'⟩,(jointEncodedWord_match T v' v).mpr he⟩
  · intro t j
    simp only [jointPayload,SeedSet,jointSystem,JointSystem.system,ite_self]
    fin_cases j <;> norm_num

end
end TranslationTiling.FiniteCompiler.Effective
