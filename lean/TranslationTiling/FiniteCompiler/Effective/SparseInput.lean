import TranslationTiling.FiniteCompiler.SparseTernaryModel
import TranslationTiling.FiniteCompiler.Effective.JointInput
import TranslationTiling.FiniteCompiler.Effective.Correctness

namespace TranslationTiling.FiniteCompiler.Effective
open Compiler.Effective SparseTernary
open scoped Classical
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

@[fun_prop] theorem sparseTileWidth_primrec : Primrec SparseTernary.tileWidth := by
  unfold SparseTernary.tileWidth
  have hl := natLog_primrec 3 (by decide)
  fun_prop

@[fun_prop] theorem sparseWidth_primrec : Primrec SparseTernary.width := by
  unfold SparseTernary.width
  fun_prop

def sparsePosition (i : ℕ) : ℕ := [1,5,7].getD i 0

@[fun_prop] theorem sparsePosition_primrec : Primrec sparsePosition := by
  unfold sparsePosition
  fun_prop

@[simp] theorem sparsePosition_eq (i : Sudoku.Sparse.TileColumn) :
    sparsePosition i.val=Sudoku.Sparse.position i := by fin_cases i <;> rfl

def sparseRawSlope (n j : ℕ) : ℤ :=
  if j<48 then (j/3:ℕ) else
  if j<48+3*SparseTernary.tileWidth n then sparsePosition ((j-48)/SparseTernary.tileWidth n) else 0

@[fun_prop] theorem sparseRawSlope_primrec : Primrec (fun z : ℕ×ℕ => sparseRawSlope z.1 z.2) := by
  unfold sparseRawSlope
  fun_prop

def sparseRawDigit (T : LeanWang.TileSet) (w : RawWord) (j : ℕ) : ℕ :=
  if j<48 then
    let s := rawWordAt w (j/3)
    ((s.1-1)*6+(s.2.1-1))/3^(j%3)%3
  else if j<48+3*SparseTernary.tileWidth T.length then
    let s := rawWordAt w (sparsePosition ((j-48)/SparseTernary.tileWidth T.length))
    T.idxOf s.2.2 / 3^((j-48)%SparseTernary.tileWidth T.length) % 3
  else 0

@[fun_prop] theorem sparseRawDigit_primrec :
    Primrec (fun z : LeanWang.TileSet×RawWord×ℕ => sparseRawDigit z.1 z.2.1 z.2.2) := by
  unfold sparseRawDigit
  fun_prop

def sparseEncodedWord (T : LeanWang.TileSet) (w : RawWord) : List ℕ :=
  (List.range (SparseTernary.width T.length)).map (sparseRawDigit T w)

@[fun_prop] theorem sparseEncodedWord_primrec :
    Primrec (fun z : LeanWang.TileSet×RawWord => sparseEncodedWord z.1 z.2) := by
  unfold sparseEncodedWord
  fun_prop

def sparsePayload (T : LeanWang.TileSet) : Payload :=
  ((List.range (SparseTernary.width T.length)).map (sparseRawSlope T.length),
   (goodRawWords T).map (sparseEncodedWord T),([0,1,2],[0,1,2]))

@[fun_prop] theorem sparsePayload_primrec : Primrec sparsePayload := by
  unfold sparsePayload
  fun_prop

theorem sparseParameterData_computable :
    Computable (fun T => parameterData (SparseTernary.system T)) := by
  have hw : Primrec (fun T : LeanWang.TileSet => SparseTernary.width T.length) := by fun_prop
  have hc := parameterCertificate_computable.comp (hw.to_comp.pair (Computable.const 3))
  exact hw.to_comp.pair ((Computable.const _).pair hc)

def sparseInput (T : LeanWang.TileSet) : InputData :=
  (parameterData (SparseTernary.system T),sparsePayload T)

theorem sparseInput_computable : Computable sparseInput :=
  sparseParameterData_computable.pair sparsePayload_primrec.to_comp

end
end TranslationTiling.FiniteCompiler.Effective
