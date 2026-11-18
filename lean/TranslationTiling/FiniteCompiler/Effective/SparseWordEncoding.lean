import TranslationTiling.FiniteCompiler.Effective.SparseInput

namespace TranslationTiling.FiniteCompiler.Effective
open Compiler.Effective SparseTernary
open scoped Classical
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

theorem sparseRawSlope_eq (T : LeanWang.TileSet) (j : Fin (SparseTernary.width T.length)) :
    sparseRawSlope T.length j.val=SparseTernary.slope T.length j := by
  unfold sparseRawSlope SparseTernary.slope
  split_ifs with h0 h1
  · rfl
  · exact congrArg (fun n : ℕ => (n:ℤ)) (sparsePosition_eq ⟨(j.val-48)/tileWidth T.length,by
      exact (Nat.div_lt_iff_lt_mul (tileWidth_pos _)).mpr (by omega)⟩)
  · rfl

 theorem sparseRawWordAt (w : Compiler.Word T) (i : Sudoku.Column) :
    rawWordAt (rawWord w) i.val=rawSymbol (w i) := by
  simp [rawWordAt,rawWord,Nat.mod_eq_of_lt i.isLt]

 theorem sparseRawDigit_eq (T : LeanWang.TileSet) (w : Compiler.Word T)
    (j : Fin (SparseTernary.width T.length)) :
    sparseRawDigit T (rawWord w) j.val=(encodeArray (fun i _ => w i) j 0).val := by
  by_cases h0 : j.val<48
  · have hi : j.val/3<16 := by omega
    simp [sparseRawDigit,encodeArray,h0,rawWordAt,rawWord,Nat.mod_eq_of_lt hi,
      arithWord,arithIndex,rawSymbol,Sudoku.Width,Sudoku.q]
  · by_cases h1 : j.val<48+3*tileWidth T.length
    · let i : Sudoku.Sparse.TileColumn := ⟨(j.val-48)/tileWidth T.length,by
        apply (Nat.div_lt_iff_lt_mul (tileWidth_pos _)).mpr
        omega⟩
      have hr : rawWordAt (rawWord w) (sparsePosition ((j.val-48)/tileWidth T.length))=
          rawSymbol (w (Sudoku.Sparse.qPosition i)) := by
        rw [show sparsePosition ((j.val-48)/tileWidth T.length)=Sudoku.Sparse.position i from sparsePosition_eq i]
        exact sparseRawWordAt w (Sudoku.Sparse.qPosition i)
      simp [sparseRawDigit,encodeArray,h0,h1,hr,tileWord,rawSymbol,i]
    · simp [sparseRawDigit,encodeArray,h0,h1]

 theorem sparseEncodedWord_eq (T : LeanWang.TileSet) (w : Compiler.Word T) :
    sparseEncodedWord T (rawWord w)=List.ofFn (fun j : Fin (SparseTernary.width T.length) =>
      (encodeArray (fun i _ => w i) j 0).val) := by
  apply List.ext_getElem
  · simp [sparseEncodedWord]
  · intro j hj hj'
    simp only [sparseEncodedWord,List.getElem_map,List.getElem_range,List.getElem_ofFn]
    have hl : j<SparseTernary.width T.length := by simpa [sparseEncodedWord] using hj
    exact sparseRawDigit_eq T w ⟨j,hl⟩

 theorem sparseCoordinate_cases (n : ℕ) (j : Fin (SparseTernary.width n)) :
    (∃ i b, j=arithSlot n i b) ∨ (∃ i b, j=tileSlot n i b) ∨ 48+3*tileWidth n≤j.val := by
  by_cases h0 : j.val<48
  · left
    refine ⟨⟨j.val/3,by change j.val/3<16; omega⟩,⟨j.val%3,Nat.mod_lt _ (by decide)⟩,?_⟩
    apply Fin.ext
    simp only [arithSlot]
    omega
  · right
    by_cases h1 : j.val<48+3*tileWidth n
    · left
      refine ⟨⟨(j.val-48)/tileWidth n,?_⟩,
        ⟨(j.val-48)%tileWidth n,Nat.mod_lt _ (tileWidth_pos _)⟩,?_⟩
      · exact (Nat.div_lt_iff_lt_mul (tileWidth_pos _)).mpr (by omega)
      · apply Fin.ext
        simp only [tileSlot]
        have hh := Nat.mod_add_div (j.val-48) (tileWidth n)
        have hs : j.val-48+48=j.val := Nat.sub_add_cancel (by omega)
        nlinarith
    · exact Or.inr (by omega)

 theorem sparseEncoded_match (T : LeanWang.TileSet) (w : Compiler.Word T)
    (v : Word (SparseTernary.system T)) :
    sparseEncodedWord T (rawWord w)=wordList v ↔
      (∀ i b, v (arithSlot T.length i b)=arithWord ((w i).1,(w i).2.1) b) ∧
      (∀ i b, v (tileSlot T.length i b)=tileWord T (w (Sudoku.Sparse.qPosition i)).2.2 b) ∧
      ∀ (j : Fin (SparseTernary.width T.length)), 48+3*tileWidth T.length≤j.val → v j=0 := by
  rw [sparseEncodedWord_eq,wordList,List.ofFn_inj]
  constructor
  · intro h
    have he (j : Fin (SparseTernary.width T.length)) :
        v j=encodeArray (fun i _ => w i) j 0 := Fin.ext (congrFun h j).symm
    refine ⟨fun i b => ?_,fun i b => ?_,fun j hj => ?_⟩
    · simpa only [encodeArray_arith] using he (arithSlot T.length i b)
    · simpa only [encodeArray_tile] using he (tileSlot T.length i b)
    · simpa only [encodeArray_padding _ j hj] using he j
  · rintro ⟨ha,ht,hp⟩
    funext j
    have he : v j=encodeArray (fun i _ => w i) j 0 := by
      rcases sparseCoordinate_cases T.length j with ⟨i,b,rfl⟩|⟨i,b,rfl⟩|hj
      · simpa only [encodeArray_arith] using ha i b
      · simpa only [encodeArray_tile] using ht i b
      · simpa only [encodeArray_padding _ j hj] using hp j hj
    exact congrArg Fin.val he.symm

 theorem sparsePayload_correct (T : LeanWang.TileSet) :
    PayloadCorrect (SparseTernary.system T) (sparsePayload T) := by
  constructor
  · intro j
    have hj : j.val<(sparsePayload T).1.length := by
      simpa [sparsePayload] using j.isLt
    rw [List.getD_eq_getElem _ _ hj]
    simp only [sparsePayload,List.getElem_map,List.getElem_range]
    exact sparseRawSlope_eq T j
  constructor
  · intro v
    change wordList v∈(goodRawWords T).map (sparseEncodedWord T) ↔ _
    simp only [List.mem_map,mem_goodRawWords]
    constructor
    · rintro ⟨w,⟨v',rfl,hv'⟩,he⟩
      exact ⟨v',hv',(sparseEncoded_match T v' v).mp he⟩
    · rintro ⟨v',hv',he⟩
      exact ⟨rawWord v',⟨v',rfl,hv'⟩,(sparseEncoded_match T v' v).mpr he⟩
  · intro t j
    simp only [sparsePayload,SeedSet,SparseTernary.system,ite_self]
    fin_cases j <;> norm_num

end
end TranslationTiling.FiniteCompiler.Effective
