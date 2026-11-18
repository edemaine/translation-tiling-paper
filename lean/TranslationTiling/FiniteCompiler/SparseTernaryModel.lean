import TranslationTiling.FiniteCompiler.SparseTernaryTests
import TranslationTiling.Compiler.Completeness

namespace TranslationTiling.FiniteCompiler.SparseTernary
open scoped Classical
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
variable {T : LeanWang.TileSet}

def encodeArray (U : Sudoku.Array T) : WordArray (system T) := fun n m =>
  if hn : n.val<48 then
    arithWord ((U ⟨n.val/3,by change n.val/3<16; omega⟩ m).1,
      (U ⟨n.val/3,by change n.val/3<16; omega⟩ m).2.1)
      ⟨n.val%3,Nat.mod_lt _ (by decide)⟩
  else if hn' : n.val<48+3*tileWidth T.length then
    let i : Sudoku.Sparse.TileColumn := ⟨(n.val-48)/tileWidth T.length,by
      apply (Nat.div_lt_iff_lt_mul (tileWidth_pos _)).mpr
      omega⟩
    let b : Fin (tileWidth T.length) := ⟨(n.val-48)%tileWidth T.length,Nat.mod_lt _ (tileWidth_pos _)⟩
    tileWord T (U (Sudoku.Sparse.qPosition i) m).2.2 b
  else 0

@[simp] theorem encodeArray_arith (U : Sudoku.Array T) (i : Sudoku.Column) (b : Fin 3) (m : ℤ) :
    encodeArray U (arithSlot T.length i b) m=arithWord ((U i m).1,(U i m).2.1) b := by
  have hi : i.val<16 := i.isLt
  have hb := b.isLt
  have hl : 3*i.val+b.val<48 := by omega
  have hd : (3*i.val+b.val)/3=i.val := by omega
  have hm : (3*i.val+b.val)%3=b.val := by omega
  simp [encodeArray,arithSlot,hl,hd,hm]

@[simp] theorem encodeArray_tile (U : Sudoku.Array T) (i : Sudoku.Sparse.TileColumn)
    (b : Fin (tileWidth T.length)) (m : ℤ) :
    encodeArray U (tileSlot T.length i b) m=tileWord T (U (Sudoku.Sparse.qPosition i) m).2.2 b := by
  have hi := i.isLt
  have hb := b.isLt
  have hk := tileWidth_pos T.length
  have hlo : ¬48+i.val*tileWidth T.length+b.val<48 := by omega
  have hhi : 48+i.val*tileWidth T.length+b.val<48+3*tileWidth T.length := by nlinarith
  have hs : 48+i.val*tileWidth T.length+b.val-48=i.val*tileWidth T.length+b.val := by omega
  have hd : (i.val*tileWidth T.length+b.val)/tileWidth T.length=i.val := by
    rw [Nat.mul_comm i.val (tileWidth T.length),Nat.mul_add_div hk,Nat.div_eq_of_lt hb,Nat.add_zero]
  have hm : (i.val*tileWidth T.length+b.val)%tileWidth T.length=b.val := by
    simp [Nat.add_mod,Nat.mul_mod,Nat.mod_eq_of_lt hb]
  simp [encodeArray,tileSlot,hlo,hhi,hs,hd,hm]

 theorem encodeArray_padding (U : Sudoku.Array T) (n : Fin (width T.length))
    (hn : 48+3*tileWidth T.length≤n.val) (m : ℤ) : encodeArray U n m=0 := by
  have h0 : ¬n.val<48 := by omega
  have h1 : ¬n.val<48+3*tileWidth T.length := by omega
  simp [encodeArray,h0,h1]

 theorem encodeArray_lineRule (U : Sudoku.Array T) (hU : Sudoku.LineRule U) :
    LineRule (system T) (encodeArray U) := by
  intro x
  refine ⟨fun i => U i (Compiler.lineValue i x),?_,?_,?_,?_⟩
  · simpa [Compiler.lineValue,mul_comm,add_comm] using hU x.1 x.2
  · intro i b
    dsimp only []
    rw [encodeArray_arith,lineValue_arith]
  · intro i b
    dsimp only []
    rw [encodeArray_tile,lineValue_tile]
    rfl
  · intro i hi
    exact encodeArray_padding U i hi _

 theorem exists_solution_of_wang (E : EncodingParameters (system T))
    (hT : LeanWang.TilesPlane T) : ∃ A : Set (Ambient E), Solves E A := by
  obtain ⟨τ,hτ⟩ := (wang_plane_iff_quadrant T).mp hT
  let U := Sudoku.canonical τ (τ (0,0))
  let W := encodeArray U
  have hr : LineRule (system T) W := encodeArray_lineRule U (Sudoku.canonical_lineRule τ hτ (τ (0,0)))
  have hbase := CommonModel.common_solution E W hr (fun _ _ _ _ => trivial)
  refine ⟨CommonModel.commonGraph E W,fun F hF => ?_⟩
  rcases Finset.mem_union.mp hF with hF|hF
  · exact hbase F hF
  · apply (seedTiles_iff E (CommonModel.outputs E W)
      (CommonModel.outputs_hasDependence E W)).mpr ?_ F hF
    intro t i b x v hs hv
    have hx := (CommonModel.active_seed_iff E W t x).mp hs
    have hx' : Compiler.SharedSeed.residue T x∈Compiler.seedActiveRegion T t := hx
    have hh := Compiler.canonical_seed_regions τ t i x hx'
    have ha : ((U i (Compiler.lineValue i x)).1,(U i (Compiler.lineValue i x)).2.1)=seedArithmetic t := by
      apply Prod.ext <;> apply Units.ext
      · simpa only [seedArithmetic_p,Nat.cast_add,Nat.cast_one] using hh.1
      · simpa only [seedArithmetic_q,Nat.cast_add,Nat.cast_one] using hh.2
    have he := (CommonModel.active_ordinary_iff E W (arithSlot T.length i b) x v).mp hv
    change v=encodeArray U (arithSlot T.length i b) _ at he
    rw [encodeArray_arith,lineValue_arith,ha] at he
    exact he

 theorem finite_system_iff_wang (E : EncodingParameters (system T)) :
    LeanWang.TilesPlane T ↔ ∃ A : Set (Ambient E), Solves E A :=
  ⟨exists_solution_of_wang E,fun ⟨_,hA⟩ => wang_of_solves E hA⟩

end
end TranslationTiling.FiniteCompiler.SparseTernary
