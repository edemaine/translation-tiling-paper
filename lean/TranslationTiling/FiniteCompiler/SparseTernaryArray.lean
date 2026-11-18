import TranslationTiling.FiniteCompiler.SparseTernaryCode

namespace TranslationTiling.FiniteCompiler.SparseTernary
open scoped Classical
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
variable {T : LeanWang.TileSet}

def arithArray (W : WordArray (system T)) (i : Sudoku.Column) (m : ℤ) : Arithmetic :=
  arithDecode (fun b => W (arithSlot T.length i b) m)

theorem arithArray_at (W : WordArray (system T)) (x : Plane)
    (w : Sudoku.Column → Sudoku.Symbol T)
    (ha : ∀ i b, W (arithSlot T.length i b) (lineValue (system T) (arithSlot T.length i b) x)=
      arithWord ((w i).1,(w i).2.1) b) (i : Sudoku.Column) :
    arithArray W i (Compiler.lineValue i x)=((w i).1,(w i).2.1) := by
  have he : (fun b => W (arithSlot T.length i b) (Compiler.lineValue i x))=
      arithWord ((w i).1,(w i).2.1) := by
    funext b
    simpa only [lineValue_arith] using ha i b
  unfold arithArray
  rw [he]
  exact arithDecode_word _

theorem exists_tile_at (W : WordArray (system T)) (hw : LineRule (system T) W)
    (i : Sudoku.Sparse.TileColumn) (m : ℤ) :
    ∃ t : LeanWang.TileIn T, ∀ b, W (tileSlot T.length i b) m=tileWord T t b := by
  obtain ⟨w,_,_,ht,_⟩ := hw (0,m)
  refine ⟨(w (Sudoku.Sparse.qPosition i)).2.2,fun b => ?_⟩
  simpa only [lineValue_tile,mul_zero,add_zero] using ht i b

def tileArray (W : WordArray (system T)) (hw : LineRule (system T) W)
    (i : Sudoku.Sparse.TileColumn) (m : ℤ) : LeanWang.TileIn T :=
  (exists_tile_at W hw i m).choose

theorem tileArray_at (W : WordArray (system T)) (hw : LineRule (system T) W)
    (x : Plane) (w : Sudoku.Column → Sudoku.Symbol T)
    (ht : ∀ i b, W (tileSlot T.length i b) (lineValue (system T) (tileSlot T.length i b) x)=
      tileWord T (w (Sudoku.Sparse.qPosition i)).2.2 b) (i : Sudoku.Sparse.TileColumn) :
    tileArray W hw i (x.2+Sudoku.Sparse.position i*x.1)=(w (Sudoku.Sparse.qPosition i)).2.2 := by
  apply tileWord_injective
  funext b
  have hc := (exists_tile_at W hw i (x.2+Sudoku.Sparse.position i*x.1)).choose_spec b
  have hh := ht i b
  rw [lineValue_tile] at hh
  exact hc.symm.trans hh

def board (W : WordArray (system T)) (hw : LineRule (system T) W) : Sudoku.Sparse.Board T where
  p i m := (arithArray W ⟨i.val,by have := i.isLt; change i.val<16; omega⟩ m).1
  q i m := (arithArray W i m).2
  tile := tileArray W hw

theorem board_lineRule (W : WordArray (system T)) (hw : LineRule (system T) W) :
    Sudoku.Sparse.LineRule (board W hw) := by
  intro a b
  obtain ⟨w,hw',ha,ht,_⟩ := hw (a,b)
  have hr := Sudoku.Sparse.restrict_lineRule (W:=fun n _ => w n) (fun _ _ => hw') a b
  convert hr using 1
  · funext n
    have hh := congrArg Prod.fst (arithArray_at W (a,b) w ha
      ⟨n.val,by have := n.isLt; change n.val<16; omega⟩)
    simpa [board,Sudoku.Sparse.restrict,Compiler.lineValue,mul_comm,add_comm] using hh
  · funext n
    have hh := congrArg Prod.snd (arithArray_at W (a,b) w ha n)
    simpa [board,Sudoku.Sparse.restrict,Compiler.lineValue,mul_comm,add_comm] using hh
  · funext n
    simpa [board,Sudoku.Sparse.restrict,mul_comm,add_comm] using tileArray_at W hw (a,b) w ht n

def seedArithmetic (t : Fin 2) : Arithmetic :=
  (ZMod.unitOfCoprime (t.val+1) (by fin_cases t <;> decide),
   ZMod.unitOfCoprime (t.val+1) (by fin_cases t <;> decide))

@[simp] theorem seedArithmetic_p (t : Fin 2) : (seedArithmetic t).1.val=t.val+1 := by
  simp [seedArithmetic,ZMod.coe_unitOfCoprime]
@[simp] theorem seedArithmetic_q (t : Fin 2) : (seedArithmetic t).2.val=t.val+1 := by
  simp [seedArithmetic,ZMod.coe_unitOfCoprime]

def SeedRule (W : WordArray (system T)) : Prop :=
  ∀ t : Fin 2, ∃ x : Plane, ∀ i b,
    W (arithSlot T.length i b) (Compiler.lineValue i x)=arithWord (seedArithmetic t) b

theorem board_nonconstant (W : WordArray (system T)) (hw : LineRule (system T) W)
    (hs : SeedRule W) : Sudoku.Sparse.Nonconstant (board W hw) := by
  obtain ⟨x0,h0⟩ := hs 0
  obtain ⟨x1,h1⟩ := hs 1
  have hd (t : Fin 2) (x : Plane)
      (hx : ∀ i b, W (arithSlot T.length i b) (Compiler.lineValue i x)=arithWord (seedArithmetic t) b)
      (i : Sudoku.Column) : arithArray W i (Compiler.lineValue i x)=seedArithmetic t := by
    unfold arithArray
    rw [show (fun b => W (arithSlot T.length i b) (Compiler.lineValue i x))=
      arithWord (seedArithmetic t) from funext (hx i)]
    exact arithDecode_word _
  constructor
  · intro n
    let i : Sudoku.Column := ⟨n.val,by have := n.isLt; change n.val<16; omega⟩
    refine ⟨Compiler.lineValue i x0,Compiler.lineValue i x1,?_⟩
    intro he
    have hv := congrArg (fun u : (ZMod 5)ˣ => u.val) he
    change (arithArray W i _).1.val=(arithArray W i _).1.val at hv
    rw [hd 0 x0 h0 i,hd 1 x1 h1 i] at hv
    norm_num only [seedArithmetic_p,Fin.val_zero,Fin.val_one,Nat.cast_zero,Nat.cast_one,zero_add] at hv
    exact (by decide : (1:ZMod 5)≠2) hv
  · intro i
    refine ⟨Compiler.lineValue i x0,Compiler.lineValue i x1,?_⟩
    intro he
    have hv := congrArg (fun u : (ZMod 7)ˣ => u.val) he
    change (arithArray W i _).2.val=(arithArray W i _).2.val at hv
    rw [hd 0 x0 h0 i,hd 1 x1 h1 i] at hv
    norm_num only [seedArithmetic_q,Fin.val_zero,Fin.val_one,Nat.cast_zero,Nat.cast_one,zero_add] at hv
    exact (by decide : (1:ZMod 7)≠2) hv

end
end TranslationTiling.FiniteCompiler.SparseTernary
