import TranslationTiling.FiniteCompiler.Effective.JointCode
import TranslationTiling.SudokuArithmetic.SparseSoundness

namespace TranslationTiling.FiniteCompiler.SparseTernary
open scoped Classical
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

abbrev Arithmetic := (ZMod 5)ˣ × (ZMod 7)ˣ

def arithIndex (a : Arithmetic) : ℕ := (a.1.val.val-1)*6+(a.2.val.val-1)

theorem arithIndex_lt : ∀ a, arithIndex a<24 := by decide +kernel
theorem arithIndex_injective : Function.Injective arithIndex := by decide +kernel

def arithWord (a : Arithmetic) (b : Fin 3) : Fin 3 :=
  ⟨arithIndex a/3^b.val%3,Nat.mod_lt _ (by decide)⟩

theorem arithWord_injective : Function.Injective arithWord := by
  intro a b h
  apply arithIndex_injective
  apply Effective.eq_of_digits (by decide : 0<3)
    ((arithIndex_lt a).trans (by decide : 24<3^3))
    ((arithIndex_lt b).trans (by decide : 24<3^3))
  intro i hi
  exact congrArg Fin.val (congrFun h ⟨i,hi⟩)

def arithDecode : (Fin 3 → Fin 3) → Arithmetic := Function.invFun arithWord

theorem arithDecode_word (a : Arithmetic) : arithDecode (arithWord a)=a :=
  Function.leftInverse_invFun arithWord_injective a

def tileWidth (n : ℕ) : ℕ := Nat.log 3 n+1

theorem tileWidth_pos (n : ℕ) : 0<tileWidth n := by unfold tileWidth; omega

def width (n : ℕ) : ℕ := 16*((48+3*tileWidth n+15)/16)

theorem raw_width_le (n : ℕ) : 48+3*tileWidth n≤width n := by
  unfold width
  omega

theorem width_upper (n : ℕ) : width n≤48+3*tileWidth n+15 := by unfold width; omega

def tileWord (T : LeanWang.TileSet) (t : LeanWang.TileIn T) (b : Fin (tileWidth T.length)) : Fin 3 :=
  ⟨T.idxOf t.val/3^b.val%3,Nat.mod_lt _ (by decide)⟩

theorem tileWord_injective (T : LeanWang.TileSet) : Function.Injective (tileWord T) := by
  intro a b h
  apply Subtype.ext
  apply (List.idxOf_inj a.property).mp
  have hc : T.length<3^tileWidth T.length := Nat.lt_pow_succ_log_self (by decide) _
  apply Effective.eq_of_digits (by decide : 0<3)
    ((List.idxOf_lt_length_of_mem a.property).trans hc)
    ((List.idxOf_lt_length_of_mem b.property).trans hc)
  intro i hi
  exact congrArg Fin.val (congrFun h ⟨i,hi⟩)

def arithSlot (n : ℕ) (i : Sudoku.Column) (b : Fin 3) : Fin (width n) :=
  ⟨3*i.val+b.val,by
    have hi := i.isLt
    have hb := b.isLt
    have hw := raw_width_le n
    change i.val<16 at hi
    omega⟩

def tileSlot (n : ℕ) (i : Sudoku.Sparse.TileColumn) (b : Fin (tileWidth n)) : Fin (width n) :=
  ⟨48+i.val*tileWidth n+b.val,by have := i.isLt; have := b.isLt; have := raw_width_le n; nlinarith⟩

def slope (n : ℕ) (i : Fin (width n)) : ℤ :=
  if i.val<48 then (i.val/3 : ℕ) else
  if h : i.val<48+3*tileWidth n then
    Sudoku.Sparse.position ⟨(i.val-48)/tileWidth n,by
      have := tileWidth_pos n
      exact (Nat.div_lt_iff_lt_mul this).mpr (by omega)⟩
  else 0

abbrev system (T : LeanWang.TileSet) : System where
  width := width T.length
  width_pos := (by have := raw_width_le T.length; omega)
  alphabet := 3
  slope := slope T.length
  allowed v := ∃ w : Sudoku.Column → Sudoku.Symbol T, Sudoku.Allowed T w ∧
    (∀ i b, v (arithSlot T.length i b)=arithWord ((w i).1,(w i).2.1) b) ∧
    (∀ i b, v (tileSlot T.length i b)=tileWord T (w (Sudoku.Sparse.qPosition i)).2.2 b) ∧
    (∀ (j : Fin (width T.length)), (48+3*tileWidth T.length : ℕ) ≤ j.val → v j = (0 : Fin 3))
  seed _ _ := True

@[simp] theorem slope_arith (n : ℕ) (i : Sudoku.Column) (b : Fin 3) :
    slope n (arithSlot n i b)=i.val := by
  have hi : i.val<16 := i.isLt
  have hb := b.isLt
  have hlt : 3*i.val+b.val<48 := by omega
  have he : (3*i.val+b.val)/3=i.val := by omega
  simp [slope,arithSlot,hlt,he]

@[simp] theorem slope_tile (n : ℕ) (i : Sudoku.Sparse.TileColumn) (b : Fin (tileWidth n)) :
    slope n (tileSlot n i b)=Sudoku.Sparse.position i := by
  have hi := i.isLt
  have hb := b.isLt
  have hk := tileWidth_pos n
  have hlo : ¬48+i.val*tileWidth n+b.val<48 := by omega
  have hhi : 48+i.val*tileWidth n+b.val<48+3*tileWidth n := by nlinarith
  have hs : 48+i.val*tileWidth n+b.val-48=i.val*tileWidth n+b.val := by omega
  have he : (i.val*tileWidth n+b.val)/tileWidth n=i.val := by
    rw [Nat.mul_comm i.val (tileWidth n),Nat.mul_add_div hk,Nat.div_eq_of_lt hb,Nat.add_zero]
  simp [slope,tileSlot,hlo,hhi,hs,he]

@[simp] theorem lineValue_arith (T : LeanWang.TileSet) (i : Sudoku.Column) (b : Fin 3) (x : Plane) :
    lineValue (system T) (arithSlot T.length i b) x=Compiler.lineValue i x := by
  simp [lineValue,system,Compiler.lineValue]

@[simp] theorem lineValue_tile (T : LeanWang.TileSet) (i : Sudoku.Sparse.TileColumn)
    (b : Fin (tileWidth T.length)) (x : Plane) :
    lineValue (system T) (tileSlot T.length i b) x=x.2+Sudoku.Sparse.position i*x.1 := by
  simp [lineValue,system]

 theorem slope_bound (T : LeanWang.TileSet) : ∀ n, ((system T).slope n).natAbs≤16 := by
  intro n
  change (slope T.length n).natAbs≤16
  unfold slope
  split_ifs with h0 h1
  · have hd : n.val/3<16 := by omega
    omega
  · generalize hi : (⟨(n.val-48)/tileWidth T.length,_⟩ : Sudoku.Sparse.TileColumn)=j
    fin_cases j <;> norm_num [Sudoku.Sparse.position]
  · norm_num

end
end TranslationTiling.FiniteCompiler.SparseTernary
