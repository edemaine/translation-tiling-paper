import TranslationTiling.FiniteCompiler.JointSystem
import TranslationTiling.FiniteCompiler.Effective.MixedInput

namespace TranslationTiling.FiniteCompiler.Effective
open Compiler.Effective
open scoped Classical
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

/-- Full ternary capacity, without coordinatewise seed restrictions. -/
def jointWidth (n : ℕ) : ℕ := Nat.log 3 (24*n)+1

@[fun_prop] theorem jointWidth_primrec : Primrec jointWidth := by
  unfold jointWidth
  have h := natLog_primrec 3 (by decide)
  fun_prop

theorem jointWidth_pos (n : ℕ) : 0 < jointWidth n := by unfold jointWidth; omega

theorem jointWidth_three {n : ℕ} (hn : 0<n) : 3≤jointWidth n := by
  have h : 3^2≤24*n := by omega
  have hl := Nat.le_log_of_pow_le (by decide : 1<3) h
  unfold jointWidth
  omega

@[simp] theorem jointWidth_one : jointWidth 1=3 := by decide

def jointIndex (T : LeanWang.TileSet) (s : Sudoku.Symbol T) : ℕ :=
  ((s.1.val.val-1)*6+(s.2.1.val.val-1))*T.length+T.idxOf s.2.2.val

private theorem unit_p_bounds (a : (ZMod Sudoku.p)ˣ) : 1≤a.val.val ∧ a.val.val≤4 := by
  letI : Fact Sudoku.p.Prime := ⟨by decide⟩
  have hp := ZMod.val_pos.mpr (Units.ne_zero a)
  have hl := ZMod.val_lt a.val
  norm_num [Sudoku.p] at hl
  omega

private theorem unit_q_bounds (a : (ZMod Sudoku.q)ˣ) : 1≤a.val.val ∧ a.val.val≤6 := by
  letI : Fact Sudoku.q.Prime := ⟨by decide⟩
  have hp := ZMod.val_pos.mpr (Units.ne_zero a)
  have hl := ZMod.val_lt a.val
  norm_num [Sudoku.q] at hl
  omega

theorem jointIndex_lt (T : LeanWang.TileSet) (s : Sudoku.Symbol T) :
    jointIndex T s < 24*T.length := by
  have ha := unit_p_bounds s.1
  have hb := unit_q_bounds s.2.1
  have hi := List.idxOf_lt_length_of_mem s.2.2.property
  have hc : (s.1.val.val-1)*6+(s.2.1.val.val-1)<24 := by omega
  unfold jointIndex
  nlinarith

theorem jointIndex_injective (T : LeanWang.TileSet) : Function.Injective (jointIndex T) := by
  intro s u h
  have hi := List.idxOf_lt_length_of_mem s.2.2.property
  have hj := List.idxOf_lt_length_of_mem u.2.2.property
  have har : (s.1.val.val-1)*6+(s.2.1.val.val-1) =
      (u.1.val.val-1)*6+(u.2.1.val.val-1) := by
    have he := congrArg (fun z => z/T.length) h
    simpa only [jointIndex,Nat.mul_comm _ T.length,
      Nat.mul_add_div (show 0<T.length by omega),Nat.div_eq_of_lt hi,
      Nat.div_eq_of_lt hj,Nat.add_zero] using he
  have ht : s.2.2=u.2.2 := by
    apply Subtype.ext
    apply (List.idxOf_inj s.2.2.property).mp
    have he := congrArg (fun z => z%T.length) h
    simpa [jointIndex,Nat.add_mod,Nat.mod_eq_of_lt hi,Nat.mod_eq_of_lt hj] using he
  have ha := unit_p_bounds s.1
  have ha' := unit_p_bounds u.1
  have hb := unit_q_bounds s.2.1
  have hb' := unit_q_bounds u.2.1
  have hae : s.1.val.val=u.1.val.val := by omega
  have hbe : s.2.1.val.val=u.2.1.val.val := by omega
  exact Prod.ext (Units.ext (ZMod.val_injective _ hae))
    (Prod.ext (Units.ext (ZMod.val_injective _ hbe)) ht)

def jointWord (T : LeanWang.TileSet) (s : Sudoku.Symbol T)
    (b : Fin (jointWidth T.length)) : Fin 3 :=
  ⟨jointIndex T s / 3^b.val % 3,Nat.mod_lt _ (by decide)⟩

def jointCode (T : LeanWang.TileSet) : JointSystem.Code T (jointWidth T.length) where
  pos := jointWidth_pos _
  word := jointWord T
  injective := by
    intro s u h
    apply jointIndex_injective T
    have hcap : 24*T.length<3^jointWidth T.length := Nat.lt_pow_succ_log_self (by decide) _
    apply eq_of_digits (by decide : 0<3) ((jointIndex_lt T s).trans hcap) ((jointIndex_lt T u).trans hcap)
    intro b hb
    exact congrArg Fin.val (congrFun h ⟨b,hb⟩)

abbrev jointSystem (T : LeanWang.TileSet) : System := JointSystem.system (jointCode T)

def rawJointCode (T : LeanWang.TileSet) (s : RawSymbol) (b : ℕ) : ℕ :=
  (((s.1-1)*6+(s.2.1-1))*T.length+T.idxOf s.2.2) / 3^b % 3

@[fun_prop] theorem rawJointCode_primrec :
    Primrec (fun z : LeanWang.TileSet × RawSymbol × ℕ => rawJointCode z.1 z.2.1 z.2.2) := by
  unfold rawJointCode
  fun_prop

@[simp] theorem rawJointCode_eq (T : LeanWang.TileSet) (s : Sudoku.Symbol T)
    (b : Fin (jointWidth T.length)) :
    rawJointCode T (rawSymbol s) b.val = (jointWord T s b).val := rfl

end
end TranslationTiling.FiniteCompiler.Effective
