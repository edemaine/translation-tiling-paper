import TranslationTiling.FiniteCompiler.Effective.JointFamily
import TranslationTiling.Compiler.JointLogBound
import TranslationTiling.Compiler.EmptyInputBound

namespace TranslationTiling.FiniteCompiler.Effective
open Compiler Compiler.Effective
open scoped Classical
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def jointCompileCore (T : LeanWang.TileSet) : Tile 3 :=
  familyTile (parameterData (jointSystem T),jointFamily T)

theorem jointCompileCore_computable : Computable jointCompileCore := by
  have h := familyTile_computable.comp (jointParameterData_computable.pair jointFamily_computable)
  exact h.of_eq (fun T => rfl)

theorem jointCompileCore_channel_bound (T : LeanWang.TileSet) (hn : 0<T.length) :
    jointCompileCore T≠[] ∧ FaceConnected (jointCompileCore T) ∧
    (LeanWang.TilesPlane T ↔ TranslationTiling.Tiles (jointCompileCore T)) ∧
    (jointCompileCore T).length≤primeBudget (jointSystem T)^(33*(jointSystem T).width+466)*
      3^(4*(jointSystem T).width+4) := by
  have hw : 48≤(jointSystem T).width := by
    have hk := jointWidth_three hn
    change 48≤Sudoku.Width*jointWidth T.length
    norm_num [Sudoku.Width,Sudoku.q]
    omega
  obtain ⟨hne,hconn,hiff,hbound⟩ := familyTile_facts (jointSystem T) (jointFamily T)
    (jointFamily_budget T hn) (jointSystem_slope_bound T) rfl hw
  have hwang := JointSystem.finite_system_iff_wang (jointCode T) (parameters (jointSystem T))
  exact ⟨hne,hconn,hwang.trans ((joint_family_solution_iff T).trans hiff),hbound⟩

def jointCompile (T : LeanWang.TileSet) : Tile 3 :=
  if T = [] then Compiler.Size.emptyTile else jointCompileCore T

theorem jointCompile_computable : Computable jointCompile := by
  unfold jointCompile
  have hd : Primrec (fun T : LeanWang.TileSet => decide (T = [])) := by fun_prop
  exact (hd.to_comp.cond (Computable.const Compiler.Size.emptyTile) jointCompileCore_computable).of_eq
    (fun T => by simp [Bool.cond_decide])

theorem jointCompile_facts (T : LeanWang.TileSet) :
    jointCompile T ≠ [] ∧ FaceConnected (jointCompile T) ∧
    (LeanWang.TilesPlane T ↔ TranslationTiling.Tiles (jointCompile T)) ∧
    ((jointCompile T).length : ℝ) ≤ ((T.length:ℝ)+4) ^
      ((6000) * Real.logb 2 (Real.logb 2 ((T.length:ℝ)+4))) := by
  by_cases ht : T = []
  · subst T
    simp only [jointCompile,if_pos rfl,List.length_nil,Nat.cast_zero,zero_add]
    obtain ⟨hn,hc,ht,hb⟩ := Compiler.Size.emptyTile_facts
    refine ⟨hn,hc,⟨fun h => (Compiler.Size.empty_wang_not_tiles h).elim,fun h => (ht h).elim⟩,?_⟩
    have hlog4 : Real.logb 2 (4:ℝ) = 2 := by
      rw [show (4:ℝ) = (2:ℝ)^2 by norm_num,Real.logb_pow]
      norm_num [Real.logb_self_eq_one]
    rw [hlog4]
    rw [show Real.logb 2 (2:ℝ) = 1 from Real.logb_self_eq_one (by norm_num),mul_one]
    have hcast : (Compiler.Size.emptyTile.length:ℝ) ≤ (2:ℝ)^250 := by exact_mod_cast hb
    apply hcast.trans
    calc
      (2:ℝ)^250 ≤ (4:ℝ)^250 := by norm_num
      _ = (4:ℝ)^(250:ℝ) := (Real.rpow_natCast (4:ℝ) 250).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)

  · have hn : 0 < T.length := List.length_pos_iff_ne_nil.mpr ht
    obtain ⟨hne,hconn,hiff,hbound⟩ := jointCompileCore_channel_bound T hn
    simp only [jointCompile,if_neg ht]
    refine ⟨hne,hconn,hiff,?_⟩
    exact Compiler.Size.joint_channel_cap_real_bound hn hbound

theorem jointCompile_real_bound (T : LeanWang.TileSet) :
    ((jointCompile T).length:ℝ) ≤ ((T.length:ℝ)+4) ^
      ((6000) * Real.logb 2 (Real.logb 2 ((T.length:ℝ)+4))) := (jointCompile_facts T).2.2.2

end
end TranslationTiling.FiniteCompiler.Effective
