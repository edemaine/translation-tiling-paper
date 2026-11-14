import TranslationTiling.FiniteCompiler.Effective.Correctness
import TranslationTiling.Compiler.CleanQuasipolynomialBound

namespace TranslationTiling.FiniteCompiler.Effective
open Compiler Compiler.Effective
open scoped Classical
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 400000

/-- The computable optimized tile has the same polynomial geometric budget. -/
theorem optimizedTile_facts (T : System) (p : Payload) (hp : PayloadCorrect T p)
    (hpos : ∀ n, 0 ≤ T.slope n) (hS : ∀ n, (T.slope n).natAbs ≤ Sudoku.Width) :
    optimizedTile (parameterData T,p) ≠ [] ∧ FaceConnected (optimizedTile (parameterData T,p)) ∧
    ((∃ A : Set (Ambient (parameters T)), Solves (parameters T) A) ↔
      TranslationTiling.Tiles (optimizedTile (parameterData T,p))) ∧
    (optimizedTile (parameterData T,p)).length ≤
      Compiler.Size.geometryCap (rawHorizontal (parameterData T))
        (Size.stackPolynomial (rawCountCap (parameterData T))) := by
  obtain ⟨hm,hne,hM,hxy,hiff⟩ := optimizedCyclic_facts T p hp hpos hS
  dsimp only [optimizedTile]
  generalize hd : optimizedCyclic (parameterData T,p) = d at hm hne hM hxy hiff ⊢
  have hn := Compiler.integerTile_nonempty d hne
  have hc := Compiler.connectedTile_nonempty (Compiler.integerTile d) hn
  refine ⟨(List.dedup_eq_nil _).not.mpr hc,?_,?_,?_⟩
  · simpa only [optimizedTile,FaceConnected,List.mem_dedup] using
      Compiler.connectedTile_connected (Compiler.integerTile d)
  · have ht := hiff.trans ((Compiler.integerTile_correct MSS.rigidity d hm hne).trans
        (Compiler.connectedTile_correct Kim.cosetRigidity (Compiler.integerTile d)).symm)
    simpa only [optimizedTile,TranslationTiling.Tiles,List.mem_dedup] using ht
  · have hg := Compiler.Size.connectedTile_geometryCap (Compiler.integerTile d)
      (rawHorizontal (parameterData T)) (Size.stackPolynomial (rawCountCap (parameterData T)))
      (Compiler.Size.integerTile_coordinateBound d _ _ hm hM hne hxy)
    simpa only [optimizedTile,Compiler.Size.cubeCount,List.card_toFinset] using hg

/-- The bit-channel encoding uses only nonnegative integer slopes. -/
theorem bitSystem_nonnegative (T : LeanWang.TileSet) : ∀ n, 0 ≤ (bitSystem T).slope n := by
  intro n
  change 0 ≤ ((finProdFinEquiv.symm n : Sudoku.Column × Fin (bitWidth T)).1.val : ℤ)
  exact Int.natCast_nonneg _

theorem optimizedCompile_channel_bound (T : LeanWang.TileSet) :
    optimizedCompile T ≠ [] ∧ FaceConnected (optimizedCompile T) ∧
    (LeanWang.TilesPlane T ↔ TranslationTiling.Tiles (optimizedCompile T)) ∧
    (optimizedCompile T).length ≤
      channelCount (bitSystem T) ^ ((12 * 2000000 * 100) * channelCount (bitSystem T)) := by
  have hp := bitPayload_correct T
  have hs := BitSystem.slope_bound (bitCode T) (by unfold bitWidth; omega)
  obtain ⟨hne,hconn,hiff,hbound⟩ := optimizedTile_facts (bitSystem T) (bitPayload T) hp
    (bitSystem_nonnegative T) hs
  have hw := BitSystem.finite_system_iff_wang (bitCode T) (bitCode_injective T)
    (by unfold bitWidth; omega) (parameters (bitSystem T))
  refine ⟨hne,hconn,hw.trans hiff,hbound.trans ?_⟩
  apply Size.bit_geometry_channel_bound
  change Sudoku.Width + 2 ≤ Sudoku.Width * bitWidth T + 2
  have : 1 ≤ bitWidth T := by unfold bitWidth; omega
  nlinarith

theorem optimizedCompile_exp_bound (T : LeanWang.TileSet) :
    (optimizedCompile T).length ≤ 2 ^ (10 ^ 20 * (Nat.log 2 (T.length+2)+1) *
      (Nat.log 2 (Nat.log 2 (T.length+2)+2)+1)) := by
  have hcubes := (optimizedCompile_channel_bound T).2.2.2
  have hlog := Compiler.Size.linear_channel_cap_le_exp_log_small Sudoku.Width
    (12 * 2000000 * 100) (bitWidth T)
    (by norm_num [Sudoku.Width,Sudoku.p,Sudoku.q]) (by unfold bitWidth; omega)
  have hcoeff : 17 * (12 * 2000000 * 100) * (Sudoku.Width + 2) ≤
      10 ^ 20 := by norm_num [Sudoku.Width,Sudoku.p,Sudoku.q]
  have hexp := Nat.mul_le_mul_right (bitWidth T * (Nat.log 2 (bitWidth T+1)+1)) hcoeff
  have hbound := hcubes.trans (hlog.trans (Nat.pow_le_pow_right (by decide)
    (by simpa only [Nat.mul_assoc] using hexp)))
  simpa only [bitWidth,Nat.mul_assoc,Nat.add_assoc] using hbound

/-- A single computable function preserves tilability and has the closed bound. -/
theorem optimizedCompile_bound (T : LeanWang.TileSet) :
    (optimizedCompile T).length ≤ (T.length+4) ^
      (10 ^ 21 * Nat.log 2 (Nat.log 2 (T.length+4))) := by
  have h := (optimizedCompile_exp_bound T).trans
    ((Compiler.Size.exp_iterated_log_le_power (10 ^ 20) T.length).trans
      (Compiler.Size.shifted_power_le_clean (10 ^ 20) T.length))
  convert h using 1 <;> norm_num

theorem optimizedCompile_real_bound (T : LeanWang.TileSet) :
    ((optimizedCompile T).length : ℝ) ≤ ((T.length : ℝ)+4) ^
      ((10 : ℝ)^21 * Real.logb 2 (Real.logb 2 ((T.length : ℝ)+4))) := by
  have h := (optimizedCompile_exp_bound T).trans
    ((Compiler.Size.exp_iterated_log_le_power (10 ^ 20) T.length).trans
      (Compiler.Size.shifted_power_le_clean (10 ^ 20) T.length))
  have hc : ((optimizedCompile T).length : ℝ) ≤
      (((T.length+4) ^ (10 * 10 ^ 20 * Nat.log 2 (Nat.log 2 (T.length+4))) : ℕ) : ℝ) := by
    exact_mod_cast h
  have hr := hc.trans (Compiler.Size.clean_power_le_real_loglog (10 ^ 20) T.length)
  convert hr using 1 <;> norm_num

end
end TranslationTiling.FiniteCompiler.Effective
