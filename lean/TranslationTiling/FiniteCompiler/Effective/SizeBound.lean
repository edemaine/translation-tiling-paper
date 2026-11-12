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
      Size.geometryPolynomial (rawCountCap (parameterData T)) := by
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
    have hbase : rawBudget (parameterData T) ≤ rawCountCap (parameterData T) :=
      Size.le_commonCap (C := channelCount T) (by unfold channelCount; omega)
    have hb := hg.trans (Size.geometryCap_mono (Size.horizontalCap_mono hbase) le_rfl)
    simpa only [optimizedTile,Compiler.Size.cubeCount,List.card_toFinset,Size.geometryPolynomial] using hb

/-- The bit-channel encoding uses only nonnegative integer slopes. -/
theorem bitSystem_nonnegative (T : LeanWang.TileSet) : ∀ n, 0 ≤ (bitSystem T).slope n := by
  intro n
  change 0 ≤ ((finProdFinEquiv.symm n : Sudoku.Column × Fin (bitWidth T)).1.val : ℤ)
  exact Int.natCast_nonneg _

theorem optimizedCompile_channel_bound (T : LeanWang.TileSet) :
    optimizedCompile T ≠ [] ∧ FaceConnected (optimizedCompile T) ∧
    (LeanWang.TilesPlane T ↔ TranslationTiling.Tiles (optimizedCompile T)) ∧
    (optimizedCompile T).length ≤
      channelCount (bitSystem T) ^ ((12 * 10 ^ 32 * 10 ^ 6) * channelCount (bitSystem T)) := by
  have hp := bitPayload_correct T
  have hs := BitSystem.slope_bound (bitCode T) (by unfold bitWidth; omega)
  obtain ⟨hne,hconn,hiff,hbound⟩ := optimizedTile_facts (bitSystem T) (bitPayload T) hp
    (bitSystem_nonnegative T) hs
  have hw := BitSystem.finite_system_iff_wang (bitCode T) (bitCode_injective T)
    (by unfold bitWidth; omega) (parameters (bitSystem T))
  refine ⟨hne,hconn,hw.trans hiff,hbound.trans ?_⟩
  obtain ⟨hb,hC,hL⟩ := parameters_budget (bitSystem T) Sudoku.Width hs
  let C := channelCount (bitSystem T)
  let b := rawBudget (parameterData (bitSystem T))
  have hC2 : 2 ≤ C := by unfold C channelCount; omega
  have hbase : b ≤ C ^ (10 ^ 32) := Size.bit_parameterBase_explicit_degree C hC2
  have hX : 2 ≤ Size.commonCap b C := hb.two.trans (Size.le_commonCap (by omega))
  calc
    _ ≤ Size.commonCap b C ^ (10 ^ 6) := Size.geometryPolynomial_explicit_degree _ hX
    _ = b ^ (12 * C * (10 ^ 6)) := by rw [Size.commonCap,← pow_mul]
    _ ≤ (C ^ (10 ^ 32)) ^ (12 * C * (10 ^ 6)) := Nat.pow_le_pow_left hbase _
    _ = C ^ ((12 * 10 ^ 32 * 10 ^ 6) * C) := by
      have he : 10 ^ 32 * (12 * C * 10 ^ 6) = (12 * 10 ^ 32 * 10 ^ 6) * C := by ring
      exact (pow_mul C (10 ^ 32) (12 * C * 10 ^ 6)).symm.trans (congrArg (fun k => C ^ k) he)

theorem optimizedCompile_exp_bound (T : LeanWang.TileSet) :
    (optimizedCompile T).length ≤ 2 ^ (10 ^ 60 * (Nat.log 2 (T.length+2)+1) *
      (Nat.log 2 (Nat.log 2 (T.length+2)+2)+1)) := by
  have hcubes := (optimizedCompile_channel_bound T).2.2.2
  have hlog := Compiler.Size.linear_channel_cap_le_exp_log_explicit Sudoku.Width
    (12 * 10 ^ 32 * 10 ^ 6) (bitWidth T) (by unfold bitWidth; omega)
  have hcoeff : (Sudoku.Width + 4) * (12 * 10 ^ 32 * 10 ^ 6) * (Sudoku.Width + 2) ≤
      10 ^ 60 := by norm_num [Sudoku.Width,Sudoku.p,Sudoku.q]
  have hexp := Nat.mul_le_mul_right (bitWidth T * (Nat.log 2 (bitWidth T+1)+1)) hcoeff
  have hbound := hcubes.trans (hlog.trans (Nat.pow_le_pow_right (by decide)
    (by simpa only [Nat.mul_assoc] using hexp)))
  simpa only [bitWidth,Nat.mul_assoc,Nat.add_assoc] using hbound

/-- A single computable function preserves tilability and has the closed bound. -/
theorem optimizedCompile_bound (T : LeanWang.TileSet) :
    (optimizedCompile T).length ≤ (T.length+4) ^
      (10 ^ 61 * Nat.log 2 (Nat.log 2 (T.length+4))) := by
  have h := (optimizedCompile_exp_bound T).trans
    ((Compiler.Size.exp_iterated_log_le_power (10 ^ 60) T.length).trans
      (Compiler.Size.shifted_power_le_clean (10 ^ 60) T.length))
  convert h using 1 <;> norm_num

theorem optimizedCompile_real_bound (T : LeanWang.TileSet) :
    ((optimizedCompile T).length : ℝ) ≤ ((T.length : ℝ)+4) ^
      ((10 : ℝ)^61 * Real.logb 2 (Real.logb 2 ((T.length : ℝ)+4))) := by
  have h := (optimizedCompile_exp_bound T).trans
    ((Compiler.Size.exp_iterated_log_le_power (10 ^ 60) T.length).trans
      (Compiler.Size.shifted_power_le_clean (10 ^ 60) T.length))
  have hc : ((optimizedCompile T).length : ℝ) ≤
      (((T.length+4) ^ (10 * 10 ^ 60 * Nat.log 2 (Nat.log 2 (T.length+4))) : ℕ) : ℝ) := by
    exact_mod_cast h
  have hr := hc.trans (Compiler.Size.clean_power_le_real_loglog (10 ^ 60) T.length)
  convert hr using 1 <;> norm_num

end
end TranslationTiling.FiniteCompiler.Effective
