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
        (Size.separateModulusCap (parameters T).cyclicOrder (canonicalInputFamily (parameterData T,p)).length) := by
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
      (rawHorizontal (parameterData T)) (Size.separateModulusCap (parameters T).cyclicOrder (canonicalInputFamily (parameterData T,p)).length)
      (Compiler.Size.integerTile_coordinateBound d _ _ hm hM hne hxy)
    simpa only [optimizedTile,Compiler.Size.cubeCount,List.card_toFinset] using hg

/-- The bit-channel encoding uses only nonnegative integer slopes. -/
theorem bitSystem_nonnegative (T : LeanWang.TileSet) : ∀ n, 0 ≤ (bitSystem T).slope n := by
  intro n
  change 0 ≤ ((finProdFinEquiv.symm n : Sudoku.Column × Fin (bitWidth T)).1.val : ℤ)
  exact Int.natCast_nonneg _

theorem ternarySystem_nonnegative (T : LeanWang.TileSet) : ∀ n, 0 ≤ (ternarySystem T).slope n := by
  intro n
  change 0 ≤ ((finProdFinEquiv.symm n : Sudoku.Column × Fin (bitWidth T + 16 + 2)).1.val : ℤ)
  exact Int.natCast_nonneg _

theorem optimizedCompile_channel_bound (T : LeanWang.TileSet) :
    optimizedCompile T ≠ [] ∧ FaceConnected (optimizedCompile T) ∧
    (LeanWang.TilesPlane T ↔ TranslationTiling.Tiles (optimizedCompile T)) ∧
    (optimizedCompile T).length ≤
      channelCount (ternarySystem T) ^ (3510 * channelCount (ternarySystem T)) := by
  have hp := ternaryPayload_correct T
  have hslope := TernarySystem.slope_bound (fullCode T)
  obtain ⟨hne,hconn,hiff,hbound⟩ := optimizedTile_facts (ternarySystem T) (ternaryPayload T) hp
    (ternarySystem_nonnegative T) hslope
  have hw := TernarySystem.finite_system_iff_wang (fullCode T) (fullCode_injective T)
    (parameters (ternarySystem T))
  refine ⟨hne,hconn,hw.trans hiff,hbound.trans ?_⟩
  let S := ternarySystem T
  let C := channelCount S
  have hC : 20 * Sudoku.Width + 2 ≤ C := by
    change 20 * Sudoku.Width + 2 ≤ Sudoku.Width * (bitWidth T + 16 + 2) + 2
    have hl : 2 ≤ bitWidth T := by
      have := Nat.le_log_of_pow_le (b := 2) (x := 1) (y := T.length + 2)
        (by decide) (by norm_num)
      unfold bitWidth
      omega
    nlinarith
  have hc : 1202≤C := by
    have hw : 61≤Sudoku.Width := by norm_num [Sudoku.Width,Sudoku.q]
    omega
  have hcompact := parameters_bounded_compact S hc rfl
  have hsmall : Size.SmallPrimes (parameters S) := ⟨fun i => ⟨(hcompact.1 i).1.trans (Nat.pow_le_pow_right (by omega) (by decide)),
    (hcompact.1 i).2.trans (Nat.pow_le_pow_right (by omega) (by decide))⟩,
    fun i j => (hcompact.2.1 i j).trans (Nat.pow_le_pow_right (by omega) (by decide))⟩
  have hV := Size.ternary_cyclicOrder_le (parameters S) rfl hsmall hC
  have hcount : (canonicalInputFamily (parameterData S,ternaryPayload T)).length ≤ C ^ (30 * C) := by
    rw [canonicalInputFamily_length S _ hp (ternarySystem_nonnegative T) hslope]
    exact Size.ternary_testTiles_card_le (parameters S) rfl hsmall hC hslope
  have hM := (Size.separateModulusCap_mono hV hcount).trans (Size.ternary_modulus_cap_le hC)
  apply (Size.geometryCap_mono (le_refl _) hM).trans
  exact Size.ternary_geometry_bound hC (show rawBudget (parameterData S)≤C^73 from by
    change (if 962≤S.width+2 ∧ S.alphabet=3 then _ else _)≤_
    rw [if_pos ⟨(by change 962≤C; omega),rfl⟩]
    exact Nat.pow_le_pow_right (by omega) (by decide))
    (parameters_rawBudget S hslope).1.two

theorem optimizedCompile_exp_bound (T : LeanWang.TileSet) :
    (optimizedCompile T).length ≤ 2 ^ ((2 * 10 ^ 10) * (Nat.log 2 (T.length+2)+1) *
      (Nat.log 2 (Nat.log 2 (T.length+2)+2)+1)) := by
  apply (optimizedCompile_channel_bound T).2.2.2.trans
  simpa only [ternarySystem,TernarySystem.system,channelCount,bitWidth,Nat.add_assoc]
    using Compiler.Size.ternary_channel_cap_bound T.length

/-- A single computable function preserves tilability and has the closed bound. -/
theorem optimizedCompile_bound (T : LeanWang.TileSet) :
    (optimizedCompile T).length ≤ (T.length+4) ^
      (10 ^ 11 * Nat.log 2 (Nat.log 2 (T.length+4))) :=
  (optimizedCompile_exp_bound T).trans (Compiler.Size.ternary_exp_le_clean T.length)

theorem optimizedCompile_real_bound (T : LeanWang.TileSet) :
    ((optimizedCompile T).length : ℝ) ≤ ((T.length : ℝ)+4) ^
      ((10 : ℝ)^11 * Real.logb 2 (Real.logb 2 ((T.length : ℝ)+4))) := by
  have hc : ((optimizedCompile T).length : ℝ) ≤
      (((T.length+4) ^ (10 ^ 11 * Nat.log 2 (Nat.log 2 (T.length+4))) : ℕ) : ℝ) := by
    exact_mod_cast optimizedCompile_bound T
  apply hc.trans
  convert Compiler.Size.clean_power_le_real_loglog (10 ^ 10) T.length using 1 <;> norm_num

end
end TranslationTiling.FiniteCompiler.Effective
