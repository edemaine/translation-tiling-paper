import TranslationTiling.FiniteCompiler.Effective.Correctness
import TranslationTiling.FiniteCompiler.Effective.SparseGeometry
import TranslationTiling.FiniteCompiler.MixedBounds
import TranslationTiling.Compiler.MixedLogBound
import TranslationTiling.Compiler.EmptyInputBound

namespace TranslationTiling.FiniteCompiler.Effective
open Compiler Compiler.Effective
open scoped Classical
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

/-- The computable optimized tile has the same polynomial geometric budget. -/
theorem optimizedTile_sparse_facts (T : System) (p : Payload) (hp : PayloadCorrect T p)
    (hpos : ∀ n, 0 ≤ T.slope n) (hS : ∀ n, (T.slope n).natAbs ≤ Sudoku.Width) :
    optimizedTile (parameterData T,p) ≠ [] ∧ FaceConnected (optimizedTile (parameterData T,p)) ∧
    ((∃ A : Set (Ambient (parameters T)), Solves (parameters T) A) ↔
      TranslationTiling.Tiles (optimizedTile (parameterData T,p))) ∧
    (optimizedTile (parameterData T,p)).length ≤
      Compiler.Size.sparseGeometryCap (rawHorizontal (parameterData T))
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
  · have hg := Compiler.Size.integerTile_connected_sparseGeometryCap d
      (rawHorizontal (parameterData T)) (Size.separateModulusCap (parameters T).cyclicOrder (canonicalInputFamily (parameterData T,p)).length)
      hm hM hne hxy
    simpa only [optimizedTile,Compiler.Size.cubeCount,List.card_toFinset] using hg


def mixedWangInput (T : LeanWang.TileSet) : InputData :=
  (parameterData (mixedSystem T),mixedPayload T)

theorem mixedWangInput_computable : Computable mixedWangInput := by
  have hw : Primrec (fun T : LeanWang.TileSet => Sudoku.Width * mixedWidth T.length) := by fun_prop
  have hshape := hw.to_comp.pair (Computable.const 3)
  have hc := parameterCertificate_computable.comp hshape
  exact (hw.to_comp.pair ((Computable.const _).pair hc)).pair mixedPayload_primrec.to_comp

def mixedCompileCore (T : LeanWang.TileSet) : Tile 3 := optimizedTile (mixedWangInput T)

theorem mixedCompileCore_computable : Computable mixedCompileCore :=
  optimizedTile_computable.comp mixedWangInput_computable

theorem mixedSystem_nonnegative (T : LeanWang.TileSet) : ∀ n, 0 ≤ (mixedSystem T).slope n := by
  intro n
  change 0 ≤ ((finProdFinEquiv.symm n : Sudoku.Column × Fin (mixedWidth T.length)).1.val : ℤ)
  exact Int.natCast_nonneg _

theorem mixedCompileCore_channel_bound (T : LeanWang.TileSet) (hn : 0 < T.length) :
    mixedCompileCore T ≠ [] ∧ FaceConnected (mixedCompileCore T) ∧
    (LeanWang.TilesPlane T ↔ TranslationTiling.Tiles (mixedCompileCore T)) ∧
    (mixedCompileCore T).length ≤ channelCount (mixedSystem T) ^ (1772*channelCount (mixedSystem T)) := by
  have hp := mixedPayload_correct T
  have hslope := TaggedSystem.slope_bound (mixedCode T)
  obtain ⟨hne,hconn,hiff,hbound⟩ := optimizedTile_sparse_facts (mixedSystem T) (mixedPayload T) hp
    (mixedSystem_nonnegative T) hslope
  have hw := TaggedSystem.finite_system_iff_wang (mixedCode T) (parameters (mixedSystem T))
  refine ⟨hne,hconn,hw.trans hiff,hbound.trans ?_⟩
  let S := mixedSystem T
  let C := channelCount S
  have hC : 12*Sudoku.Width+2 ≤ C := by
    change 12*Sudoku.Width+2 ≤ Sudoku.Width*mixedWidth T.length+2
    have hl := Compiler.Size.mixedWidth_lower hn
    nlinarith
  have hsmall := MixedSize.smallPrimes_of_caps (parameters S) rfl hC
    (parameters_bounded S).1 (parameters_bounded S).2
  have hV := MixedSize.mixed_cyclicOrder_le (parameters S) rfl hsmall hC
  have hcount : (canonicalInputFamily (parameterData S,mixedPayload T)).length ≤ C ^ (28*C) := by
    rw [canonicalInputFamily_length S _ hp (mixedSystem_nonnegative T) hslope]
    exact MixedSize.mixed_testTiles_card_le (parameters S) rfl hsmall hC hslope
  have hM := (Size.separateModulusCap_mono hV hcount).trans (MixedSize.mixed_modulus_cap_le hC)
  apply (Compiler.Size.sparseGeometryCap_mono (le_refl _) hM).trans
  exact MixedSize.mixed_geometry_bound hC (MixedSize.mixed_parameterBase_le hC)
    (parameters_budget S Sudoku.Width hslope).1.two

def mixedCompile (T : LeanWang.TileSet) : Tile 3 :=
  if T = [] then Compiler.Size.emptyTile else mixedCompileCore T

theorem mixedCompile_computable : Computable mixedCompile := by
  unfold mixedCompile
  have hd : Primrec (fun T : LeanWang.TileSet => decide (T = [])) := by fun_prop
  exact (hd.to_comp.cond (Computable.const Compiler.Size.emptyTile) mixedCompileCore_computable).of_eq
    (fun T => by simp [Bool.cond_decide])

theorem mixedCompile_facts (T : LeanWang.TileSet) :
    mixedCompile T ≠ [] ∧ FaceConnected (mixedCompile T) ∧
    (LeanWang.TilesPlane T ↔ TranslationTiling.Tiles (mixedCompile T)) ∧
    ((mixedCompile T).length : ℝ) ≤ ((T.length:ℝ)+4) ^
      ((10:ℝ)^10 * Real.logb 2 (Real.logb 2 ((T.length:ℝ)+4))) := by
  by_cases ht : T = []
  · subst T
    simp only [mixedCompile,if_pos rfl,List.length_nil,Nat.cast_zero,zero_add]
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
    obtain ⟨hne,hconn,hiff,hbound⟩ := mixedCompileCore_channel_bound T hn
    simp only [mixedCompile,if_neg ht]
    refine ⟨hne,hconn,hiff,?_⟩
    have hcast : ((mixedCompileCore T).length:ℝ) ≤
        ((channelCount (mixedSystem T) ^ (1772*channelCount (mixedSystem T)):ℕ):ℝ) := by exact_mod_cast hbound
    apply hcast.trans
    exact Compiler.Size.mixed_channel_cap_real_bound hn

theorem mixedCompile_real_bound (T : LeanWang.TileSet) :
    ((mixedCompile T).length:ℝ) ≤ ((T.length:ℝ)+4) ^
      ((10:ℝ)^10 * Real.logb 2 (Real.logb 2 ((T.length:ℝ)+4))) := (mixedCompile_facts T).2.2.2

end
end TranslationTiling.FiniteCompiler.Effective
