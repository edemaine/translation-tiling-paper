import TranslationTiling.FiniteCompiler.Effective.SevenCompilerCore
import TranslationTiling.Compiler.FiveTileClassification

namespace TranslationTiling.Compiler.FiveTile

/-- For a nonempty input of at most five tiles, a finite square decides plane tilability. -/
theorem hasPatch_iff_tilesPlane (T : LeanWang.TileSet) (hn : T≠[]) (hsize : T.length≤5) :
    hasPatch T ↔ LeanWang.TilesPlane T :=
  (hasPatch_iff_accepts T).trans (accepts_iff plane_of_patch T hn hsize)

end TranslationTiling.Compiler.FiveTile

namespace TranslationTiling.FiniteCompiler.Effective

theorem sevenCompile_checked_facts (T : LeanWang.TileSet) :
    sevenCompile T≠[] ∧ FaceConnected (sevenCompile T) ∧
    (LeanWang.TilesPlane T ↔ TranslationTiling.Tiles (sevenCompile T)) ∧
    ((sevenCompile T).length:ℝ)≤((T.length:ℝ)+4)^
      (700*Real.logb 2 (Real.logb 2 ((T.length:ℝ)+4))) :=
  sevenCompile_facts Compiler.FiveTile.plane_of_patch T

theorem sevenCompile_checked_small_bound (T : LeanWang.TileSet) (h : T.length≤5) :
    (sevenCompile T).length≤2^250 :=
  sevenCompile_small_bound Compiler.FiveTile.plane_of_patch T h

theorem sevenCompile_checked_real_bound (T : LeanWang.TileSet) :
    ((sevenCompile T).length:ℝ)≤((T.length:ℝ)+4)^
      (700*Real.logb 2 (Real.logb 2 ((T.length:ℝ)+4))) :=
  (sevenCompile_checked_facts T).2.2.2

theorem sevenCompile_checked_single_bound (T : LeanWang.TileSet) (h : T.length=1) :
    (sevenCompile T).length≤2^250 :=
  sevenCompile_checked_small_bound T (by omega)

end TranslationTiling.FiniteCompiler.Effective
