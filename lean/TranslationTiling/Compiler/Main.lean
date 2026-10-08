import TranslationTiling.Compiler.EffectiveSystem
import TranslationTiling.Compiler.EffectiveConnected

set_option maxRecDepth 1000
set_option maxHeartbeats 100000

namespace TranslationTiling.Compiler

open scoped Classical

/-- Uniform consolidation of the complete Wang gadget family. -/
noncomputable def cyclicCompiler (T : LeanWang.TileSet) : CyclicTileData :=
  Effective.stackCompiler (Effective.numericalOrder T, Effective.family T)

theorem cyclicCompiler_computable : Computable cyclicCompiler := by
  have h := Effective.stackCompiler_computable.comp
    (Effective.numericalOrder_computable.pair Effective.family_computable)
  exact h

theorem cyclicCompiler_pos (T : LeanWang.TileSet) : 0 < (cyclicCompiler T).1 :=
  Effective.stackCompiler_pos _ (by
    rw [Effective.numericalOrder_eq]
    exact (Effective.parameters T).cyclicOrder_pos) _

theorem cyclicCompiler_nonempty (T : LeanWang.TileSet) : (cyclicCompiler T).2 ≠ [] := by
  have hs := Effective.family_length_pos T
  apply Effective.stackCompiler_nonempty _ _ hs
  refine ⟨⟨0, hs⟩, ?_⟩
  change (Effective.family T).getD 0 [] ≠ []
  simpa only [Effective.family, List.getD_cons_zero] using Effective.kernelCompiler_nonempty T

theorem cyclicCompiler_correct (sound : Sudoku.Soundness) (T : LeanWang.TileSet) :
    LeanWang.TilesPlane T ↔ ∃ A : Set (Plane × ZMod (cyclicCompiler T).1),
      Tiles (cyclicTileSet (cyclicCompiler T).1 (cyclicCompiler T).2) A := by
  have hN : 0 < Effective.numericalOrder T := by
    rw [Effective.numericalOrder_eq]
    exact (Effective.parameters T).cyclicOrder_pos
  exact (Effective.family_tiling_iff sound T).trans
    (Effective.stackCompiler_correct _ hN _ (Effective.family_length_pos T))

/-- The main Wang-to-integer-lattice compiler. -/
noncomputable def compile (T : LeanWang.TileSet) : Tile 3 := integerTile (cyclicCompiler T)

theorem compile_computable : Computable compile :=
  integerTile_computable.comp cyclicCompiler_computable

theorem compile_nonempty (T : LeanWang.TileSet) : compile T ≠ [] :=
  integerTile_nonempty _ (cyclicCompiler_nonempty T)

theorem compile_correct (T : LeanWang.TileSet) :
    LeanWang.TilesPlane T ↔ TranslationTiling.Tiles (compile T) :=
  (cyclicCompiler_correct Sudoku.soundness T).trans
    (integerTile_correct MSS.rigidity _ (cyclicCompiler_pos T) (cyclicCompiler_nonempty T))

/-- The unconditional computable Wang-to-integer-tile reduction. -/
noncomputable def wangReduction : WangReduction where
  tile := compile
  computable := compile_computable
  nonempty := fun T _ => compile_nonempty T
  correct := compile_correct

noncomputable def connectedCompile (T : LeanWang.TileSet) : Tile 3 := connectedTile (compile T)

theorem connectedCompile_computable : Computable connectedCompile :=
  connectedTile_computable.comp compile_computable

theorem connectedCompile_nonempty (T : LeanWang.TileSet) :
    connectedCompile T ≠ [] := connectedTile_nonempty _ (compile_nonempty T)

theorem connectedCompile_connected (T : LeanWang.TileSet) :
    FaceConnected (connectedCompile T) := connectedTile_connected _

theorem connectedCompile_correct (T : LeanWang.TileSet) :
    LeanWang.TilesPlane T ↔ TranslationTiling.Tiles (connectedCompile T) :=
  (compile_correct T).trans
    (connectedTile_correct Kim.cosetRigidity _).symm

noncomputable def connectedWangReduction : ConnectedWangReduction where
  tile := connectedCompile
  computable := connectedCompile_computable
  nonempty := fun T _ => connectedCompile_nonempty T
  correct := connectedCompile_correct
  connected := fun T _ => connectedCompile_connected T

end TranslationTiling.Compiler
