import TranslationTiling.ExternalInputs
import TranslationTiling.Proofs.Complexity
import TranslationTiling.Proofs.CanonicalLineRule
import TranslationTiling.Proofs.PeriodicCertificates
import TranslationTiling.Proofs.PlanarPeriodicity
import TranslationTiling.Compiler.Main

/-! Short public statements. All imported mathematical inputs are explicit;
the complete compiler and its uniform computability are proved internally. -/

namespace TranslationTiling

theorem reduction (h : ReductionInputs) : Nonempty ConnectedWangReduction :=
  ⟨Compiler.connectedWangReduction h⟩

theorem compiler_effectivity : Computable Compiler.connectedCompile :=
  Compiler.connectedCompile_computable

/-- Connectivity of the compiler output has no mathematical input. -/
theorem compiler_connectivity (T : LeanWang.TileSet) :
    FaceConnected (Compiler.connectedCompile T) := Compiler.connectedCompile_connected T

theorem compiler_correct (h : ReductionInputs) (T : LeanWang.TileSet) :
    LeanWang.TilesPlane T ↔ Tiles (Compiler.connectedCompile T) :=
  Compiler.connectedCompile_correct h T

theorem compilation (h : ReductionInputs) (T : LeanWang.TileSet) :
    ∃ F : Tile 3, F ≠ [] ∧ FaceConnected F ∧ (LeanWang.TilesPlane T ↔ Tiles F) :=
  ⟨Compiler.connectedCompile T, Compiler.connectedCompile_nonempty T,
    Compiler.connectedCompile_connected T, compiler_correct h T⟩

theorem lattice_effectivity : Computable Compiler.integerTile :=
  Compiler.integerTile_computable

theorem shell_effectivity : Computable Compiler.connectedTile :=
  Compiler.connectedTile_computable

theorem sudoku_soundness : Sudoku.Soundness := Sudoku.soundness

theorem sudoku_equivalence (T : LeanWang.TileSet) :
    LeanWang.TilesPlane T ↔ ∃ W : Sudoku.Array T,
      Sudoku.LineRule W ∧ Sudoku.NonconstantColumns W := Sudoku.sudoku_iff_wang T

theorem membership (d : ℕ) : LeanWang.CoREPred (@Tiles d) := tiles_coRE d

theorem planar_periodicity : PlanarPeriodicity := planarPeriodicity_proved

theorem planar_decidability : ComputablePred (@Tiles 2) :=
  planar_decidable planar_periodicity

theorem rounding {d : ℕ} (F : Tile d) : RealTiles F ↔ Tiles F := realTiles_iff_tiles F

theorem completeness (h : ReductionInputs) : LeanWang.CoREComplete (@Tiles 3) :=
  coRE_complete_of_reduction (Compiler.wangReduction Sudoku.soundness h.rigidity)

theorem undecidability (h : ReductionInputs) : ¬ ComputablePred (@Tiles 3) :=
  undecidable_of_reduction (Compiler.wangReduction Sudoku.soundness h.rigidity)

theorem higher_dimension (h : ReductionInputs) {d : ℕ} (hd : 3 ≤ d) :
    LeanWang.CoREComplete (@Tiles d) :=
  coRE_complete_in_dimension (Compiler.wangReduction Sudoku.soundness h.rigidity) hd

theorem real_membership (d : ℕ) : LeanWang.CoREPred (@RealTiles d) := realTiles_coRE d

theorem connected_hardness (h : ReductionInputs) : LeanWang.CoREHard (@ConnectedTiles 3) :=
  connected_hard_of_reduction (Compiler.connectedWangReduction h)

theorem connected_membership (d : ℕ) : LeanWang.CoREPred (@ConnectedTiles d) :=
  connectedTiles_coRE d

theorem connected_completeness (h : ReductionInputs) : LeanWang.CoREComplete (@ConnectedTiles 3) :=
  connected_complete_of_reduction (Compiler.connectedWangReduction h)

theorem real_completeness (h : ReductionInputs) : LeanWang.CoREComplete (@RealTiles 3) :=
  real_coRE_complete_of_reduction (Compiler.wangReduction Sudoku.soundness h.rigidity)

theorem dimension_optimality (h : ReductionInputs) :
    IsLeast {d : ℕ | ¬ ComputablePred (@Tiles d)} 3 :=
  optimal_dimension_of_planar (Compiler.wangReduction Sudoku.soundness h.rigidity)
    planar_decidability

theorem connected_output (h : ReductionInputs) (T : LeanWang.TileSet) :
    Compiler.connectedCompile T ≠ [] ∧ FaceConnected (Compiler.connectedCompile T) ∧
      (LeanWang.TilesPlane T ↔ Tiles (Compiler.connectedCompile T)) :=
  ⟨Compiler.connectedCompile_nonempty T,
    Compiler.connectedCompile_connected T, compiler_correct h T⟩

end TranslationTiling
