import TranslationTiling.ExternalInputs
import TranslationTiling.Proofs.Complexity
import TranslationTiling.Proofs.CanonicalLineRule
import TranslationTiling.Proofs.PeriodicCertificates

/-! The public statement surface. Theorems below have checked proofs in `Proofs/`.
`Claims` records outstanding targets as propositions, not as assumed theorems. -/

namespace TranslationTiling

namespace Claims

/-- Outstanding: the paper's computable construction from its geometric imports. -/
def reduction : Prop := ReductionInputs → Nonempty ConnectedWangReduction

/-- Outstanding: the main lattice consequence using only the named external inputs. -/
def completeness : Prop := ReductionInputs → LeanWang.CoREComplete (@Tiles 3)

/-- Outstanding: the connected-input assertion of the current main theorem. -/
def connected_completeness : Prop :=
  ReductionInputs → LeanWang.CoREComplete (@ConnectedTiles 3)

/-- Outstanding: the real-translation version using only the named external inputs. -/
def real_completeness : Prop := ReductionInputs → LeanWang.CoREComplete (@RealTiles 3)

/-- Outstanding: dimension three is the least undecidable dimension. -/
def optimal_dimension : Prop :=
  ExternalInputs → IsLeast {d : ℕ | ¬ ComputablePred (@Tiles d)} 3

end Claims

theorem sudoku_equivalence (h : Sudoku.Soundness) (T : LeanWang.TileSet) :
    LeanWang.TilesPlane T ↔ ∃ W : Sudoku.Array T,
      Sudoku.LineRule W ∧ Sudoku.NonconstantColumns W := Sudoku.sudoku_iff_wang h T

theorem membership (d : ℕ) : LeanWang.CoREPred (@Tiles d) := tiles_coRE d

theorem planar_decidability (h : PlanarPeriodicity) : ComputablePred (@Tiles 2) :=
  planar_decidable h

theorem rounding {d : ℕ} (F : Tile d) : RealTiles F ↔ Tiles F := realTiles_iff_tiles F

theorem completeness (r : WangReduction) : LeanWang.CoREComplete (@Tiles 3) :=
  coRE_complete_of_reduction r

theorem undecidability (r : WangReduction) : ¬ ComputablePred (@Tiles 3) :=
  undecidable_of_reduction r

theorem higher_dimension (r : WangReduction) {d : ℕ} (h : 3 ≤ d) :
    LeanWang.CoREComplete (@Tiles d) := coRE_complete_in_dimension r h

theorem real_membership (d : ℕ) : LeanWang.CoREPred (@RealTiles d) := realTiles_coRE d

theorem connected_hardness (r : ConnectedWangReduction) :
    LeanWang.CoREHard (@ConnectedTiles 3) := connected_hard_of_reduction r

theorem connected_membership (d : ℕ) : LeanWang.CoREPred (@ConnectedTiles d) :=
  connectedTiles_coRE d

theorem connected_completeness (r : ConnectedWangReduction) :
    LeanWang.CoREComplete (@ConnectedTiles 3) := connected_complete_of_reduction r

theorem real_completeness (r : WangReduction) : LeanWang.CoREComplete (@RealTiles 3) :=
  real_coRE_complete_of_reduction r

theorem dimension_optimality (r : WangReduction) (h : PlanarPeriodicity) :
    IsLeast {d : ℕ | ¬ ComputablePred (@Tiles d)} 3 :=
  optimal_dimension_of_planar r (planar_decidable h)

theorem connected_output (r : ConnectedWangReduction) (T : LeanWang.TileSet) (h : T ≠ []) :
    r.tile T ≠ [] ∧ FaceConnected (r.tile T) ∧ (LeanWang.TilesPlane T ↔ Tiles (r.tile T)) :=
  ⟨r.nonempty T h, r.connected T h, r.correct T⟩

end TranslationTiling
