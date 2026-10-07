import TranslationTiling.External.Sudoku
import TranslationTiling.External.Geometry
import TranslationTiling.External.Kim

namespace TranslationTiling

/-- The inputs used by the connected reduction itself. -/
structure ReductionInputs : Prop where
  sudoku : Sudoku.Soundness
  rigidity : MSS.Rigidity
  connectedness : Kim.Rigidity

/-- Planar periodicity is additionally used for dimension optimality. -/
structure ExternalInputs : Prop extends ReductionInputs where
  planar : PlanarPeriodicity

end TranslationTiling
