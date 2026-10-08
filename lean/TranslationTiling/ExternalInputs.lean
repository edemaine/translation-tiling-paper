import TranslationTiling.SudokuArithmetic.Soundness
import TranslationTiling.External.Geometry
import TranslationTiling.External.Kim

namespace TranslationTiling

/-- The inputs used by the connected reduction itself. -/
structure ReductionInputs : Prop where
  rigidity : MSS.Rigidity
  shellRigidity : Kim.CosetRigidity

end TranslationTiling
