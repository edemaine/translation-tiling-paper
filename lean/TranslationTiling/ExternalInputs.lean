import TranslationTiling.SudokuArithmetic.Soundness
import TranslationTiling.MSS.GridAssembly
import TranslationTiling.External.Kim

namespace TranslationTiling

/-- The inputs used by the connected reduction itself. -/
structure ReductionInputs : Prop where
  shellRigidity : Kim.CosetRigidity

end TranslationTiling
