import TranslationTiling.FiniteCompiler.SupportBounds
import TranslationTiling.Compiler.PowerBounds

namespace TranslationTiling.FiniteCompiler.Size

open Compiler.Size

theorem usefulPrimeCap_powerBound : PowerBound usefulPrimeCap := by
  exact (((PowerBound.const 8).mul
    (((PowerBound.const usefulStart).add ((PowerBound.const 2).mul PowerBound.id)).add
      (PowerBound.const 1))).pow 2)

theorem digitPrimeCap_powerBound (B : ℕ) : PowerBound (digitPrimeCap B) := by
  have hU := usefulPrimeCap_powerBound
  have hthreshold := ((((hU.pow 2).add ((PowerBound.const 2).mul hU)).add
    (PowerBound.const Sudoku.p)).add (PowerBound.const Sudoku.q)).add (PowerBound.const 3)
  exact ((PowerBound.const 8).mul
    ((hthreshold.add (PowerBound.id.mul (PowerBound.const (B + 1)))).add
      (PowerBound.const 1))).pow 2

theorem parameterBase_powerBound (B S : ℕ) : PowerBound (parameterBase B S) := by
  exact (((((((digitPrimeCap_powerBound B).pow (B + 1)).add usefulPrimeCap_powerBound).add
    (PowerBound.const residueModulus)).add PowerBound.id).add
      (PowerBound.const (B + 1))).add (PowerBound.const S)).add (PowerBound.const 2)

end TranslationTiling.FiniteCompiler.Size
