import TranslationTiling.SudokuArithmetic.SmallPrimeRecovery
import TranslationTiling.SudokuArithmetic.SmallPrimeCertificate5
import TranslationTiling.SudokuArithmetic.SmallPrimeCertificate7
import TranslationTiling.SudokuArithmetic.FivePointRecovery
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.Prime

namespace TranslationTiling.Sudoku.ArithmeticRule

/-- All primes at least five admit the global affine approximation. -/
theorem global_affine_approximation_improved {p : Nat} (hp : p.Prime) (hlarge : 4<p)
    {W : WordArray p} (hW : LineRule p W) :
    ∃ A B C : ZMod p, AffineApproximation W A B C := by
  by_cases hsmall : p=5 ∨ p=7
  · rcases hsmall with rfl|rfl
    · exact SmallPrime.global_affine_of_certificates hp hlarge SmallPrime.seed5_unsat
        SmallPrime.thirdTest5 SmallPrime.midTest5_1 SmallPrime.midTest5_3 hW
    · exact SmallPrime.global_affine_of_certificates hp hlarge SmallPrime.seed7_unsat
        SmallPrime.thirdTest7 SmallPrime.midTest7_1 SmallPrime.midTest7_3 hW
  · have hlarge' : 10<p := by
      by_contra hn
      interval_cases p <;> norm_num at *
    exact global_affine_approximation hp hlarge' hW

end TranslationTiling.Sudoku.ArithmeticRule
