import Mathlib.Data.Nat.Log

namespace TranslationTiling.FiniteCompiler.PairSmall

/-- The four word tests, the structural tests, and one spare stack index. -/
def testLimit (d : ℕ) : ℕ := 4^9+6^9+(4^4*6^3+4^3*6^4)*d^2+550+80*d

/-- The numerical stacking cap. It is definitionally equal to
`freshCap (testLimit d) (256^4)`. -/
def projectedCap (d : ℕ) : ℕ :=
  let X := testLimit d
  2*(64*X^2*(Nat.log 2 (2*X)+1)+256^4+3)

end TranslationTiling.FiniteCompiler.PairSmall
