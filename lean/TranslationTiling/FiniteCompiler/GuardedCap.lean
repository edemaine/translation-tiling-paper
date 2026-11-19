import Mathlib.Data.Nat.Log

namespace TranslationTiling.FiniteCompiler.GuardedCompiler

def testLimit (d : ℕ) : ℕ := 2313+72*d^2+550+80*d

def stackCap (X : ℕ) : ℕ := 2*(6*X^2*(Nat.log 2 (2*X)+1)+65536+3)

def railCap (H Q : ℕ) : ℕ :=
  let A := 4000*H+2003
  let B := max (A^2) (4000*max (H^2) Q+2003)
  let a := (2*A+1)^2
  216*(4*a+7*(B+2)+1)*(4*a+1)

def cubeCap (H V J L : ℕ) : ℕ :=
  (201^3+3*7^3+11^3)*J*L*railCap H (V*L)

end TranslationTiling.FiniteCompiler.GuardedCompiler
