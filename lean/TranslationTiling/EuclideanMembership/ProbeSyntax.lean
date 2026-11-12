import TranslationTiling.EuclideanMembership.OrientationSyntax

namespace TranslationTiling.EuclideanMembership
open Rotations.General (EPoint)
open Compiler.Effective (indexed)
noncomputable section
variable {d : ℕ}

def reciprocalPolynomial (d n : ℕ) := pVar (reciprocalIndex d n)
def shiftPolynomial (z : Lattice d) (i : Fin d) := pVar (slotIndex z (Nat.pair 1 i.val))
def rowPolynomial (z : Lattice d) (i j : Fin d) :=
  pVar (slotIndex z (Nat.pair 2 (Nat.pair i.val j.val)))
def presencePolynomial (z : Lattice d) := pVar (slotIndex z (Nat.pair 0 0))
def centerPolynomial (z : Lattice d) (i : Fin d) :=
  pMul (pAdd (pConst (2*indexed z i)) (shiftPolynomial z i)) (reciprocalPolynomial d (cellScale d-1))
def probePolynomial (a : Probe d) (i : Fin d) :=
  pMul (pConst (indexed a.1 i)) (reciprocalPolynomial d a.2)
def inversePolynomial (P : Tile d) (z : Lattice d) (a : Probe d) (i : Fin d) :=
  pAdd (pConst (indexed (anchorPoint P) i)) (pSum ((indices d).map fun j =>
    pMul (rowPolynomial z j i) (pSub (probePolynomial a j) (centerPolynomial z j))))
def offsetPolynomial (P : Tile d) (z : Lattice d) (a : Probe d) (p : Lattice d) (i : Fin d) :=
  pSub (inversePolynomial P z a i) (pConst (indexed p i))

 theorem evaluate_inversePolynomial (P : Tile d) (z : Lattice d) (a : Probe d)
    (i : Fin d) (x : Assignment) :
    evaluate (inversePolynomial P z a i) (coordinates x)=inversePoint x P z (probeValue x a) i := by
  simp [inversePolynomial,probePolynomial,centerPolynomial,rowPolynomial,shiftPolynomial,
    reciprocalPolynomial,evaluate_sum,List.map_map,sum_indices,inversePoint,slotRows,
    probeValue,slotCenter,slotShift,reciprocalValue,coordinates,Int.cast_mul,indexed]

 theorem evaluate_offsetPolynomial (P : Tile d) (z : Lattice d) (a : Probe d)
    (p : Lattice d) (i : Fin d) (x : Assignment) :
    evaluate (offsetPolynomial P z a p i) (coordinates x)=
      inversePoint x P z (probeValue x a) i-(p i : ℝ) := by
  simp only [offsetPolynomial,evaluate_sub,evaluate_inversePolynomial,evaluate_const,indexed]

def closedScalar (p : Polynomial) :=
  fAnd (fLe (pSub (pMul (pConst 2) p) (pConst 1)))
    (fLe (pSub (pNeg (pMul (pConst 2) p)) (pConst 1)))
def outsideScalar (p : Polynomial) :=
  fOr (fLe (pSub (pConst 1) (pMul (pConst 2) p)))
    (fLe (pAdd (pConst 1) (pMul (pConst 2) p)))
@[simp] theorem closedScalar_iff (p : Polynomial) (v : ℕ → ℝ) :
    Holds (closedScalar p) 0 v ↔ |evaluate p v| ≤ 1/2 := by
  simp only [closedScalar,holds_and,holds_le,evaluate_sub,evaluate_mul,evaluate_const,evaluate_neg,Int.cast_ofNat,Int.cast_one,Int.cast_zero]
  rw [abs_le]
  constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> linarith
@[simp] theorem outsideScalar_iff (p : Polynomial) (v : ℕ → ℝ) :
    Holds (outsideScalar p) 0 v ↔ ¬ |evaluate p v| < 1/2 := by
  simp only [outsideScalar,holds_or,holds_le,evaluate_sub,evaluate_mul,evaluate_const,evaluate_add,Int.cast_ofNat,Int.cast_one,Int.cast_zero]
  rw [abs_lt,not_and_or,not_lt,not_lt]
  constructor <;> rintro (h | h)
  · exact Or.inr (by linarith)
  · exact Or.inl (by linarith)
  · exact Or.inr (by linarith)
  · exact Or.inl (by linarith)

def closedFormula (P : Tile d) (z : Lattice d) (a : Probe d) (p : Lattice d) :=
  fAll ((indices d).map fun i => closedScalar (offsetPolynomial P z a p i))
def outsideFormula (P : Tile d) (z : Lattice d) (a : Probe d) (p : Lattice d) :=
  fAny ((indices d).map fun i => outsideScalar (offsetPolynomial P z a p i))
def enabledFormula (z : Lattice d) := fEq (presencePolynomial z) (pConst 1)
def disabledFormula (z : Lattice d) := fEq (presencePolynomial z) (pConst 0)
def coverageFormula (P : Tile d) (a : Probe d) :=
  fAny ((probeCells P a).map fun z => fAnd (enabledFormula z)
    (fAny (P.map fun p => closedFormula P z a p)))
def packingFormula (P : Tile d) (z w : Lattice d) (p q : Lattice d) (a : Probe d) :=
  fOr (disabledFormula z) (fOr (disabledFormula w)
    (fOr (outsideFormula P z a p) (outsideFormula P w a q)))
def reciprocalFormula (d n : ℕ) :=
  fEq (pMul (pConst ((n : ℤ)+1)) (reciprocalPolynomial d n)) (pConst 1)

@[simp] theorem closedFormula_iff (P : Tile d) (z : Lattice d) (a : Probe d) (p : Lattice d)
    (x : Assignment) : Holds (closedFormula P z a p) 0 (coordinates x) ↔
      ClosedAt x P z (probeValue x a) p := by
  simp [closedFormula,ClosedAt,evaluate_offsetPolynomial]
@[simp] theorem outsideFormula_iff (P : Tile d) (z : Lattice d) (a : Probe d) (p : Lattice d)
    (x : Assignment) : Holds (outsideFormula P z a p) 0 (coordinates x) ↔
      ¬ OpenAt x P z (probeValue x a) p := by
  simp [outsideFormula,OpenAt,evaluate_offsetPolynomial]
@[simp] theorem enabledFormula_iff (z : Lattice d) (x : Assignment) :
    Holds (enabledFormula z) 0 (coordinates x) ↔ Enabled x z := by
  simp [enabledFormula,presencePolynomial,presence,coordinates,Enabled]
@[simp] theorem disabledFormula_iff (z : Lattice d) (x : Assignment) :
    Holds (disabledFormula z) 0 (coordinates x) ↔ presence x z=0 := by
  simp [disabledFormula,presencePolynomial,presence,coordinates]
@[simp] theorem coverageFormula_iff (P : Tile d) (a : Probe d) (x : Assignment) :
    Holds (coverageFormula P a) 0 (coordinates x) ↔
      ∃ z ∈ probeCells P a, Enabled x z ∧ ∃ p ∈ P, ClosedAt x P z (probeValue x a) p := by
  simp [coverageFormula]
@[simp] theorem packingFormula_iff (P : Tile d) (z w : Lattice d) (p q : Lattice d)
    (a : Probe d) (x : Assignment) : Holds (packingFormula P z w p q a) 0 (coordinates x) ↔
      presence x z=0 ∨ presence x w=0 ∨
        ¬ OpenAt x P z (probeValue x a) p ∨ ¬ OpenAt x P w (probeValue x a) q := by
  simp [packingFormula]
@[simp] theorem reciprocalFormula_iff (n : ℕ) (x : Assignment) :
    Holds (reciprocalFormula d n) 0 (coordinates x) ↔
      ((n : ℝ)+1)*reciprocalValue (d := d) x n=1 := by
  simp [reciprocalFormula,reciprocalPolynomial,reciprocalValue,coordinates]
end
end TranslationTiling.EuclideanMembership
