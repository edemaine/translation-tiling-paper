import TranslationTiling.EuclideanMembership.ConstraintSystem
import TranslationTiling.EuclideanMembership.EffectiveParameters

namespace TranslationTiling.EuclideanMembership
open Compiler.Effective
variable {d : ℕ}
@[fun_prop] theorem anchorPointApply {α : Type*} [Primcodable α]
    {p : α → Tile d} {i : α → Fin d} (hp : Primrec p) (hi : Primrec i) :
    Primrec (fun t => anchorPoint (p t) (i t)) :=
  applyFin (anchorPoint_primrec.comp hp) hi

@[fun_prop] theorem slotFormulaValue {α : Type*} [Primcodable α] (ar af : Bool)
    {z : α → Lattice d} (hz : Primrec z) : Primrec (fun a => slotFormula ar af (z a)) := by
  unfold slotFormula
  apply renameFormulaValue (hf := Primrec.const _)
  fun_prop

@[fun_prop] theorem reciprocalFormulaValue {α : Type*} [Primcodable α]
    {n : α → ℕ} (hn : Primrec n) : Primrec (fun a => reciprocalFormula d (n a)) := by
  unfold reciprocalFormula reciprocalPolynomial
  fun_prop

@[fun_prop] theorem offsetPolynomialValue {α : Type*} [Primcodable α]
    {p : α → Tile d} {z q : α → Lattice d} {a : α → Probe d} {i : α → Fin d}
    (hp : Primrec p) (hz : Primrec z) (hq : Primrec q) (ha : Primrec a) (hi : Primrec i) :
    Primrec (fun t => offsetPolynomial (p t) (z t) (a t) (q t) (i t)) := by
  unfold offsetPolynomial inversePolynomial probePolynomial centerPolynomial rowPolynomial
    shiftPolynomial reciprocalPolynomial indices
  fun_prop

@[fun_prop] theorem closedScalarValue {α : Type*} [Primcodable α]
    {p : α → Polynomial} (hp : Primrec p) : Primrec (fun a => closedScalar (p a)) := by
  unfold closedScalar
  fun_prop
@[fun_prop] theorem outsideScalarValue {α : Type*} [Primcodable α]
    {p : α → Polynomial} (hp : Primrec p) : Primrec (fun a => outsideScalar (p a)) := by
  unfold outsideScalar
  fun_prop

@[fun_prop] theorem closedFormulaValue {α : Type*} [Primcodable α]
    {p : α → Tile d} {z q : α → Lattice d} {a : α → Probe d}
    (hp : Primrec p) (hz : Primrec z) (hq : Primrec q) (ha : Primrec a) :
    Primrec (fun t => closedFormula (p t) (z t) (a t) (q t)) := by
  unfold closedFormula
  fun_prop
@[fun_prop] theorem outsideFormulaValue {α : Type*} [Primcodable α]
    {p : α → Tile d} {z q : α → Lattice d} {a : α → Probe d}
    (hp : Primrec p) (hz : Primrec z) (hq : Primrec q) (ha : Primrec a) :
    Primrec (fun t => outsideFormula (p t) (z t) (a t) (q t)) := by
  unfold outsideFormula
  fun_prop
@[fun_prop] theorem enabledFormulaValue {α : Type*} [Primcodable α]
    {z : α → Lattice d} (hz : Primrec z) : Primrec (fun t => enabledFormula (z t)) := by
  unfold enabledFormula presencePolynomial
  fun_prop
@[fun_prop] theorem disabledFormulaValue {α : Type*} [Primcodable α]
    {z : α → Lattice d} (hz : Primrec z) : Primrec (fun t => disabledFormula (z t)) := by
  unfold disabledFormula presencePolynomial
  fun_prop

@[fun_prop] theorem coverageFormulaValue {α : Type*} [Primcodable α]
    {p : α → Tile d} {a : α → Probe d} (hp : Primrec p) (ha : Primrec a) :
    Primrec (fun t => coverageFormula (p t) (a t)) := by
  unfold coverageFormula
  fun_prop

@[fun_prop] theorem packingFormulaValue {α : Type*} [Primcodable α]
    {p : α → Tile d} {z w q r : α → Lattice d} {a : α → Probe d}
    (hp : Primrec p) (hz : Primrec z) (hw : Primrec w) (hq : Primrec q)
    (hr : Primrec r) (ha : Primrec a) :
    Primrec (fun t => packingFormula (p t) (z t) (w t) (q t) (r t) (a t)) := by
  unfold packingFormula
  fun_prop

end TranslationTiling.EuclideanMembership
