import TranslationTiling.SudokuArithmetic.SmallPrimeSAT

/-! Kernel-checked finite seed certificates. The LRAT elaborator constructs ordinary
propositional proofs; the kernel also checks that the input CNFs are definitionally
identical to `satFormula`. No native-evaluation axioms are used. -/
namespace TranslationTiling.Sudoku.ArithmeticRule.SmallPrime
open Mathlib.Tactic
open Lean Elab
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

elab "small_prime_seed_certificate " p:num ppSpace cnf:term:max ppSpace lrat:term:max : command => do
  let p := p.getNat
  unless p=5 || p=7 do throwError "expected prime 5 or 7"
  let ns ← getCurrNamespace
  Command.liftTermElabM do
    let cnf ← unsafe Term.evalTerm String (mkConst ``String) cnf
    let lrat ← unsafe Term.evalTerm String (mkConst ``String) lrat
    let (_,_,_,pf) ← Sat.fromLRATAux cnf lrat (ns ++ Name.mkSimple s!"seed{p}")
    let type := mkApp2 (mkConst ``Sat.Fmla.proof)
      (mkApp (mkConst ``satFormula) (mkNatLit p)) (Sat.buildClause #[])
    addDecl <| Declaration.thmDecl {
      name := ns ++ Name.mkSimple s!"seed{p}_unsat", levelParams := [], type, value := pf }
