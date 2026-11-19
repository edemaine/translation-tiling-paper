import TranslationTiling.Compiler.FiveTileInputs

/-! Kernel-checked patch certificates. Derived clauses are named separately
so later steps refer to theorem constants rather than embedding their proofs.
This controls memory use without changing the kernel's checking obligations. -/
namespace TranslationTiling.Compiler.FiveTile
open Mathlib.Tactic
open Lean Elab Meta
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

private partial def namedConj (arr : Array (Array Int)) (name : Name)
    (start stop : Nat) : MetaM Expr := do
  let value ← if stop-start=1 then
      pure <| mkApp (mkConst ``Sat.Fmla.one) (Sat.buildClause arr[start]!)
    else do
      let mid := start+(stop-start)/2
      let left ← namedConj arr name start mid
      let right ← namedConj arr name mid stop
      pure <| mkApp2 (mkConst ``Sat.Fmla.and) left right
  let n := name ++ Name.mkSimple s!"context{start}_{stop}"
  addDecl <| Declaration.defnDecl {
    name := n, levelParams := [], type := mkConst ``Sat.Fmla,
    value, hints := ReducibilityHints.regular 0, safety := .safe }
  return mkConst n

private partial def namedClauses (arr : Array (Array Int)) (ctx : Expr)
    (start stop : Nat) (f proof : Expr) (db : Std.HashMap Nat Mathlib.Tactic.Sat.Clause) :
    MetaM (Std.HashMap Nat Mathlib.Tactic.Sat.Clause) := do
  let info ← getConstInfoDefn f.constName!
  if stop-start=1 then
    let clause := info.value.appArg!
    let pr := mkApp3 (mkConst ``Sat.Fmla.proof_of_subsumes) ctx clause proof
    return db.insert (start+1) { lits := arr[start]!, expr := clause, proof := pr }
  else
    let mid := start+(stop-start)/2
    let left := info.value.appFn!.appArg!
    let right := info.value.appArg!
    let lp := mkApp4 (mkConst ``Sat.Fmla.subsumes_left) ctx left right proof
    let rp := mkApp4 (mkConst ``Sat.Fmla.subsumes_right) ctx left right proof
    let db ← namedClauses arr ctx start mid left lp db
    namedClauses arr ctx mid stop right rp db

private def namedFromLRAT (cnf lrat : String) (name : Name) : MetaM Expr := do
  let .success _ (_,arr) := Sat.Parser.parseDimacs ⟨_, cnf.startPos⟩
    | throwError "parse CNF failed"
  let .success _ steps := Sat.Parser.parseLRAT ⟨_, lrat.startPos⟩
    | throwError "parse LRAT failed"
  if arr.isEmpty then throwError "empty CNF"
  let ctx ← namedConj arr name 0 arr.size
  let mut db ← namedClauses arr ctx 0 arr.size ctx
    (mkApp (mkConst ``Sat.Fmla.subsumes_self) ctx) {}
  let mut named : Std.HashSet Nat := {}
  for step in steps do
    match step with
    | .del ds => db := ds.foldl (·.erase ·) db
    | .add i ns hints =>
      for hint in hints do
        let j := hint.natAbs
        if j ≤ arr.size && !named.contains j then
          let some cl := db[j]? | throwError "missing input clause {j}"
          let inputName := name ++ Name.mkSimple s!"input{j}"
          addDecl <| Declaration.thmDecl {
            name := inputName, levelParams := [],
            type := mkApp2 (mkConst ``Sat.Fmla.proof) ctx cl.expr, value := cl.proof }
          db := db.insert j { cl with proof := mkConst inputName }
          named := named.insert j
      if i % 1000 == 0 then logInfo m!"checked LRAT through clause {i}"
      let clause := Sat.buildClause ns
      let .ok proof := Sat.buildProofStep db ns hints ctx clause
        | throwError "invalid RUP step {i}"
      let stepName := name ++ Name.mkSimple s!"step{i}"
      addDecl <| Declaration.thmDecl {
        name := stepName, levelParams := [],
        type := mkApp2 (mkConst ``Sat.Fmla.proof) ctx clause, value := proof }
      if ns.isEmpty then return mkConst stepName
      db := db.insert i { lits := ns, expr := clause, proof := mkConst stepName }
  throwError "no empty clause"

elab "five_tile_certificate " p:num ppSpace cnf:term:max ppSpace lrat:term:max : command => do
  let p := p.getNat
  let ns ← getCurrNamespace
  Command.liftTermElabM do
    let cnf ← unsafe Term.evalTerm String (mkConst ``String) cnf
    let lrat ← unsafe Term.evalTerm String (mkConst ``String) lrat
    let pf ← namedFromLRAT cnf lrat (ns ++ Name.mkSimple s!"case{p}")
    let type := mkApp2 (mkConst ``Sat.Fmla.proof)
      (mkConst (ns ++ Name.mkSimple s!"formula{p}")) (Sat.buildClause #[])
    addDecl <| Declaration.thmDecl {
      name := ns ++ Name.mkSimple s!"case{p}_unsat", levelParams := [], type, value := pf }

end TranslationTiling.Compiler.FiveTile
