import TranslationTiling.FiniteCompiler.Effective.CompactActivation
import TranslationTiling.FiniteCompiler.Effective.FixedCorrect

namespace TranslationTiling.FiniteCompiler.Effective

open Compiler Compiler.Effective

noncomputable section

set_option maxRecDepth 10000
set_option maxHeartbeats 2500000

/-- The two useful primes and the digit primes of each channel in dense order. -/
abbrev GuardedRows := List (ℕ × ℕ × List ℕ)
abbrev GuardedAssignments := List (ℕ × ℕ)

def rowA (rs : GuardedRows) (i : ℕ) : ℕ := (rs.getD i (0,0,[])).1
def rowB (rs : GuardedRows) (i : ℕ) : ℕ := (rs.getD i (0,0,[])).2.1
def rowDigits (rs : GuardedRows) (i : ℕ) : List ℕ := (rs.getD i (0,0,[])).2.2
def rowR (rs : GuardedRows) (i : ℕ) : ℕ := (rowDigits rs i).prod

def guardedModuli (rs : GuardedRows) : List ℕ :=
  (List.range rs.length).map (rowR rs)

def guardedOrder (rs : GuardedRows) : ℕ :=
  1225*((List.range rs.length).map (fun i => (rowR rs i)^2 * rowA rs i * rowB rs i)).prod

@[fun_prop] theorem rowA_primrec : Primrec (fun z : GuardedRows × ℕ => rowA z.1 z.2) := by
  unfold rowA
  fun_prop
@[fun_prop] theorem rowB_primrec : Primrec (fun z : GuardedRows × ℕ => rowB z.1 z.2) := by
  unfold rowB
  fun_prop
@[fun_prop] theorem rowDigits_primrec : Primrec (fun z : GuardedRows × ℕ => rowDigits z.1 z.2) := by
  unfold rowDigits
  fun_prop
@[fun_prop] theorem rowR_primrec : Primrec (fun z : GuardedRows × ℕ => rowR z.1 z.2) :=
  product_primrec.comp rowDigits_primrec
@[fun_prop] theorem guardedModuli_primrec : Primrec guardedModuli := by
  unfold guardedModuli
  fun_prop
@[fun_prop] theorem guardedOrder_primrec : Primrec guardedOrder := by
  have hp : Primrec (fun rs : GuardedRows =>
      (List.range rs.length).map (fun i => (rowR rs i)^2 * rowA rs i * rowB rs i)) := by
    simp only [pow_two]
    fun_prop
  exact natMul (Primrec.const 1225) (product_primrec.comp hp)

def guardedOther (rs : GuardedRows) (i : ℕ) : List ℕ :=
  ((List.range rs.length).filter (fun j => decide (j ≠ i))).map (rowR rs)

def guardedEnv (rs : GuardedRows) (i : ℕ) : ActivationEnvironment :=
  ((guardedOrder rs,guardedOther rs i),(rowR rs i,rowA rs i,rowB rs i,1225))

def guardedInvariance (rs : GuardedRows) (i : ℕ) (h : Plane) (g : Option ℕ) : CyclicTile :=
  invarianceCodes (guardedOrder rs) (guardedModuli rs) (rowA rs i) (rowB rs i) h
    ((List.range rs.length).map fun j => (rowR rs j, if g = some j then 1 % rowR rs j else 0))

@[fun_prop] theorem guardedEnv_primrec : Primrec (fun z : GuardedRows × ℕ => guardedEnv z.1 z.2) := by
  unfold guardedEnv guardedOther
  fun_prop

@[fun_prop] theorem guardedInvariance_primrec :
    Primrec (fun z : GuardedRows × ℕ × Plane × Option ℕ => guardedInvariance z.1 z.2.1 z.2.2.1 z.2.2.2) := by
  unfold guardedInvariance
  apply invarianceCodes_primrec.comp (g := fun z : GuardedRows × ℕ × Plane × Option ℕ =>
    ((guardedOrder z.1,guardedModuli z.1),(rowA z.1 z.2.1,rowB z.1 z.2.1),z.2.2.1,
      (List.range z.1.length).map fun j =>
        (rowR z.1 j,if z.2.2.2 = some j then 1 % rowR z.1 j else 0)))
  fun_prop

def guardedRawActivation (rs : GuardedRows) (slopes : List ℕ) : List CyclicTile :=
  ((List.range (rs.length-2)).map fun i => compactCodes (guardedEnv rs i) (slopes.getD i 0)) ++
    (List.range 2).map fun j =>
      seedCodes (guardedEnv rs (rs.length-2+j)) (rowA rs (rs.length-2+(1-j))) 35

def guardedRawDependence (rs : GuardedRows) (slopes : List ℕ) : List CyclicTile :=
  (List.range rs.length).flatMap (fun i =>
    ((List.range rs.length).filter (fun j => decide (j ≠ i))).map
      (fun j => guardedInvariance rs i 0 (some j))) ++
  ((List.range (rs.length-2)).map fun i =>
    guardedInvariance rs i (1,-(slopes.getD i 0 : ℤ)) none) ++
  (List.range 2).flatMap fun j =>
    [guardedInvariance rs (rs.length-2+j) (35,0) none,
     guardedInvariance rs (rs.length-2+j) (0,35) none]

@[fun_prop] theorem guardedRawActivation_primrec :
    Primrec (fun z : GuardedRows × List ℕ => guardedRawActivation z.1 z.2) := by
  unfold guardedRawActivation
  have hs : Primrec (fun z : (GuardedRows × List ℕ) × ℕ =>
      (guardedEnv z.1.1 (z.1.1.length-2+z.2),rowA z.1.1 (z.1.1.length-2+(1-z.2)),35)) := by
    fun_prop
  have h := seedCodes_primrec.comp hs
  fun_prop

@[fun_prop] theorem guardedRawDependence_primrec :
    Primrec (fun z : GuardedRows × List ℕ => guardedRawDependence z.1 z.2) := by
  unfold guardedRawDependence
  fun_prop

/-- A row reads the useful pair of the preceding specified column in the cycle. -/
def previousColumn (xs : GuardedAssignments) (j : ℕ) : ℕ :=
  (xs.getD ((j+xs.length-1)%xs.length) (0,0)).1

def guardedCycleRows (rs : GuardedRows) (xs : GuardedAssignments) : List (CycleConfiguration × ℕ) :=
  let keys := xs.map Prod.fst
  (List.range rs.length).map fun i =>
    let j := keys.idxOf i
    let p := previousColumn xs j
    let label := (xs.getD j (0,0)).2
    ((rowR rs i, [], rowA rs p, rowB rs p, decide (j < xs.length)), (rowDigits rs i).getD label 0)

def guardedCycle (rs : GuardedRows) (xs : GuardedAssignments) : List CyclicTile :=
  let rows := guardedCycleRows rs xs
  if xs.length = 0 then [] else fixedGadgets (guardedOrder rs) (rows.map Prod.fst) (rows.map Prod.snd)

@[fun_prop] theorem previousColumn_primrec :
    Primrec (fun z : GuardedAssignments × ℕ => previousColumn z.1 z.2) := by
  unfold previousColumn
  fun_prop

private theorem keyIndex_primrec :
    Primrec (fun z : GuardedAssignments × ℕ => (z.1.map Prod.fst).idxOf z.2) := by
  exact Primrec.list_idxOf.comp Primrec.snd
    (show Primrec (fun z : GuardedAssignments × ℕ => z.1.map Prod.fst) by fun_prop)

@[fun_prop] theorem guardedCycleRows_primrec :
    Primrec (fun z : GuardedRows × GuardedAssignments => guardedCycleRows z.1 z.2) := by
  unfold guardedCycleRows
  have h := keyIndex_primrec.comp
    (show Primrec (fun z : (GuardedRows × GuardedAssignments) × ℕ => (z.1.2,z.2)) by fun_prop)
  fun_prop

@[fun_prop] theorem guardedCycle_primrec :
    Primrec (fun z : GuardedRows × GuardedAssignments => guardedCycle z.1 z.2) := by
  unfold guardedCycle
  have hf := fixedGadgets_primrec.comp (show Primrec (fun z : GuardedRows × GuardedAssignments =>
      (guardedOrder z.1, (guardedCycleRows z.1 z.2).map Prod.fst, (guardedCycleRows z.1 z.2).map Prod.snd)) by
    fun_prop)
  fun_prop

def guardedRawDeck (rs : GuardedRows) (slopes : List ℕ) (tests : List GuardedAssignments) :
    List CyclicTile :=
  kernelCodes (guardedOrder rs) (guardedModuli rs) ::
    (guardedRawDependence rs slopes ++ guardedRawActivation rs slopes ++ tests.flatMap (guardedCycle rs))

@[fun_prop] theorem guardedRawDeck_primrec :
    Primrec (fun z : GuardedRows × List ℕ × List GuardedAssignments =>
      guardedRawDeck z.1 z.2.1 z.2.2) := by
  unfold guardedRawDeck
  have hk := kernelCodes_primrec.comp (show Primrec (fun z : GuardedRows × List ℕ × List GuardedAssignments =>
    (guardedOrder z.1,guardedModuli z.1)) by fun_prop)
  fun_prop

end
end TranslationTiling.FiniteCompiler.Effective
