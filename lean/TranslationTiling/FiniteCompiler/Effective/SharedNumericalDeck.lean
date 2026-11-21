import TranslationTiling.FiniteCompiler.Effective.GuardedNumericalDeck

namespace TranslationTiling.FiniteCompiler.Effective

open Compiler Compiler.Effective

noncomputable section

/-- A Wang row observes only its private useful prime in dependence and cycle
tests. In its activation test it also observes the useful prime for its slope. -/
def sharedObservedA (rs : GuardedRows) (i : ℕ) : ℕ :=
  if 18 ≤ i ∧ i < rs.length - 2 then 1 else rowA rs i

def sharedOrder (rs : GuardedRows) : ℕ :=
  1225 * 199 * 163 * ((List.range rs.length).map
    fun i => (rowR rs i)^2 * sharedObservedA rs i * rowB rs i).prod

/-- Cardinality of a fibre of the low projection. -/
def sharedMass (rs : GuardedRows) : ℕ :=
  1225 * 199 * 163 * ((List.range rs.length).map
    fun i => rowR rs i * sharedObservedA rs i * rowB rs i).prod

theorem shared_input_mul_mass (rs : GuardedRows) :
    (guardedModuli rs).prod * sharedMass rs = sharedOrder rs := by
  unfold guardedModuli sharedMass sharedOrder
  rw [mul_left_comm, ← List.prod_map_mul]
  congr 1
  congr 1
  apply List.map_congr_left
  intro i _
  ring

def sharedEnvironment (rs : GuardedRows) (i : ℕ) : ActivationEnvironment :=
  ((sharedOrder rs, guardedOther rs i), (rowR rs i, rowA rs i, rowB rs i, 1225))

def sharedInvariance (rs : GuardedRows) (a b : ℕ) (h : Plane) (g : Option ℕ) : CyclicTile :=
  invarianceCodes (sharedOrder rs) (guardedModuli rs) a b h
    ((List.range rs.length).map fun j => (rowR rs j, if g = some j then 1 % rowR rs j else 0))

def sharedDependence (rs : GuardedRows) (slopes : List ℕ) : List CyclicTile :=
  let own := fun i => sharedInvariance rs (sharedObservedA rs i) (rowB rs i)
  (List.range rs.length).flatMap (fun i =>
    ((List.range rs.length).filter (fun j => decide (j ≠ i))).map
      (fun j => own i 0 (some j))) ++
  ((List.range (rs.length - 2)).map fun i => own i (1,-(slopes.getD i 0 : ℤ)) none) ++
  (List.range 2).flatMap (fun t =>
    [own (rs.length-2+t) (35,0) none, own (rs.length-2+t) (0,35) none]) ++
  [sharedInvariance rs 199 1 (1,0) none, sharedInvariance rs 163 1 (1,-2) none]

def sharedActivationCodes (rs : GuardedRows) (slopes : List ℕ) : List CyclicTile :=
  ((List.range (rs.length-2)).map fun i => compactCodes (sharedEnvironment rs i) (slopes.getD i 0)) ++
    (List.range 2).map fun t =>
      seedCodes (sharedEnvironment rs (rs.length-2+t)) (rowA rs (rs.length-2+(1-t))) 35

def sharedCycleRows (rs : GuardedRows) (xs : GuardedAssignments) : List (CycleConfiguration × ℕ) :=
  let keys := xs.map Prod.fst
  (List.range rs.length).map fun i =>
    let j := keys.idxOf i
    let p := previousColumn xs j
    let label := (xs.getD j (0,0)).2
    ((rowR rs i, [], sharedObservedA rs p, rowB rs p, decide (j < xs.length)),
      (rowDigits rs i).getD label 0)

def sharedCycle (rs : GuardedRows) (xs : GuardedAssignments) : List CyclicTile :=
  let rows := sharedCycleRows rs xs
  if xs.length = 0 then [] else fixedGadgets (sharedOrder rs) (rows.map Prod.fst) (rows.map Prod.snd)

def sharedRawDeck (rs : GuardedRows) (slopes : List ℕ) (tests : List GuardedAssignments) :
    List CyclicTile :=
  kernelCodes (sharedOrder rs) (guardedModuli rs) ::
    (sharedDependence rs slopes ++ sharedActivationCodes rs slopes ++ tests.flatMap (sharedCycle rs))

@[fun_prop] theorem sharedObservedA_primrec :
    Primrec (fun z : GuardedRows × ℕ => sharedObservedA z.1 z.2) := by
  unfold sharedObservedA
  fun_prop

@[fun_prop] theorem sharedOrder_primrec : Primrec sharedOrder := by
  have hp : Primrec (fun rs : GuardedRows =>
      (List.range rs.length).map (fun i => (rowR rs i)^2 * sharedObservedA rs i * rowB rs i)) := by
    simp only [pow_two]
    fun_prop
  exact natMul (Primrec.const (1225*199*163)) (product_primrec.comp hp)

@[fun_prop] theorem sharedEnvironment_primrec :
    Primrec (fun z : GuardedRows × ℕ => sharedEnvironment z.1 z.2) := by
  unfold sharedEnvironment guardedOther
  fun_prop

@[fun_prop] theorem sharedInvariance_primrec :
    Primrec (fun z : GuardedRows × ℕ × ℕ × Plane × Option ℕ =>
      sharedInvariance z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2) := by
  unfold sharedInvariance
  apply invarianceCodes_primrec.comp (g := fun z : GuardedRows × ℕ × ℕ × Plane × Option ℕ =>
    ((sharedOrder z.1,guardedModuli z.1),(z.2.1,z.2.2.1),z.2.2.2.1,
      (List.range z.1.length).map fun j =>
        (rowR z.1 j,if z.2.2.2.2 = some j then 1 % rowR z.1 j else 0)))
  fun_prop

@[fun_prop] theorem sharedDependence_primrec :
    Primrec (fun z : GuardedRows × List ℕ => sharedDependence z.1 z.2) := by
  unfold sharedDependence
  dsimp only
  fun_prop

@[fun_prop] theorem sharedActivationCodes_primrec :
    Primrec (fun z : GuardedRows × List ℕ => sharedActivationCodes z.1 z.2) := by
  unfold sharedActivationCodes
  have hs : Primrec (fun z : (GuardedRows × List ℕ) × ℕ =>
      (sharedEnvironment z.1.1 (z.1.1.length-2+z.2),rowA z.1.1 (z.1.1.length-2+(1-z.2)),35)) := by
    fun_prop
  have h := seedCodes_primrec.comp hs
  fun_prop

@[fun_prop] theorem sharedCycleRows_primrec :
    Primrec (fun z : GuardedRows × GuardedAssignments => sharedCycleRows z.1 z.2) := by
  unfold sharedCycleRows
  have h : Primrec (fun z : (GuardedRows × GuardedAssignments) × ℕ =>
      (z.1.2.map Prod.fst).idxOf z.2) :=
    Primrec.list_idxOf.comp Primrec.snd (by fun_prop)
  fun_prop

@[fun_prop] theorem sharedCycle_primrec :
    Primrec (fun z : GuardedRows × GuardedAssignments => sharedCycle z.1 z.2) := by
  unfold sharedCycle
  have hf := fixedGadgets_primrec.comp (show Primrec (fun z : GuardedRows × GuardedAssignments =>
      (sharedOrder z.1, (sharedCycleRows z.1 z.2).map Prod.fst,
        (sharedCycleRows z.1 z.2).map Prod.snd)) by fun_prop)
  fun_prop

@[fun_prop] theorem sharedRawDeck_primrec :
    Primrec (fun z : GuardedRows × List ℕ × List GuardedAssignments => sharedRawDeck z.1 z.2.1 z.2.2) := by
  unfold sharedRawDeck
  have hk := kernelCodes_primrec.comp (show Primrec (fun z : GuardedRows × List ℕ × List GuardedAssignments =>
    (sharedOrder z.1,guardedModuli z.1)) by fun_prop)
  fun_prop

theorem sharedCycle_length (rs : GuardedRows) (xs : GuardedAssignments) :
    (sharedCycle rs xs).length ≤ 1 := by
  unfold sharedCycle fixedGadgets
  split <;> simp

theorem sharedRawDeck_length (rs : GuardedRows) (slopes : List ℕ)
    (tests : List GuardedAssignments) :
    (sharedRawDeck rs slopes tests).length ≤ rs.length^2 + 2*(rs.length-2)+tests.length+9 := by
  have hi : ((List.range rs.length).flatMap fun i =>
      ((List.range rs.length).filter (fun j => decide (j ≠ i))).map
        (fun j => sharedInvariance rs (sharedObservedA rs i) (rowB rs i) 0 (some j))).length ≤
      rs.length^2 := by
    rw [List.length_flatMap]
    have hl (i : ℕ) :
        ((List.range rs.length).filter (fun j => decide (j ≠ i))).length ≤ rs.length :=
      by simpa only [List.length_range] using
        (List.length_filter_le (l := List.range rs.length) (p := fun j => decide (j ≠ i)))
    calc
      _ ≤ ((List.range rs.length).map fun _ => rs.length).sum := by
        have hsum {ls : List ℕ} :
            (ls.map (fun i => ((List.range rs.length).filter (fun j => decide (j ≠ i))).length)).sum ≤
              (ls.map fun _ => rs.length).sum := by
          induction ls with
          | nil => simp
          | cons i ls ih =>
            simp only [List.map_cons,List.sum_cons]
            exact Nat.add_le_add (hl i) ih
        simpa only [Function.comp_apply,List.length_map] using hsum (ls := List.range rs.length)
      _ = _ := by simp [pow_two]
  have ht : (tests.flatMap (sharedCycle rs)).length ≤ tests.length := by
    induction tests with
    | nil => simp
    | cons test tests ih =>
      have h := sharedCycle_length rs test
      simp only [List.flatMap_cons,List.length_append,List.length_cons]
      omega
  unfold sharedRawDeck sharedDependence sharedActivationCodes
  dsimp only
  simp only [List.length_cons,List.length_append,List.length_map,List.length_range,List.length_nil]
  have hseed : ((List.range 2).flatMap fun t =>
      [sharedInvariance rs (sharedObservedA rs (rs.length-2+t)) (rowB rs (rs.length-2+t)) (35,0) none,
       sharedInvariance rs (sharedObservedA rs (rs.length-2+t)) (rowB rs (rs.length-2+t)) (0,35) none]).length = 4 := rfl
  omega

end
end TranslationTiling.FiniteCompiler.Effective
