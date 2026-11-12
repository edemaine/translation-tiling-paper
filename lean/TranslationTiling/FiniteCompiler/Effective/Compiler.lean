import TranslationTiling.FiniteCompiler.Effective.WordLists
import TranslationTiling.FiniteCompiler.Effective.NumericalParameters
import TranslationTiling.FiniteCompiler.Effective.SparsePrimitives
import TranslationTiling.FiniteCompiler.Effective.Canonical
import TranslationTiling.FiniteCompiler.Effective.BoundedStack
import TranslationTiling.Compiler.Main
import TranslationTiling.FiniteCompiler.StackBound

/-! # A total numerical optimized compiler

The input contains finite arithmetic parameter certificates, slopes, line words,
and seed alphabets. All varying domains are represented by natural-indexed
lists. In particular, no arbitrary enumeration of an input-dependent finite
type is treated as a computable constant.
-/

namespace TranslationTiling.FiniteCompiler.Effective

open Compiler Compiler.Effective
set_option maxRecDepth 10000
set_option maxHeartbeats 300000
noncomputable section

abbrev InputData := ParameterData × Payload
abbrev NumericalSpec := Bool × ℕ × ℕ

attribute [local fun_prop] kernelCodes_primrec invarianceCodes_primrec ordinaryCodes_primrec
attribute [local fun_prop] seedCodes_primrec sparseGadgets_primrec numericalBadWords_primrec
attribute [local fun_prop] product_primrec

def rawCongruences (d : ParameterData) (generators : List ℕ) : CongruenceList :=
  (channelKeys d.1).map fun i => (rawR d i, if i ∈ generators then 1 else 0)

@[fun_prop] theorem rawCongruences_primrec : Primrec (fun d : ParameterData × List ℕ =>
    rawCongruences d.1 d.2) := by
  unfold rawCongruences
  fun_prop

def rawInvariance (d : ParameterData) (i : ℕ) (h : ℤ × ℤ) (generators : List ℕ) : CyclicTile :=
  invarianceCodes (rawOrder d) (rawModuli d) (rawA d i) (rawB d i) h (rawCongruences d generators)

@[fun_prop] theorem rawInvariance_primrec : Primrec (fun z :
    ParameterData × ℕ × (ℤ × ℤ) × List ℕ => rawInvariance z.1 z.2.1 z.2.2.1 z.2.2.2) := by
  have hp : Primrec (fun z : ParameterData × ℕ × (ℤ × ℤ) × List ℕ =>
      ((rawOrder z.1,rawModuli z.1),(rawA z.1 z.2.1,rawB z.1 z.2.1),z.2.2.1,rawCongruences z.1 z.2.2.2)) := by
    fun_prop
  exact invarianceCodes_primrec.comp hp

def lowDependenceFamily (d : ParameterData) : List CyclicTile :=
  (channelKeys d.1).flatMap fun i =>
    ((channelKeys d.1).filter fun j => decide (j ≠ i)).map fun j => rawInvariance d i (0,0) [j]

@[fun_prop] theorem lowDependenceFamily_primrec : Primrec lowDependenceFamily := by
  unfold lowDependenceFamily
  fun_prop

def lineDependenceFamily (d : InputData) : List CyclicTile :=
  (List.range d.1.1).map fun n => rawInvariance d.1 (denseChannelKey d.1.1 n)
    (1,-(d.2.1.getD n 0)) []

@[fun_prop] theorem lineDependenceFamily_primrec : Primrec lineDependenceFamily := by
  unfold lineDependenceFamily
  fun_prop

def seedDependenceFamily (d : ParameterData) : List CyclicTile :=
  (List.range 2).flatMap fun t =>
    [rawInvariance d (Nat.pair 1 t) ((Sudoku.Width : ℤ),0) [],
     rawInvariance d (Nat.pair 1 t) (0,(Sudoku.Width : ℤ)) []]

@[fun_prop] theorem seedDependenceFamily_primrec : Primrec seedDependenceFamily := by
  unfold seedDependenceFamily
  fun_prop

def rawDependenceFamily (d : InputData) : List CyclicTile :=
  lowDependenceFamily d.1 ++ lineDependenceFamily d ++ seedDependenceFamily d.1

@[fun_prop] theorem rawDependenceFamily_primrec : Primrec rawDependenceFamily := by
  unfold rawDependenceFamily
  fun_prop

def rawWordSpec (d : ParameterData) (w : List ℕ) : List NumericalSpec :=
  (List.range (d.1 + 2)).map fun k =>
    if k < d.1 then
      (true,denseChannelKey d.1 (differenceResidue d.1 k 1),w.getD k 0)
    else (false,denseChannelKey d.1 k,0)

@[fun_prop] theorem rawWordSpec_primrec : Primrec (fun d : ParameterData × List ℕ =>
    rawWordSpec d.1 d.2) := by
  unfold rawWordSpec
  fun_prop

def rawSeedSpec (d : ParameterData) (t n j : ℕ) : List NumericalSpec :=
  (List.range (d.1 + 2)).map fun k =>
    if k = d.1 + t then (true,denseChannelKey d.1 n,0)
    else if k = n then (true,Nat.pair 1 t,j)
    else (false,denseChannelKey d.1 k,0)

@[fun_prop] theorem rawSeedSpec_primrec : Primrec (fun z : ParameterData × ℕ × ℕ × ℕ =>
    rawSeedSpec z.1 z.2.1 z.2.2.1 z.2.2.2) := by
  unfold rawSeedSpec
  fun_prop

def rawConfigurations (d : ParameterData) (spec : List NumericalSpec) : List CycleConfiguration :=
  (List.range (d.1 + 2)).map fun k =>
    let i := denseChannelKey d.1 k
    let entry := spec.getD k (false,0,0)
    (rawR d i,rawOtherDigits d i entry.2.2,rawA d entry.2.1,rawB d entry.2.1,entry.1)

@[fun_prop] theorem rawConfigurations_primrec : Primrec (fun z : ParameterData × List NumericalSpec =>
    rawConfigurations z.1 z.2) := by
  unfold rawConfigurations
  fun_prop

def rawWordFamily (d : InputData) : List CyclicTile :=
  (numericalBadWords d.1 d.2).flatMap fun w =>
    sparseGadgets (rawOrder d.1) (rawConfigurations d.1 (rawWordSpec d.1 w))

@[fun_prop] theorem rawWordFamily_primrec : Primrec rawWordFamily := by
  unfold rawWordFamily
  fun_prop

def rawSeedAlphabet (p : Payload) (t : ℕ) : List ℕ :=
  if t = 0 then p.2.2.1 else p.2.2.2

def badSeedArguments (d : InputData) : List (ℕ × ℕ × ℕ) :=
  ((List.range 2).flatMap fun t => (List.range d.1.1).flatMap fun n =>
    (List.range d.1.2.1).map fun j => (t,n,j)).filter fun z => decide (z.2.2 ∉ rawSeedAlphabet d.2 z.1)

@[fun_prop] theorem badSeedArguments_primrec : Primrec badSeedArguments := by
  unfold badSeedArguments rawSeedAlphabet
  fun_prop

def rawSeedConstraintFamily (d : InputData) : List CyclicTile :=
  (badSeedArguments d).flatMap fun z =>
    sparseGadgets (rawOrder d.1) (rawConfigurations d.1 (rawSeedSpec d.1 z.1 z.2.1 z.2.2))

@[fun_prop] theorem rawSeedConstraintFamily_primrec : Primrec rawSeedConstraintFamily := by
  unfold rawSeedConstraintFamily
  fun_prop

def rawEnvironment (d : ParameterData) (i : ℕ) : ActivationEnvironment :=
  ((rawOrder d,rawOtherModuli d i),(rawR d i,rawA d i,rawB d i,Sudoku.Width ^ 2))

@[fun_prop] theorem rawEnvironment_primrec : Primrec (fun z : ParameterData × ℕ =>
    rawEnvironment z.1 z.2) := by
  unfold rawEnvironment
  fun_prop

def rawOrdinaryFamily (d : InputData) : List CyclicTile :=
  (List.range d.1.1).map fun n =>
    ordinaryCodes (rawEnvironment d.1 (denseChannelKey d.1.1 n)) (d.2.1.getD n 0).toNat

@[fun_prop] theorem rawOrdinaryFamily_primrec : Primrec rawOrdinaryFamily := by
  unfold rawOrdinaryFamily
  fun_prop

def rawSeedFamily (d : ParameterData) : List CyclicTile :=
  (List.range 2).map fun t =>
    seedCodes (rawEnvironment d (Nat.pair 1 t)) (rawA d (Nat.pair 1 (1 - t))) Sudoku.Width

@[fun_prop] theorem rawSeedFamily_primrec : Primrec rawSeedFamily := by
  unfold rawSeedFamily
  fun_prop

def rawFamily (d : InputData) : List CyclicTile :=
  kernelCodes (rawOrder d.1) (rawModuli d.1) ::
    (rawDependenceFamily d ++ rawWordFamily d ++ rawSeedConstraintFamily d ++
      rawOrdinaryFamily d ++ rawSeedFamily d.1)

@[fun_prop] theorem rawFamily_primrec : Primrec rawFamily := by
  unfold rawFamily
  fun_prop

def rawBudget (d : ParameterData) : ℕ := Size.parameterBase d.2.1 Sudoku.Width (d.1 + 2)
def rawHorizontal (d : ParameterData) : ℕ := Size.horizontalCap (rawBudget d)
def rawCountCap (d : ParameterData) : ℕ := Size.commonCap (rawBudget d) (d.1 + 2)

@[fun_prop] theorem rawBudget_primrec : Primrec rawBudget := by
  unfold rawBudget Size.parameterBase digitPrimeCap usefulPrimeCap primeThreshold
  fun_prop
@[fun_prop] theorem rawHorizontal_primrec : Primrec rawHorizontal := by
  unfold rawHorizontal Size.horizontalCap Size.indexCap Size.pairCap
  fun_prop
@[fun_prop] theorem rawCountCap_primrec : Primrec rawCountCap := by
  change Primrec (fun d : ParameterData => rawBudget d ^ (12 * (d.1 + 2)))
  exact natPower rawBudget_primrec (by fun_prop)

def canonicalInputFamily (d : InputData) : List CyclicTile :=
  canonicalFamily (rawHorizontal d.1) (rawOrder d.1) (rawFamily d)

theorem canonicalInputFamily_computable : Computable canonicalInputFamily := by
  have hp : Primrec (fun d : InputData => ((rawHorizontal d.1,rawOrder d.1),rawFamily d)) := by
    fun_prop
  have hc := canonicalFamily_primrec.to_comp.comp hp.to_comp
  exact hc.of_eq (fun d => rfl)

def optimizedCyclic (d : InputData) : CyclicTileData :=
  boundedStack (rawCountCap d.1,rawOrder d.1,canonicalInputFamily d)

theorem optimizedCyclic_computable : Computable optimizedCyclic := by
  have h1 : Computable (fun d : InputData => rawCountCap d.1) :=
    rawCountCap_primrec.to_comp.comp Computable.fst
  have h2 : Computable (fun d : InputData => rawOrder d.1) :=
    rawOrder_primrec.to_comp.comp Computable.fst
  exact boundedStack_computable.comp (h1.pair (h2.pair canonicalInputFamily_computable))

def optimizedTile (d : InputData) : Tile 3 :=
  (Compiler.connectedTile (Compiler.integerTile (optimizedCyclic d))).dedup

theorem optimizedTile_computable : Computable optimizedTile :=
  dedup_primrec.to_comp.comp (Compiler.connectedTile_computable.comp
    (Compiler.integerTile_computable.comp optimizedCyclic_computable))

/-- The algorithmic input for the optimized Wang compiler. -/
def wangInput (T : LeanWang.TileSet) : InputData :=
  (parameterData (bitSystem T),bitPayload T)

theorem wangInput_computable : Computable wangInput := by
  have hw : Primrec (fun T : LeanWang.TileSet => Sudoku.Width * bitWidth T) :=
    natMul (Primrec.const _) bitWidth_primrec
  have hshape := hw.to_comp.pair (Computable.const BitSystem.alphabet)
  have hc := parameterCertificate_computable.comp hshape
  exact (hw.to_comp.pair ((Computable.const _).pair hc)).pair bitPayload_primrec.to_comp

def optimizedCompile (T : LeanWang.TileSet) : Tile 3 := optimizedTile (wangInput T)

theorem optimizedCompile_computable : Computable optimizedCompile :=
  optimizedTile_computable.comp wangInput_computable

end
end TranslationTiling.FiniteCompiler.Effective
