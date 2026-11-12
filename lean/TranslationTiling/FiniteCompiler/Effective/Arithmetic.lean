import TranslationTiling.FiniteCompiler.Effective.ParameterSelection
import TranslationTiling.Compiler.EffectiveNumericParameters
import Mathlib.Algebra.BigOperators.Fin

namespace TranslationTiling.FiniteCompiler.Effective

open Compiler.Effective
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
noncomputable section

abbrev ParameterData := ℕ × ℕ × ParameterCertificate

def rawPrime (d : ParameterData) (k : ℕ) : ℕ := d.2.2.1.getD k 0
def rawA (d : ParameterData) (i : ℕ) : ℕ := rawPrime d (Nat.pair 0 i)
def rawB (d : ParameterData) (i : ℕ) : ℕ := rawPrime d (Nat.pair 1 i)
def rawDigit (d : ParameterData) (i j : ℕ) : ℕ := rawPrime d (Nat.pair 2 (Nat.pair i j))
def rawLabels (d : ParameterData) (i : ℕ) : List ℕ :=
  if i.unpair.1 = 0 then List.range d.2.1 else [0]
def rawR (d : ParameterData) (i : ℕ) : ℕ :=
  ((rawLabels d i).map (rawDigit d i)).prod

def rawModuli (d : ParameterData) : List ℕ := (channelKeys d.1).map (rawR d)
def rawOrder (d : ParameterData) : ℕ :=
  Sudoku.Width ^ 2 * ((channelKeys d.1).map fun i => rawR d i ^ 2 * rawA d i * rawB d i).prod

@[fun_prop] theorem rawPrime_primrec : Primrec (fun z : ParameterData × ℕ => rawPrime z.1 z.2) := by
  unfold rawPrime
  fun_prop
@[fun_prop] theorem rawA_primrec : Primrec (fun z : ParameterData × ℕ => rawA z.1 z.2) := by
  unfold rawA
  fun_prop
@[fun_prop] theorem rawB_primrec : Primrec (fun z : ParameterData × ℕ => rawB z.1 z.2) := by
  unfold rawB
  fun_prop
@[fun_prop] theorem rawDigit_primrec : Primrec (fun z : ParameterData × ℕ × ℕ =>
    rawDigit z.1 z.2.1 z.2.2) := by
  unfold rawDigit
  fun_prop
@[fun_prop] theorem rawLabels_primrec : Primrec (fun z : ParameterData × ℕ => rawLabels z.1 z.2) := by
  unfold rawLabels
  fun_prop
@[fun_prop] theorem rawR_primrec : Primrec (fun z : ParameterData × ℕ => rawR z.1 z.2) := by
  unfold rawR
  apply product_primrec.comp
  fun_prop
@[fun_prop] theorem rawModuli_primrec : Primrec rawModuli := by
  unfold rawModuli
  fun_prop
@[fun_prop] theorem rawOrder_primrec : Primrec rawOrder := by
  unfold rawOrder
  have hprod : Primrec (fun d : ParameterData =>
      ((channelKeys d.1).map fun i => rawR d i ^ 2 * rawA d i * rawB d i).prod) := by
    apply product_primrec.comp
    simp only [pow_two]
    fun_prop
  exact natMul (Primrec.const _) hprod

def parameterData (T : System) : ParameterData :=
  (T.width,T.alphabet,parameterCertificate (T.width,T.alphabet))

theorem rawA_eq (T : System) (i : Channel T) :
    rawA (parameterData T) (channelKey i) = (parameters T).a i := rfl

theorem rawB_eq (T : System) (i : Channel T) :
    rawB (parameterData T) (channelKey i) = (parameters T).b i := rfl

theorem rawDigit_eq (T : System) (i : Channel T) (j : Label T i) :
    rawDigit (parameterData T) (channelKey i) (labelKey i j) = (parameters T).digitPrime i j := rfl

theorem rawR_eq (T : System) (i : Channel T) :
    rawR (parameterData T) (channelKey i) = (parameters T).r i := by
  rw [(parameters T).r_eq_prod]
  cases i with
  | inl n =>
    simp only [rawR, rawLabels, channelKey, Nat.unpair_pair, ite_true]
    change ((List.range T.alphabet).map fun j =>
      rawDigit (parameterData T) (Nat.pair 0 n.val) j).prod = _
    have he : (List.range T.alphabet).map (rawDigit (parameterData T) (Nat.pair 0 n.val)) =
        List.ofFn (fun j : Fin T.alphabet => rawDigit (parameterData T) (Nat.pair 0 n.val) j.val) := by
      apply List.ext_getElem
      · simp
      · intro k hk hk'; simp
    rw [he, Fin.prod_ofFn]
    rfl
  | inr t =>
    simp only [rawR, rawLabels, channelKey, Nat.unpair_pair, reduceCtorEq, ite_false,
      List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    haveI : Unique (Label T (.inr t)) := by change Unique Unit; infer_instance
    rw [Fintype.prod_unique]
    rfl

theorem rawKernelTest_iff (T : System) (n : ℕ) :
    KernelTest (rawModuli (parameterData T)) n ↔ ∀ i : Channel T, n % (parameters T).r i = 0 := by
  unfold KernelTest rawModuli
  constructor
  · intro h i
    have hi := h _ (List.mem_map.mpr ⟨channelKey i,(mem_channelKeys T _).mpr ⟨i,rfl⟩,rfl⟩)
    simpa only [rawR_eq] using hi
  · intro h r hr
    obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hr
    obtain ⟨i,rfl⟩ := (mem_channelKeys T k).mp hk
    simpa only [rawR_eq] using h i

end
end TranslationTiling.FiniteCompiler.Effective
