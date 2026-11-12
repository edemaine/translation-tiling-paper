import TranslationTiling.FiniteCompiler.Effective.Arithmetic
import TranslationTiling.FiniteCompiler.SupportBounds
import TranslationTiling.FiniteCompiler.Effective.BitCode
import Mathlib.Logic.Equiv.Fin.Basic

namespace TranslationTiling.FiniteCompiler.Effective

open Compiler.Effective
open scoped BigOperators
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
noncomputable section

def channelEquiv (T : System) : Channel T ≃ Fin (T.width + 2) := finSumFinEquiv

def denseChannelKey (w i : ℕ) : ℕ :=
  if i < w then Nat.pair 0 i else Nat.pair 1 (i - w)

@[fun_prop] theorem denseChannelKey_primrec : Primrec (fun d : ℕ × ℕ =>
    denseChannelKey d.1 d.2) := by
  unfold denseChannelKey
  fun_prop

theorem denseChannelKey_eq (T : System) (i : Channel T) :
    denseChannelKey T.width ((channelEquiv T) i).val = channelKey i := by
  cases i with
  | inl n => simp [channelEquiv,denseChannelKey,channelKey,n.isLt]
  | inr t => simp [channelEquiv,denseChannelKey,channelKey]

theorem channelKeys_nodup (w : ℕ) : (channelKeys w).Nodup := by
  have hi : Function.Injective (Nat.pair 0) := fun _ _ h => (Nat.pair_eq_pair.mp h).2
  unfold channelKeys
  apply List.nodup_append.mpr
  refine ⟨(List.nodup_range (n := w)).map hi,by simp [Nat.pair_eq_pair],?_⟩
  intro a ha b hb he
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ha
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl | rfl <;> simp [Nat.pair_eq_pair] at he

theorem rawOrder_eq (T : System) : rawOrder (parameterData T) = (parameters T).cyclicOrder := by
  have he : (channelKeys T.width).toFinset = Finset.univ.image (channelKey (T := T)) := by
    ext k
    simp only [List.mem_toFinset,mem_channelKeys,Finset.mem_image,Finset.mem_univ,true_and]
  unfold rawOrder
  change Sudoku.Width ^ 2 * ((channelKeys T.width).map
    (fun i => rawR (parameterData T) i ^ 2 * rawA (parameterData T) i * rawB (parameterData T) i)).prod = _
  rw [← List.prod_toFinset _ (channelKeys_nodup T.width),he,
    Finset.prod_image (channelKey_injective T).injOn]
  simp only [rawR_eq,rawA_eq,rawB_eq]
  rw [EncodingParameters.cyclicOrder,residueModulus_eq]
  rfl

def rawOtherModuli (d : ParameterData) (i : ℕ) : List ℕ :=
  ((channelKeys d.1).filter (fun j => decide (j ≠ i))).map (rawR d)

def rawOtherDigits (d : ParameterData) (i j : ℕ) : List ℕ :=
  ((rawLabels d i).filter (fun k => decide (k ≠ j))).map (rawDigit d i)

@[fun_prop] theorem rawOtherModuli_primrec : Primrec (fun z : ParameterData × ℕ =>
    rawOtherModuli z.1 z.2) := by
  unfold rawOtherModuli
  fun_prop

@[fun_prop] theorem rawOtherDigits_primrec : Primrec (fun z : ParameterData × ℕ × ℕ =>
    rawOtherDigits z.1 z.2.1 z.2.2) := by
  unfold rawOtherDigits
  fun_prop

theorem mem_rawLabels (T : System) (i : Channel T) (k : ℕ) :
    k ∈ rawLabels (parameterData T) (channelKey i) ↔ ∃ j : Label T i, labelKey i j = k := by
  cases i with
  | inl n =>
    simp only [rawLabels,channelKey,Nat.unpair_pair,ite_true,List.mem_range]
    constructor
    · intro hk; exact ⟨⟨k,hk⟩,rfl⟩
    · rintro ⟨j,rfl⟩; exact j.isLt
  | inr t =>
    simp only [rawLabels,channelKey,Nat.unpair_pair,reduceCtorEq,ite_false,List.mem_singleton]
    constructor
    · intro hk; exact ⟨(),hk.symm⟩
    · rintro ⟨j,hj⟩; exact hj.symm

theorem rawOtherKernelTest_iff (T : System) (i : Channel T) (n : ℕ) :
    KernelTest (rawOtherModuli (parameterData T) (channelKey i)) n ↔
      ∀ j : Channel T, j ≠ i → n % (parameters T).r j = 0 := by
  unfold KernelTest rawOtherModuli
  constructor
  · intro h j hji
    have hne : channelKey j ≠ channelKey i := fun he => hji (channelKey_injective T he)
    have hm : channelKey j ∈ (channelKeys T.width).filter (fun k => decide (k ≠ channelKey i)) :=
      List.mem_filter.mpr ⟨(mem_channelKeys T _).mpr ⟨j,rfl⟩,decide_eq_true hne⟩
    simpa only [rawR_eq] using h _ (List.mem_map.mpr ⟨channelKey j,hm,rfl⟩)
  · intro h r hr
    obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hr
    obtain ⟨hm,hne⟩ := List.mem_filter.mp hk
    obtain ⟨j,rfl⟩ := (mem_channelKeys T k).mp hm
    have hj : j ≠ i := fun he => (of_decide_eq_true hne) (congrArg channelKey he)
    simpa only [rawR_eq] using h j hj

/-- The searched parameters satisfy exactly the budget of the size proof. -/
theorem parameters_budget (T : System) (S : ℕ) (hS : ∀ n, (T.slope n).natAbs ≤ S) :
    Size.ParameterBudget (parameters T) (Size.parameterBase T.alphabet S (channelCount T)) ∧
      channelCount T ≤ Size.parameterBase T.alphabet S (channelCount T) ∧
      T.alphabet + 1 ≤ Size.parameterBase T.alphabet S (channelCount T) := by
  obtain ⟨hu,hp⟩ := parameters_bounded T
  have hQ : 1 ≤ digitPrimeCap T.alphabet (channelCount T) := by
    unfold digitPrimeCap
    have : 1 ≤ primeThreshold (usefulPrimeCap (channelCount T)) +
        channelCount T * (T.alphabet + 1) + 1 := by omega
    nlinarith [Nat.mul_le_mul_left 8 this]
  have hr (i : Channel T) :
      (parameters T).r i ≤ digitPrimeCap T.alphabet (channelCount T) ^ (T.alphabet + 1) := by
    rw [(parameters T).r_eq_prod]
    calc
      _ ≤ ∏ _j : Label T i, digitPrimeCap T.alphabet (channelCount T) :=
        Finset.prod_le_prod (fun j _ => hp i j)
      _ = digitPrimeCap T.alphabet (channelCount T) ^ Fintype.card (Label T i) := by simp
      _ ≤ _ := Nat.pow_le_pow_right hQ (label_card_le T i)
  refine ⟨⟨?_,?_,?_,?_,?_,?_⟩,?_,?_⟩
  · unfold Size.parameterBase; omega
  · unfold Size.parameterBase; omega
  · intro i; have := hr i; unfold Size.parameterBase; omega
  · intro i; have := (hu i).1; unfold Size.parameterBase; omega
  · intro i; have := (hu i).2; unfold Size.parameterBase; omega
  · intro n; have := hS n; unfold Size.parameterBase; omega
  · unfold Size.parameterBase; omega
  · unfold Size.parameterBase; omega

end
end TranslationTiling.FiniteCompiler.Effective
