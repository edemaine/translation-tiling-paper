import TranslationTiling.FiniteCompiler.Effective.NumericalParameters
import TranslationTiling.FiniteCompiler.Effective.GeometryPrimitives

namespace TranslationTiling.FiniteCompiler.Effective
open Compiler.Effective
open scoped Classical
noncomputable section

/-- The finite divisibility test is exactly membership in a single digit subgroup. -/
theorem rawOtherDigits_test (T : System) (i : Channel T) (j : Label T i) (n : ℕ) :
    KernelTest (rawOtherDigits (parameterData T) (channelKey i) (labelKey i j)) n ↔
      (n : K (parameters T) i) ∈ digitSubgroup (parameters T) i j := by
  have hcast (k : Label T i) :
      digitEquiv (parameters T) i (n : K (parameters T) i) k =
        (n : ZMod ((parameters T).digitPrime i k)) := by
    exact congrFun (map_natCast (digitEquivRing (parameters T) i) n) k
  rw [mem_digitSubgroup]
  simp only [hcast]
  unfold KernelTest rawOtherDigits
  constructor
  · intro h k hk
    have hne : labelKey i k ≠ labelKey i j := fun he => hk (labelKey_injective i he)
    have hm : labelKey i k ∈ (rawLabels (parameterData T) (channelKey i)).filter
        (fun l => decide (l ≠ labelKey i j)) :=
      List.mem_filter.mpr ⟨(mem_rawLabels T i _).mpr ⟨k,rfl⟩,decide_eq_true hne⟩
    have hv := h _ (List.mem_map.mpr ⟨labelKey i k,hm,rfl⟩)
    rw [rawDigit_eq] at hv
    apply ZMod.val_injective
    simpa only [ZMod.val_natCast,ZMod.val_zero] using hv
  · intro h r hr
    obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hr
    obtain ⟨hk,hne⟩ := List.mem_filter.mp hk
    obtain ⟨k,rfl⟩ := (mem_rawLabels T i k).mp hk
    have hkj : k ≠ j := fun he => (of_decide_eq_true hne) (congrArg (labelKey i) he)
    rw [rawDigit_eq]
    simpa only [ZMod.val_natCast,ZMod.val_zero] using congrArg ZMod.val (h k hkj)

end
end TranslationTiling.FiniteCompiler.Effective
