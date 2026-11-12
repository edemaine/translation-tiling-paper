import TranslationTiling.FiniteCompiler.Effective.Compiler
import TranslationTiling.FiniteCompiler.Effective.GeometryPrimitives

namespace TranslationTiling.FiniteCompiler.Effective
open Compiler.Effective
open scoped Classical
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def lowFromKeys {T : System} (E : EncodingParameters T) (gs : List ℕ) : Input E :=
  fun i => ((if channelKey i ∈ gs then 1 else 0 : ℕ) : K E i)

theorem rawCongruences_iff (T : System) (gs : List ℕ) (n : ℕ) :
    Congruences (rawCongruences (parameterData T) gs) n ↔
      ∀ i, (n : K (parameters T) i) = lowFromKeys (parameters T) gs i := by
  unfold Congruences rawCongruences
  constructor
  · intro h i
    have hi := h _ (List.mem_map.mpr ⟨channelKey i,(mem_channelKeys T _).mpr ⟨i,rfl⟩,rfl⟩)
    rw [rawR_eq] at hi
    apply ZMod.val_injective
    simpa only [lowFromKeys,ZMod.val_natCast] using hi
  · intro h r hr
    obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hr
    obtain ⟨i,rfl⟩ := (mem_channelKeys T k).mp hk
    rw [rawR_eq]
    simpa only [lowFromKeys,ZMod.val_natCast] using congrArg ZMod.val (h i)

theorem rawKernel_correct (T : System) :
    (kernelCodes (rawOrder (parameterData T)) (rawModuli (parameterData T))).toFinset.image
      (decodeNumericalPoint (parameters T)) = kernelTile (parameters T) := by
  have hk (n : ℕ) : KernelTest (rawModuli (parameterData T)) n ↔
      KernelTest ((Finset.univ : Finset (Channel T)).toList.map (parameters T).r) n := by
    rw [rawKernelTest_iff]
    simp only [KernelTest,List.mem_map,Finset.mem_toList,Finset.mem_univ,true_and]
    constructor
    · rintro h r ⟨i,rfl⟩; exact h i
    · intro h i; exact h _ ⟨i,rfl⟩
  rw [rawOrder_eq]
  have he : kernelCodes (parameters T).cyclicOrder (rawModuli (parameterData T)) =
      kernelCodes (parameters T).cyclicOrder
        ((Finset.univ : Finset (Channel T)).toList.map (parameters T).r) := by
    simp only [kernelCodes,hk]
  rw [he]
  exact kernelCodes_correct (parameters T)

theorem rawInvariance_correct (T : System) (i : Channel T) (h : ℤ × ℤ) (gs : List ℕ) :
    (rawInvariance (parameterData T) (channelKey i) h gs).toFinset.image
      (decodeNumericalPoint (parameters T)) =
      invarianceTile (parameters T) i (h,lowFromKeys (parameters T) gs) := by
  have hk (n : ℕ) : KernelTest (rawModuli (parameterData T)) n ↔
      KernelTest ((Finset.univ : Finset (Channel T)).toList.map (parameters T).r) n := by
    rw [rawKernelTest_iff]
    simp only [KernelTest,List.mem_map,Finset.mem_toList,Finset.mem_univ,true_and]
    constructor
    · rintro h r ⟨i,rfl⟩; exact h i
    · intro h i; exact h _ ⟨i,rfl⟩
  have hc (n : ℕ) : Congruences (rawCongruences (parameterData T) gs) n ↔
      Congruences ((Finset.univ : Finset (Channel T)).toList.map
        (fun j => ((parameters T).r j,(lowFromKeys (parameters T) gs j).val))) n := by
    rw [rawCongruences_iff,lowCongruences_iff]
  unfold rawInvariance
  rw [rawOrder_eq,rawA_eq,rawB_eq]
  have he : invarianceCodes (parameters T).cyclicOrder (rawModuli (parameterData T))
      ((parameters T).a i) ((parameters T).b i) h (rawCongruences (parameterData T) gs) =
      invarianceCodes (parameters T).cyclicOrder
        ((Finset.univ : Finset (Channel T)).toList.map (parameters T).r)
        ((parameters T).a i) ((parameters T).b i) h
        ((Finset.univ : Finset (Channel T)).toList.map
          (fun j => ((parameters T).r j,(lowFromKeys (parameters T) gs j).val))) := by
    simp only [invarianceCodes,hk,hc]
  rw [he]
  exact invarianceCodes_correct (parameters T) i (h,lowFromKeys (parameters T) gs)

end
end TranslationTiling.FiniteCompiler.Effective
