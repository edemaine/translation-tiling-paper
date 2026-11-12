import TranslationTiling.FiniteCompiler.Effective.Compiler
import TranslationTiling.FiniteCompiler.Effective.GeometryPrimitives

namespace TranslationTiling.FiniteCompiler.Effective
open Compiler.Effective
open scoped Classical
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem rawOther_test (T : System) (i : Channel T) (n : ℕ) :
    KernelTest (rawOtherModuli (parameterData T) (channelKey i)) n ↔
    KernelTest (((Finset.univ : Finset (Channel T)).filter (· ≠ i)).toList.map (parameters T).r) n := by
  rw [rawOtherKernelTest_iff]
  simp only [KernelTest,List.mem_map,Finset.mem_toList,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · rintro h r ⟨j,hj,rfl⟩; exact h j hj
  · intro h j hj; exact h _ ⟨j,hj,rfl⟩

theorem rawOrdinaryCodes_eq (T : System) (i : Channel T) (k : ℕ) :
    ordinaryCodes (rawEnvironment (parameterData T) (channelKey i)) k =
      ordinaryCodes (nativeActivationEnvironment (parameters T) i) k := by
  unfold ordinaryCodes ordinaryBatchCodes activationBatchCodes ActivationBatchTest
    rawEnvironment nativeActivationEnvironment
  simp only [rawOrder_eq,rawR_eq,rawA_eq,rawB_eq]
  simp_rw [rawOther_test]
  simp only [D,residueModulus_eq]

theorem rawSeedCodes_eq (T : System) (t : Fin 2) :
    seedCodes (rawEnvironment (parameterData T) (channelKey (T := T) (.inr t)))
      (rawA (parameterData T) (channelKey (T := T) (.inr (otherSeed t)))) Sudoku.Width =
    seedCodes (nativeActivationEnvironment (parameters T) (.inr t))
      ((parameters T).a (.inr (otherSeed t))) residueModulus := by
  unfold seedCodes seedBatchCodes activationBatchCodes ActivationBatchTest
    rawEnvironment nativeActivationEnvironment
  simp only [rawOrder_eq,rawR_eq,rawA_eq,rawB_eq]
  simp_rw [rawOther_test]
  simp only [D,residueModulus_eq]

theorem rawOrdinaryTile_correct (T : System) (n : Column T) (k : ℕ) (hk : T.slope n = (k : ℤ)) :
    (ordinaryCodes (rawEnvironment (parameterData T) (channelKey (.inl n))) k).toFinset.image
      (decodeNumericalPoint (parameters T)) = ordinaryActivationTile (parameters T) n := by
  rw [rawOrdinaryCodes_eq]
  exact ordinaryCodes_correct (parameters T) n k hk

theorem rawSeedTile_correct (T : System) (t : Fin 2) :
    (seedCodes (rawEnvironment (parameterData T) (Nat.pair 1 t.val))
      (rawA (parameterData T) (Nat.pair 1 (1-t.val))) Sudoku.Width).toFinset.image
      (decodeNumericalPoint (parameters T)) = seedActivationTile (parameters T) t := by
  have he : Nat.pair 1 (1-t.val) = channelKey (Sum.inr (otherSeed t) : Channel T) := by
    simp only [channelKey,otherSeed,Fin.val_mk]
  rw [he]
  change (seedCodes (rawEnvironment (parameterData T) (channelKey (T := T) (.inr t))) _ _).toFinset.image _ = _
  rw [rawSeedCodes_eq]
  exact seedCodes_correct (parameters T) t

end
end TranslationTiling.FiniteCompiler.Effective
