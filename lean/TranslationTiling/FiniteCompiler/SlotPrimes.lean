import TranslationTiling.Compiler.GuardedPrimeCounting

namespace TranslationTiling.FiniteCompiler

open Compiler.Size
open scoped Classical

/-- Pick distinct primes above all previously reserved primes and the
largest threshold needed for a block partition. -/
theorem exists_slot_primes_above (threshold count : ℕ) :
    ∃ p : Fin count → ℕ, Function.Injective p ∧ ∀ i,
      (p i).Prime ∧ threshold < p i ∧ p i ≤ guardedPrimeCap (threshold+count+16) := by
  let P := guardedPrimeCap (threshold+count+16)
  let F := Nat.primesLE P
  let G := F \ Nat.primesLE threshold
  have hF : threshold+count+16 ≤ F.card := by
    rw [Nat.primesLE_card_eq_primeCounting]
    exact guardedPrimeCap_count (by omega)
  have hbad : (Nat.primesLE threshold).card ≤ threshold+1 := by
    rw [Nat.primesLE_eq_filter_range]
    exact (Finset.card_filter_le _ _).trans (by simp)
  have hG : count ≤ G.card := by
    have hs := Finset.le_card_sdiff (Nat.primesLE threshold) F
    change F.card - (Nat.primesLE threshold).card ≤ G.card at hs
    omega
  obtain ⟨U,hU,hc⟩ := Finset.exists_subset_card_eq hG
  let e := (Fintype.equivFinOfCardEq ((Fintype.card_coe U).trans hc)).symm
  refine ⟨fun i => (e i : ℕ), fun i j hij => e.injective (Subtype.ext hij),fun i => ?_⟩
  obtain ⟨hP,ht⟩ := Finset.mem_sdiff.mp (hU (e i).property)
  have hf := Nat.mem_primesLE.mp hP
  exact ⟨hf.2,lt_of_not_ge (fun h => ht (Nat.mem_primesLE.mpr ⟨h,hf.2⟩)),hf.1⟩

end TranslationTiling.FiniteCompiler
