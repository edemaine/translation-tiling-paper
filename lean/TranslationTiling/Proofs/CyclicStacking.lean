import TranslationTiling.Proofs.Stacking
import TranslationTiling.Proofs.FullDifferencePartition

namespace TranslationTiling.Stacking

/-- A sufficiently large fresh cyclic prime consolidates any finite nonempty
family of tiling equations. The computable partition choice is proved in
`Compiler.EffectivePartition`. -/
theorem exists_cyclic_stack {H : Type*} [AddCommGroup H]
    (s : ℕ) (hs : 0 < s) (F : Fin s → Finset H)
    (hF : ∀ i, (F i).Nonempty) (forbidden : Finset ℕ) (lower : ℕ) :
    ∃ q : ℕ, q.Prime ∧ lower < q ∧ q ∉ forbidden ∧
      ∃ E : Fin s → Finset (ZMod q),
        (stack F E).Nonempty ∧
        ((∃ A : Set H, ∀ i, Covers (F i) A) ↔
          ∃ B : Set (H × ZMod q), Covers (stack F E) B) := by
  obtain ⟨q, hq, hl, hfresh, E, hE, hpart, hfull⟩ :=
    exists_fresh_prime_fullDifference_partition s hs forbidden lower
  letI : NeZero q := ⟨hq.ne_zero⟩
  letI : Nonempty (Fin s) := ⟨⟨0, hs⟩⟩
  exact ⟨q, hq, hl, hfresh, E, stack_nonempty hF hE,
    exists_tiles_stack_iff hpart hfull hE⟩

end TranslationTiling.Stacking
