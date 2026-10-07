import TranslationTiling.Compiler.CyclicFactorCRT

set_option maxRecDepth 1000
set_option maxHeartbeats 100000

namespace TranslationTiling.Compiler

noncomputable section
open scoped BigOperators

/-- Decode a cyclic coordinate by reduction modulo each factor. -/
def numericalFactor {T : LeanWang.TileSet} (E : EncodingParameters T) (n : ℕ) : V E :=
  ((n : ZMod (D T)), fun i => ((n : ZMod (E.r i ^ 2)),
    ((n : ZMod (E.a i)), (n : ZMod (E.b i)))))

theorem numericalFactor_eq {T : LeanWang.TileSet} (E : EncodingParameters T) (n : ℕ) :
    numericalFactor E n = cyclicToFiniteFactor E (n : ZMod E.cyclicOrder) := by
  have houter : ZMod.chineseRemainder E.p4_coprime_blocks (n : ZMod E.cyclicOrder) =
      ((n : ZMod (D T)), (n : ZMod (∏ i : Channel T, E.blockModulus i))) := by
    change ZMod.chineseRemainder E.p4_coprime_blocks
      (n : ZMod (residueModulus ^ 2 * ∏ i : Channel T, E.blockModulus i)) =
        ((n : ZMod (residueModulus ^ 2)), (n : ZMod (∏ i : Channel T, E.blockModulus i)))
    rw [map_natCast]
    rfl
  have hpi : ZMod.prodEquivPi E.blockModulus E.blockModulus_pairwise
      (n : ZMod (∏ i : Channel T, E.blockModulus i)) = fun i =>
        (n : ZMod (E.blockModulus i)) := by
    rw [map_natCast]
    rfl
  have hchannel (i : Channel T) : channelCRT E i (n : ZMod (E.blockModulus i)) =
      ((n : ZMod (E.r i ^ 2)), ((n : ZMod (E.a i)), (n : ZMod (E.b i)))) := by
    let hRA := (E.r_coprime_a i i).pow_left 2
    let hRAB := Nat.coprime_mul_iff_left.mpr
      ⟨(E.r_coprime_b i i).pow_left 2, E.a_coprime_b i⟩
    change (((ZMod.chineseRemainder hRA)
        ((ZMod.chineseRemainder hRAB) (n : ZMod (E.r i ^ 2 * E.a i * E.b i))).1).1,
      ((ZMod.chineseRemainder hRA)
        ((ZMod.chineseRemainder hRAB) (n : ZMod (E.r i ^ 2 * E.a i * E.b i))).1).2,
      ((ZMod.chineseRemainder hRAB) (n : ZMod (E.r i ^ 2 * E.a i * E.b i))).2) = _
    simp only [map_natCast, Prod.fst_natCast, Prod.snd_natCast]
  change ((n : ZMod (D T)), fun i => ((n : ZMod (E.r i ^ 2)),
      ((n : ZMod (E.a i)), (n : ZMod (E.b i))))) =
    ((ZMod.chineseRemainder E.p4_coprime_blocks (n : ZMod E.cyclicOrder)).1,
      fun i => channelCRT E i
        ((ZMod.prodEquivPi E.blockModulus E.blockModulus_pairwise)
          (ZMod.chineseRemainder E.p4_coprime_blocks (n : ZMod E.cyclicOrder)).2 i))
  rw [houter]
  dsimp only
  rw [hpi]
  exact Prod.ext rfl (funext fun i => (hchannel i).symm)

theorem numericalFactor_surjective {T : LeanWang.TileSet} (E : EncodingParameters T)
    (v : V E) : ∃ n : ℕ, n < E.cyclicOrder ∧ numericalFactor E n = v := by
  refine ⟨(finiteFactorEquiv E v).val, ZMod.val_lt _, ?_⟩
  rw [numericalFactor_eq, ZMod.natCast_zmod_val]
  exact (cyclicToFiniteFactor E).apply_symm_apply v

end
end TranslationTiling.Compiler
