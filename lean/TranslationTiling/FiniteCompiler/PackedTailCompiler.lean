import TranslationTiling.FiniteCompiler.PackedCompiler
import TranslationTiling.FiniteCompiler.PackedTailParameters
import TranslationTiling.Compiler.GuardedVolumeBound

namespace TranslationTiling.FiniteCompiler.Packed

open PairSmall Compiler Compiler.Size Compiler.StripLift
open TranslationTiling.FiniteCompiler.Effective
open scoped Classical BigOperators

noncomputable section

local instance packedTailCompilerFrame : SeedFrame := compactSeedFrame
attribute [local instance] ColumnRefinement.family

set_option maxHeartbeats 4000000
set_option exponentiation.threshold 20000

theorem tailSupport {S : System} [AlphabetFamily S] {k : ℕ} (hk : 20 ≤ k)
    (hw : S.width = (ternaryLayoutProfile k).width)
    (ha : ∀ i : Column S, AlphabetFamily.size (T:=S) i = (ternaryLayoutProfile k).arity i.val)
    (hslope : ∀ i : Column S, S.slope i = ((ternaryLayoutProfile k).slope i.val : ℤ)) :
    PartialStrip.StripBounds (tailEncoding hk hw ha) (fun _ => guardedRadius k) := by
  let E := tailEncoding hk hw ha
  let H := guardedRadius k
  let P := guardedDigitCap k
  have hpair := guardedPairCaps_ge hk
  have hPlo : guardedPairCap k ^ 2 ≤ P :=
    (show guardedPairCap k ^ 2 ≤ guardedDigitStart k by unfold guardedDigitStart; omega).trans
      (guardedDigitCap_gt hk).le
  have hH : 2^51 ≤ H := by
    have h₁ : 16^2 ≤ guardedPairCap k^2 := Nat.pow_le_pow_left hpair.1 _
    have h₂ : 16^2 ≤ P := h₁.trans hPlo
    unfold H guardedRadius
    exact (by decide : 2^51 ≤ 2*16^2*(16^2)^6).trans
      (Nat.mul_le_mul (Nat.mul_le_mul_left 2 h₁) (Nat.pow_le_pow_left h₂ _))
  refine ⟨(by decide : 35 ≤ 2^51).trans hH, ?_, ?_, ?_⟩
  · intro i
    rw [hslope, Int.natAbs_natCast]
    refine ⟨by positivity, ?_⟩
    unfold Profile.slope ternaryLayoutProfile
    split_ifs with hi hj
    · have he : i.val < ([0,1,2,3,4,5,6,7,10,0,1,2,3,4,7,8,9,14] : List ℕ).length := hi
      have hh := getD_mem_of_lt _ _ 0 he
      exact (by decide : ∀ x ∈ ([0,1,2,3,4,5,6,7,10,0,1,2,3,4,7,8,9,14] : List ℕ), x≤16) _ hh
    · decide
    · decide
  · intro i
    have hr : E.r (.inl i) ≤ P^6 := tailEncoding_r hk hw ha i
    have ha : E.a (.inl i) ≤ guardedPairCap k ∧ E.b (.inl i) ≤ guardedPairCap k :=
      tailEncoding_pair hk hw ha i
    unfold guardedRadius
    calc
      _ ≤ 2*(P^6*guardedPairCap k*guardedPairCap k) :=
        Nat.mul_le_mul_left 2 (Nat.mul_le_mul (Nat.mul_le_mul hr ha.1) ha.2)
      _ = _ := by unfold P; ring
  · intro t
    have hsa (z : Fin 2) : E.a (.inr z) = tailSeedA z := rfl
    have hb (z : Fin 2) : E.b (.inr z) = tailSeedB z := rfl
    have hr (z : Fin 2) : E.r (.inr z) = tailSeedDigit z :=
      tailEncoding_seed_r hk hw ha z
    have hm : residueModulus = 35 := by norm_num [residueModulus_value,compactSeedFrame]
    unfold CompactSupport.B
    rw [hsa,hsa,hb,hr,hm]
    exact (show _ ≤ 2^51 by fin_cases t <;> decide).trans hH

/-- At large input sizes all Wang digits use the same radix, with prime budgets
given by the size of the refined system. -/
theorem tail_tile_exists (T : LeanWang.TileSet) (hn : 3^21 < T.length) :
    ∃ U : Tile 3, U ≠ [] ∧ FaceConnected U ∧
      (LeanWang.TilesPlane T ↔ TranslationTiling.Tiles U) ∧
      (U.length : ℝ) ≤ guardedBound T.length := by
  let n := T.length
  let k := guardedTrits n
  let p := ternaryLayoutProfile k
  have hk : 20 ≤ k := guardedTrits_ge hn
  have hp : p.radices.prod = 3^k := by simp [p,ternaryLayoutProfile,List.prod_replicate]
  have hlo : 0 < T.length := (by decide : 0 < 3^21).trans hn
  let C := code T p.radices.prod hlo (by rw [hp]; exact guardedTrits_capacity n)
  letI : AlphabetFamily (system C) := GuardedCompiler.alphabet C
  let S := refinement p (packedTernary_layout p (by omega) rfl) C
  letI : AlphabetFamily S.system := S.family
  let E : EncodingParameters S.system := tailEncoding hk rfl (fun _ => rfl)
  let H := guardedRadius k
  let X := guardedTests n
  let P := guardedDigitCap k
  have hpair := guardedPairCaps_ge hk
  have hPlo : guardedPairCap k ^ 2 ≤ P :=
    (show guardedPairCap k ^ 2 ≤ guardedDigitStart k by unfold guardedDigitStart; omega).trans
      (guardedDigitCap_gt hk).le
  have hsupport : PartialStrip.StripBounds E (fun _ => H) :=
    tailSupport hk rfl (fun _ => rfl)
      (packedTernary_layout p (by omega : 0 < k) rfl).slope
  have hP : 35 ≤ P :=
    (by decide : 35 ≤ 16^2).trans ((Nat.pow_le_pow_left hpair.1 2).trans hPlo)
  have hprime : PrimeBound E.cyclicOrder P :=
    prime_bound E hP (tailEncoding_prime_bound hk rfl (fun _ => rfl))
  have hsize : (PartialStrip.family (GuardedCompiler.refinedPatterns C S) E).length ≤ X := by
    have ht := PartialStrip.family_length_bound (GuardedCompiler.refinedPatterns C S) E
    simp only [GuardedCompiler.refinedPatterns,List.length_map] at ht
    have hpat := patterns_length_bound C
    change _ ≤ 2313+72*(p.radices.prod)^2 at hpat
    have hpat' : (GuardedCompiler.patterns C).length ≤ 2313+72*(3^k)^2 :=
      hpat.trans_eq (congrArg (fun d : ℕ => 2313+72*d^2) hp)
    have hcap := guardedTrits_capacity_le ((by decide : 1 < 3^21).trans hn)
    have hcap₂ := Nat.pow_le_pow_left hcap 2
    have hw : S.system.width ≤ 3*(n+4) := by
      change p.width ≤ _
      rw [show p.width = 18+2*k from ternaryLayout_width k]
      have hh := Nat.log_le_self 3 (n-1)
      unfold k guardedTrits
      have hh' : 6 ≤ n := (by decide : 6 ≤ 3^21).trans hn.le
      omega
    have hw₂ := Nat.pow_le_pow_left (show S.system.width+2 ≤ 4*(n+4) by omega) 2
    have hs : (∑ i : Column S.system, AlphabetFamily.size (T:=S.system) i) ≤ 6*S.system.width := by
      calc
        _ ≤ ∑ _i : Column S.system, 6 := by
          apply Finset.sum_le_sum
          intro i _
          change p.arity i.val ≤ 6
          rw [ternaryLayout_arity (by omega) i.isLt]
          split_ifs <;> decide
        _ = _ := by simp [Column, Nat.mul_comm]
    have hn' : (6 : ℕ) ≤ n := (by decide : 6 ≤ 3^21).trans hn.le
    change (PartialStrip.family (List.map S.expand (GuardedCompiler.patterns C)) E).length ≤
      1024*(n+4)^2
    change (3^k)^2 ≤ (3*n)^2 at hcap₂
    nlinarith only [ht, hpat', hcap₂, hw, hw₂, hs, hn']
  have hX : 2313 ≤ X := by unfold X guardedTests; nlinarith
  obtain ⟨U,hne,hc,hiff,hvol⟩ :=
    PartialStrip.exists_strip_tile _ E _ hsupport X P (by omega) hprime hX hsize (guard_stack_budget hn)
  refine ⟨U,hne,hc,(GuardedCompiler.refined_deck_equiv C S E).trans hiff,?_⟩
  have hv : (U.length : ℝ) ≤ (reservedVolumeCap 35 (fun _ => H) (inputOrder E)
      (MassSize.mass E) (reservedCap X P) : ℕ) := by exact_mod_cast hvol
  exact hv.trans (guarded_volume_bound hn (inputOrder_pos E)
    (tailEncoding_order_mass hk rfl (fun _ => rfl)))

end
end TranslationTiling.FiniteCompiler.Packed
