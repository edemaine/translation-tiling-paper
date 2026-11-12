import TranslationTiling.Compiler.EffectiveSystem
import TranslationTiling.FiniteCompiler.EncodedSystem
import TranslationTiling.FiniteCompiler.CyclicFactorCRT

/-! Numerical primitives of the original compiler, generalized to finite
line-rule systems. The arithmetic algorithms are reused unchanged. -/

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace TranslationTiling.FiniteCompiler
noncomputable section
open scoped BigOperators
/-- Decode a cyclic coordinate by reduction modulo each factor. -/
def numericalFactor {T : System} (E : EncodingParameters T) (n : ℕ) : V E :=
  ((n : ZMod (D T)), fun i => ((n : ZMod (E.r i ^ 2)),
    ((n : ZMod (E.a i)), (n : ZMod (E.b i)))))

theorem numericalFactor_eq {T : System} (E : EncodingParameters T) (n : ℕ) :
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

theorem numericalFactor_surjective {T : System} (E : EncodingParameters T)
    (v : V E) : ∃ n : ℕ, n < E.cyclicOrder ∧ numericalFactor E n = v := by
  refine ⟨(finiteFactorEquiv E v).val, ZMod.val_lt _, ?_⟩
  rw [numericalFactor_eq, ZMod.natCast_zmod_val]
  exact (cyclicToFiniteFactor E).apply_symm_apply v

namespace Effective
open Compiler.Effective
open scoped Classical

private theorem numericalRank_compat : Compiler.numericalRank = numericalRank := rfl
private theorem numericalMultiplicity_compat : Compiler.numericalMultiplicity = numericalMultiplicity := rfl

noncomputable def decodeNumericalPoint {T : System} (E : EncodingParameters T)
    (f : NumericalPoint) : Ambient E := (f.1, numericalFactor E f.2)

theorem kernelTest_iff {T : System} (E : EncodingParameters T) (n : ℕ) :
    KernelTest ((Finset.univ : Finset (Channel T)).toList.map E.r) n ↔
      q0 E (decodeNumericalPoint E ((0, 0), n)) = 0 := by
  simp only [KernelTest, List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and]
  constructor
  · intro h
    change (((0, 0) : Plane), fun i => low E i ((n : ZMod (E.r i ^ 2)))) =
      ((0, 0), (0 : Input E))
    refine Prod.ext (by rfl) ?_
    funext i
    change low E i ((n : ZMod (E.r i ^ 2))) = 0
    rw [CyclicShear.low_natCast]
    apply ZMod.val_injective (E.r i)
    simpa only [ZMod.val_natCast, ZMod.val_zero] using h _ ⟨i, rfl⟩
  · intro h r ⟨i, he⟩
    subst r
    have hi := congrFun (congrArg Prod.snd h) i
    change low E i ((n : ZMod (E.r i ^ 2))) = 0 at hi
    rw [CyclicShear.low_natCast] at hi
    simpa only [ZMod.val_natCast, ZMod.val_zero] using congrArg ZMod.val hi

theorem lowCongruences_iff {T : System} (E : EncodingParameters T)
    (k : Input E) (n : ℕ) :
    Congruences ((Finset.univ : Finset (Channel T)).toList.map
      (fun i => (E.r i, (k i).val))) n ↔ ∀ i, (n : K E i) = k i := by
  simp only [Congruences, List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and]
  constructor
  · intro h i
    apply ZMod.val_injective (E.r i)
    simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt (ZMod.val_lt (k i))] using
      h _ ⟨i, rfl⟩
  · intro h c ⟨i, he⟩
    subst c
    have hi := congrArg ZMod.val (h i)
    simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt (ZMod.val_lt (k i))] using hi

theorem usefulZero_iff {T : System} (E : EncodingParameters T) (i : Channel T)
    (h : Plane) (n : ℕ) : UsefulZero (E.a i) (E.b i) n ↔
      usefulCoord E i (decodeNumericalPoint E (h, n)) = 0 := by
  change (n % E.a i = 0 ∧ n % E.b i = 0) ↔
    (((n : ZMod (E.a i)), (n : ZMod (E.b i))) = (0, 0))
  simp only [Prod.mk.injEq, ← (ZMod.val_injective (E.a i)).eq_iff,
    ← (ZMod.val_injective (E.b i)).eq_iff, ZMod.val_natCast, ZMod.val_zero]


theorem kernelCodes_correct {T : System} (E : EncodingParameters T) :
    (kernelCodes E.cyclicOrder ((Finset.univ : Finset (Channel T)).toList.map E.r)).toFinset.image
      (decodeNumericalPoint E) = kernelTile E := by
  classical
  ext g
  constructor
  · intro hg
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hg
    obtain ⟨n, hn, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hf)
    exact (mem_kernelTile E _).mpr ((kernelTest_iff E n).mp
      (of_decide_eq_true (List.mem_filter.mp hn).2))
  · intro hg
    have hq := (mem_kernelTile E g).mp hg
    obtain ⟨n, hn, hv⟩ := numericalFactor_surjective E g.2
    have hp : g.1 = (0, 0) := congrArg Prod.fst hq
    have he : decodeNumericalPoint E ((0, 0), n) = g := Prod.ext hp.symm hv
    apply Finset.mem_image.mpr
    refine ⟨((0, 0), n), List.mem_toFinset.mpr ?_, he⟩
    apply List.mem_map.mpr
    refine ⟨n, List.mem_filter.mpr ⟨List.mem_range.mpr hn, ?_⟩, rfl⟩
    apply decide_eq_true ((kernelTest_iff E n).mpr (he.symm ▸ hq))
theorem q0_decode_iff {T : System} (E : EncodingParameters T)
    (h : Plane) (n : ℕ) (b : Base E) :
    q0 E (decodeNumericalPoint E (h, n)) = b ↔ h = b.1 ∧
      Congruences ((Finset.univ : Finset (Channel T)).toList.map
        (fun i => (E.r i, (b.2 i).val))) n := by
  rw [lowCongruences_iff]
  constructor
  · intro he
    refine ⟨congrArg Prod.fst he, ?_⟩
    intro i
    have hi := congrFun (congrArg Prod.snd he) i
    change low E i ((n : ZMod (E.r i ^ 2))) = b.2 i at hi
    rw [CyclicShear.low_natCast] at hi
    exact hi
  · rintro ⟨hh, hk⟩
    refine Prod.ext hh ?_
    funext i
    change low E i ((n : ZMod (E.r i ^ 2))) = b.2 i
    rw [CyclicShear.low_natCast]
    exact hk i

theorem invarianceCodes_correct {T : System} (E : EncodingParameters T)
    (i : Channel T) (σ : Base E) :
    (invarianceCodes E.cyclicOrder
      ((Finset.univ : Finset (Channel T)).toList.map E.r) (E.a i) (E.b i) σ.1
      ((Finset.univ : Finset (Channel T)).toList.map
        (fun j => (E.r j, (σ.2 j).val)))).toFinset.image (decodeNumericalPoint E) =
      invarianceTile E i σ := by
  ext g
  constructor
  · intro hg
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hg
    rcases List.mem_append.mp (List.mem_toFinset.mp hf) with hf | hf
    · obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hf
      obtain ⟨_, htests⟩ := List.mem_filter.mp hn
      obtain ⟨hk, hz⟩ := of_decide_eq_true htests
      apply (mem_invarianceTile E i σ _).mpr
      refine Or.inl ⟨(kernelTest_iff E n).mp hk, ?_⟩
      exact fun h => hz ((usefulZero_iff E i (0, 0) n).mpr h)
    · obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hf
      obtain ⟨_, htests⟩ := List.mem_filter.mp hn
      obtain ⟨hc, hz⟩ := of_decide_eq_true htests
      apply (mem_invarianceTile E i σ _).mpr
      exact Or.inr ⟨(q0_decode_iff E σ.1 n σ).mpr ⟨rfl, hc⟩,
        (usefulZero_iff E i σ.1 n).mp hz⟩
  · intro hg
    obtain ⟨n, hn, hv⟩ := numericalFactor_surjective E g.2
    rcases (mem_invarianceTile E i σ g).mp hg with ⟨hq, hc⟩ | ⟨hq, hc⟩
    · have hp : g.1 = (0, 0) := congrArg Prod.fst hq
      have he : decodeNumericalPoint E ((0, 0), n) = g := Prod.ext hp.symm hv
      apply Finset.mem_image.mpr
      refine ⟨((0, 0), n), List.mem_toFinset.mpr ?_, he⟩
      apply List.mem_append.mpr
      apply Or.inl
      apply List.mem_map.mpr
      refine ⟨n, List.mem_filter.mpr ⟨List.mem_range.mpr hn, ?_⟩, rfl⟩
      apply decide_eq_true
      refine ⟨(kernelTest_iff E n).mpr (he.symm ▸ hq), ?_⟩
      intro hz
      have hc' := (usefulZero_iff E i (0, 0) n).mp hz
      exact hc (he ▸ hc')
    · have hp : g.1 = σ.1 := congrArg Prod.fst hq
      have he : decodeNumericalPoint E (σ.1, n) = g := Prod.ext hp.symm hv
      apply Finset.mem_image.mpr
      refine ⟨(σ.1, n), List.mem_toFinset.mpr ?_, he⟩
      apply List.mem_append.mpr
      apply Or.inr
      apply List.mem_map.mpr
      refine ⟨n, List.mem_filter.mpr ⟨List.mem_range.mpr hn, ?_⟩, rfl⟩
      apply decide_eq_true
      exact ⟨((q0_decode_iff E σ.1 n σ).mp (he.symm ▸ hq)).2,
        (usefulZero_iff E i σ.1 n).mpr (he.symm ▸ hc)⟩
noncomputable def nativeActivationNumbers {T : System} (E : EncodingParameters T)
    (i : Channel T) (j : ActivationIndex E i) : ActivationNumbers :=
  ((E.a i, E.b i, E.r i), (j.1.val, j.2.1.1.val, j.2.1.2.val, j.2.2.val))

private theorem activationCongruences_iff {T : System} (E : EncodingParameters T)
    (i : Channel T) (j : ActivationIndex E i) (n : ℕ) :
    Congruences [(E.r i, j.1.val),
      (E.a i, (rhoA (E.a_two_le i) (E.b_two_le i) j.2).val),
      (E.b i, (rhoB (E.a_two_le i) (E.b_two_le i) j.2).val)] n ↔
      activationCRT E i (n : ZMod (activationModulus E i)) =
        ((j.1, rhoA (E.a_two_le i) (E.b_two_le i) j.2),
          rhoB (E.a_two_le i) (E.b_two_le i) j.2) := by
  have he : activationCRT E i (n : ZMod (activationModulus E i)) =
      (((n : K E i), (n : ZMod (E.a i))), (n : ZMod (E.b i))) := by
    rw [map_natCast]
    rfl
  rw [he]
  simp only [Congruences, List.forall_mem_cons, List.not_mem_nil, false_implies, forall_const, and_true,
    Prod.mk.injEq, ← (ZMod.val_injective (E.r i)).eq_iff,
    ← (ZMod.val_injective (E.a i)).eq_iff, ← (ZMod.val_injective (E.b i)).eq_iff,
    ZMod.val_natCast, Nat.mod_eq_of_lt (ZMod.val_lt j.1),
    Nat.mod_eq_of_lt (ZMod.val_lt (rhoA (E.a_two_le i) (E.b_two_le i) j.2)),
    Nat.mod_eq_of_lt (ZMod.val_lt (rhoB (E.a_two_le i) (E.b_two_le i) j.2))]
  exact and_assoc.symm

theorem numericalActivationFirst_eq {T : System} (E : EncodingParameters T)
    (n : Column T) (j : ActivationIndex E (.inl n)) :
    numericalActivationFirst (nativeActivationNumbers E (.inl n) j) = ordinaryFirst E n j := by
  let i : Channel T := .inl n
  have hA : differenceResidue (E.a i)
      (numericalRank j.2.1.1.val j.2.1.2.val j.2.2.val) j.2.1.1.val =
        (rhoA (E.a_two_le i) (E.b_two_le i) j.2).val := by
    rw [differenceResidue_eq, ZMod.natCast_zmod_val]
    rfl
  have hB : differenceResidue (E.b i)
      (numericalRank j.2.1.2.val j.2.1.1.val j.2.2.val) j.2.1.2.val =
        (rhoB (E.a_two_le i) (E.b_two_le i) j.2).val := by
    rw [differenceResidue_eq, ZMod.natCast_zmod_val]
    rfl
  have hs := residueSearch_of_equiv (activationCRT E i).toEquiv
    ((j.1, rhoA (E.a_two_le i) (E.b_two_le i) j.2),
      rhoB (E.a_two_le i) (E.b_two_le i) j.2)
    [(E.r i, j.1.val), (E.a i, (rhoA (E.a_two_le i) (E.b_two_le i) j.2).val),
      (E.b i, (rhoB (E.a_two_le i) (E.b_two_le i) j.2).val)]
    (activationCongruences_iff E i j)
  unfold numericalActivationFirst nativeActivationNumbers ordinaryFirst separatedResidueLift
  dsimp only
  dsimp only [i, activationModulus] at hs
  simp only [numericalRank_compat]
  rw [hA, hB, hs]
  rfl
noncomputable def nativeSeedNumbers {T : System} (E : EncodingParameters T)
    (t : Fin 2) (j : SeedActivationIndex E t) : SeedNumbers :=
  (nativeActivationNumbers E (.inr t) j.1,
    (residueModulus, E.a (.inr (otherSeed t)), j.2.1.val, j.2.2.val))

private theorem seedCongruences_iff {T : System} (E : EncodingParameters T)
    (t : Fin 2) (j : SeedActivationIndex E t) (n : ℕ) :
    Congruences [(E.r (.inr t), j.1.1.val),
      (E.a (.inr t), (rhoA (E.a_two_le (.inr t)) (E.b_two_le (.inr t)) j.1.2).val),
      (E.b (.inr t), (rhoB (E.a_two_le (.inr t)) (E.b_two_le (.inr t)) j.1.2).val),
      (residueModulus, j.2.1.val), (E.a (.inr (otherSeed t)), 0)] n ↔
      seedCRT E t (n : ZMod (seedModulus E t)) =
        ((((j.1.1, rhoA (E.a_two_le (.inr t)) (E.b_two_le (.inr t)) j.1.2),
          rhoB (E.a_two_le (.inr t)) (E.b_two_le (.inr t)) j.1.2), j.2.1), 0) := by
  have he : seedCRT E t (n : ZMod (seedModulus E t)) =
      (((((n : K E (.inr t)), (n : ZMod (E.a (.inr t)))),
        (n : ZMod (E.b (.inr t)))), (n : ZMod residueModulus)),
          (n : ZMod (E.a (.inr (otherSeed t))))) := by
    rw [map_natCast]
    rfl
  rw [he]
  simp only [Congruences, List.forall_mem_cons, List.not_mem_nil, false_implies,
    forall_const, and_true, Prod.mk.injEq,
    ← (ZMod.val_injective (E.r (.inr t))).eq_iff,
    ← (ZMod.val_injective (E.a (.inr t))).eq_iff,
    ← (ZMod.val_injective (E.b (.inr t))).eq_iff,
    ← (ZMod.val_injective residueModulus).eq_iff,
    ← (ZMod.val_injective (E.a (.inr (otherSeed t)))).eq_iff,
    ZMod.val_natCast, ZMod.val_zero, Nat.zero_mod,
    Nat.mod_eq_of_lt (ZMod.val_lt j.1.1), Nat.mod_eq_of_lt (ZMod.val_lt j.2.1),
    Nat.mod_eq_of_lt (ZMod.val_lt (rhoA (E.a_two_le (.inr t)) (E.b_two_le (.inr t)) j.1.2)),
    Nat.mod_eq_of_lt (ZMod.val_lt (rhoB (E.a_two_le (.inr t)) (E.b_two_le (.inr t)) j.1.2))]
  tauto

theorem numericalSeedFirst_eq {T : System} (E : EncodingParameters T)
    (t : Fin 2) (j : SeedActivationIndex E t) :
    numericalSeedFirst (nativeSeedNumbers E t j) = seedFirst E t j := by
  let i : Channel T := .inr t
  have hA : differenceResidue (E.a i)
      (numericalRank j.1.2.1.1.val j.1.2.1.2.val j.1.2.2.val) j.1.2.1.1.val =
        (rhoA (E.a_two_le i) (E.b_two_le i) j.1.2).val := by
    rw [differenceResidue_eq, ZMod.natCast_zmod_val]
    rfl
  have hB : differenceResidue (E.b i)
      (numericalRank j.1.2.1.2.val j.1.2.1.1.val j.1.2.2.val) j.1.2.1.2.val =
        (rhoB (E.a_two_le i) (E.b_two_le i) j.1.2).val := by
    rw [differenceResidue_eq, ZMod.natCast_zmod_val]
    rfl
  have hs := residueSearch_of_equiv (seedCRT E t).toEquiv
    ((((j.1.1, rhoA (E.a_two_le i) (E.b_two_le i) j.1.2),
      rhoB (E.a_two_le i) (E.b_two_le i) j.1.2), j.2.1), 0)
    [(E.r i, j.1.1.val), (E.a i, (rhoA (E.a_two_le i) (E.b_two_le i) j.1.2).val),
      (E.b i, (rhoB (E.a_two_le i) (E.b_two_le i) j.1.2).val),
      (residueModulus, j.2.1.val), (E.a (.inr (otherSeed t)), 0)]
    (seedCongruences_iff E t j)
  unfold numericalSeedFirst nativeSeedNumbers nativeActivationNumbers seedFirst separatedResidueLift
  dsimp only
  dsimp only [i, seedModulus, activationModulus] at hs
  simp only [numericalRank_compat]
  rw [hA, hB, hs]
  rfl
noncomputable def rawActivationIndex {T : System} (E : EncodingParameters T)
    (i : Channel T) (j : ActivationIndex E i) : ActivationCode :=
  (j.1.val, j.2.1.1.val, j.2.1.2.val, j.2.2.val)

theorem rawActivationIndex_mem {T : System} (E : EncodingParameters T)
    (i : Channel T) (j : ActivationIndex E i) :
    rawActivationIndex E i j ∈ activationIndices (E.a i) (E.b i) (E.r i) := by
  apply (mem_activationIndices _ _ _ _).mpr
  refine ⟨ZMod.val_lt j.1, ZMod.val_lt j.2.1.1, ZMod.val_lt j.2.1.2, ?_⟩
  change j.2.2.val < Compiler.numericalMultiplicity j.2.1.1.val j.2.1.2.val
  rw [numericalMultiplicity_compat, ← shiftMultiplicity_numerical (E.a_two_le i) (E.b_two_le i)]
  exact j.2.2.isLt

theorem activationIndices_native {T : System} (E : EncodingParameters T)
    (i : Channel T) (code : ActivationCode) :
    code ∈ activationIndices (E.a i) (E.b i) (E.r i) ↔
      ∃ j : ActivationIndex E i, rawActivationIndex E i j = code := by
  constructor
  · intro hc
    obtain ⟨hk, hα, hξ, hd⟩ := (mem_activationIndices _ _ _ _).mp hc
    let e : P E i := ((code.2.1 : ℕ), (code.2.2.1 : ℕ))
    have he₁ : e.1.val = code.2.1 := by
      change (code.2.1 : ZMod (E.a i)).val = _
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt hα]
    have he₂ : e.2.val = code.2.2.1 := by
      change (code.2.2.1 : ZMod (E.b i)).val = _
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt hξ]
    have he : code.2.2.2 < shiftMultiplicity (E.a i) (E.b i) e := by
      rw [shiftMultiplicity_numerical (E.a_two_le i) (E.b_two_le i), he₁, he₂]
      exact hd
    refine ⟨((code.1 : ℕ), ⟨e, ⟨code.2.2.2, he⟩⟩), ?_⟩
    change ((code.1 : ZMod (E.r i)).val, e.1.val, e.2.val, code.2.2.2) = code
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hk, he₁, he₂]
  · rintro ⟨j, rfl⟩
    exact rawActivationIndex_mem E i j

noncomputable def rawSeedIndex {T : System} (E : EncodingParameters T)
    (t : Fin 2) (j : SeedActivationIndex E t) : SeedCode :=
  (rawActivationIndex E (.inr t) j.1, j.2.1.val, j.2.2.val)

theorem seedIndices_native {T : System} (E : EncodingParameters T)
    (t : Fin 2) (code : SeedCode) :
    code ∈ seedIndices (E.a (.inr t)) (E.b (.inr t)) (E.r (.inr t)) residueModulus ↔
      ∃ j : SeedActivationIndex E t, rawSeedIndex E t j = code := by
  simp only [seedIndices, List.mem_flatMap, List.mem_map, List.mem_range, Prod.mk.injEq]
  constructor
  · rintro ⟨c, hc, x, hx, y, hy, rfl⟩
    obtain ⟨j, rfl⟩ := (activationIndices_native E (.inr t) c).mp hc
    refine ⟨(j, ((x : ℕ), (y : ℕ))), ?_⟩
    change (rawActivationIndex E (.inr t) j,
      (x : ZMod residueModulus).val, (y : ZMod residueModulus).val) =
        (rawActivationIndex E (.inr t) j, x, y)
    rw [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy]
  · rintro ⟨j, rfl⟩
    exact ⟨rawActivationIndex E (.inr t) j.1, rawActivationIndex_mem E (.inr t) j.1,
      j.2.1.val, ZMod.val_lt j.2.1, j.2.2.val, ZMod.val_lt j.2.2, rfl⟩
noncomputable def nativeActivationBatchData {T : System}
    (E : EncodingParameters T) (i : Channel T) (h : Plane) (e : P E i)
    (freeZ : Bool) : ActivationBatchData :=
  ((E.cyclicOrder, ((Finset.univ : Finset (Channel T)).filter (· ≠ i)).toList.map E.r),
    (E.r i, E.a i, E.b i, D T), h, (e.1.val, e.2.val), freeZ)

theorem activationBatchTest_iff {T : System} (E : EncodingParameters T)
    (i : Channel T) (h : Plane) (e : P E i) (freeZ : Bool) (n : ℕ) :
    ActivationBatchTest (nativeActivationBatchData E i h e freeZ) n ↔
      decodeNumericalPoint E (h, n) ∈ activationBatch E i h e freeZ := by
  have hother : KernelTest
      (((Finset.univ : Finset (Channel T)).filter (· ≠ i)).toList.map E.r) n ↔
      ∀ j, j ≠ i → low E j (n : ZMod (E.r j ^ 2)) = 0 := by
    simp only [KernelTest, List.mem_map, Finset.mem_toList, Finset.mem_filter,
      Finset.mem_univ, true_and, CyclicShear.low_natCast]
    constructor
    · intro hn j hj
      apply ZMod.val_injective (E.r j)
      simpa only [ZMod.val_natCast, ZMod.val_zero] using hn _ ⟨j, hj, rfl⟩
    · intro hn r ⟨j, hj, he⟩
      subst r
      simpa only [ZMod.val_natCast, ZMod.val_zero] using congrArg ZMod.val (hn j hj)
  rw [mem_activationBatch]
  change ActivationBatchTest (nativeActivationBatchData E i h e freeZ) n ↔
    h = h ∧ (n : ZMod (E.r i ^ 2)) = (h.1 : ZMod (E.r i ^ 2)) ∧
    (((n : ZMod (E.a i)), (n : ZMod (E.b i))) = e) ∧
    (∀ j, j ≠ i → low E j (n : ZMod (E.r j ^ 2)) = 0) ∧
    (freeZ = true ∨ (n : ZMod (D T)) = 0)
  simp only [true_and, ← hother, ← (ZMod.val_injective (E.r i ^ 2)).eq_iff,
    ← (ZMod.val_injective (D T)).eq_iff, ZMod.val_natCast, ZMod.val_intCast,
    ZMod.val_zero, Prod.ext_iff, ← (ZMod.val_injective (E.a i)).eq_iff,
    ← (ZMod.val_injective (E.b i)).eq_iff, ZMod.val_natCast]
  unfold ActivationBatchTest nativeActivationBatchData
  dsimp only
  have hval : (h.1 : ZMod (E.r i ^ 2)).val = (h.1 % (E.r i ^ 2 : ℕ)).toNat := by
    have hv := congrArg Int.toNat (ZMod.val_intCast (n := E.r i ^ 2) h.1)
    simpa only [Int.toNat_natCast] using hv
  rw [hval]
  rw [Nat.mod_eq_of_lt (ZMod.val_lt e.1), Nat.mod_eq_of_lt (ZMod.val_lt e.2)]
  tauto

theorem activationBatchCodes_correct {T : System} (E : EncodingParameters T)
    (i : Channel T) (h : Plane) (e : P E i) (freeZ : Bool) :
    (activationBatchCodes (nativeActivationBatchData E i h e freeZ)).toFinset.image
      (decodeNumericalPoint E) = activationBatch E i h e freeZ := by
  ext g
  constructor
  · intro hg
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hg
    obtain ⟨n, hn, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hf)
    exact (activationBatchTest_iff E i h e freeZ n).mp
      (of_decide_eq_true (List.mem_filter.mp hn).2)
  · intro hg
    obtain ⟨n, hn, hv⟩ := numericalFactor_surjective E g.2
    have hp : g.1 = h := ((mem_activationBatch E i h e freeZ g).mp hg).1
    have he : decodeNumericalPoint E (h, n) = g := Prod.ext hp.symm hv
    apply Finset.mem_image.mpr
    refine ⟨(h, n), List.mem_toFinset.mpr ?_, he⟩
    apply List.mem_map.mpr
    refine ⟨n, List.mem_filter.mpr ⟨List.mem_range.mpr hn, ?_⟩, rfl⟩
    exact decide_eq_true ((activationBatchTest_iff E i h e freeZ n).mpr (he.symm ▸ hg))

noncomputable def nativeActivationEnvironment {T : System}
    (E : EncodingParameters T) (i : Channel T) : ActivationEnvironment :=
  ((E.cyclicOrder, ((Finset.univ : Finset (Channel T)).filter (· ≠ i)).toList.map E.r),
    (E.r i, E.a i, E.b i, D T))

theorem ordinaryBatchCodes_correct {T : System} (E : EncodingParameters T)
    (n : Column T) (k : ℕ) (hs : T.slope n = (k : ℤ)) (j : ActivationIndex E (.inl n)) :
    (ordinaryBatchCodes (nativeActivationEnvironment E (.inl n)) k
      (rawActivationIndex E (.inl n) j)).toFinset.image (decodeNumericalPoint E) =
      activationBatch E (.inl n) (ordinaryOffset E n j)
        (shift (E.a (.inl n)) (E.b (.inl n)) j.2) true := by
  unfold ordinaryBatchCodes
  change (activationBatchCodes (_, _,
    (numericalActivationFirst (nativeActivationNumbers E (.inl n) j),
      -(k : ℤ) * numericalActivationFirst (nativeActivationNumbers E (.inl n) j)), _, _)).toFinset.image _ = _
  rw [numericalActivationFirst_eq]
  simpa only [ordinaryOffset, hs, nativeActivationBatchData, nativeActivationEnvironment,
    rawActivationIndex, shift] using
    (activationBatchCodes_correct E (.inl n) (ordinaryOffset E n j)
      (shift (E.a (.inl n)) (E.b (.inl n)) j.2) true)

theorem seedBatchCodes_correct {T : System} (E : EncodingParameters T)
    (t : Fin 2) (j : SeedActivationIndex E t) :
    (seedBatchCodes (nativeActivationEnvironment E (.inr t))
      (E.a (.inr (otherSeed t))) residueModulus (rawSeedIndex E t j)).toFinset.image
        (decodeNumericalPoint E) = activationBatch E (.inr t) (seedOffset E t j)
          (shift (E.a (.inr t)) (E.b (.inr t)) j.1.2) false := by
  unfold seedBatchCodes
  change (activationBatchCodes (_, _,
    (numericalSeedFirst (nativeSeedNumbers E t j), (j.2.2.val : ℤ)), _, _)).toFinset.image _ = _
  rw [numericalSeedFirst_eq]
  exact activationBatchCodes_correct E (.inr t) _ _ _

theorem ordinaryCodes_correct {T : System} (E : EncodingParameters T) (n : Column T)
    (k : ℕ) (hs : T.slope n = (k : ℤ)) :
    (ordinaryCodes (nativeActivationEnvironment E (.inl n)) k).toFinset.image
      (decodeNumericalPoint E) = ordinaryActivationTile E n := by
  ext g
  simp only [ordinaryCodes, nativeActivationEnvironment, Finset.mem_image, List.mem_toFinset,
    List.mem_flatMap, activationIndices_native, ordinaryActivationTile,
    Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨f, ⟨code, ⟨j, rfl⟩, hf⟩, he⟩
    refine ⟨j, ?_⟩
    rw [← ordinaryBatchCodes_correct E n k hs j]
    exact Finset.mem_image.mpr ⟨f, List.mem_toFinset.mpr hf, he⟩
  · rintro ⟨j, hg⟩
    rw [← ordinaryBatchCodes_correct E n k hs j] at hg
    obtain ⟨f, hf, he⟩ := Finset.mem_image.mp hg
    exact ⟨f, ⟨_, ⟨j, rfl⟩, List.mem_toFinset.mp hf⟩, he⟩

theorem seedCodes_correct {T : System} (E : EncodingParameters T) (t : Fin 2) :
    (seedCodes (nativeActivationEnvironment E (.inr t)) (E.a (.inr (otherSeed t)))
      residueModulus).toFinset.image (decodeNumericalPoint E) = seedActivationTile E t := by
  ext g
  simp only [seedCodes, nativeActivationEnvironment, Finset.mem_image, List.mem_toFinset,
    List.mem_flatMap, seedIndices_native, seedActivationTile,
    Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨f, ⟨code, ⟨j, rfl⟩, hf⟩, he⟩
    refine ⟨j, ?_⟩
    rw [← seedBatchCodes_correct E t j]
    exact Finset.mem_image.mpr ⟨f, List.mem_toFinset.mpr hf, he⟩
  · rintro ⟨j, hg⟩
    rw [← seedBatchCodes_correct E t j] at hg
    obtain ⟨f, hf, he⟩ := Finset.mem_image.mp hg
    exact ⟨f, ⟨_, ⟨j, rfl⟩, List.mem_toFinset.mp hf⟩, he⟩

end Effective
end
end TranslationTiling.FiniteCompiler
