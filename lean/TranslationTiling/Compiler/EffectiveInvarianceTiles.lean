import TranslationTiling.Compiler.EffectiveGraphTiles

set_option maxRecDepth 1000
set_option maxHeartbeats 100000

namespace TranslationTiling.Compiler.Effective

open scoped Classical

theorem q0_decode_iff {T : LeanWang.TileSet} (E : EncodingParameters T)
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

theorem invarianceCodes_correct {T : LeanWang.TileSet} (E : EncodingParameters T)
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

end TranslationTiling.Compiler.Effective
