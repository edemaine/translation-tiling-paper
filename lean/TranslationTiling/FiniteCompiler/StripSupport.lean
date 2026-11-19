import TranslationTiling.FiniteCompiler.StripLift
import TranslationTiling.FiniteCompiler.GuardedGeometry
import TranslationTiling.FiniteCompiler.Effective.SparseCompiler

namespace TranslationTiling.FiniteCompiler
open Compiler Compiler.Effective Compiler.StripLift
open scoped Classical
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 1500000

variable [SeedFrame] {T : System} [AlphabetFamily T] (E : EncodingParameters T)

theorem test_strip {H : ℕ} (hsupport : CompactSupport.Bound E H)
    (hlo : ∀ n, 0≤T.slope n) (hhi : ∀ n, (T.slope n).natAbs≤16)
    {F : Finset (Ambient E)} (hF : F∈testTiles E) {g : Ambient E} (hg : g∈F) :
    TestSupport H g.1 := by
  refine ⟨(CompactSupport.test_horizontal E hsupport hhi hF hg).1,?_⟩
  have hR : residueModulus≤175 := by rw [residueModulus_value]; split <;> decide
  have hz (h : q0 E g=0) : g.1=0 := congrArg Prod.fst h
  have ho {t : ℕ} [NeZero t] (c : ZMod t ↪ Channel T) (labels : ∀ j, Label T (c j))
      (hF : F∈fixedCycleTiles E c labels) : g.1=0 := by
    obtain rfl := Finset.mem_singleton.mp hF
    exact congrArg Prod.fst ((mem_offsetTile E _ _).mp hg)
  rcases (mem_testTiles_iff E F).mp hF with rfl | hF | hF | hF | ⟨n,rfl⟩ | ⟨t,rfl⟩
  · rw [hz ((mem_kernelTile E g).mp hg)]
    exact Or.inl (by decide)
  · obtain ⟨d,_,rfl⟩ := Finset.mem_image.mp hF
    rcases (mem_invarianceTile E _ _ g).mp hg with ⟨h,_⟩ | ⟨h,_⟩
    · rw [hz h]; exact Or.inl (by decide)
    · have hh := congrArg Prod.fst h
      change g.1=(dependenceShift E d).1 at hh
      rw [hh]
      left
      rcases d with d | (n | ⟨t,axis⟩)
      · simp [dependenceShift,lowGenerator]
      · change (-T.slope n).natAbs≤175
        rw [Int.natAbs_neg]
        exact (hhi n).trans (by decide)
      · cases axis <;> simp [dependenceShift,seedStep,hR]
  · obtain ⟨w,_,hF⟩ := Finset.mem_biUnion.mp hF
    rw [ho _ _ hF]; exact Or.inl (by decide)
  · obtain ⟨q,_,hF⟩ := Finset.mem_biUnion.mp hF
    rw [ho _ _ hF]; exact Or.inl (by decide)
  · obtain ⟨j,_,hj⟩ := Finset.mem_biUnion.mp hg
    rw [((mem_activationBatch E _ _ _ _ g).mp hj).1]
    refine Or.inr ⟨_,hhi n,?_⟩
    have he : ((T.slope n).natAbs:ℤ)=T.slope n := by have := hlo n; omega
    rw [he]
    rfl
  · obtain ⟨j,_,hj⟩ := Finset.mem_biUnion.mp hg
    rw [((mem_activationBatch E _ _ _ _ g).mp hj).1]
    exact Or.inl ((CompactSupport.seed_bound E t j).2.trans hR)

omit E in
theorem stack_strip (N : ℕ) (c : PartitionCertificate) (Fs : List CyclicTile) (H : ℕ)
    (hs : ∀ F∈Fs, ∀ f∈F, TestSupport H f.1) :
    ∀ f∈stackCodes (N,c,Fs), TestSupport H f.1 := by
  intro f hf
  simp only [stackCodes,List.mem_flatMap,List.mem_map,List.mem_filter,List.mem_range] at hf
  obtain ⟨i,hi,g,hg,j,_,rfl⟩ := hf
  exact hs (Fs.getD i []) (by rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi) g hg

end
end TranslationTiling.FiniteCompiler
