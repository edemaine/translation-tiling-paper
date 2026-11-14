import TranslationTiling.Compiler.SparseGeometryBound
import TranslationTiling.FiniteCompiler.Effective.ConcreteGeometryBound

namespace TranslationTiling.Compiler.Size
open scoped Classical
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

theorem integerTile_cubeCount_sparse (d : CyclicTileData) (H : ℕ) (hm : 0 < d.1)
    (hxy : ∀ f ∈ d.2, f.1.1.natAbs ≤ H ∧ f.1.2.natAbs ≤ H) :
    cubeCount (integerTile d) ≤ 2 ^ 24 * ((2*H+1)^2*d.1) := by
  letI : NeZero d.1 := ⟨hm.ne'⟩
  have hcoord : ∀ f ∈ cyclicTileSet d.1 d.2,
      f.1.1.natAbs ≤ H ∧ f.1.2.natAbs ≤ H := by
    intro f hf
    obtain ⟨g,hg,rfl⟩ := Finset.mem_image.mp hf
    exact hxy g (List.mem_toFinset.mp hg)
  unfold cubeCount
  rw [integerTile_toFinset,latticeRepresentatives_toFinset d.1 hm d.2]
  apply (assembled_card_le _ _).trans
  have hc : (CyclicQuotient.representatives d.1
      ((cyclicTileSet d.1 d.2).image (fun f => f - cyclicPoint d.1 (d.2.headD ((0,0),0))))).card ≤
      (2*H+1)^2*d.1 := by
    exact Finset.card_image_le.trans (Finset.card_image_le.trans (cyclic_card_le_box _ hcoord))
  calc
    _ ≤ ((2*H+1)^2*d.1) * 2^24 := Nat.mul_le_mul_right _ hc
    _ = _ := by ring

theorem integerTile_connected_sparseGeometryCap (d : CyclicTileData) (H M : ℕ)
    (hm : 0 < d.1) (hmM : d.1 ≤ M) (hne : d.2 ≠ [])
    (hxy : ∀ f ∈ d.2, f.1.1.natAbs ≤ H ∧ f.1.2.natAbs ≤ H) :
    cubeCount (connectedTile (integerTile d)) ≤ sparseGeometryCap H M := by
  apply connectedTile_sparseGeometryCap
  · exact (integerTile_cubeCount_sparse d H hm hxy).trans
      (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hmM))
  · exact integerTile_coordinateBound d H M hm hmM hne hxy

theorem sparseGeometryCap_mono {H H' M M' : ℕ} (hH : H ≤ H') (hM : M ≤ M') :
    sparseGeometryCap H M ≤ sparseGeometryCap H' M' := by
  unfold sparseGeometryCap latticeSide latticeRadius
  gcongr

end
end TranslationTiling.Compiler.Size
