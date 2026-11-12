import TranslationTiling.Compiler.Main
import TranslationTiling.Compiler.ClosedGeometryBound

namespace TranslationTiling.Compiler.Size
open scoped Classical
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 500000

/-- The concrete numerical lattice compiler obeys the geometric bound. -/
theorem integerTile_coordinateBound (d : CyclicTileData) (H M : ℕ)
    (hm : 0 < d.1) (hmM : d.1 ≤ M) (hne : d.2 ≠ [])
    (hxy : ∀ f ∈ d.2, f.1.1.natAbs ≤ H ∧ f.1.2.natAbs ≤ H) :
    coordinateBound (integerTile d) ≤ latticeRadius H M := by
  let m := d.1
  letI : NeZero m := ⟨hm.ne'⟩
  let F := cyclicTileSet m d.2
  have hhead : d.2.headD ((0,0),0) ∈ d.2 := by
    cases he : d.2 with
    | nil => exact False.elim (hne he)
    | cons f fs => simp
  let f₀ := cyclicPoint m (d.2.headD ((0,0),0))
  have hf₀ : f₀ ∈ F := Finset.mem_image.mpr ⟨_,List.mem_toFinset.mpr hhead,rfl⟩
  have hcoord : ∀ f ∈ F, f.1.1.natAbs ≤ H ∧ f.1.2.natAbs ≤ H := by
    intro f hf
    obtain ⟨g,hg,rfl⟩ := Finset.mem_image.mp hf
    exact hxy g (List.mem_toFinset.mp hg)
  let F₀ := F.image (fun f => f - f₀)
  let U := CyclicQuotient.representatives m F₀
  let G := LatticeGeometry.assembled m U
  have hU (u : Lattice 3) (hu : u ∈ U) (i : Fin 3) : (u i).natAbs ≤ 2 * H + M := by
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hf
    have hgcoord := hcoord g hg
    have h₀coord := hcoord f₀ hf₀
    fin_cases i
    · change (g.1.1 - f₀.1.1).natAbs ≤ _
      have h := (Int.natAbs_sub_le _ _).trans (Nat.add_le_add hgcoord.1 h₀coord.1)
      omega
    · change (g.1.2 - f₀.1.2).natAbs ≤ _
      have h := (Int.natAbs_sub_le _ _).trans (Nat.add_le_add hgcoord.2 h₀coord.2)
      omega
    · change (((g - f₀).2.val : ℤ)).natAbs ≤ _
      rw [Int.natAbs_natCast]
      have h := ZMod.val_lt (g - f₀).2
      omega
  have hG (v : Lattice 3) (hv : v ∈ G) (i : Fin 3) : (v i).natAbs ≤ latticeRadius H M := by
    obtain ⟨u, hu, w, hw, rfl⟩ := (LatticeGeometry.mem_assembled m U v).mp hv
    have hwbound : (w i).natAbs ≤ 201 * m + 1000 := by
      by_cases hu0 : u = 0
      · exact mss_component_coordinate_bound m 5 (by decide) (by simpa [LatticeGeometry.part, hu0] using hw) i
      · exact mss_component_coordinate_bound m 4 (by decide) (by simpa [LatticeGeometry.part, hu0] using hw) i
    have hubound := hU u hu i
    have hscale : ((LatticeGeometry.scaleHom u) i).natAbs ≤ 201 * (2 * H + M) := by
      change ((201 : ℤ) * u i).natAbs ≤ _
      rw [Int.natAbs_mul]
      exact Nat.mul_le_mul_left 201 hubound
    have h := (Int.natAbs_add_le _ _).trans (Nat.add_le_add hscale hwbound)
    unfold latticeRadius
    change (((LatticeGeometry.scaleHom u) i) + w i).natAbs ≤ _
    omega
  apply coordinateBound_le_of_forall
  intro v hv i
  apply hG v _ i
  have he := integerTile_toFinset d
  rw [latticeRepresentatives_toFinset d.1 hm d.2] at he
  change v ∈ LatticeGeometry.assembled d.1 (CyclicQuotient.representatives d.1
    ((cyclicTileSet d.1 d.2).image (fun f => f - cyclicPoint d.1 (d.2.headD ((0,0),0)))))
  rw [← he]
  exact List.mem_toFinset.mpr hv

end
end TranslationTiling.Compiler.Size
