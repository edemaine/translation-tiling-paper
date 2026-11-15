import TranslationTiling.FourLayer.Compiler
import TranslationTiling.FiniteCompiler.Effective.SparseGeometry
import TranslationTiling.Compiler.ClosedGeometryBound

namespace TranslationTiling.Compiler.Size
open scoped Classical
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 500000

theorem mss_component_horizontal_bound (m j : ℕ) (hj : j≤5)
    {v : Lattice 3} (hv : v∈MSS.component m j) (i : Fin 3) (hi : i≠2) :
    (v i).natAbs≤1000 := by
  rcases Finset.mem_union.mp hv with hv | hv
  · exact (mss_base_coordinate_bound (Finset.mem_sdiff.mp hv).1 i).trans (by decide)
  · obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hv
    have h := (MSS.mem_box_iff j u).mp (Finset.mem_sdiff.mp hu).1 i
    have hjz : (j:ℤ)≤5 := by exact_mod_cast hj
    apply natAbs_le_of_bounds
    fin_cases i <;> simp_all [MSS.kernelStep,MSS.marker,Pi.add_apply] <;> omega

theorem integerTile_rectangle_bound (d : CyclicTileData) (H M : ℕ)
    (hm : 0<d.1) (hmM : d.1≤M) (hne : d.2≠[])
    (hxy : ∀ f∈d.2, f.1.1.natAbs≤H ∧ f.1.2.natAbs≤H) :
    ∀ v∈integerTile d, (v 0).natAbs≤FourLayer.radius H ∧
      (v 1).natAbs≤FourLayer.radius H ∧ (v 2).natAbs≤FourLayer.radius M := by
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
  have hU (u : Lattice 3) (hu : u ∈ U) (i : Fin 3) : (u i).natAbs ≤ (if i=2 then M else 2*H) := by
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hf
    have hgcoord := hcoord g hg
    have h₀coord := hcoord f₀ hf₀
    fin_cases i
    · simp only [show (0:Fin 3)≠2 by decide,ite_false]
      change (g.1.1 - f₀.1.1).natAbs ≤ 2*H
      have h := (Int.natAbs_sub_le _ _).trans (Nat.add_le_add hgcoord.1 h₀coord.1)
      omega
    · simp only [show (1:Fin 3)≠2 by decide,ite_false]
      change (g.1.2 - f₀.1.2).natAbs ≤ 2*H
      have h := (Int.natAbs_sub_le _ _).trans (Nat.add_le_add hgcoord.2 h₀coord.2)
      omega
    · simp only [ite_true]
      change (((g - f₀).2.val : ℤ)).natAbs ≤ M
      rw [Int.natAbs_natCast]
      have h := ZMod.val_lt (g - f₀).2
      omega
  have hG (v : Lattice 3) (hv : v∈G) (i : Fin 3) :
      (v i).natAbs≤FourLayer.radius (if i=2 then M else H) := by
    obtain ⟨u,hu,w,hw,rfl⟩ := (LatticeGeometry.mem_assembled m U v).mp hv
    have hwbound : (w i).natAbs≤(if i=2 then 201*m+1000 else 1000) := by
      by_cases hi : i=2
      · simp only [hi,ite_true]
        by_cases hu0 : u=0
        · exact mss_component_coordinate_bound m 5 (by decide) (by simpa [LatticeGeometry.part,hu0] using hw) 2
        · exact mss_component_coordinate_bound m 4 (by decide) (by simpa [LatticeGeometry.part,hu0] using hw) 2
      · simp only [hi,ite_false]
        by_cases hu0 : u=0
        · exact mss_component_horizontal_bound m 5 (by decide) (by simpa [LatticeGeometry.part,hu0] using hw) i hi
        · exact mss_component_horizontal_bound m 4 (by decide) (by simpa [LatticeGeometry.part,hu0] using hw) i hi
    have hscale : ((LatticeGeometry.scaleHom u) i).natAbs≤201*(if i=2 then M else 2*H) := by
      change ((201:ℤ)*u i).natAbs≤_
      rw [Int.natAbs_mul]
      exact Nat.mul_le_mul_left 201 (hU u hu i)
    have hh := (Int.natAbs_add_le ((LatticeGeometry.scaleHom u) i) (w i)).trans (Nat.add_le_add hscale hwbound)
    change (((LatticeGeometry.scaleHom u) i)+w i).natAbs≤_
    by_cases hi : i=2 <;> simp only [hi,ite_true,ite_false,FourLayer.radius] at * <;> omega
  intro v hv
  have hvG : v∈G := by
    have he := integerTile_toFinset d
    rw [latticeRepresentatives_toFinset d.1 hm d.2] at he
    change v∈LatticeGeometry.assembled d.1 (CyclicQuotient.representatives d.1
      ((cyclicTileSet d.1 d.2).image (fun f => f-cyclicPoint d.1 (d.2.headD ((0,0),0)))))
    rw [← he]
    exact List.mem_toFinset.mpr hv
  exact ⟨by simpa using hG v hvG 0,by simpa using hG v hvG 1,by simpa using hG v hvG 2⟩

end
end TranslationTiling.Compiler.Size
