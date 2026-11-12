import TranslationTiling.Rotations.General.Real.GlobalRigidity
import TranslationTiling.Rotations.General.Real.GridCorrespondence

namespace TranslationTiling.Rotations.General.Real
variable {d : ℕ} [NeZero d]

noncomputable section
open Set General MeasureTheory

def submotion (m : (RigidMotion d)) (e : (Lattice d)) : (RigidMotion d) :=
  m.comp (embedMotion (gridTranslation e))

@[simp] theorem submotion_apply (m : (RigidMotion d)) (e : (Lattice d)) (x : (EPoint d)) :
    (submotion m e).apply x=m.apply (castPoint (grid e)+x) := by
  simp [submotion,gridTranslation]

theorem solid_assembly_iff (E : Finset (Lattice d)) (x : (EPoint d)) :
    x ∈ solid (assembly E) ↔ ∃ e ∈ E, x ∈ Real.Placed gadget (embedMotion (gridTranslation e)) := by
  constructor
  · rintro ⟨p,hp,hxp⟩
    obtain ⟨e,he,u,hu,rfl⟩ := (mem_assembly E p).mp hp
    refine ⟨e,he,?_⟩
    have hcenter : (gridTranslation e).apply u=grid e+u := by simp [gridTranslation,Motion.apply]
    rw [← hcenter,← embedMotion_voxel] at hxp
    obtain ⟨y,hy,he⟩ := hxp
    exact ⟨y,⟨u,hu,hy⟩,he⟩
  · rintro ⟨e,he,y,⟨u,hu,hy⟩,rfl⟩
    refine ⟨grid e+u,(mem_assembly _ _).mpr ⟨e,he,u,hu,rfl⟩,?_⟩
    have hcenter : (gridTranslation e).apply u=grid e+u := by simp [gridTranslation,Motion.apply]
    rw [← hcenter,← embedMotion_voxel]
    exact ⟨y,hy,rfl⟩

theorem placed_assembly_iff (E : Finset (Lattice d)) (m : (RigidMotion d)) (x : (EPoint d)) :
    x ∈ Real.Placed (assembly E) m ↔ ∃ e ∈ E, x ∈ Real.Placed gadget (submotion m e) := by
  constructor
  · rintro ⟨y,hy,he⟩
    obtain ⟨e,heE,v,hv,hev⟩ := (solid_assembly_iff E y).mp hy
    exact ⟨e,heE,v,hv,by simpa only [submotion,RigidMotion.comp_apply,hev] using he⟩
  · rintro ⟨e,heE,v,hv,he⟩
    refine ⟨(embedMotion (gridTranslation e)).apply v,?_,?_⟩
    · exact (solid_assembly_iff E _).mpr ⟨e,heE,v,hv,rfl⟩
    · simpa only [submotion,RigidMotion.comp_apply] using he

theorem subcell_source (m : (RigidMotion d)) (e : (Lattice d)) {x : (EPoint d)}
    (hx : x ∈ Real.Placed gadget (submotion m e)) :
    ∃ u ∈ gadget, m.inverse.apply x ∈ voxel (grid e+u) := by
  obtain ⟨v,⟨u,hu,hv⟩,rfl⟩ := hx
  refine ⟨u,hu,?_⟩
  simp only [submotion,RigidMotion.comp_apply,RigidMotion.inverse_apply]
  have hcenter : (gridTranslation e).apply u=grid e+u := by simp [gridTranslation,Motion.apply]
  rw [← hcenter,← embedMotion_voxel]
  exact ⟨v,hv,rfl⟩

theorem euclidean_expand_cover (hd : 3 ≤ d) {ι : Type*} (E : Finset (Lattice d)) (hE : E.Nonempty)
    (M : ι → (RigidMotion d)) (cover : AECover (fun j => Real.Placed (assembly E) (M j))) :
    AECover (fun p : ι × ↥E => Real.Placed gadget (submotion (M p.1) p.2.val)) := by
  have hAssembly : (assembly E).Nonempty := by
    obtain ⟨e,he⟩ := hE
    exact ⟨grid e+0,(mem_assembly _ _).mpr ⟨e,he,0,body_subset_gadget (zero_body (by omega : 2 ≤ d)),rfl⟩⟩
  haveI := cover.countable hAssembly M
  have hb : ∀ᵐ x ∂volume, ∀ j, ∀ k : Fin d, ∀ z : ℤ,
      (M j).inverse.apply x k ≠ (z:ℝ)+(1:ℝ)/2 := by
    apply ae_all_iff.mpr
    intro j
    exact (M j).inverse.measurePreserving.quasiMeasurePreserving.ae ae_nonboundary
  filter_upwards [cover,hb] with x hx hxb
  obtain ⟨j,hxj,unique⟩ := hx
  obtain ⟨e,he,hxe⟩ := (placed_assembly_iff E (M j) x).mp hxj
  refine ⟨(j,⟨e,he⟩),hxe,?_⟩
  rintro ⟨k,f⟩ hxf
  have hkj : k=j := unique k ((placed_assembly_iff E (M k) x).mpr ⟨f.val,f.property,hxf⟩)
  subst k
  obtain ⟨u,hu,hxu⟩ := subcell_source (M j) e hxe
  obtain ⟨v,hv,hxv⟩ := subcell_source (M j) f.val hxf
  have hcenter := voxel_centers_unique (hxb j) hxu hxv
  have hef := (grid_unique hu hv hcenter).1
  exact Prod.ext rfl (Subtype.ext hef.symm)

end
end TranslationTiling.Rotations.General.Real
