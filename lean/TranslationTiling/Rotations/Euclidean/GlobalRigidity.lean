import TranslationTiling.Rotations.Euclidean.LocalForcing
import TranslationTiling.Rotations.FundamentalDomain

namespace TranslationTiling.Rotations.Euclidean

noncomputable section
open Set SixKeys MeasureTheory

def gridTranslation (z : Point) : Motion := ⟨Orientation.ident,grid z⟩

@[simp] theorem embed_translation_apply (t : Point) (x : EPoint) :
    (embedMotion (⟨Orientation.ident,t⟩ : Motion)).apply x=castPoint t+x := by
  ext i
  simp [embedMotion,RigidMotion.apply,Orientation.ident,Orientation.sign]

theorem normalized_rigidity {ι : Type*} (M : ι → RigidMotion)
    (cover : AECover (fun j => Placed gadget (M j)))
    (host : ι) (hhost : M host=RigidMotion.ident) :
    ∀ j, ∃ z : Point, M j=embedMotion (gridTranslation z) := by
  let Present (z : Point) := ∃ j, M j=embedMotion (gridTranslation z)
  have first : Present 0 := by
    refine ⟨host,hhost.trans ?_⟩
    apply RigidMotion.ext_apply
    intro x
    simp [gridTranslation,grid]
  have force (z : Point) (hz : Present z) (f : Face) : Present (z-normal f) := by
    obtain ⟨a,ha⟩ := hz
    let t := embedMotion (gridTranslation z)
    let N := fun j => t.inverse.comp (M j)
    have hc := RigidMotion.normalize_cover M cover t
    have hn : N a=RigidMotion.ident := by
      apply RigidMotion.ext_apply
      intro x
      simp [N,ha,t]
    obtain ⟨j,hj⟩ := euclidean_chamber_forces_neighbor N hc a hn f
    refine ⟨j,?_⟩
    apply RigidMotion.ext_apply
    intro x
    have hh := congrArg (fun m : RigidMotion => t.apply (m.apply x)) hj
    simp only [N,RigidMotion.comp_apply,RigidMotion.apply_inverse] at hh
    rw [hh]
    simp only [t,gridTranslation,embed_translation_apply]
    have he : castPoint (grid z)+castPoint (-shift f)=castPoint (grid (z-normal f)) := by
      rw [← castPoint_add]
      congr 1
      simp [grid,shift,smul_sub,sub_eq_add_neg]
    rw [← add_assoc,he]
  have step {z w : Point} (hz : Present z) (hzw : FaceAdjacent z w) : Present w := by
    obtain ⟨k,he | he⟩ := hzw
    · let f : Face := ⟨2*k.val+1,by omega⟩
      have hf : normal f= -Pi.single k 1 := by
        ext i
        fin_cases k <;> fin_cases i <;> simp [f,normal,axis,negative,Pi.single_apply]
      simpa [hf,he] using force z hz f
    · let f : Face := ⟨2*k.val,by omega⟩
      have hf : normal f=Pi.single k 1 := by
        ext i
        fin_cases k <;> fin_cases i <;> simp [f,normal,axis,negative,Pi.single_apply]
      have hw : z-normal f=w := by rw [hf,he]; abel
      simpa [hw] using force z hz f
  have present (z : Point) : Present z := by
    have path := FacePath.box3 (fun _ => True) (fun i => min 0 (z i)) (fun i => max 0 (z i))
      (0 : Point) z
      (by intro i; exact ⟨min_le_left _ _,le_max_left _ _⟩)
      (by intro i; exact ⟨min_le_right _ _,le_max_right _ _⟩)
      (by intro _ _; trivial)
    induction path with
    | refl => exact first
    | tail _ hab ih => exact step ih hab.2.2
  have covered (x : EPoint) : ∃ z j, M j=embedMotion (gridTranslation z) ∧ x ∈ Placed gadget (M j) := by
    let p := starLo x
    have hxp : x ∈ voxel p := by
      apply (mem_star x p).mp
      apply (mem_block _ _ _).mpr
      intro k
      exact ⟨le_refl _,star_bounds x k⟩
    obtain ⟨⟨a,u⟩,he⟩ := fundamental_domain.2 p
    obtain ⟨z,hz⟩ := a.property
    obtain ⟨j,hj⟩ := present z
    refine ⟨z,j,hj,?_⟩
    have hcenter : (gridTranslation z).apply u.val=p := by
      simpa only [gridTranslation,Motion.apply,Orientation.ident_apply,hz] using he
    rw [← hcenter,← embedMotion_voxel] at hxp
    obtain ⟨y,hy,hey⟩ := hxp
    rw [hj]
    exact ⟨y,⟨u.val,u.property,hy⟩,hey⟩
  intro j
  obtain ⟨z,k,hk,hxk⟩ := covered ((M j).apply (castPoint 0))
  have hxj : (M j).apply (castPoint 0) ∈ interior (Placed gadget (M j)) := by
    change (M j).homeomorph (castPoint 0) ∈ interior ((M j).homeomorph '' solid gadget)
    rw [← (M j).homeomorph.image_interior]
    exact mem_image_of_mem _ (openVoxel_subset_interior (body_subset_gadget zero_body) (castPoint_openVoxel 0))
  have hjk : j=k := by
    by_contra hn
    exact Set.disjoint_left.mp (cover.interior_solid_disjoint hn) hxj hxk
  exact ⟨z,hjk ▸ hk⟩

/-- Every arbitrary Euclidean tiling of the six-key gadget has a single
Euclidean frame; relative orientations are identical and origins lie on 40ℤ³. -/
theorem rigidity {ι : Type*} (M : ι → RigidMotion)
    (cover : AECover (fun j => Placed gadget (M j))) :
    ∃ r : RigidMotion, ∀ j, ∃ z : Point, M j=r.comp (embedMotion (gridTranslation z)) := by
  obtain ⟨_,a,_,_⟩ := cover.exists
  let r := M a
  let N := fun j => r.inverse.comp (M j)
  have hc := RigidMotion.normalize_cover M cover r
  have hn : N a=RigidMotion.ident := by
    apply RigidMotion.ext_apply
    intro x
    simp [N,r]
  have rigid := normalized_rigidity N hc a hn
  refine ⟨r,?_⟩
  intro j
  obtain ⟨z,hz⟩ := rigid j
  refine ⟨z,?_⟩
  apply RigidMotion.ext_apply
  intro x
  have hh := congrArg (fun m : RigidMotion => r.apply (m.apply x)) hz
  simpa only [N,RigidMotion.comp_apply,RigidMotion.apply_inverse] using hh

end
end TranslationTiling.Rotations.Euclidean
