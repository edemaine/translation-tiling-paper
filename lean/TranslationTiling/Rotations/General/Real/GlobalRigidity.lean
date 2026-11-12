import TranslationTiling.Rotations.General.Real.LocalForcing
import TranslationTiling.Rotations.General.FundamentalDomain

namespace TranslationTiling.Rotations.General.Real
variable {d : ℕ} [NeZero d]

noncomputable section
open Set MeasureTheory

def gridTranslation (z : (Lattice d)) : (Motion d) := ⟨Orientation.ident,grid z⟩

@[simp] theorem embed_translation_apply (t : (Lattice d)) (x : (EPoint d)) :
    (embedMotion (⟨Orientation.ident,t⟩ : (Motion d))).apply x=castPoint t+x := by
  ext i
  simp [embedMotion,RigidMotion.apply,Orientation.ident,Orientation.sign]

theorem normalized_rigidity (hd : 3 ≤ d) {ι : Type*} (M : ι → (RigidMotion d))
    (cover : AECover (fun j => Placed gadget (M j)))
    (host : ι) (hhost : M host=RigidMotion.ident) :
    ∀ j, ∃ z : (Lattice d), M j=embedMotion (gridTranslation z) := by
  let Present (z : (Lattice d)) := ∃ j, M j=embedMotion (gridTranslation z)
  have first : Present 0 := by
    refine ⟨host,hhost.trans ?_⟩
    apply RigidMotion.ext_apply
    intro x
    simp [gridTranslation,grid]
  have force (z : (Lattice d)) (hz : Present z) (f : (Face d)) : Present (z-normal f) := by
    obtain ⟨a,ha⟩ := hz
    let t := embedMotion (gridTranslation z)
    let N := fun j => t.inverse.comp (M j)
    have hc := RigidMotion.normalize_cover M cover t
    have hn : N a=RigidMotion.ident := by
      apply RigidMotion.ext_apply
      intro x
      simp [N,ha,t]
    obtain ⟨j,hj⟩ := euclidean_chamber_forces_neighbor hd N hc a hn f
    refine ⟨j,?_⟩
    apply RigidMotion.ext_apply
    intro x
    have hh := congrArg (fun m : (RigidMotion d) => t.apply (m.apply x)) hj
    simp only [N,RigidMotion.comp_apply,RigidMotion.apply_inverse] at hh
    rw [hh]
    simp only [t,gridTranslation,embed_translation_apply]
    have he : castPoint (grid z)+castPoint (-shift f)=castPoint (grid (z-normal f)) := by
      rw [← castPoint_add]
      congr 1
      simp [grid,shift,scale,smul_sub,sub_eq_add_neg]
    rw [← add_assoc,he]
  have step {z w : (Lattice d)} (hz : Present z) (hzw : FaceAdjacent z w) : Present w := by
    obtain ⟨k,he | he⟩ := hzw
    · let f : (Face d) := ⟨2*k.val+1,by omega⟩
      have hax : faceAxis f=k := by apply Fin.ext; dsimp [faceAxis,f]; omega
      have hneg : negative f=false := by simp [negative,f]
      have hf : normal f= -Pi.single k 1 := by
        ext i
        by_cases hi : i=k
        · subst i; simp [normal,hax,hneg]
        · simp [normal,hax,hneg,Pi.single_eq_of_ne hi]
      simpa [hf,he] using force z hz f
    · let f : (Face d) := ⟨2*k.val,by omega⟩
      have hax : faceAxis f=k := by apply Fin.ext; dsimp [faceAxis,f]; omega
      have hneg : negative f=true := by simp [negative,f]
      have hf : normal f=Pi.single k 1 := by simp [normal,hax,hneg]
      have hw : z-normal f=w := by rw [hf,he]; abel
      simpa [hw] using force z hz f
  have present (z : (Lattice d)) : Present z := by
    have p0 := box_path (fun i => min 0 (z i)) (fun i => max 0 (z i)) (0 : Lattice d) z
      (by intro i; exact ⟨min_le_left _ _,le_max_left _ _⟩)
      (by intro i; exact ⟨min_le_right _ _,le_max_right _ _⟩)
    have path : FacePath (fun _ => True) (0 : Lattice d) z := p0.mono (fun _ _ => trivial)
    clear p0
    induction path with
    | refl => exact first
    | tail _ hab ih => exact step ih hab.2.2
  have covered (x : (EPoint d)) : ∃ z j, M j=embedMotion (gridTranslation z) ∧ x ∈ Placed gadget (M j) := by
    let p := starLo x
    have hxp : x ∈ voxel p := by
      apply (mem_star x p).mp
      apply (mem_block _ _ _).mpr
      intro k
      exact ⟨le_refl _,star_bounds x k⟩
    obtain ⟨⟨a,u⟩,he⟩ := fundamental_domain.2 p
    obtain ⟨z,hz⟩ := a.property
    change grid z=a.val at hz
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
    exact mem_image_of_mem _ (openVoxel_subset_interior (body_subset_gadget (zero_body (by omega : 2 ≤ d))) (castPoint_openVoxel 0))
  have hjk : j=k := by
    by_contra hn
    exact Set.disjoint_left.mp (cover.interior_solid_disjoint hn) hxj hxk
  exact ⟨z,hjk ▸ hk⟩

/-- Every arbitrary Euclidean tiling of the dimension-generic key gadget has a single
Euclidean frame; relative orientations are identical and origins lie on the period lattice. -/
theorem rigidity (hd : 3 ≤ d) {ι : Type*} (M : ι → (RigidMotion d))
    (cover : AECover (fun j => Placed gadget (M j))) :
    ∃ r : (RigidMotion d), ∀ j, ∃ z : (Lattice d), M j=r.comp (embedMotion (gridTranslation z)) := by
  obtain ⟨_,a,_,_⟩ := cover.exists
  let r := M a
  let N := fun j => r.inverse.comp (M j)
  have hc := RigidMotion.normalize_cover M cover r
  have hn : N a=RigidMotion.ident := by
    apply RigidMotion.ext_apply
    intro x
    simp [N,r]
  have rigid := normalized_rigidity hd N hc a hn
  refine ⟨r,?_⟩
  intro j
  obtain ⟨z,hz⟩ := rigid j
  refine ⟨z,?_⟩
  apply RigidMotion.ext_apply
  intro x
  have hh := congrArg (fun m : (RigidMotion d) => r.apply (m.apply x)) hz
  simpa only [N,RigidMotion.comp_apply,RigidMotion.apply_inverse] using hh

end
end TranslationTiling.Rotations.General.Real
