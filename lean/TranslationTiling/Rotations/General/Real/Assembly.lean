import TranslationTiling.Rotations.General.Real.Expansion

namespace TranslationTiling.Rotations.General.Real
variable {d : ℕ} [NeZero d]

noncomputable section
open Set General

def AllowedEuclideanTiles (allowed : Set (Rotation d)) (F : Finset (Lattice d)) : Prop :=
  ∃ C : Set (RigidMotion d), (∀ m ∈ C,m.rotation ∈ allowed) ∧
    AECover (fun m : C => Real.Placed F m.val)

@[simp] theorem gridRotation_ident : gridRotation Orientation.ident=LinearIsometryEquiv.refl ℝ (EPoint d) := by
  ext x i
  simp [Orientation.ident,Orientation.sign]

theorem assembly_forward_allowed (allowed : Set (Rotation d))
    (hid : LinearIsometryEquiv.refl ℝ (EPoint d) ∈ allowed)
    (E : Finset (Lattice d)) (hE : FiniteTiles E) : AllowedEuclideanTiles allowed (assembly E) := by
  obtain ⟨C,hC,cover⟩ := General.assembly_forward_allowed {Orientation.ident} (by simp) E hE
  let M : C → (RigidMotion d) := fun m => embedMotion m.val
  have hc := ae_cover_of_grid_cover (assembly E) (fun m : C => m.val) cover
  refine ⟨range M,?_,ae_cover_range M hc⟩
  rintro m ⟨a,rfl⟩
  have ha : a.val.orientation=Orientation.ident := by simpa using hC a.val a.property
  simpa only [M,embedMotion,ha,gridRotation_ident] using hid

theorem assembly_backward (hd : 3 ≤ d) {ι : Type*} (E : Finset (Lattice d)) (hE : E.Nonempty)
    (M : ι → (RigidMotion d)) (cover : AECover (fun j => Real.Placed (assembly E) (M j))) :
    FiniteTiles E := by
  have expanded := euclidean_expand_cover hd E hE M cover
  obtain ⟨r,rigid⟩ := rigidity hd (fun p : ι × ↥E => submotion (M p.1) p.2.val) expanded
  obtain ⟨e0,he0⟩ := hE
  choose z hz using fun j => rigid (j,⟨e0,he0⟩)
  let a : ι → (Lattice d) := fun j => z j-e0
  have parent (j : ι) (y : (EPoint d)) : (M j).apply y=r.apply (castPoint (grid (a j))+y) := by
    have hh := congrArg (fun m : (RigidMotion d) => m.apply (y-castPoint (grid e0))) (hz j)
    simp only [submotion_apply,RigidMotion.comp_apply,gridTranslation,embed_translation_apply] at hh
    have heL : castPoint (grid e0)+(y-castPoint (grid e0))=y := by abel
    have heR : castPoint (grid (z j))+(y-castPoint (grid e0))=castPoint (grid (a j))+y := by
      have he : grid (z j)=grid (a j)+grid e0 := by
        simp [a,grid,smul_sub]
      rw [he,castPoint_add]
      abel
    rwa [heL,heR] at hh
  let N := fun j => r.inverse.comp (M j)
  have hn (j : ι) : N j=embedMotion (gridTranslation (a j)) := by
    apply RigidMotion.ext_apply
    intro x
    simp only [N,RigidMotion.comp_apply,parent,RigidMotion.inverse_apply,gridTranslation,embed_translation_apply]
  have hc := RigidMotion.normalize_cover M cover r
  change AECover (fun j => Real.Placed (assembly E) (N j)) at hc
  simp only [hn] at hc
  exact General.assembly_backward hd E ⟨e0,he0⟩ (fun j => gridTranslation (a j))
    (grid_cover_of_ae_cover (assembly E) (fun j => gridTranslation (a j)) hc)

/-- The dimension-generic replacement works for arbitrary orthogonal motions. -/
theorem assembly_tiles_iff (hd : 3 ≤ d) (E : Finset (Lattice d)) (hE : E.Nonempty) :
    FiniteTiles E ↔ EuclideanTiles (assembly E) := by
  constructor
  · intro h
    obtain ⟨C,_,hc⟩ := assembly_forward_allowed Set.univ (Set.mem_univ _) E h
    exact ⟨C,hc⟩
  · rintro ⟨C,hc⟩
    exact assembly_backward hd E hE (fun m : C => m.val) hc

theorem assembly_allowed_iff (hd : 3 ≤ d) (E : Finset (Lattice d)) (hE : E.Nonempty)
    (allowed : Set (Rotation d)) (hid : LinearIsometryEquiv.refl ℝ (EPoint d) ∈ allowed) :
    FiniteTiles E ↔ AllowedEuclideanTiles allowed (assembly E) := by
  constructor
  · exact assembly_forward_allowed allowed hid E
  · rintro ⟨C,_,hc⟩
    exact assembly_backward hd E hE (fun m : C => m.val) hc

end
end TranslationTiling.Rotations.General.Real
