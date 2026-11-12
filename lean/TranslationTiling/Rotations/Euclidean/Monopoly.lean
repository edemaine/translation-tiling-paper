import TranslationTiling.Rotations.Euclidean.Barriers

namespace TranslationTiling.Rotations.Euclidean

noncomputable section
open Set MeasureTheory

/-- Closing the entrance with the interior of one tile monopolizes a bounded
chamber. The escape hypothesis can be witnessed by two distant voxel centers. -/
theorem chamber_monopoly {ι : Type*} {F : Finset (Lattice 3)}
    (hF : F.Nonempty) (hconn : Connected (F : Set (Lattice 3)))
    (M : ι → RigidMotion) (cover : AECover (fun j => Placed F (M j)))
    (host blocker : ι) (U : Set EPoint) (hU : IsOpen U)
    (hhost : Disjoint U (Placed F (M host)))
    (boundary : frontier U ⊆ Placed F (M host) ∪ interior (Placed F (M blocker)))
    (escape : ∀ j, ¬ (∀ p ∈ F, (M j).apply (castPoint p) ∈ U)) :
    U ⊆ Placed F (M blocker) := by
  have others (j : ι) (hneH : j ≠ host) (hneB : j ≠ blocker)
      (p : Lattice 3) (hp : p ∈ F) (x : EPoint)
      (hx : x ∈ (M j).apply '' openVoxel p) (hxU : x ∈ U) : False := by
    have hd : Disjoint (frontier U) (interior (Placed F (M j))) := by
      apply Set.disjoint_left.mpr
      intro y hy hyj
      rcases boundary hy with hyH | hyB
      · exact Set.disjoint_left.mp (cover.interior_solid_disjoint hneH) hyj hyH
      · exact Set.disjoint_left.mp (cover.interior_disjoint hneB) hyj hyB
    obtain ⟨z,hz,rfl⟩ := hx
    apply escape j
    intro q hq
    have path := (openVoxel_joined_center hp hz).trans (facePath_joined hp (hconn p hp q hq))
    have mapped := path.map (M j).homeomorph.continuous.continuousOn
    have mapped' : JoinedIn (interior (Placed F (M j)))
        ((M j).apply z) ((M j).apply (castPoint q)) := by
      change JoinedIn (interior ((M j).homeomorph '' solid F))
        ((M j).homeomorph z) ((M j).homeomorph (castPoint q))
      rw [← (M j).homeomorph.image_interior]
      exact mapped
    exact joined_barrier hU hd mapped' hxU
  have hae : ∀ᵐ x ∂volume, x ∈ U → x ∈ Placed F (M blocker) := by
    filter_upwards [cover.ae_open_voxel hF M] with x hx hxU
    obtain ⟨j,p,hp,hxp⟩ := hx
    by_cases hj : j = blocker
    · subst j
      obtain ⟨y,hy,rfl⟩ := hxp
      exact ⟨y,⟨p,hp,openVoxel_subset_voxel p hy⟩,rfl⟩
    by_cases hh : j = host
    · subst j
      obtain ⟨y,hy,rfl⟩ := hxp
      exact (Set.disjoint_left.mp hhost hxU
        ⟨y,⟨p,hp,openVoxel_subset_voxel p hy⟩,rfl⟩).elim
    exact (others j hh hj p hp x hxp hxU).elim
  have hopen : IsOpen (U \ Placed F (M blocker)) := hU.sdiff (isClosed_placed F (M blocker))
  have hnull : volume (U \ Placed F (M blocker)) = 0 := by
    apply measure_mono_null ?_ (ae_iff.mp hae)
    intro x hx
    exact fun h => hx.2 (h hx.1)
  have he := hopen.eq_empty_of_measure_zero hnull
  intro x hx
  by_contra hn
  have : x ∈ U \ Placed F (M blocker) := ⟨hx,hn⟩
  simpa [he] using this

end
end TranslationTiling.Rotations.Euclidean
