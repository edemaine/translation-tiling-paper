import TranslationTiling.Rotations.Gadget
import TranslationTiling.Rotations.KeyRigidity

namespace TranslationTiling.Rotations.SixKeys

abbrev Footprint (m : Motion) : Set Point := m.apply '' {x | x ∈ gadget}

/-- The one-entrance argument forces the exactly positioned neighbor, rather
than merely a key with the correct outward normal. -/
theorem chamber_forces_neighbor {ι : Type*} (M : ι → Motion)
    (cover : ExactCover (fun j => Footprint (M j)))
    (host : ι) (hhost : Footprint (M host) = {x | x ∈ gadget}) (i : Face) :
    ∃ j, ∀ x, (M j).apply x = -shift i + x := by
  have escape (j : ι) : ∃ y ∈ Footprint (M j), y ∉ ({x | x ∈ chamber i} : Set Point) := by
    apply escape_of_card (chamber i).finite_toSet
    rw [Set.InjOn.ncard_image (M j).injective.injOn]
    simpa only [Set.ncard_coe_finset, chamber_card] using gadget_large
  obtain ⟨j, _, _, hc⟩ := chamber_component cover
    (fun j => (M j).connected gadget_connected) host {x | x ∈ chamber i} (gate i)
    ⟨chamberVoxel i 0, chamberVoxel_mem i 0⟩ (chamber_connected i)
    (by simp [chamber])
    (by intro x hx; rw [hhost]; exact recess_free i (Finset.mem_of_mem_erase hx))
    (by rw [hhost]; exact recess_free i (gate_mem_recess i))
    (by
      intro x hx y hxy
      rcases chamber_boundary i hx hxy with hy | hy | hy
      · exact Or.inl hy
      · exact Or.inr (Or.inl hy)
      · exact Or.inr (Or.inr (by rw [hhost]; exact body_subset_gadget hy))) escape
  have hc' := (M j).pullback_component hc
  have hkFinite : ((M j).apply ⁻¹' {x | x ∈ chamber i}).Finite := by
    rw [(M j).preimage_eq]
    exact (chamber i).finite_toSet.image _
  have hkCard : ((M j).apply ⁻¹' {x | x ∈ chamber i}).ncard = 364 := by
    rw [(M j).preimage_eq, Set.InjOn.ncard_image (M j).inverse.injective.injOn]
    simp only [Finset.setOfPred_mem, Set.ncard_coe_finset, chamber_card]
  obtain ⟨k, _, hcore⟩ := recognize_component hc' hkFinite hkCard
  have hset : (M j).apply '' {x | x ∈ (chamber k).image (shift k + ·)} =
      {x | x ∈ chamber i} := by
    rw [← hcore]
    exact Set.image_preimage_eq _ (M j).equiv.surjective
  have hfin : ((chamber k).image (shift k + ·)).image (M j).apply = chamber i := by
    apply Finset.coe_injective
    simpa only [Finset.setOfPred_mem, Finset.coe_image] using hset
  let m : Motion := ⟨(M j).orientation, (M j).offset + (M j).orientation.linear (shift k)⟩
  have hm : m.apply = (M j).apply ∘ (shift k + ·) := by
    funext x
    simp [m, Motion.apply, map_add, add_assoc]
  rw [Finset.image_image, ← hm] at hfin
  obtain ⟨hki, hr, ht⟩ := chamber_rigid k i m hfin
  subst k
  have hr' : (M j).orientation = Orientation.ident := hr
  have ht' : (M j).offset + shift i = 0 := by
    change (M j).offset + (M j).orientation.linear (shift i) = 0 at ht
    simpa [hr'] using ht
  have hoff : (M j).offset = -shift i := eq_neg_of_add_eq_zero_left ht'
  exact ⟨j, fun x => by simp [Motion.apply, hr', hoff]⟩

/-- Undoing any one placement preserves exact coverage by grid isometries. -/
theorem normalize_cover {ι : Type*} (M : ι → Motion)
    (cover : ExactCover (fun j => Footprint (M j))) (r : Motion) :
    ExactCover (fun j => Footprint (r.inverse.comp (M j))) := by
  intro x
  obtain ⟨j, ⟨u, hu, he⟩, unique⟩ := cover (r.apply x)
  refine ⟨j, ⟨u, hu, ?_⟩, ?_⟩
  · simp [Motion.comp_apply, he]
  · rintro k ⟨v, hv, he⟩
    apply unique k
    refine ⟨v, hv, ?_⟩
    have hh := congrArg r.apply he
    simpa only [Motion.comp_apply, Motion.apply_inverse_apply] using hh

end TranslationTiling.Rotations.SixKeys
