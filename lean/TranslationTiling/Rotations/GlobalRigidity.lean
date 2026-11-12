import TranslationTiling.Rotations.LocalForcing
import TranslationTiling.Rotations.FundamentalDomain

namespace TranslationTiling.Rotations.SixKeys

theorem normalized_rigidity {ι : Type*} (M : ι → Motion)
    (cover : ExactCover (fun j => Footprint (M j)))
    (host : ι) (hhost : ∀ x, (M host).apply x = x) :
    ∀ j, ∃ z : Point, ∀ x, (M j).apply x = grid z + x := by
  let Present (z : Point) := ∃ j, ∀ x, (M j).apply x = grid z + x
  have first : Present 0 := ⟨host, by simpa [grid] using hhost⟩
  have force (z : Point) (hz : Present z) (f : Face) : Present (z - normal f) := by
    obtain ⟨a, ha⟩ := hz
    let t : Motion := ⟨Orientation.ident, grid z⟩
    let N := fun j => t.inverse.comp (M j)
    have hc := normalize_cover M cover t
    have hN : (N a).apply = id := by
      funext x
      simp only [N, Motion.comp_apply, id_eq]
      rw [ha]
      have ht : t.apply x = grid z + x := by simp [t, Motion.apply]
      rw [← ht]
      exact t.inverse_apply_apply x
    have hs : Footprint (N a) = {x | x ∈ gadget} := by
      simp only [Footprint, hN, Set.image_id]
    obtain ⟨j, hj⟩ := chamber_forces_neighbor N hc a hs f
    refine ⟨j, ?_⟩
    intro x
    have hh := hj x
    simp only [N, Motion.comp_apply] at hh
    have he := congrArg t.apply hh
    simp only [Motion.apply_inverse_apply] at he
    simpa [t, Motion.apply, grid, shift, smul_sub, sub_eq_add_neg, add_assoc] using he
  have step {z w : Point} (hz : Present z) (hzw : FaceAdjacent z w) : Present w := by
    obtain ⟨k, he | he⟩ := hzw
    · let f : Face := ⟨2*k.val+1, by omega⟩
      have hf : normal f = -Pi.single k 1 := by
        ext i
        fin_cases k <;> fin_cases i <;> simp [f, normal, axis, negative, Pi.single_apply]
      have hh := force z hz f
      simpa [hf, he] using hh
    · let f : Face := ⟨2*k.val, by omega⟩
      have hf : normal f = Pi.single k 1 := by
        ext i
        fin_cases k <;> fin_cases i <;> simp [f, normal, axis, negative, Pi.single_apply]
      have hw : z - normal f = w := by rw [hf, he]; abel
      simpa [hw] using force z hz f
  have present (z : Point) : Present z := by
    have p := FacePath.box3 (fun _ => True) (fun i => min 0 (z i)) (fun i => max 0 (z i))
      (0 : Point) z
      (by intro i; exact ⟨min_le_left _ _, le_max_left _ _⟩)
      (by intro i; exact ⟨min_le_right _ _, le_max_right _ _⟩)
      (by intro _ _; trivial)
    induction p with
    | refl => exact first
    | @tail a b _ hab ih => exact step ih hab.2.2
  intro j
  obtain ⟨⟨a, t⟩, he⟩ := fundamental_domain.2 ((M j).apply 0)
  obtain ⟨z, hz⟩ := a.property
  obtain ⟨k, hk⟩ := present z
  have hj : (M j).apply 0 ∈ Footprint (M j) :=
    ⟨0, body_subset_gadget zero_body, rfl⟩
  have hkj : (M j).apply 0 ∈ Footprint (M k) := by
    refine ⟨t.val, t.property, ?_⟩
    rw [hk, hz]
    exact he
  have hjk := cover.same hj hkj
  exact ⟨z, by simpa only [hjk] using hk⟩

/-- Every tiling by the six-key gadget has a common grid and a common complete
orientation. No periodicity is assumed, and reflections are allowed as well. -/
theorem rigidity {ι : Type*} (M : ι → Motion)
    (cover : ExactCover (fun j => Footprint (M j))) :
    ∃ r : Motion, ∀ j, ∃ z : Point, ∀ x, (M j).apply x = r.apply (grid z + x) := by
  obtain ⟨a, _, _⟩ := cover 0
  let r := M a
  let N := fun j => r.inverse.comp (M j)
  have hcover := normalize_cover M cover r
  have hhost : ∀ x, (N a).apply x = x := by
    intro x
    simpa only [N, Motion.comp_apply] using r.inverse_apply_apply x
  have hrigid := normalized_rigidity N hcover a hhost
  refine ⟨r, ?_⟩
  intro j
  obtain ⟨z, hz⟩ := hrigid j
  refine ⟨z, ?_⟩
  intro x
  have he := congrArg r.apply (hz x)
  simpa only [N, Motion.comp_apply, Motion.apply_inverse_apply] using he

end TranslationTiling.Rotations.SixKeys
