import TranslationTiling.Rotations.General.LocalForcing

namespace TranslationTiling.Rotations.General
variable {d : ℕ} [NeZero d]

theorem normalized_rigidity (hd : 3 ≤ d) {ι : Type*} (M : ι → Motion d)
    (cover : ExactCover (fun j => Footprint (M j)))
    (host : ι) (hhost : ∀ x, (M host).apply x = x) :
    ∀ j, ∃ z : Lattice d, ∀ x, (M j).apply x = scale (cubeSide d) z + x := by
  let Present (z : Lattice d) := ∃ j, ∀ x, (M j).apply x = scale (cubeSide d) z + x
  have first : Present 0 := ⟨host, by simpa [scale] using hhost⟩
  have force (z : Lattice d) (hz : Present z) (f : Face d) : Present (z - normal f) := by
    obtain ⟨a, ha⟩ := hz
    let t : Motion d := ⟨Orientation.ident, scale (cubeSide d) z⟩
    let N := fun j => t.inverse.comp (M j)
    have hc := normalize_cover M cover t
    have hN : (N a).apply = id := by
      funext x
      simp only [N, Motion.comp_apply, id_eq]
      rw [ha]
      have ht : t.apply x = scale (cubeSide d) z + x := by simp [t, Motion.apply]
      rw [← ht]
      exact t.inverse_apply_apply x
    have hs : Footprint (N a) = (↑(gadget : Finset (Lattice d)) : Set (Lattice d)) := by
      simp only [Footprint, hN, Set.image_id]
    obtain ⟨j, hj⟩ := chamber_forces_neighbor hd N hc a hs f
    refine ⟨j, ?_⟩
    intro x
    have hh := hj x
    simp only [N, Motion.comp_apply] at hh
    have he := congrArg t.apply hh
    simp only [Motion.apply_inverse_apply] at he
    simpa [t, Motion.apply, scale, shift, smul_sub, sub_eq_add_neg, add_assoc] using he
  have step {z w : Lattice d} (hz : Present z) (hzw : FaceAdjacent z w) : Present w := by
    obtain ⟨k, he | he⟩ := hzw
    · let f : Face d := ⟨2*k.val+1, by omega⟩
      have hax : faceAxis f = k := by apply Fin.ext; dsimp [faceAxis,f]; omega
      have hneg : negative f = false := by simp [negative,f]
      have hf : normal f = -Pi.single k 1 := by
        ext j
        by_cases hj : j = k
        · subst j; simp [normal,hax,hneg]
        · simp [normal,hax,hneg,Pi.single_eq_of_ne hj]
      have hh := force z hz f
      simpa [hf, he] using hh
    · let f : Face d := ⟨2*k.val, by omega⟩
      have hax : faceAxis f = k := by apply Fin.ext; dsimp [faceAxis,f]; omega
      have hneg : negative f = true := by simp [negative,f]
      have hf : normal f = Pi.single k 1 := by simp [normal,hax,hneg]
      have hw : z - normal f = w := by rw [hf, he]; abel
      simpa [hw] using force z hz f
  have present (z : Lattice d) : Present z := by
    have p0 := box_path (fun i => min 0 (z i)) (fun i => max 0 (z i)) (0 : Lattice d) z
      (by intro i; exact ⟨min_le_left _ _,le_max_left _ _⟩)
      (by intro i; exact ⟨min_le_right _ _,le_max_right _ _⟩)
    have p : FacePath (fun _ => True) (0 : Lattice d) z := p0.mono (fun _ _ => trivial)
    clear p0
    induction p with
    | refl => exact first
    | @tail a b _ hab ih => exact step ih hab.2.2
  intro j
  obtain ⟨z,⟨t,ht,he⟩,_⟩ := gadget_exact ((M j).apply 0)
  obtain ⟨k,hk⟩ := present z
  have hj : (M j).apply 0 ∈ Footprint (M j) :=
    ⟨0, body_subset_gadget (zero_body (by omega : 2 ≤ d)), rfl⟩
  have hkj : (M j).apply 0 ∈ Footprint (M k) := by
    refine ⟨t,ht,?_⟩
    rw [hk]
    exact he
  have hjk := cover.same hj hkj
  exact ⟨z, by simpa only [hjk] using hk⟩

/-- Every grid tiling by the dimension-generic key gadget has a common lattice and a common complete
orientation. No periodicity is assumed, and reflections are allowed as well. -/
theorem rigidity (hd : 3 ≤ d) {ι : Type*} (M : ι → Motion d)
    (cover : ExactCover (fun j => Footprint (M j))) :
    ∃ r : Motion d, ∀ j, ∃ z : Lattice d, ∀ x, (M j).apply x = r.apply (scale (cubeSide d) z + x) := by
  obtain ⟨a, _, _⟩ := cover 0
  let r := M a
  let N := fun j => r.inverse.comp (M j)
  have hcover := normalize_cover M cover r
  have hhost : ∀ x, (N a).apply x = x := by
    intro x
    simpa only [N, Motion.comp_apply] using r.inverse_apply_apply x
  have hrigid := normalized_rigidity hd N hcover a hhost
  refine ⟨r, ?_⟩
  intro j
  obtain ⟨z, hz⟩ := hrigid j
  refine ⟨z, ?_⟩
  intro x
  have he := congrArg r.apply (hz x)
  simpa only [N, Motion.comp_apply, Motion.apply_inverse_apply] using he

end TranslationTiling.Rotations.General
