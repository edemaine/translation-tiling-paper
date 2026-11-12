import TranslationTiling.Rotations.General.KeyedGadget

namespace TranslationTiling.Rotations.General
variable {d : ℕ} [NeZero d]

def chamber (f : Face d) : Set (Lattice d) := placedKey frameMotion f

theorem frame_zero (f : Face d) : (frameMotion f).apply 0 = gate f := by
  simp [frameMotion,Motion.apply]

theorem recess_chamber (f : Face d) : (recess f : Set (Lattice d)) = chamber f ∪ {gate f} := by
  simp only [recess,Finset.coe_image,fullKeyFinset_set,Set.image_union,Set.image_singleton,
    chamber,placedKey,frame_zero]

theorem gate_mem_recess (f : Face d) : gate f ∈ recess f := by
  rw [← Finset.mem_coe,recess_chamber]
  exact Or.inr rfl

theorem gate_not_chamber (f : Face d) : gate f ∉ chamber f := by
  rintro ⟨u,hu,he⟩
  rw [← frame_zero f] at he
  have he' := (frameMotion f).injective he
  exact zero_not_key f (he' ▸ hu)

theorem chamber_subset_recess (f : Face d) {x : Lattice d} (hx : x ∈ chamber f) : x ∈ recess f := by
  rw [← Finset.mem_coe,recess_chamber]
  exact Or.inl hx

theorem chamber_connected (f : Face d) : Connected (chamber f) :=
  (frameMotion f).connected (key_connected f)

theorem chamber_finite (f : Face d) : (chamber f).Finite := (key_finite f).image _

theorem chamber_card (hd : 2 ≤ d) (f : Face d) :
    (chamber f).ncard = boxVolume d+neckLength d-1 := by
  rw [chamber,placedKey,Set.ncard_image_of_injective _ (frameMotion f).injective,key_card hd f]

theorem recess_free (f : Face d) {x : Lattice d} (hx : x ∈ recess f) : x ∉ gadget := by
  intro hg
  have hxc : InCube x := by
    have hh := recess_subset_cell f hx
    exact (mem_boxFinset _ _ _).mp hh
  rcases gadget_parts hg with hb | ⟨g,hg⟩
  · exact ((body_iff x).mp hb).2 f hx
  · exact protrusion_outside g hg hxc

theorem chamber_interior (f : Face d) {x : Lattice d} (hx : x ∈ chamber f) (j : Fin d) :
    1 ≤ x j ∧ x j ≤ (cubeSide d : ℤ)-2 := by
  obtain ⟨u,hu,rfl⟩ := hx
  have hup : u ∈ fullKeyFinset f := by
    rw [← Finset.mem_coe,fullKeyFinset_set]
    exact Or.inl hu
  have ub := fullKey_bounds f hup 0
  have up : 1 ≤ u 0 := by
    rcases hu with hc | hs
    · have hh := (hc 0).1
      simp only [keyLo,ite_true] at hh
      unfold neckLength at *
      omega
    · exact hs.1
  have hp := margin_pos (d := d)
  have hL := margin_five_lt_cubeSide (d := d)
  by_cases hj : j = faceAxis f
  · subst j
    rw [frame_normal_apply]
    cases h : negative f <;> simp only [h,Bool.false_eq_true,ite_true,ite_false]
    all_goals omega
  · rw [frame_tangent_apply f u j hj]
    have hb := fullKey_bounds f hup ((frameOrientation f).axes j)
    cases h : negative f <;> simp only [h,Bool.false_eq_true,ite_true,ite_false]
    all_goals omega

theorem recesses_separated {f g : Face d} (hfg : f ≠ g) {x y : Lattice d}
    (hx : x ∈ recess f) (hy : y ∈ recess g) : ¬ FaceAdjacent x y := by
  intro hxy
  have hbf := recess_bounds f hx
  have hbg := recess_bounds g hy
  have hp := margin_pos (d := d)
  have hL := margin_five_lt_cubeSide (d := d)
  have hcoord := abs_le.mp (adjacent_coordinate hxy (faceAxis f))
  by_cases ha : faceAxis f = faceAxis g
  · have hn : negative f ≠ negative g := fun he => hfg (face_ext ha he)
    have hfn := hbf.1
    have hgn := hbg.1
    rw [← ha] at hgn
    cases h1 : negative f <;> cases h2 : negative g
    all_goals simp [h1,h2] at hfn hgn hn
    all_goals omega
  · have hfn := hbf.1
    have hgt := hbg.2 (faceAxis f) ha
    cases h1 : negative f <;> simp only [h1,Bool.false_eq_true,ite_false,ite_true] at hfn
    all_goals omega

/-- Every face neighbor of a chamber voxel lies in the chamber, at its gate,
or in the body. In particular there is exactly one entrance. -/
theorem chamber_boundary (f : Face d) {x y : Lattice d} (hx : x ∈ chamber f)
    (hxy : FaceAdjacent x y) : y ∈ chamber f ∨ y = gate f ∨ y ∈ body := by
  classical
  by_cases hc : y ∈ chamber f
  · exact Or.inl hc
  by_cases hg : y = gate f
  · exact Or.inr (Or.inl hg)
  right; right
  apply (body_iff y).mpr
  constructor
  · intro j
    have hb := chamber_interior f hx j
    have hdiff := abs_le.mp (adjacent_coordinate hxy j)
    dsimp
    omega
  · intro g hy
    have hfg : f = g := by
      by_contra hn
      exact recesses_separated hn (chamber_subset_recess f hx) hy hxy
    subst g
    rw [← Finset.mem_coe,recess_chamber] at hy
    exact hy.elim hc hg

end TranslationTiling.Rotations.General
