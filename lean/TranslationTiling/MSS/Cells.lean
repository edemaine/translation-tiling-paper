import TranslationTiling.MSS.ComponentIsolation

/-! The marked cells in the fundamental cube are pairwise separated. -/

namespace TranslationTiling.MSS

noncomputable section
open scoped Classical
attribute [local irreducible] box

def cell (j : ℕ) : Finset (Lattice 3) := (frame j).image (marker j + ·)

theorem mem_cell_iff (j : ℕ) (v : Lattice 3) : v ∈ cell j ↔ v - marker j ∈ frame j := by
  constructor
  · rintro hv
    obtain ⟨u, hu, he⟩ := Finset.mem_image.mp hv
    rw [← he]
    simpa only [add_sub_cancel_left] using hu
  · intro hv
    exact Finset.mem_image.mpr ⟨v - marker j, hv, add_sub_cancel _ _⟩

theorem cell_subset_box (j : ℕ) (hj : 0 < j) (hj5 : j ≤ 5) {v : Lattice 3}
    (hv : v ∈ cell j) : v ∈ box 100 := by
  obtain ⟨u, hu, he⟩ := Finset.mem_image.mp hv
  rw [← he]
  exact marker_frame_in_box j hj hj5 hu

theorem cells_same_radius (j k : ℕ) (hj : 0 < j) (hk : 0 < k)
    (hj5 : j ≤ 5) (hk5 : k ≤ 5) {v : Lattice 3}
    (hvj : v ∈ cell j) (hvk : v ∈ cell k) : j = k := by
  have hjb := ((mem_frame_iff j hj _).mp ((mem_cell_iff j v).mp hvj)).1 0
  have hkb := ((mem_frame_iff k hk _).mp ((mem_cell_iff k v).mp hvk)).1 0
  simp only [Pi.sub_apply, marker] at hjb hkb
  push_cast at hjb hkb
  omega

theorem mem_removed_iff (v : Lattice 3) :
    v ∈ removed ↔ ∃ i : Fin 3, v ∈ cell (i.val + 1) := by
  simp only [removed, Finset.mem_biUnion, Finset.mem_univ, true_and, cell]

theorem other_special_cell_in_body (j k : ℕ) (hj : 4 ≤ j) (hj5 : j ≤ 5)
    (hk : 4 ≤ k) (hk5 : k ≤ 5) (hne : j ≠ k) {v : Lattice 3}
    (hv : v ∈ cell j) : v ∈ body k := by
  apply Finset.mem_sdiff.mpr
  refine ⟨cell_subset_box j (by omega) hj5 hv, ?_⟩
  intro hh
  rcases Finset.mem_union.mp hh with hh | hh
  · obtain ⟨i, hi⟩ := (mem_removed_iff v).mp hh
    have he := cells_same_radius j (i.val + 1) (by omega) (by omega) hj5
      (by have := i.isLt; omega) hv hi
    have hi3 := i.isLt
    omega
  · exact hne (cells_same_radius j k (by omega) (by omega) hj5 hk5 hv hh)

theorem axis_frame_vertex (j : ℕ) (hj : 0 < j) :
    (Pi.single (0 : Fin 3) (j : ℤ) : Lattice 3) ∈ frame j := by
  apply (mem_frame_iff j hj _).mpr
  refine ⟨?_, 0, Or.inr (by simp)⟩
  intro i
  by_cases hi : i = 0
  · subst i; simp only [Pi.single_eq_same]; omega
  · simp only [Pi.single_eq_of_ne hi]; omega

theorem component_mem_pieces (Q j : ℕ) (hj : 0 < j) (hj5 : j ≤ 5)
    {v : Lattice 3} (hv : v ∈ component Q j) :
    v ∈ body j ∨
    (∃ i : Fin 3, ∃ u ∈ cell (i.val + 1), v = scale • Pi.single i 1 + u) ∨
    ∃ u ∈ cell j, v = scale • kernelStep Q + u := by
  rcases Finset.mem_union.mp hv with hv | hv
  · obtain ⟨hv, hs⟩ := Finset.mem_sdiff.mp hv
    rcases Finset.mem_union.mp hv with hv | hv
    · obtain ⟨hb, hr⟩ := Finset.mem_sdiff.mp hv
      exact Or.inl (Finset.mem_sdiff.mpr ⟨hb, by
        simpa only [holes, Finset.mem_union, not_or] using ⟨hr, hs⟩⟩)
    · obtain ⟨i, _, hv⟩ := Finset.mem_biUnion.mp hv
      obtain ⟨u, hu, he⟩ := Finset.mem_image.mp hv
      exact Or.inr (Or.inl ⟨i, marker (i.val + 1) + u,
        Finset.mem_image.mpr ⟨u, hu, rfl⟩, by rw [← he]; abel⟩)
  · obtain ⟨u, hu, he⟩ := Finset.mem_image.mp hv
    exact Or.inr (Or.inr ⟨marker j + u, Finset.mem_image.mpr ⟨u, hu, rfl⟩,
      by rw [← he]; abel⟩)

theorem common_cell_mem_component (Q j : ℕ) (hj : 0 < j) (hj5 : j ≤ 5)
    (i : Fin 3) {u : Lattice 3} (hu : u ∈ cell (i.val + 1)) :
    scale • Pi.single i 1 + u ∈ component Q j := by
  obtain ⟨v, hv, he⟩ := Finset.mem_image.mp hu
  rw [← he, ← add_assoc]
  exact common_bump_mem_component Q j hj hj5 i hv

theorem special_cell_mem_component (Q j : ℕ) {u : Lattice 3} (hu : u ∈ cell j) :
    scale • kernelStep Q + u ∈ component Q j := by
  obtain ⟨v, hv, he⟩ := Finset.mem_image.mp hu
  exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨v, hv, by rw [← he]; abel⟩)

end
end TranslationTiling.MSS
