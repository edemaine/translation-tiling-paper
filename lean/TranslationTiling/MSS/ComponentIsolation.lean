import TranslationTiling.MSS.BodyIsolation
import TranslationTiling.MSS.FrameConnectivity

/-! The only isolated vertex of either rigid component is the first marker. -/

namespace TranslationTiling.MSS

noncomputable section
open scoped Classical
attribute [local irreducible] box

theorem negative_box_mem_component (Q j : ℕ) (hj : 0 < j)
    {v : Lattice 3} (hv : v ∈ box 100) (hx : v 0 ≤ 0) : v ∈ component Q j := by
  apply body_subset_component
  apply Finset.mem_sdiff.mpr
  refine ⟨hv, ?_⟩
  intro hh
  rcases Finset.mem_union.mp hh with hh | hh
  · obtain ⟨i, _, hh⟩ := Finset.mem_biUnion.mp hh
    obtain ⟨u, hu, he⟩ := Finset.mem_image.mp hh
    have h0 := congrFun he 0
    have hb := (mem_box_iff _ _).mp (Finset.mem_sdiff.mp hu).1 0
    simp only [Pi.add_apply, marker] at h0
    push_cast at h0
    omega
  · obtain ⟨u, hu, he⟩ := Finset.mem_image.mp hh
    have h0 := congrFun he 0
    have hb := (mem_box_iff _ _).mp (Finset.mem_sdiff.mp hu).1 0
    simp only [Pi.add_apply, marker] at h0
    push_cast at h0
    omega

theorem zero_mem_component (Q j : ℕ) (hj : 0 < j) : (0 : Lattice 3) ∈ component Q j :=
  negative_box_mem_component Q j hj
    ((mem_box_iff 100 _).mpr (by intro i; norm_num)) (by simp)

theorem marker_frame_in_box (r : ℕ) (hr : 0 < r) (hr5 : r ≤ 5)
    {u : Lattice 3} (hu : u ∈ frame r) : marker r + u ∈ box 100 := by
  apply (mem_box_iff 100 _).mpr
  intro i
  have h := ((mem_frame_iff r hr u).mp hu).1 i
  simp only [Pi.add_apply, marker]
  split_ifs <;> push_cast <;> omega

theorem common_bump_outside_box (i : Fin 3) {u : Lattice 3}
    (hu : u ∈ frame (i.val + 1)) :
    scale • Pi.single i 1 + marker (i.val + 1) + u ∉ box 100 := by
  intro hbox
  have h := (mem_box_iff 100 _).mp hbox i
  have hb := ((mem_frame_iff (i.val + 1) (by omega) u).mp hu).1 i
  simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, scale,
    mul_one, marker] at h
  have hi := i.isLt
  split_ifs at h <;> push_cast at h <;> omega

theorem common_bump_mem_component (Q j : ℕ) (hj : 0 < j) (hj5 : j ≤ 5)
    (i : Fin 3) {u : Lattice 3} (hu : u ∈ frame (i.val + 1)) :
    scale • Pi.single i 1 + marker (i.val + 1) + u ∈ component Q j := by
  apply Finset.mem_union_left
  apply Finset.mem_sdiff.mpr
  refine ⟨Finset.mem_union_right _ ?_, ?_⟩
  · exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _,
      Finset.mem_image.mpr ⟨u, hu, rfl⟩⟩
  · intro h
    obtain ⟨v, hv, he⟩ := Finset.mem_image.mp h
    have hb := marker_frame_in_box j hj hj5 hv
    rw [he] at hb
    exact common_bump_outside_box i hu hb

theorem adjacent_add {d : ℕ} (c : Lattice d) {x y : Lattice d}
    (h : FaceAdjacent x y) : FaceAdjacent (c + x) (c + y) := by
  obtain ⟨i, h | h⟩ := h
  · refine ⟨i, Or.inl ?_⟩
    rw [h, add_assoc]
  · refine ⟨i, Or.inr ?_⟩
    rw [h, add_assoc]

theorem adjacent_update_plus (v : Lattice 3) (i : Fin 3) :
    FaceAdjacent v (Function.update v i (v i + 1)) := by
  refine ⟨i, Or.inl ?_⟩
  funext k
  by_cases hk : k = i
  · subst k; simp
  · simp [Function.update_of_ne hk, Pi.single_eq_of_ne hk]

theorem adjacent_update_minus (v : Lattice 3) (i : Fin 3) :
    FaceAdjacent v (Function.update v i (v i - 1)) := by
  refine ⟨i, Or.inr ?_⟩
  funext k
  by_cases hk : k = i
  · subst k; simp
  · simp [Function.update_of_ne hk, Pi.single_eq_of_ne hk]

theorem component_isolated_point (Q j : ℕ) (hj : 0 < j) (hj5 : j ≤ 5)
    (v : Lattice 3) (hv : v ∈ component Q j)
    (hiso : ∀ w ∈ component Q j, ¬ FaceAdjacent v w) : v = marker 1 := by
  rcases Finset.mem_union.mp hv with hv | hv
  · obtain ⟨hv, hspecial⟩ := Finset.mem_sdiff.mp hv
    rcases Finset.mem_union.mp hv with hv | hv
    · obtain ⟨hbox, hremoved⟩ := Finset.mem_sdiff.mp hv
      have hbody : v ∈ body j := Finset.mem_sdiff.mpr ⟨hbox, by
        simpa only [holes, Finset.mem_union, not_or] using ⟨hremoved, hspecial⟩⟩
      apply body_isolated_point j hj hj5 v hbody
      · exact fun h => hiso _ (body_subset_component Q j h) (adjacent_update_plus v 1)
      · exact fun h => hiso _ (body_subset_component Q j h) (adjacent_update_minus v 1)
    · obtain ⟨i, _, hv⟩ := Finset.mem_biUnion.mp hv
      obtain ⟨u, hu, he⟩ := Finset.mem_image.mp hv
      obtain ⟨w, hw, hadj⟩ := frame_has_neighbor (i.val + 1) (by omega) u hu
      have ha := adjacent_add (scale • Pi.single i 1 + marker (i.val + 1)) hadj
      rw [he] at ha
      exact (hiso _ (common_bump_mem_component Q j hj hj5 i hw) ha).elim
  · obtain ⟨u, hu, he⟩ := Finset.mem_image.mp hv
    obtain ⟨w, hw, hadj⟩ := frame_has_neighbor j hj u hu
    have ha := adjacent_add (scale • kernelStep Q + marker j) hadj
    rw [he] at ha
    exact (hiso _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨w, hw, rfl⟩)) ha).elim

end
end TranslationTiling.MSS
