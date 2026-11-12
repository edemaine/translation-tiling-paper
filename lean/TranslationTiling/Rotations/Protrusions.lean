import TranslationTiling.Rotations.KeyGeometry

namespace TranslationTiling.Rotations.SixKeys

def ProtrusionBounds (i : Face) (x : Point) : Prop := ∀ k,
  if k = axis i then (if negative i then 40 ≤ x k ∧ x k ≤ 49 else -10 ≤ x k ∧ x k ≤ -1)
  else 12 ≤ x k ∧ x k ≤ 26

theorem protrusion_bounds (i : Face) {x : Point} (hx : x ∈ protrusion i) :
    ProtrusionBounds i x := by
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
  intro k
  have hb := recess_bounds i hu k
  fin_cases i <;> fin_cases k <;>
    simp [ProtrusionBounds, shift, normal, axis, negative] at * <;> omega

theorem protrusions_apart {i j : Face} (hne : i ≠ j) {x y : Point}
    (hx : x ∈ protrusion i) (hy : y ∈ protrusion j) :
    ∃ k : Fin 3, x k + 2 ≤ y k ∨ y k + 2 ≤ x k := by
  have hx0 := protrusion_bounds i hx 0; have hx1 := protrusion_bounds i hx 1
  have hx2 := protrusion_bounds i hx 2
  have hy0 := protrusion_bounds j hy 0; have hy1 := protrusion_bounds j hy 1
  have hy2 := protrusion_bounds j hy 2
  fin_cases i <;> fin_cases j <;> dsimp at hne <;> simp_all [axis, negative]
  all_goals first | exact ⟨0, by omega⟩ | exact ⟨1, by omega⟩ | exact ⟨2, by omega⟩

theorem protrusion_disjoint_cube (i : Face) : Disjoint (protrusion i) cube := by
  apply Finset.disjoint_left.mpr
  intro x hx hc
  have hp := protrusion_bounds i hx (axis i)
  have hq := Fintype.mem_piFinset.mp hc (axis i)
  simp only [Finset.mem_Icc] at hq
  simp only [ite_eq_left_iff, if_pos rfl] at hp
  split_ifs at hp <;> omega

theorem recess_boundary_gate (i : Face) {x : Point} (hx : x ∈ recess i)
    (he : x (axis i) = gate i (axis i)) : x = gate i := by
  have hp := (inRecess_iff_hole i x).mp ((mem_recess_iff i x).mp hx)
  ext k
  fin_cases i <;> fin_cases k <;> simp [HolePred, axis, gate, negative] at * <;> omega

theorem protrusion_touch (i : Face) {x y : Point} (hx : x ∈ protrusion i)
    (hy : y ∈ cube) (hxy : FaceAdjacent x y) :
    x = shift i + gate i ∧ y = attachment i := by
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
  have hb := recess_bounds i hu (axis i)
  have hc := Fintype.mem_piFinset.mp hy (axis i)
  have hd := adjacent_delta hxy (axis i)
  simp only [Finset.mem_Icc] at hc
  have he : u (axis i) = gate i (axis i) := by
    fin_cases i <;> simp [axis, negative, shift, normal, gate] at hb hc hd ⊢ <;> omega
  have huG := recess_boundary_gate i hu he
  subst u
  refine ⟨rfl, ?_⟩
  have q0 := Fintype.mem_piFinset.mp hy 0
  have q1 := Fintype.mem_piFinset.mp hy 1
  have q2 := Fintype.mem_piFinset.mp hy 2
  simp only [Finset.mem_Icc] at q0 q1 q2
  obtain ⟨k, he | he⟩ := hxy
  all_goals
    have h0 := congrFun he 0
    have h1 := congrFun he 1
    have h2 := congrFun he 2
    ext j
    fin_cases i <;> fin_cases k <;> fin_cases j <;>
      simp [attachment, shift, normal, gate, axis, negative] at h0 h1 h2 ⊢ <;> omega

theorem protrusion_boundary (i : Face) {x y : Point} (hx : x ∈ protrusion i)
    (hy : y ∈ gadget) (hxy : FaceAdjacent x y) : y ∈ protrusion i ∨ y ∈ body := by
  rcases Finset.mem_union.mp hy with hb | hp
  · exact Or.inr hb
  obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hp
  by_cases he : i = j
  · exact Or.inl (he ▸ hj)
  obtain ⟨k, hk⟩ := protrusions_apart he hx hj
  have hd := adjacent_delta hxy k
  omega

theorem attachment_adjacent (i : Face) : FaceAdjacent (shift i + gate i) (attachment i) := by
  refine ⟨axis i, ?_⟩
  by_cases hn : negative i = true
  · right
    simp [attachment, normal, hn]
  · left
    have hf : negative i = false := by cases h : negative i <;> simp_all
    ext k
    simp [attachment, normal, hf, Pi.single_apply]
    split_ifs <;> omega

end TranslationTiling.Rotations.SixKeys
