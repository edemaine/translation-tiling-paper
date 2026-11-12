import TranslationTiling.Rotations.KeyParameters
import TranslationTiling.Rotations.BodyPaths

namespace TranslationTiling.Rotations.SixKeys

def FaceBounds (i : Face) (x : Point) : Prop := ∀ k,
  if k = axis i then (if negative i then 0 ≤ x k ∧ x k ≤ 9 else 30 ≤ x k ∧ x k ≤ 39)
  else 12 ≤ x k ∧ x k ≤ 26

theorem recess_bounds (i : Face) {x : Point} (hx : x ∈ recess i) : FaceBounds i x := by
  have hp := (inRecess_iff_hole i x).mp ((mem_recess_iff i x).mp hx)
  intro k
  fin_cases i <;> fin_cases k <;>
    simp [FaceBounds, HolePred, axis, negative] at * <;> omega

theorem recesses_apart {i j : Face} (hne : i ≠ j) {x y : Point}
    (hx : x ∈ recess i) (hy : y ∈ recess j) :
    ∃ k : Fin 3, x k + 2 ≤ y k ∨ y k + 2 ≤ x k := by
  have hx0 := recess_bounds i hx 0; have hx1 := recess_bounds i hx 1
  have hx2 := recess_bounds i hx 2
  have hy0 := recess_bounds j hy 0; have hy1 := recess_bounds j hy 1
  have hy2 := recess_bounds j hy 2
  fin_cases i <;> fin_cases j <;> dsimp at hne <;>
    simp_all [axis, negative]
  all_goals first | exact ⟨0, by omega⟩ | exact ⟨1, by omega⟩ | exact ⟨2, by omega⟩

theorem adjacent_delta {x y : Point} (h : FaceAdjacent x y) (i : Fin 3) :
    -1 ≤ y i - x i ∧ y i - x i ≤ 1 := by
  obtain ⟨k, he | he⟩ := h
  · have hh := congrFun he i
    simp only [Pi.add_apply, Pi.single_apply] at hh
    split_ifs at hh <;> omega
  · have hh := congrFun he i
    simp only [Pi.add_apply, Pi.single_apply] at hh
    split_ifs at hh <;> omega

theorem recesses_disjoint {i j : Face} (hne : i ≠ j) : Disjoint (recess i) (recess j) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  obtain ⟨k, hk⟩ := recesses_apart hne hx hy
  omega

theorem recesses_not_adjacent {i j : Face} (hne : i ≠ j) {x y : Point}
    (hx : x ∈ recess i) (hy : y ∈ recess j) : ¬ FaceAdjacent x y := by
  intro hxy
  obtain ⟨k, hk⟩ := recesses_apart hne hx hy
  have := adjacent_delta hxy k
  omega

theorem chamber_interior (i : Face) {x : Point} (hx : x ∈ chamber i) :
    ∀ k, 1 ≤ x k ∧ x k ≤ 38 := by
  obtain ⟨j, rfl⟩ := chamberVoxel_surjective i hx
  intro k
  have hlt := j.isLt
  unfold chamberVoxel
  split_ifs with hj
  all_goals fin_cases i <;> fin_cases k <;>
    simp [localPoint, gate, normal, axis, negative, tangent₁, tangent₂, dimensions] <;> omega

theorem gate_mem_recess (i : Face) : gate i ∈ recess i := by
  apply Finset.mem_union_left
  apply Finset.mem_image.mpr
  exact ⟨0, by simp, by simp [localPoint]⟩

theorem recess_card (i : Face) : (recess i).card = 365 := by
  have h := Finset.card_erase_add_one (gate_mem_recess i)
  change (chamber i).card + 1 = (recess i).card at h
  rw [chamber_card] at h
  omega

theorem recess_subset_cube (i : Face) : recess i ⊆ cube := by
  intro x hx
  apply Fintype.mem_piFinset.mpr
  intro k
  have hh := recess_bounds i hx k
  apply Finset.mem_Icc.mpr
  split_ifs at hh <;> omega

def attachment (i : Face) : Point := shift i + gate i - normal i

theorem attachment_body (i : Face) : attachment i ∈ body := by
  apply (mem_body_iff _).mpr
  fin_cases i <;>
    simp [attachment, shift, gate, normal, axis, negative, BodyPred, InCube, Fin.forall_fin_succ]

theorem chamber_boundary (i : Face) {x y : Point}
    (hx : x ∈ chamber i) (hxy : FaceAdjacent x y) :
    y ∈ chamber i ∨ y = gate i ∨ y ∈ body := by
  by_cases hy : y ∈ recess i
  · by_cases hg : y = gate i
    · exact Or.inr (Or.inl hg)
    · exact Or.inl (Finset.mem_erase.mpr ⟨hg, hy⟩)
  right; right
  apply Finset.mem_sdiff.mpr
  refine ⟨?_, ?_⟩
  · apply Fintype.mem_piFinset.mpr
    intro k
    have hb := chamber_interior i hx k
    have hd := adjacent_delta hxy k
    exact Finset.mem_Icc.mpr (by omega)
  · intro hrem
    obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hrem
    by_cases he : i = j
    · exact hy (he ▸ hj)
    · exact recesses_not_adjacent he (Finset.mem_of_mem_erase hx) hj hxy

end TranslationTiling.Rotations.SixKeys
