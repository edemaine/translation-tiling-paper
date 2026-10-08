import TranslationTiling.MSS.FrameGeometry
import TranslationTiling.Proofs.FacePaths

/-! A closed cubical frame confines every connected component that enters it. -/

namespace TranslationTiling.MSS

theorem adjacent_inner_mem_box (k : ℕ) (hk : 0 < k) {x y : Lattice 3}
    (hx : x ∈ box (k - 1)) (hxy : FaceAdjacent x y) : y ∈ box k := by
  apply (mem_box_iff k y).mpr
  intro j
  have hbounds := (mem_box_iff _ _).mp hx j
  obtain ⟨i, he | he⟩ := hxy
  · have h := congrFun he j
    by_cases hji : j = i
    · subst j
      simp only [Pi.add_apply, Pi.single_eq_same] at h
      omega
    · simp only [Pi.add_apply, Pi.single_eq_of_ne hji, add_zero] at h
      omega
  · have h := congrFun he j
    by_cases hji : j = i
    · subst j
      simp only [Pi.add_apply, Pi.single_eq_same] at h
      omega
    · simp only [Pi.add_apply, Pi.single_eq_of_ne hji, add_zero] at h
      omega

theorem adjacent_avoiding_frame (k : ℕ) (hk : 0 < k) {x y : Lattice 3}
    (hx : x ∈ box (k - 1)) (hy : y ∉ frame k) (hxy : FaceAdjacent x y) :
    y ∈ box (k - 1) := by
  by_contra hh
  exact hy (Finset.mem_sdiff.mpr ⟨adjacent_inner_mem_box k hk hx hxy, hh⟩)

theorem path_avoiding_frame (k : ℕ) (hk : 0 < k) {x y : Lattice 3}
    (hx : x ∈ box (k - 1)) (hpath : FacePath (fun z => z ∉ frame k) x y) :
    y ∈ box (k - 1) := by
  induction hpath with
  | refl => exact hx
  | @tail z w hpath hzw ih => exact adjacent_avoiding_frame k hk ih hzw.2.1 hzw.2.2

/-- This is the global confinement property needed in place of one-point
local forcing: a connected piece cannot enter and leave a closed frame. -/
theorem connected_piece_inside_frame (k : ℕ) (hk : 0 < k) (F : Tile 3)
    (hF : FaceConnected F) (havoid : ∀ z ∈ F, z ∉ frame k)
    {x : Lattice 3} (hx : x ∈ F) (hinner : x ∈ box (k - 1)) :
    ∀ y ∈ F, y ∈ box (k - 1) := by
  intro y hy
  apply path_avoiding_frame k hk hinner
  exact (hF x hx y hy).mono fun z hz => havoid z hz

end TranslationTiling.MSS
