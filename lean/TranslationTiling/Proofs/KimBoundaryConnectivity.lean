import TranslationTiling.Proofs.KimGeometry
import TranslationTiling.Proofs.FacePaths

/-! The outer boundary of a lattice cube is face connected. -/

namespace TranslationTiling.Kim

theorem mem_boundary_iff (l : ℕ) (q : Lattice 3) :
    q ∈ boundary l ↔ q ∈ cube l ∧ ∃ k, q k = 0 ∨ q k = (l : ℤ) - 1 := by
  simp [boundary]

theorem boundary_path_to_zero (l : ℕ) (hl : 0 < l) (q : Lattice 3)
    (hq : q ∈ boundary l) : FacePath (fun z => z ∈ boundary l) q 0 := by
  obtain ⟨hqc, k, hk⟩ := (mem_boundary_iff _ _).mp hq
  let P := fun z => z ∈ boundary l
  let r := Function.update (0 : Lattice 3) k (q k)
  have first : FacePath P q r := by
    apply FacePath.box3 P
      (Function.update (0 : Lattice 3) k (q k))
      (Function.update (fun _ => (l : ℤ) - 1) k (q k)) q r
    · intro j
      by_cases hj : j = k
      · subst j; simp
      · have := (mem_cube_iff _ _).mp hqc j
        simp [hj]; omega
    · intro j
      by_cases hj : j = k
      · subst j; simp [r]
      · simp [r, hj]; omega
    · intro z hz
      apply (mem_boundary_iff _ _).mpr
      refine ⟨(mem_cube_iff _ _).mpr ?_, k, ?_⟩
      · intro j
        have hjz := hz j
        have hjq := (mem_cube_iff _ _).mp hqc j
        by_cases hj : j = k
        · subst j; simp at hjz; omega
        · simp [hj] at hjz; omega
      · have hzk := hz k
        simp at hzk
        have he : z k = q k := by omega
        simpa only [he] using hk
  have last : FacePath P r (Function.update r k 0) := by
    apply FacePath.axis
    intro t ht hu
    have hqk := (mem_cube_iff _ _).mp hqc k
    simp [r] at ht hu
    apply (mem_boundary_iff _ _).mpr
    constructor
    · apply (mem_cube_iff _ _).mpr
      intro j
      by_cases hj : j = k
      · subst j; simp; omega
      · simp [r, hj]; omega
    · have other : ∃ j : Fin 3, j ≠ k := by
        fin_cases k
        · exact ⟨1, by decide⟩
        · exact ⟨0, by decide⟩
        · exact ⟨0, by decide⟩
      obtain ⟨j, hj⟩ := other
      exact ⟨j, Or.inl (by simp [r, hj])⟩
  have he : Function.update r k 0 = (0 : Lattice 3) := by
    simp [r, Function.update_idem]
  exact first.trans (he ▸ last)

theorem boundary_connected (l : ℕ) (hl : 0 < l) : FaceConnected (boundary l) := by
  intro x hx y hy
  exact (boundary_path_to_zero l hl x hx).trans
    (FacePath.reverse (boundary_path_to_zero l hl y hy))

end TranslationTiling.Kim
