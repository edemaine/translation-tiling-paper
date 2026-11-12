import TranslationTiling.Rotations.General.BodyGeometry

namespace TranslationTiling.Rotations.General
variable {d : ℕ} [NeZero d]

theorem frame_tangent_axis_ne_zero (f : Face d) (j : Fin d) (hj : j ≠ faceAxis f) :
    (frameOrientation f).axes j ≠ 0 := by
  intro he
  have ha : (frameOrientation f).axes (faceAxis f) = 0 := by simp [frameOrientation]
  exact hj ((frameOrientation f).axes.injective (he.trans ha.symm))

/-- In a broad neighborhood of a face gate, only that face's recess can occur. -/
theorem frame_near_body (f : Face d) {p : Lattice d}
    (hn : 0 ≤ p 0 ∧ p 0 < (margin d : ℤ))
    (ht : ∀ j : Fin d, j ≠ 0 → |p j| < (margin d : ℤ))
    (hout : p ∉ fullKeyFinset f) : (frameMotion f).apply p ∈ body := by
  have hp := margin_pos (d := d)
  have hL := margin_five_lt_cubeSide (d := d)
  have normalBound :
      (if negative f then 0 ≤ (frameMotion f).apply p (faceAxis f) ∧
          (frameMotion f).apply p (faceAxis f) < (margin d : ℤ)
       else (cubeSide d : ℤ)-(margin d : ℤ) ≤ (frameMotion f).apply p (faceAxis f) ∧
          (frameMotion f).apply p (faceAxis f) < cubeSide d) := by
    rw [frame_normal_apply]
    cases h : negative f <;> simp only [h,Bool.false_eq_true,ite_true,ite_false]
    all_goals omega
  have tangentBound (j : Fin d) (hj : j ≠ faceAxis f) :
      0 ≤ (frameMotion f).apply p j ∧ (frameMotion f).apply p j < cubeSide d := by
    rw [frame_tangent_apply f p j hj]
    have hb := abs_lt.mp (ht _ (frame_tangent_axis_ne_zero f j hj))
    cases h : negative f <;> simp only [h,Bool.false_eq_true,ite_true,ite_false]
    all_goals omega
  apply (body_iff _).mpr
  constructor
  · intro j
    by_cases hj : j = faceAxis f
    · subst j
      have hh := normalBound
      cases h : negative f <;> simp only [h,Bool.false_eq_true,ite_true,ite_false] at hh
      all_goals dsimp; omega
    · have hh := tangentBound j hj
      dsimp
      omega
  · intro g hg
    have ha : faceAxis g = faceAxis f := by
      by_contra he
      have hb := recess_tangent_central g hg (faceAxis f) (Ne.symm he)
      dsimp [Central] at hb
      have hh := normalBound
      cases h : negative f <;> simp only [h,Bool.false_eq_true,ite_true,ite_false] at hh
      all_goals omega
    have hneg : negative g = negative f := by
      have hb := (recess_bounds g hg).1
      rw [ha] at hb
      have hh := normalBound
      cases h1 : negative g <;> cases h2 : negative f
      all_goals simp only [h1,h2,Bool.false_eq_true,ite_true,ite_false] at hb hh ⊢
      all_goals first | rfl | omega
    have hgf := face_ext ha hneg
    subst g
    obtain ⟨u,hu,he⟩ := Finset.mem_image.mp hg
    have he' := (frameMotion f).injective he
    exact hout (he' ▸ hu)

end TranslationTiling.Rotations.General
