import TranslationTiling.Rotations.General.Crossing

namespace TranslationTiling.Rotations.General
variable {d : ℕ} [NeZero d]

def ClearLine (x : Lattice d) (i : Fin d) : Prop :=
  ∀ t : ℤ, (margin d : ℤ) ≤ t → t ≤ (cubeSide d : ℤ)-(margin d : ℤ) →
    Function.update x i t ∈ body

theorem blocked_line {x : Lattice d} (hx : InCube x) (i : Fin d) (hn : ¬ ClearLine x i) :
    ∃ f : Face d, ∃ t : ℤ,
      (margin d : ℤ) ≤ t ∧ t ≤ (cubeSide d : ℤ)-(margin d : ℤ) ∧
      Function.update x i t ∈ recess f ∧ i ≠ faceAxis f := by
  classical
  unfold ClearLine at hn
  push_neg at hn
  obtain ⟨t,ht,hu,hb⟩ := hn
  have hp := margin_pos (d := d)
  have hL := margin_five_lt_cubeSide (d := d)
  have hxc : InCube (Function.update x i t) := inCube_update hx i t (by omega)
  obtain ⟨f,hf⟩ : ∃ f : Face d, Function.update x i t ∈ recess f := by
    by_contra! hh
    exact hb ((body_iff _).mpr ⟨hxc,hh⟩)
  refine ⟨f,t,ht,hu,hf,?_⟩
  intro he
  have hh := recess_normal_not_closed f hf
  rw [← he,Function.update_self] at hh
  exact hh ⟨ht,hu⟩

/-- With d ≥ 3, every body point with a central coordinate has a clear central
coordinate line. Two blocked transverse lines would put the point in a recess. -/
theorem exists_clear_line (hd : 3 ≤ d) {x : Lattice d} (hx : x ∈ body)
    (i : Fin d) (hi : Central (d := d) (x i)) :
    ∃ j, Central (d := d) (x j) ∧ ClearLine x j := by
  classical
  by_cases hc : ClearLine x i
  · exact ⟨i,hi,hc⟩
  obtain ⟨f,t,ht,hu,hf,hia⟩ := blocked_line ((body_iff x).mp hx).1 i hc
  have cent (k : Fin d) (hk : k ≠ faceAxis f) : Central (d := d) (x k) := by
    by_cases hki : k = i
    · subst k; exact hi
    · have h := recess_tangent_central f hf k hk
      simpa [Function.update_of_ne hki] using h
  obtain ⟨j,hji,hja⟩ := exists_third hd i (faceAxis f)
  refine ⟨j,cent j hja,?_⟩
  by_contra hcj
  obtain ⟨g,s,hs,hv,hg,hjga⟩ := blocked_line ((body_iff x).mp hx).1 j hcj
  have ha : faceAxis g = faceAxis f := by
    by_contra hne
    have hcen := cent (faceAxis g) hne
    have hnormal := recess_normal_not_closed g hg
    simp only [Function.update_of_ne (Ne.symm hjga)] at hnormal
    exact hnormal ⟨hcen.1.le,hcen.2.le⟩
  have hn : negative g = negative f := by
    have hb1 := (recess_bounds f hf).1
    have hb2 := (recess_bounds g hg).1
    simp only [Function.update_of_ne (Ne.symm hia)] at hb1
    simp only [ha,Function.update_of_ne (Ne.symm hja)] at hb2
    have hp := margin_pos (d := d)
    have hL := margin_five_lt_cubeSide (d := d)
    cases h1 : negative g <;> cases h2 : negative f
    all_goals simp only [h1,h2,Bool.false_eq_true,ite_true,ite_false] at hb1 hb2 ⊢
    all_goals first | rfl | omega
  have hgf := face_ext ha hn
  subst g
  have hxr := recess_cross f (Ne.symm hji) hia hja t s hf hg
  exact ((body_iff x).mp hx).2 f hxr

end TranslationTiling.Rotations.General
