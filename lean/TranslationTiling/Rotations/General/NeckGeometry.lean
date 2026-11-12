import TranslationTiling.Rotations.General.NearBody

namespace TranslationTiling.Rotations.General
variable {d : ℕ} [NeZero d]

theorem neck_wall_voxel (f : Face d) (p : Lattice d)
    (hp : 0 ≤ p 0 ∧ p 0 < neckLength d)
    (ht : ∀ j : Fin d, j ≠ 0 → |p j| ≤ (d : ℤ)+1)
    (hne : ∃ j : Fin d, j ≠ 0 ∧ p j ≠ 0) : (frameMotion f).apply p ∈ body := by
  apply frame_near_body f
  · unfold margin neckLength at *
    omega
  · intro j hj
    have hh := ht j hj
    unfold margin neckLength
    omega
  · intro hm
    rw [← Finset.mem_coe,fullKeyFinset_set] at hm
    rcases hm with (hb | hs) | hz
    · have hh := (hb 0).1
      simp only [keyLo,ite_true] at hh
      omega
    · obtain ⟨j,hj,hne⟩ := hne
      exact hne (hs.2.2 j hj)
    · obtain ⟨j,_,hne⟩ := hne
      have he : p=0 := hz
      exact hne (by simp [he])

theorem far_wall_voxel (f : Face d) :
    (frameMotion f).apply (Pi.single 0 ((neckLength d : ℤ)+(boxSide f 0 : ℤ))) ∈ body := by
  let p : Lattice d := Pi.single 0 ((neckLength d : ℤ)+(boxSide f 0 : ℤ))
  change (frameMotion f).apply p ∈ body
  apply frame_near_body f
  · have hs := boxSide_lt_max f (0 : Fin d)
    simp only [p,Pi.single_eq_same]
    unfold margin
    omega
  · intro j hj
    simp only [p,Pi.single_eq_of_ne hj,abs_zero]
    exact_mod_cast margin_pos (d := d)
  · intro hm
    rw [← Finset.mem_coe,fullKeyFinset_set] at hm
    rcases hm with (hb | hs) | hz
    · have hh := (hb 0).2
      simp only [p,Pi.single_eq_same,keyHi,keyLo,ite_true] at hh
      omega
    · have hh := hs.2.1
      simp only [p,Pi.single_eq_same] at hh
      have hpos := boxSide_two_le f (0 : Fin d)
      omega
    · have he : p=0 := hz
      have hh := congrFun he 0
      simp only [p,Pi.single_eq_same,Pi.zero_apply] at hh
      have hpos := boxSide_two_le f (0 : Fin d)
      omega

end TranslationTiling.Rotations.General
