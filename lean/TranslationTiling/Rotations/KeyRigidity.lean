import TranslationTiling.Rotations.KeyMoments

namespace TranslationTiling.Rotations.SixKeys

/-- Even a compensating translation cannot make one chamber match another
under a nontrivial signed coordinate permutation. -/
theorem chamber_rigid (i j : Face) (m : Motion)
    (he : (chamber i).image m.apply = chamber j) :
    i = j ∧ m.orientation = Orientation.ident ∧ m.offset = 0 := by
  have sig := signature_rigid i j m.orientation (by
    intro a
    have h₂ := moment_motion m (chamber i) a 2
    have h₃ := moment_motion m (chamber i) a 3
    rw [he, chamber_second, chamber_second] at h₂
    rw [he, chamber_third, chamber_third] at h₃
    have s₂ : m.orientation.sign a ^ 2 = 1 := by
      simpa only [pow_two] using m.orientation.sign_sq a
    have s₃ : m.orientation.sign a ^ 3 = m.orientation.sign a := by
      unfold Orientation.sign; split_ifs <;> norm_num
    exact ⟨by simpa [s₂] using h₂, by simpa [s₃] using h₃⟩)
  obtain ⟨hij, hor⟩ := sig
  subst j
  refine ⟨rfl, hor, ?_⟩
  ext a
  have hinj : ∀ x ∈ chamber i, ∀ y ∈ chamber i, m.apply x = m.apply y → x = y :=
    fun _ _ _ _ h => m.injective h
  have hs : (∑ x ∈ chamber i, m.apply x a) = ∑ x ∈ chamber i, x a := by
    calc
      _ = ∑ x ∈ (chamber i).image m.apply, x a :=
        (Finset.sum_image hinj).symm
      _ = _ := by rw [he]
  have hs' : (364 : ℤ) * m.offset a = 0 := by
    simp [Motion.apply, hor, Finset.sum_add_distrib, chamber_card] at hs
    omega
  change m.offset a = 0
  omega

end TranslationTiling.Rotations.SixKeys
