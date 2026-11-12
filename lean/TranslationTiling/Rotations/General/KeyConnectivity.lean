import TranslationTiling.Rotations.General.KeyShapes

namespace TranslationTiling.Rotations.General
variable {d : ℕ} [NeZero d]

def stemLo : Lattice d := fun j => if j = 0 then 1 else 0

def stemHi : Lattice d := fun j => if j = 0 then (neckLength d : ℤ) - 1 else 0

theorem stem_eq_box : (Stem : Set (Lattice d)) = Box stemLo stemHi := by
  ext x
  constructor
  · intro hx j
    by_cases hj : j = 0
    · subst j; simp only [stemLo,stemHi,ite_true]; have := hx.1; have := hx.2.1; omega
    · simp only [stemLo,stemHi,ite_eq_right hj,hx.2.2 j hj,le_refl,and_self]
  · intro hx
    have hz := hx 0
    simp only [stemLo,stemHi,ite_true] at hz
    refine ⟨hz.1,by omega,?_⟩
    intro j hj
    have hj' := hx j
    simp only [stemLo,stemHi,ite_eq_right hj] at hj'
    omega

theorem stem_finite : (Stem : Set (Lattice d)).Finite := by
  rw [stem_eq_box]
  exact box_finite _ _

theorem stem_card : (Stem : Set (Lattice d)).ncard = neckLength d - 1 := by
  rw [stem_eq_box,box_ncard]
  have hs (j : Fin d) : (stemHi j + 1 - stemLo j).toNat =
      if j = 0 then neckLength d - 1 else 1 := by
    by_cases hj : j = 0
    · subst j; simp [stemHi,stemLo]
    · simp [stemHi,stemLo,hj]
  simp_rw [hs]
  simp

theorem key_finite (f : Face d) : (Key f).Finite :=
  (keyBox_finite f).union stem_finite

/-- All face keys have exactly the same number of voxels. -/
theorem key_card (hd : 2 ≤ d) (f : Face d) :
    (Key f).ncard = boxVolume d + neckLength d - 1 := by
  have hdis : Disjoint (KeyBox f) Stem := Set.disjoint_left.mpr (fun _ hx => keyBox_not_stem f hx)
  rw [Key,Set.ncard_union_eq hdis (keyBox_finite f) stem_finite,keyBox_card hd f,stem_card]
  unfold neckLength
  omega

/-- The rectangular chamber and its one-voxel-wide stem are face connected. -/
theorem key_connected (f : Face d) : Connected (Key f) := by
  have hq : keyLo ∈ KeyBox f := fun j => ⟨le_rfl,key_bounds f j⟩
  have path (x : Lattice d) (hx : x ∈ Key f) :
      FacePath (· ∈ Key f) x keyLo := by
    rcases hx with hb | hs
    · exact (box_path _ _ _ _ hb hq).mono (fun _ hz => Or.inl hz)
    · have he : Function.update x 0 (neckLength d : ℤ) = keyLo := by
        ext j
        by_cases hj : j = 0
        · subst j; simp [keyLo]
        · simp [Function.update_of_ne hj,keyLo,hj,hs.2.2 j hj]
      rw [← he]
      apply FacePath.axis
      intro t ht hu
      have hxt : x 0 ≤ (neckLength d : ℤ) := hs.2.1.le
      rw [min_eq_left hxt] at ht
      rw [max_eq_right hxt] at hu
      by_cases ht' : t = neckLength d
      · subst t
        rw [he]
        exact Or.inl hq
      · right
        refine ⟨?_,?_,?_⟩
        · simpa only [Function.update_self] using le_trans hs.1 ht
        · simp only [Function.update_self]; omega
        · intro j hj
          simpa [Function.update_of_ne hj] using hs.2.2 j hj
  intro x hx y hy
  exact (path x hx).trans (path y hy).reverse

end TranslationTiling.Rotations.General
