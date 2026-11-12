import TranslationTiling.Rotations.General.BodyGeometry

namespace TranslationTiling.Rotations.General
variable {d : ℕ} [NeZero d]

def neckHi : Lattice d := fun j => if j = 0 then (neckLength d : ℤ)-1 else 0

theorem fullKey_two_boxes (f : Face d) :
    (fullKeyFinset f : Set (Lattice d)) = KeyBox f ∪ Box 0 neckHi := by
  rw [fullKeyFinset_set]
  ext x
  constructor
  · rintro ((hb | hs) | hz)
    · exact Or.inl hb
    · right
      intro j
      by_cases hj : j = 0
      · subst j; have := hs.1; have := hs.2.1; simp only [neckHi,ite_true,Pi.zero_apply]; omega
      · simp [neckHi,hj,hs.2.2 j hj]
    · right
      have he : x = 0 := hz
      subst x
      intro j
      have hn : 0 < neckLength d := by unfold neckLength; omega
      simp only [neckHi,Pi.zero_apply]
      split_ifs <;> omega
  · rintro (hb | hn)
    · exact Or.inl (Or.inl hb)
    · have hn0 := hn 0
      simp only [neckHi,ite_true,Pi.zero_apply] at hn0
      have ht (j : Fin d) (hj : j ≠ 0) : x j = 0 := by
        have hh := hn j
        simp only [neckHi,ite_eq_right hj,Pi.zero_apply] at hh
        omega
      by_cases hz : x 0 = 0
      · right
        apply funext
        intro j
        by_cases hj : j = 0
        · subst j; exact hz
        · exact ht j hj
      · left; right
        exact ⟨by omega,by omega,ht⟩

theorem recess_two_boxes (f : Face d) : (recess f : Set (Lattice d)) =
    (frameMotion f).apply '' KeyBox f ∪ (frameMotion f).apply '' Box 0 neckHi := by
  simp only [recess,Finset.coe_image,fullKey_two_boxes,Set.image_union]

theorem box_cross {lo hi x : Lattice d} {i j : Fin d} (hij : i ≠ j) (t s : ℤ)
    (ht : Function.update x i t ∈ Box lo hi) (hs : Function.update x j s ∈ Box lo hi) :
    x ∈ Box lo hi := by
  intro k
  by_cases hk : k = i
  · subst k; simpa [Function.update_of_ne hij] using hs i
  · simpa [Function.update_of_ne hk] using ht k

/-- The two rectangular parts of a recess are separated in its normal direction. -/
theorem recess_parts_separated (f : Face d) {u v : Lattice d} (hu : u ∈ KeyBox f)
    (hv : v ∈ Box 0 neckHi)
    (he : (frameMotion f).apply u (faceAxis f) = (frameMotion f).apply v (faceAxis f)) : False := by
  have hu0 := (hu 0).1
  have hv0 := (hv 0).2
  simp only [keyLo,neckHi,ite_true] at hu0 hv0
  rw [frame_normal_apply,frame_normal_apply] at he
  cases hn : negative f <;> simp only [hn,Bool.false_eq_true,ite_false,ite_true] at he
  all_goals omega

/-- If two distinct transverse coordinate lines meet the same recess, their
intersection already belongs to that recess. -/
theorem recess_cross (f : Face d) {x : Lattice d} {i j : Fin d} (hij : i ≠ j)
    (hi : i ≠ faceAxis f) (hj : j ≠ faceAxis f) (t s : ℤ)
    (ht : Function.update x i t ∈ recess f) (hs : Function.update x j s ∈ recess f) :
    x ∈ recess f := by
  have hn : (Function.update x i t) (faceAxis f) = (Function.update x j s) (faceAxis f) := by
    simp [Ne.symm hi,Ne.symm hj]
  rw [← Finset.mem_coe,recess_two_boxes] at ht hs ⊢
  rcases ht with ht | ht <;> rcases hs with hs | hs
  · left
    rw [KeyBox,(frameMotion f).image_box] at ht hs ⊢
    exact box_cross hij t s ht hs
  · obtain ⟨u,hu,he⟩ := ht
    obtain ⟨v,hv,he'⟩ := hs
    rw [← he,← he'] at hn
    exact (recess_parts_separated f hu hv hn).elim
  · obtain ⟨u,hu,he⟩ := hs
    obtain ⟨v,hv,he'⟩ := ht
    rw [← he,← he'] at hn
    exact (recess_parts_separated f hu hv hn.symm).elim
  · right
    rw [(frameMotion f).image_box] at ht hs ⊢
    exact box_cross hij t s ht hs

end TranslationTiling.Rotations.General
