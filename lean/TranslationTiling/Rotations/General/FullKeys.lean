import TranslationTiling.Rotations.General.Gadget

namespace TranslationTiling.Rotations.General
variable {d : ℕ} [NeZero d]

theorem zero_not_key (f : Face d) : (0 : Lattice d) ∉ Key f := by
  have hn : 0 < neckLength d := by unfold neckLength; omega
  rintro (hb | hs)
  · have := (hb 0).1
    simp only [keyLo,ite_true,Pi.zero_apply] at this
    omega
  · have := hs.1
    change 1 ≤ (0 : ℤ) at this
    omega

theorem fullKey_card (hd : 2 ≤ d) (f : Face d) :
    (fullKeyFinset f).card = boxVolume d + neckLength d := by
  have hdis : Disjoint (Key f) {0} := Set.disjoint_singleton_right.mpr (zero_not_key f)
  have hn : 0 < neckLength d := by unfold neckLength; omega
  have hh := Set.ncard_union_eq hdis (key_finite f) (Set.finite_singleton 0)
  rw [← fullKeyFinset_set,Set.ncard_coe_finset,key_card hd f,Set.ncard_singleton] at hh
  omega

theorem fullKey_connected (f : Face d) : Connected (↑(fullKeyFinset f) : Set (Lattice d)) := by
  let p : Lattice d := Pi.single 0 1
  have hp : p ∈ Key f := by
    right
    refine ⟨?_,?_,?_⟩
    · simp [p]
    · simp only [p,Pi.single_eq_same]
      unfold neckLength
      omega
    · intro j hj; simp [p,Pi.single_eq_of_ne hj]
  have h0 : (0 : Lattice d) ∈ fullKeyFinset f := by simp [fullKeyFinset]
  have hpk : p ∈ fullKeyFinset f := by rw [← Finset.mem_coe,fullKeyFinset_set]; exact Or.inl hp
  have hstep : FacePath (· ∈ fullKeyFinset f) 0 p :=
    FacePath.step h0 hpk ⟨0,Or.inl (by simp [p])⟩
  have path (x : Lattice d) (hx : x ∈ fullKeyFinset f) :
      FacePath (· ∈ fullKeyFinset f) x p := by
    rw [← Finset.mem_coe,fullKeyFinset_set] at hx
    rcases hx with hx | hx
    · exact (key_connected f x hx p hp).mono (fun _ hz => by
        rw [← Finset.mem_coe,fullKeyFinset_set]; exact Or.inl hz)
    · have he : x = 0 := hx
      subst x
      exact hstep
  intro x hx y hy
  exact (path x hx).trans (path y hy).reverse

end TranslationTiling.Rotations.General
