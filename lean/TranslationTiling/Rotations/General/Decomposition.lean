import TranslationTiling.Rotations.General.Geometry

namespace TranslationTiling.Rotations.General
variable {d : ℕ} [NeZero d]

def removed : Finset (Lattice d) := Finset.univ.biUnion recess

def body : Finset (Lattice d) := cell (cubeSide d) \ removed

def protrusion (f : Face d) : Finset (Lattice d) :=
  (recess f).image (scale (cubeSide d) (normal f) + ·)

theorem home_of_recess (f : Face d) {q : Lattice d} (hq : q ∈ recess f) : home q = normal f := by
  unfold home
  cases hf : (List.finRange (2*d)).find? (fun g => q ∈ recess g) with
  | none =>
    have hn := List.find?_eq_none.mp hf f (by simp)
    simp [hq] at hn
  | some g =>
    have hg : q ∈ recess g := by simpa using List.find?_some hf
    have he : g = f := by
      by_contra hne
      exact Finset.disjoint_left.mp (recesses_disjoint hne) hg hq
    subst g
    rfl

theorem home_of_body {q : Lattice d} (hq : q ∈ body) : home q = 0 := by
  have hn : ∀ f : Face d, q ∉ recess f := by
    intro f hf
    exact (Finset.mem_sdiff.mp hq).2 (Finset.mem_biUnion.mpr ⟨f,Finset.mem_univ _,hf⟩)
  have hf : (List.finRange (2*d)).find? (fun f => q ∈ recess f) = none := by
    apply List.find?_eq_none.mpr
    intro f _
    simpa using hn f
  simp only [home,hf]

/-- The effective relocation definition is exactly the intended geometric
construction: remove each recess and attach its period-shifted copy. -/
theorem gadget_decomposition :
    (gadget : Finset (Lattice d)) = body ∪ Finset.univ.biUnion protrusion := by
  ext x
  constructor
  · intro hx
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hx
    apply Finset.mem_union.mpr
    by_cases hb : q ∈ removed
    · obtain ⟨f,_,hf⟩ := Finset.mem_biUnion.mp hb
      right
      apply Finset.mem_biUnion.mpr
      refine ⟨f,Finset.mem_univ _,?_⟩
      apply Finset.mem_image.mpr
      refine ⟨q,hf,?_⟩
      simp [relocate,home_of_recess f hf,add_comm]
    · have hqb : q ∈ body := Finset.mem_sdiff.mpr ⟨hq,hb⟩
      left
      simpa [relocate,home_of_body hqb,scale] using hqb
  · intro hx
    rcases Finset.mem_union.mp hx with hb | hp
    · apply Finset.mem_image.mpr
      refine ⟨x,(Finset.mem_sdiff.mp hb).1,?_⟩
      simp [relocate,home_of_body hb,scale]
    · obtain ⟨f,_,hf⟩ := Finset.mem_biUnion.mp hp
      obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hf
      apply Finset.mem_image.mpr
      refine ⟨q,recess_subset_cell f hq,?_⟩
      simp [relocate,home_of_recess f hq,add_comm]

end TranslationTiling.Rotations.General
