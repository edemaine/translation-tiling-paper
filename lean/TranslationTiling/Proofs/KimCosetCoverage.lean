import TranslationTiling.Proofs.KimResidues

/-! Transport the shell's grid fundamental domain to any grid coset. -/

namespace TranslationTiling.Kim

theorem exactTiling_coset (l : ℕ) (hl : 0 < l) (t : Lattice 3) :
    ExactTiling (gridCoset (scale (boundary l).length) t) {v | v ∈ shell l} := by
  have ht := shell_exactTiling l hl
  rw [exactTiling_iff] at ht ⊢
  intro x
  obtain ⟨f, hf, hu⟩ := ht (x - t)
  refine ⟨f, ?_, ?_⟩
  · obtain ⟨z, hz⟩ := hf
    refine ⟨z, ?_⟩
    change x - t - f.val = 0 + (scale (boundary l).length : ℤ) • z at hz
    change x - f.val = t + (scale (boundary l).length : ℤ) • z
    rw [zero_add] at hz
    rw [← hz]
    abel
  · intro g hg
    apply hu
    obtain ⟨z, hz⟩ := hg
    refine ⟨z, ?_⟩
    change x - g.val = t + (scale (boundary l).length : ℤ) • z at hz
    change x - t - g.val = 0 + (scale (boundary l).length : ℤ) • z
    rw [zero_add]
    calc
      x - t - g.val = (x - g.val) - t := by abel
      _ = (scale (boundary l).length : ℤ) • z := by rw [hz]; abel

end TranslationTiling.Kim
