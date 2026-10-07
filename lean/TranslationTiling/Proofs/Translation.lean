import TranslationTiling.Proofs.Basic

namespace TranslationTiling

/-- Translating the finite tile does not change tilability. -/
theorem tiles_translate_iff {d : ℕ} (F : Tile d) (t : Lattice d) :
    Tiles (F.map fun f => f + t) ↔ Tiles F := by
  constructor
  · rintro ⟨A, ha⟩
    refine ⟨{a | a - t ∈ A}, (exactTiling_iff _ _).mpr ?_⟩
    intro x
    obtain ⟨f', hf', hu⟩ := (exactTiling_iff _ _).mp ha x
    obtain ⟨f, hf, he⟩ := List.mem_map.mp f'.property
    refine ⟨⟨f, hf⟩, ?_, ?_⟩
    · change x - f - t ∈ A
      simpa only [← he, sub_add_eq_sub_sub] using hf'
    · intro g hg
      change x - g.val - t ∈ A at hg
      have hg' : x - (g.val + t) ∈ A := by
        simpa only [sub_add_eq_sub_sub] using hg
      have hgf := congrArg Subtype.val (hu
        ⟨g.val + t, List.mem_map.mpr ⟨g.val, g.property, rfl⟩⟩ hg')
      exact Subtype.ext (add_right_cancel (hgf.trans he.symm))
  · rintro ⟨A, ha⟩
    refine ⟨{a | a + t ∈ A}, (exactTiling_iff _ _).mpr ?_⟩
    intro x
    obtain ⟨f, hf, hu⟩ := (exactTiling_iff _ _).mp ha x
    refine ⟨⟨f.val + t, List.mem_map.mpr ⟨f.val, f.property, rfl⟩⟩, ?_, ?_⟩
    · change x - (f.val + t) + t ∈ A
      simpa only [sub_add_eq_sub_sub, sub_add_cancel] using hf
    · intro g hg
      obtain ⟨g', hg', he⟩ := List.mem_map.mp g.property
      have hgA : x - g' ∈ A := by
        change x - g.val + t ∈ A at hg
        simpa only [← he, sub_add_eq_sub_sub, sub_add_cancel] using hg
      have hgf := congrArg Subtype.val (hu ⟨g', hg'⟩ hgA)
      apply Subtype.ext
      change g.val = f.val + t
      rw [← he]
      exact congrArg (· + t) hgf

end TranslationTiling
