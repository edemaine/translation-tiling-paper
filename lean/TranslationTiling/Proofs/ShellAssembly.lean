import TranslationTiling.Proofs.Basic

namespace TranslationTiling

section
variable {H G : Type*} [AddCommGroup H] [AddCommGroup G]

def Assembly (ι : H →+ G) (E : Set H) (S : Set G) : Set G :=
  {v | ∃ f ∈ E, ∃ s ∈ S, v = ι f + s}

private theorem assembly_unique (ι : H →+ G) (hi : Function.Injective ι)
    {S : Set G} (hs : ExactTiling (Set.range ι) S)
    {f g : H} {s t : G} (hS : s ∈ S) (hT : t ∈ S)
    (he : ι f + s = ι g + t) : f = g ∧ s = t := by
  have h := hs.1 (a₁ := (⟨ι f, ⟨f, rfl⟩⟩, ⟨s, hS⟩))
    (a₂ := (⟨ι g, ⟨g, rfl⟩⟩, ⟨t, hT⟩)) he
  exact ⟨hi (congrArg (fun p => p.1.val) h), congrArg (fun p => p.2.val) h⟩

/-- The arbitrary-tiling part of Kim's assembly argument, abstracted from its geometry.
The shell is a fundamental domain for an embedded lattice, and every shell tiling
has a coset of that lattice as its translation set. -/
theorem shell_assembly_iff (ι : H →+ G) (hi : Function.Injective ι)
    (E : Set H) (S : Set G) (hs : ExactTiling (Set.range ι) S)
    (rigid : ∀ C : Set G, ExactTiling C S → ∃ t, C = {c | ∃ z, c = t + ι z}) :
    (∃ A : Set H, ExactTiling A E) ↔
      ∃ B : Set G, ExactTiling B (Assembly ι E S) := by
  constructor
  · rintro ⟨A, ha⟩
    refine ⟨ι '' A, (exactTiling_iff _ _).mpr ?_⟩
    intro x
    obtain ⟨s, hxs, hus⟩ := (exactTiling_iff _ _).mp hs x
    obtain ⟨h, hh⟩ := hxs
    obtain ⟨f, hf, huf⟩ := (exactTiling_iff _ _).mp ha h
    let v : Assembly ι E S := ⟨ι f.val + s.val, f.val, f.property, s.val, s.property, rfl⟩
    refine ⟨v, ?_, ?_⟩
    · refine ⟨h - f.val, hf, ?_⟩
      change ι (h - f.val) = x - (ι f.val + s.val)
      rw [map_sub, hh]
      abel
    · intro w hw
      obtain ⟨g, hg, t, ht, hew⟩ := w.property
      obtain ⟨a, ha', hea⟩ := hw
      have hxt : x - t ∈ Set.range ι := by
        refine ⟨a + g, ?_⟩
        rw [map_add, hea, hew]
        abel
      have hts : t = s.val := congrArg Subtype.val (hus ⟨t, ht⟩ hxt)
      have hga : h - g = a := by
        apply hi
        rw [map_sub, hh, hea, hew, hts]
        abel
      have hgf : g = f.val := congrArg Subtype.val
        (huf ⟨g, hg⟩ (by change h - g ∈ A; rw [hga]; exact ha'))
      apply Subtype.ext
      change w.val = ι f.val + s.val
      rw [hew, hgf, hts]
  · rintro ⟨B, hb⟩
    let C : Set G := {c | ∃ a ∈ B, ∃ f ∈ E, c = a + ι f}
    have hc : ExactTiling C S := by
      constructor
      · rintro ⟨c, s⟩ ⟨c', s'⟩ he
        obtain ⟨a, ha, f, hf, hcf⟩ := c.property
        obtain ⟨a', ha', f', hf', hcf'⟩ := c'.property
        let v : Assembly ι E S := ⟨ι f + s.val, f, hf, s.val, s.property, rfl⟩
        let v' : Assembly ι E S := ⟨ι f' + s'.val, f', hf', s'.val, s'.property, rfl⟩
        have he' : a + v.val = a' + v'.val := by
          change c.val + s.val = c'.val + s'.val at he
          dsimp [v, v']
          rw [hcf, hcf'] at he
          simpa only [add_assoc] using he
        have hp := hb.1 (a₁ := (⟨a, ha⟩, v)) (a₂ := (⟨a', ha'⟩, v')) he'
        have haa : a = a' := congrArg (fun p => p.1.val) hp
        have hv : ι f + s.val = ι f' + s'.val := congrArg (fun p => p.2.val) hp
        obtain ⟨hff, hss⟩ := assembly_unique ι hi hs s.property s'.property hv
        apply Prod.ext
        · apply Subtype.ext
          rw [hcf, hcf', haa, hff]
        · exact Subtype.ext hss
      · intro x
        obtain ⟨⟨a, v⟩, hx⟩ := hb.2 x
        obtain ⟨f, hf, s, hS, hv⟩ := v.property
        refine ⟨(⟨a.val + ι f, a.val, a.property, f, hf, rfl⟩, ⟨s, hS⟩), ?_⟩
        change (a.val + ι f) + s = x
        change a.val + v.val = x at hx
        simpa only [hv, add_assoc] using hx
    obtain ⟨t, hC⟩ := rigid C hc
    obtain ⟨⟨_, s₀⟩, _⟩ := hs.2 0
    refine ⟨{a | t + ι a ∈ B}, (exactTiling_iff _ _).mpr ?_⟩
    intro x
    let y := t + ι x + s₀.val
    obtain ⟨v, hv, huv⟩ := (exactTiling_iff _ _).mp hb y
    obtain ⟨f, hf, s, hS, he⟩ := v.property
    have hcs : y - s ∈ C := by
      refine ⟨y - v.val, hv, f, hf, ?_⟩
      rw [he]
      abel
    have hxC : y - s₀.val ∈ C := by
      rw [hC]
      exact ⟨x, by dsimp [y]; abel⟩
    obtain ⟨su, _, hu⟩ := (exactTiling_iff _ _).mp hc y
    have hss : s = s₀.val := congrArg Subtype.val
      ((hu ⟨s, hS⟩ hcs).trans (hu s₀ hxC).symm)
    refine ⟨⟨f, hf⟩, ?_, ?_⟩
    · change t + ι (x - f) ∈ B
      convert hv using 1
      rw [he, hss, map_sub]
      dsimp [y]
      abel
    · intro g hg
      have hvg : y - (ι g.val + s₀.val) ∈ B := by
        change t + ι (x - g.val) ∈ B at hg
        convert hg using 1
        rw [map_sub]
        dsimp [y]
        abel
      have hgv := congrArg Subtype.val (huv
        ⟨ι g.val + s₀.val, g.val, g.property, s₀.val, s₀.property, rfl⟩ hvg)
      rw [he, hss] at hgv
      exact Subtype.ext (hi (add_right_cancel hgv))

end
end TranslationTiling
