import TranslationTiling.Definitions
import Mathlib.Tactic.Abel

namespace TranslationTiling

variable {G : Type*} [AddCommGroup G]

/-- A tile point uniquely determines the translation in a representation of `x`. -/
theorem exactTiling_iff (A F : Set G) :
    ExactTiling A F ↔ ∀ x, ∃! f : F, x - f.val ∈ A := by
  constructor
  · intro h x
    obtain ⟨⟨a, f⟩, hx⟩ := h.2 x
    refine ⟨f, ?_, ?_⟩
    · simp [← hx]
    · intro g hg
      have he : ((⟨x - g.val, hg⟩ : A), g) = (a, f) := by
        apply h.1
        change x - g.val + g.val = a.val + f.val
        simpa using hx.symm
      exact congrArg Prod.snd he
  · intro h
    constructor
    · rintro ⟨a, f⟩ ⟨b, g⟩ he
      obtain ⟨f₀, _, hu⟩ := h (a.val + f.val)
      have hf : a.val + f.val - f.val ∈ A := by simp
      have hg : a.val + f.val - g.val ∈ A := by
        change a.val + f.val = b.val + g.val at he
        simp [he]
      have hfg : f = g := (hu f hf).trans (hu g hg).symm
      subst g
      exact Prod.ext (Subtype.ext (add_right_cancel he)) rfl
    · intro x
      obtain ⟨f, hf, _⟩ := h x
      exact ⟨(⟨x - f.val, hf⟩, f), sub_add_cancel x f.val⟩

theorem exactTiling_tile_nonempty {A F : Set G} (h : ExactTiling A F) : F.Nonempty := by
  obtain ⟨⟨_, f⟩, _⟩ := h.2 0
  exact ⟨f.val, f.property⟩

theorem tiles_nonempty {d : ℕ} {F : Tile d} (h : Tiles F) : F ≠ [] := by
  obtain ⟨A, hA⟩ := h
  obtain ⟨f, hf⟩ := exactTiling_tile_nonempty hA
  intro he
  simp [he] at hf

@[simp] theorem not_tiles_nil (d : ℕ) : ¬ Tiles ([] : Tile d) := by
  intro h
  exact tiles_nonempty h rfl

/-- Duplicating or reordering the input list cannot change tilability. -/
theorem tiles_of_same_members {d : ℕ} {F F' : Tile d}
    (h : ∀ f, f ∈ F ↔ f ∈ F') : Tiles F ↔ Tiles F' := by
  have he : {f | f ∈ F} = {f | f ∈ F'} := Set.ext h
  simp only [Tiles, he]

/-- Transport exact coverage along an additive equivalence. -/
theorem exactTiling_transport {H : Type*} [AddCommGroup H] (e : G ≃+ H)
    {A F : Set G} (h : ExactTiling A F) : ExactTiling (e '' A) (e '' F) := by
  rw [exactTiling_iff] at h ⊢
  intro x
  obtain ⟨f, hf, hu⟩ := h (e.symm x)
  refine ⟨⟨e f.val, Set.mem_image_of_mem _ f.property⟩, ?_, ?_⟩
  · refine ⟨e.symm x - f.val, hf, ?_⟩
    simp
  · intro g hg
    obtain ⟨g', hg', he⟩ := g.property
    have ha : e.symm x - g' ∈ A := by
      obtain ⟨a, ha, hea⟩ := hg
      have heq : a = e.symm x - g' := by
        apply e.injective
        simpa [map_sub, he] using hea
      rwa [← heq]
    have hgf := hu ⟨g', hg'⟩ ha
    apply Subtype.ext
    rw [← he]
    exact congrArg e (congrArg Subtype.val hgf)

end TranslationTiling
