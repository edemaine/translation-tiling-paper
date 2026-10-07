import TranslationTiling.Proofs.Basic
import Mathlib.Algebra.Group.Subgroup.Ker

namespace TranslationTiling

variable {G B : Type*} [AddCommGroup G] [AddCommGroup B]

/-- The graph equation is exactly bijectivity of the projection on the translation set. -/
theorem graph_equation_iff (π : G →+ B) (hπ : Function.Surjective π) (A : Set G) :
    ExactTiling A (π.ker : Set G) ↔ Function.Bijective (fun a : A => π a.val) := by
  constructor
  · intro h
    constructor
    · intro a b he
      have hk : a.val - b.val ∈ π.ker := by
        change π (a.val - b.val) = 0
        simp [map_sub, he]
      have hsum : (a.val + 0 : G) = b.val + (a.val - b.val) := by abel
      have hp : (a, (⟨0, π.ker.zero_mem⟩ : π.ker)) = (b, ⟨a.val - b.val, hk⟩) :=
        h.1 hsum
      exact congrArg Prod.fst hp
    · intro b
      obtain ⟨x, hx⟩ := hπ b
      obtain ⟨⟨a, f⟩, haf⟩ := h.2 x
      refine ⟨a, ?_⟩
      have hf : π f.val = 0 := f.property
      rw [← hx, ← haf, map_add, hf, add_zero]
  · intro h
    constructor
    · rintro ⟨a, f⟩ ⟨a', f'⟩ he
      have ha : a = a' := h.1 (by
        have hp := congrArg π he
        simpa only [map_add, show π f.val = 0 from f.property,
          show π f'.val = 0 from f'.property, add_zero] using hp)
      subst a'
      exact Prod.ext rfl (Subtype.ext (add_left_cancel he))
    · intro x
      obtain ⟨a, ha⟩ := h.2 (π x)
      have hf : x - a.val ∈ π.ker := by
        change π (x - a.val) = 0
        simp [map_sub, ha]
      exact ⟨(a, ⟨x - a.val, hf⟩), by change a.val + (x - a.val) = x; abel⟩

end TranslationTiling
