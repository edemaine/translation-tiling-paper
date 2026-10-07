/- Adapted from openai/math, OAI/Geometry/PeriodicTiling, commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a. Apache 2.0; see
third_party/openai-math.LICENSE. Namespace and imports changed for Lean 4.31. -/
import TranslationTiling.Proofs.Basic
import Mathlib.Data.Finset.Basic

namespace TranslationTiling.Stacking

universe uG
variable {G : Type uG} [AddCommGroup G]

/-- The finite-set version, with the tile point first in each pair. -/
def Covers (F : Finset G) (A : Set G) : Prop :=
  Function.Bijective (fun p : ↥F × A => p.1.val + p.2.val)

theorem covers_iff_unique_tile {F : Finset G} {A : Set G} :
    Covers F A ↔ ∀ x : G, ∃! f : ↥F, x - (f : G) ∈ A := by
  constructor
  · intro h x
    obtain ⟨⟨f, a⟩, hx⟩ := h.2 x
    have hfa : x - (f : G) = (a : G) := by
      rw [← hx]
      simp
    refine ⟨f, ?_, ?_⟩
    · change x - (f : G) ∈ A
      rw [hfa]
      exact a.property
    · intro g hg
      have hp : (g, (⟨x - (g : G), hg⟩ : A)) = (f, a) := by
        apply h.1
        change (g : G) + (x - (g : G)) = (f : G) + (a : G)
        simpa [add_comm] using hx.symm
      exact congrArg Prod.fst hp
  · intro h
    constructor
    · rintro ⟨f, a⟩ ⟨g, b⟩ he
      obtain ⟨f₀, _hf₀, huniq⟩ := h ((f : G) + (a : G))
      have hf : (f : G) + (a : G) - (f : G) ∈ A := by
        simp [a.property]
      have hg : (f : G) + (a : G) - (g : G) ∈ A := by
        change (f : G) + (a : G) = (g : G) + (b : G) at he
        rw [he]
        simp [b.property]
      have hfg : f = g := (huniq f hf).trans (huniq g hg).symm
      cases hfg
      have hab : a = b := Subtype.ext (add_left_cancel he)
      exact Prod.ext rfl hab
    · intro x
      obtain ⟨f, hf, _huniq⟩ := h x
      refine ⟨(f, ⟨x - (f : G), hf⟩), ?_⟩
      change (f : G) + (x - (f : G)) = x
      simp

theorem covers_iff_exactTiling {F : Finset G} {A : Set G} :
    Covers F A ↔ ExactTiling A (F : Set G) := by
  rw [covers_iff_unique_tile, exactTiling_iff]
  rfl

end TranslationTiling.Stacking
