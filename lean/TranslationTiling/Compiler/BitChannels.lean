import TranslationTiling.Compiler.Symbols
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Nat.Log

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

/-! # Splitting finite symbols into bit channels

These lemmas encode finite alphabets by short bit strings and recover an array
from a bit-channel line rule. `FiniteCompiler.BitSystem` uses them in the
end-to-end construction proved in `QuasipolynomialBound.lean`.
-/

namespace TranslationTiling.Compiler.BitChannels

open scoped Classical
noncomputable section

theorem exists_bit_code (α : Type*) [Fintype α] (l : ℕ)
    (h : Fintype.card α ≤ 2 ^ l) :
    ∃ code : α → (Fin l → Bool), Function.Injective code := by
  have hc : Fintype.card (Fin l → Bool) = 2 ^ l := by simp
  let e : (Fin l → Bool) ≃ Fin (2 ^ l) :=
    (Fintype.equivFin _).trans (finCongr hc)
  let f : α → Fin (2 ^ l) := fun a => Fin.castLE h (Fintype.equivFin α a)
  refine ⟨fun a => e.symm (f a), e.symm.injective.comp ?_⟩
  intro a b hab
  apply (Fintype.equivFin α).injective
  exact Fin.ext (congrArg (fun z : Fin (2 ^ l) => z.val) hab)

theorem exists_log_bit_code (α : Type*) [Fintype α] :
    ∃ code : α → (Fin (Nat.log 2 (Fintype.card α + 2) + 1) → Bool),
      Function.Injective code :=
  exists_bit_code α _ ((by omega : Fintype.card α ≤ Fintype.card α + 2).trans
    (Nat.lt_pow_succ_log_self (by decide : 1 < 2) _).le)

def splitCode {A α κ : Type*} (code : α → κ → Bool) (s : A × α) : κ → A × Bool :=
  fun k => (s.1, code s.2 k)

theorem splitCode_injective {A α κ : Type*} [Nonempty κ]
    {code : α → κ → Bool} (hc : Function.Injective code) :
    Function.Injective (splitCode (A := A) code) := by
  intro a b hab
  obtain ⟨k⟩ := ‹Nonempty κ›
  apply Prod.ext
  · exact congrArg (fun z : A × Bool => z.1) (congrFun hab k)
  · apply hc
    funext j
    exact congrArg (fun z : A × Bool => z.2) (congrFun hab j)

def encodeWord {ι α κ β : Type*} (code : α → κ → β) (w : ι → α) : ι × κ → β :=
  fun j => code (w j.1) j.2

def EncodedAllowed {ι α κ β : Type*} (code : α → κ → β) (allowed : Set (ι → α))
    (v : ι × κ → β) : Prop :=
  ∃ w ∈ allowed, encodeWord code w = v

/-- A section where all line values equal `m` makes pointwise decoding coherent
along each original column. Repeated bit channels may have the same line map. -/
theorem array_of_encoded_line_rule {ι α κ β X R : Type*}
    (code : α → κ → β) (hc : Function.Injective code) (allowed : Set (ι → α))
    (line : ι → X → R) (sectionAt : R → X)
    (hs : ∀ i m, line i (sectionAt m) = m)
    (v : ι × κ → R → β)
    (hv : ∀ x, EncodedAllowed code allowed (fun j => v j (line j.1 x))) :
    ∃ w : ι → R → α,
      (∀ i m k, code (w i m) k = v (i, k) m) ∧
      ∀ x, (fun i => w i (line i x)) ∈ allowed := by
  choose rows hrows hbits using fun m => hv (sectionAt m)
  refine ⟨fun i m => rows m i, ?_, ?_⟩
  · intro i m k
    have h := congrFun (hbits m) (i, k)
    simpa only [encodeWord, hs] using h
  · intro x
    obtain ⟨row, hrow, hrowbits⟩ := hv x
    have heq : (fun i => rows (line i x) i) = row := by
      funext i
      apply hc
      funext k
      have h₁ := congrFun (hbits (line i x)) (i, k)
      have h₂ := congrFun hrowbits (i, k)
      simp only [encodeWord, hs] at h₁ h₂
      exact h₁.trans h₂.symm
    rw [heq]
    exact hrow

end
end TranslationTiling.Compiler.BitChannels
