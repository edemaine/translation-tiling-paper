/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in third_party/openai-math.LICENSE.
Adapted from openai/math, commit adc7f1241b42e322a6451854ab7e4b4c146bf78a.
-/
import Mathlib.GroupTheory.Index
import Mathlib.Data.Finset.Basic

namespace TranslationTiling

noncomputable section

universe u

namespace Planar

abbrev Lattice (d : ℕ) := Fin d → ℤ

section AdditiveGroup

variable {G : Type u} [AddCommGroup G]

def Tiles (F : Finset G) (A : Set G) : Prop :=
  Function.Bijective (fun p : ↥F × A => (p.1 : G) + (p.2 : G))

def Period (A : Set G) (v : G) : Prop :=
  ∀ x : G, x + v ∈ A ↔ x ∈ A

def FullyPeriodic (A : Set G) : Prop :=
  ∃ P : AddSubgroup G, P.FiniteIndex ∧ ∀ v ∈ P, Period A v

end AdditiveGroup

end Planar

end

end TranslationTiling
