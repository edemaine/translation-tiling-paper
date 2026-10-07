import TranslationTiling.Definitions
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

namespace TranslationTiling

/-- The Euclidean tile is the union of the closed integer unit cubes indexed by `F`. -/
def CubeUnion {d : ℕ} (F : Tile d) : Set (Fin d → ℝ) :=
  {x | ∃ f ∈ F, ∀ i, (f i : ℝ) ≤ x i ∧ x i ≤ (f i : ℝ) + 1}

/-- Coverage with multiplicity one almost everywhere, allowing real translations. -/
def RealTiles {d : ℕ} (F : Tile d) : Prop :=
  ∃ A : Set (Fin d → ℝ), ∀ᵐ x ∂MeasureTheory.volume,
    ∃! a : A, x - a.val ∈ CubeUnion F

end TranslationTiling
