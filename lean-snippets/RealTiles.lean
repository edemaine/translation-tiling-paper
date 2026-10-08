def RealTiles (P : Prototile) : Prop :=
  ∃ A : Set (Fin 3 → ℝ), ∀ᵐ x ∂MeasureTheory.volume, ∃! a : A, x - a.val ∈ Solid P
