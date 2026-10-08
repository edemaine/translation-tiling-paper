def RealTiles (P : Prototile) : Prop :=
  ∃ T : Set RealPoint, ∀ᵐ x ∂MeasureTheory.volume, ∃! t : RealPoint, t ∈ T ∧ x - t ∈ Solid P
