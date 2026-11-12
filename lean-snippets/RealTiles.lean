def RealTiles {d : ℕ} (P : Prototile d) (motions : Set (Motion d)) : Prop :=
  ∃ T ⊆ motions, ∀ᵐ x ∂MeasureTheory.volume,
    ∃! f ∈ T, x ∈ f '' Solid P
