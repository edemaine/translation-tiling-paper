def Tiles (P : Prototile) : Prop :=
  ∃ T : Set Point, ∀ x : Point, ∃! t : Point, t ∈ T ∧ x - t ∈ P
