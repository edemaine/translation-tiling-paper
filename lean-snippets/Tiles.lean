def Tiles (P : Prototile) : Prop :=
  ∃ A : Set Point, ∀ x : Point, ∃! t : Point × Point, t.1 ∈ A ∧ t.2 ∈ P ∧ t.1 + t.2 = x
