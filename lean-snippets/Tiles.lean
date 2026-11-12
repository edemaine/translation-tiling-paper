def Tiles {d : ℕ} (P : Prototile d) : Prop :=
  ∃ T : Set (Point d), ∀ x : Point d, ∃! t ∈ T, x - t ∈ P
