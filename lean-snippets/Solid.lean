def Solid {d : ℕ} (P : Prototile d) : Set (RealPoint d) :=
  {x | ∃ p ∈ P, ∀ i, p i ≤ x i ∧ x i ≤ p i + 1}
