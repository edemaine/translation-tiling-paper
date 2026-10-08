def Solid (P : Prototile) : Set RealPoint :=
  {x | ∃ p ∈ P, ∀ i, p i ≤ x i ∧ x i ≤ p i + 1}
