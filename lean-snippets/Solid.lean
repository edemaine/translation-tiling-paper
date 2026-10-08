def Solid (P : Prototile) : Set (Fin 3 → ℝ) :=
  {x | ∃ p ∈ P, x - ![(p.1 : ℝ), p.2.1, p.2.2] ∈ Set.Icc 0 1}
