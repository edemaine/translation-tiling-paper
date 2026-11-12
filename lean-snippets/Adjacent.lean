def Adjacent {d : ℕ} (a b : Point d) : Prop :=
  ∑ i, |a i - b i| = 1
