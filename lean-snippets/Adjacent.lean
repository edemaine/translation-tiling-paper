def Adjacent (a b : Point) : Prop :=
  ∑ i, |a i - b i| = 1
