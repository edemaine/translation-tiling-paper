def translationsAndReflections {d : ℕ} : Set (Motion d) :=
  {f | ∃ t ∈ translations, ∃ p q : RealPoint d,
    f = t * EuclideanGeometry.reflection (AffineSubspace.perpBisector p q)}
