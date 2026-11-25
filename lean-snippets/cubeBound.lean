noncomputable def cubeBound (n : ℕ) : ℝ :=
  max ((n + 4) ^
    (5 * Real.logb 2 (Real.logb 2 (n + 4)) +
      65 * Real.logb 2 (Real.logb 2 (Real.logb 2 (n + 4)))) *
    n ^ 8400) (2 ^ 2067)
