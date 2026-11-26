noncomputable def cubeBound (n : ℕ) : ℝ :=
  if n ≤ 1 then 2 ^ 2059 else
    (n + 4) ^ (5 * Real.logb 2 (Real.logb 2 (n + 4)) +
      7.000001 * Real.logb 2 (Real.logb 2 (Real.logb 2 (n + 4))) + 900)
