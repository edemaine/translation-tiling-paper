noncomputable def cubeBound (n : ℕ) : ℝ :=
  if n ≤ 1 then 2 ^ 2065 else
    (n + 4) ^ (5 * Real.logb 2 (Real.logb 2 (n + 4)) +
      65 * Real.logb 2 (Real.logb 2 (Real.logb 2 (n + 4))) + 2700)
