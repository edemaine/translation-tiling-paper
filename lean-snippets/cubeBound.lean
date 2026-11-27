noncomputable def cubeBound (n : ℕ) : ℝ :=
  if n ≤ 1 then 2 ^ 2055 else
    (n + 4) ^ (5 * Real.logb 2 (Real.logb 2 (n + 4)) +
      5 * Real.logb 2 (Real.logb 2 (Real.logb 2 (n + 4))) +
      330 + 1322 / Real.logb 2 (n + 4))
