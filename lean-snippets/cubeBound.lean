noncomputable def cubeBound (n : ℕ) : ℝ :=
  if n ≤ 1 then 2 ^ 2056 else
    (n + 4) ^ (5 * Real.logb 2 (Real.logb 2 (n + 4)) +
      5 * Real.logb 2 (Real.logb 2 (Real.logb 2 (n + 4))) + 842)
