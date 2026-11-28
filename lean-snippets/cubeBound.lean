noncomputable def cubeBound (n : ℕ) : ℝ :=
  if n ≤ 1 then 2^2055 else
    (n + 2) ^ (4.986901 * (Real.logb 2 (Real.logb 2 (n + 2)) +
      Real.logb 2 (Real.logb 2 (Real.logb 2 (n + 2)))) + 172) * (2 : ℝ) ^ 1844
