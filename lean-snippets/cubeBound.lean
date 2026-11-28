noncomputable def cubeBound (n : ℕ) : ℝ :=
  if n ≤ 1 then 2 ^ 2055 else
    (n + 4) ^ (4.986901 * (Real.logb 2 (Real.logb 2 (n + 4)) +
      Real.logb 2 (Real.logb 2 (Real.logb 2 (n + 4)))) +
      247 + 1539 / Real.logb 2 (n + 4))
