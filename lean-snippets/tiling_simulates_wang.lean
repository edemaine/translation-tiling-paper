theorem tiling_simulates_wang :
  ∀ T : LeanWang.TileSet,
    ∃ P : Prototile, P ≠ [] ∧ Connected P ∧
      (LeanWang.TilesPlane T ↔ Tiles P) ∧
      (P.length : ℝ) ≤ ((T.length : ℝ) + 4) ^
        (10 ^ 61 * Real.logb 2 (Real.logb 2 ((T.length : ℝ) + 4))) := ...
