theorem tiling_reduction (d : ℕ) (hd : 3 ≤ d) :
  ∃ f : LeanWang.TileSet → Prototile d, Computable f ∧
    ∀ T, f T ≠ [] ∧ Connected (f T) ∧ (LeanWang.TilesPlane T ↔ Tiles (f T)) ∧
      ((f T).length : ℝ) ≤ ((T.length : ℝ) + 4) ^
        (5 * 10 ^ 6 * Real.logb 2 (Real.logb 2 ((T.length : ℝ) + 4))) := ...
