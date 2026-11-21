theorem tiling_reduction (d : ℕ) (hd : 3 ≤ d) :
  ∃ f : LeanWang.TileSet → Prototile d, Computable f ∧
    ∀ T, f T ≠ [] ∧ Connected (f T) ∧ (LeanWang.TilesPlane T ↔ Tiles (f T)) ∧
      ((f T).length : ℝ) ≤ max (((T.length : ℝ) + 4) ^
        ((441651 / 50000 : ℝ) * (Real.logb 2 (Real.logb 2 ((T.length : ℝ) + 4)) +
          Real.logb 2 (Real.logb 2 (Real.logb 2 ((T.length : ℝ) + 4)))) + 570))
        ((2 : ℝ)^2392) := ...
