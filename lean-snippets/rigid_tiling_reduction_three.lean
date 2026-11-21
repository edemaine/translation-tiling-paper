theorem rigid_tiling_reduction_three :
  ∃ f : LeanWang.TileSet → Prototile 3, Computable f ∧
    ∀ T, f T ≠ [] ∧ Connected (f T) ∧
      (LeanWang.TilesPlane T ↔ Tiles (f T)) ∧
      (∀ motions : Set (Motion 3), translations ⊆ motions →
        (Tiles (f T) ↔ RealTiles (f T) motions)) ∧
      ((f T).length : ℝ) ≤ 64000 * (max (((T.length : ℝ) + 4) ^
        ((88331 / 5000 : ℝ) * Real.logb 2 (Real.logb 2 ((T.length : ℝ) + 4)) + 561))
        ((2 : ℝ)^2392)) := ...
