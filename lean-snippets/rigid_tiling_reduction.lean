theorem rigid_tiling_reduction (d : ℕ) (hd : 3 ≤ d) :
  ∃ f : LeanWang.TileSet → Prototile d, Computable f ∧
    ∀ T, f T ≠ [] ∧ Connected (f T) ∧
      (LeanWang.TilesPlane T ↔ Tiles (f T)) ∧
      (∀ motions : Set (Motion d), translations ⊆ motions →
        (Tiles (f T) ↔ RealTiles (f T) motions)) ∧
      ((f T).length : ℝ) ≤ (2 : ℝ) ^ (10 * (d + 1) ^ 2) * (max (((T.length : ℝ) + 4) ^
        (312 * Real.logb 2 (Real.logb 2 ((T.length : ℝ) + 4)))) ((2 : ℝ)^2392)) := ...
