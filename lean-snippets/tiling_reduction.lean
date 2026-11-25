theorem tiling_reduction (d : ℕ) (hd : 3 ≤ d) :
  ∃ f : LeanWang.TileSet → Prototile d, Computable f ∧
    ∀ T, f T ≠ [] ∧ Connected (f T) ∧ (LeanWang.TilesPlane T ↔ Tiles (f T)) ∧
      ((f T).length : ℝ) ≤ cubeBound T.length := ...
