theorem real_tiling_reduction (d : ℕ) (hd : 3 ≤ d) :
  ∃ f : LeanWang.TileSet → Prototile d, Computable f ∧
    ∀ T, f T ≠ [] ∧ Connected (f T) ∧
      (LeanWang.TilesPlane T ↔ Tiles (f T)) ∧
      (Tiles (f T) ↔ RealTiles (f T) translations) ∧
      ((f T).length : ℝ) ≤ max (((T.length : ℝ) + 4) ^
        ((88331 / 5000 : ℝ) * Real.logb 2 (Real.logb 2 ((T.length : ℝ) + 4)) + 561))
        ((2 : ℝ)^2392) := ...
