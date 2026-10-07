import TranslationTiling.Definitions
import LeanWang.Compactness

namespace TranslationTiling

/-- Quadrant solvability and plane solvability coincide for the imported Wang objects. -/
theorem wang_plane_iff_quadrant (T : LeanWang.TileSet) :
    LeanWang.TilesPlane T ↔
      ∃ τ : ℕ × ℕ → LeanWang.TileIn T, LeanWang.ValidQuarterTiling T τ := by
  constructor
  · rintro ⟨τ, hh, hv⟩
    refine ⟨fun p => τ (p.1, p.2), ?_, ?_⟩
    · intro p
      exact hh (p.1, p.2)
    · intro p
      exact hv (p.1, p.2)
  · rintro ⟨τ, hh, hv⟩
    apply LeanWang.tilesPlane_of_cofinal_tileableSquares
    intro n
    refine ⟨n, le_rfl, fun i j => (τ (i.val, j.val)).val, ?_⟩
    exact ⟨fun i j => (τ (i.val, j.val)).property,
      fun i j _ => hh (i.val, j.val), fun i j _ => hv (i.val, j.val)⟩

end TranslationTiling
