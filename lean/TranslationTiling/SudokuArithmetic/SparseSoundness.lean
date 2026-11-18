import TranslationTiling.SudokuArithmetic.SparseRecovery
import TranslationTiling.Proofs.CanonicalLineRule

namespace TranslationTiling.Sudoku.Sparse
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem canonical_rectangle {T : LeanWang.TileSet} {W : Board T} (hW : LineRule W)
    (w h : ℕ) {Bₚ : ZMod p} {Bᵩ : ZMod q}
    (hₚ : CanonicalP W Bₚ w)
    (hᵩ : CanonicalQ W Bᵩ h) :
    ValidRectangle T w h (fun u v => W.tile 0 (height u.val v.val)) := by
  constructor
  · intro u v hu
    have hh := canonical_adjacent_rows hW hₚ hᵩ (height u.val v.val)
      (height_ne_zero _ _) (by rw [height_valuation_p]; omega)
      (by rw [height_valuation_q]; exact v.isLt)
    simpa only [height_horizontal] using hh.1
  · intro u v hv
    have hh := canonical_adjacent_rows hW hₚ hᵩ (height u.val v.val)
      (height_ne_zero _ _) (by rw [height_valuation_p]; exact u.isLt)
      (by rw [height_valuation_q]; omega)
    simpa only [height_vertical] using hh.2

theorem exists_valid_rectangle {T : LeanWang.TileSet} {W : Board T}
    (hW : LineRule W) (hcols : Nonconstant W) (w h : ℕ) :
    ∃ σ : Fin w → Fin h → LeanWang.TileIn T, ValidRectangle T w h σ := by
  obtain ⟨D, E, Bₚ, Bᵩ, hp, hq, hₚ, hᵩ⟩ := finite_structure hW hcols w h
  exact ⟨_, canonical_rectangle (reparametrize_lineRule hW 1 D E) w h ⟨hp, hₚ⟩ ⟨hq, hᵩ⟩⟩

/-- Soundness after retaining only the three Wang-decoration columns. -/
theorem soundness (T : LeanWang.TileSet) (W : Board T)
    (hW : LineRule W) (hcols : Nonconstant W) : LeanWang.TilesPlane T := by
  apply LeanWang.tilesPlane_of_cofinal_tileableSquares
  intro n
  obtain ⟨σ, hσ⟩ := exists_valid_rectangle hW hcols n n
  refine ⟨n, le_rfl, fun i j => (σ i j).val, ?_⟩
  exact ⟨fun i j => (σ i j).property, hσ.1, hσ.2⟩


/-- The three-decoration rule has exactly the Wang-tilability instances. -/
theorem wang_iff (T : LeanWang.TileSet) :
    LeanWang.TilesPlane T ↔ ∃ W : Board T, LineRule W ∧ Nonconstant W := by
  constructor
  · intro hT
    obtain ⟨τ,hτ⟩ := (wang_plane_iff_quadrant T).mp hT
    let W := Sudoku.canonical τ (τ (0,0))
    refine ⟨restrict W, restrict_lineRule (Sudoku.canonical_lineRule τ hτ (τ (0,0))), ?_⟩
    have hc := Sudoku.canonical_nonconstantColumns τ (τ (0,0))
    exact ⟨fun n => hc.1 ⟨n.val,by have := n.isLt; change n.val<16; omega⟩,
      fun n => hc.2 n⟩
  · rintro ⟨W,hw,hc⟩
    exact soundness T W hw hc

end
end TranslationTiling.Sudoku.Sparse
