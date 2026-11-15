import TranslationTiling.FiniteCompiler.TightBounds

namespace TranslationTiling.FiniteCompiler.TightSize
open Compiler.Size Size
open scoped Classical
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

theorem four_layer_geometry_bound {C b : ℕ} (hC : 596750≤C)
    (hb : b≤C^73) (hb2 : 2≤b) :
    (9*2^24*972*36*8003^4)*(Size.horizontalCap b)^4*(C^(34*C))^3≤C^(103*C) := by
  have hbig : 596750≤C := by simpa [Sudoku.Width,Sudoku.q] using hC
  have h1 : 1≤C := by omega
  have hH : Size.horizontalCap b≤C^15403 := by
    calc
      _ ≤ b^211 := horizontalCap_degree_211 b hb2
      _ ≤ (C^73)^211 := Nat.pow_le_pow_left hb _
      _ = _ := by rw [← pow_mul]
  have hk : 9*2^24*972*36*8003^4≤C^5 := by
    apply (by norm_num : 9*2^24*972*36*8003^4≤(2^19)^5).trans
    exact Nat.pow_le_pow_left (by norm_num; omega) _
  calc
    _ ≤ C^5*(C^15403)^4*(C^(34*C))^3 := Nat.mul_le_mul (Nat.mul_le_mul hk (Nat.pow_le_pow_left hH 4)) le_rfl
    _ = C^(102*C+61617) := by simp only [← pow_mul,← pow_add]; congr 1; ring
    _ ≤ _ := Nat.pow_le_pow_right h1 (by omega)

end
end TranslationTiling.FiniteCompiler.TightSize
