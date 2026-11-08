import TranslationTiling.FiniteCompiler.BitSystem
import TranslationTiling.FiniteCompiler.ExplicitDegrees
import TranslationTiling.Compiler.BitChannelSize

set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

/-! # An end-to-end `n^O(log log n)` connected-polycube bound

The constant is uniform in the number of distinct Wang tiles. The theorem
includes nonemptiness, face connectedness, and both tilability directions.
-/

namespace TranslationTiling.Compiler.Size

open scoped Classical
noncomputable section

theorem tileIn_card (T : LeanWang.TileSet) [Fintype (LeanWang.TileIn T)] :
    Fintype.card (LeanWang.TileIn T) = T.toFinset.card := by
  let e : LeanWang.TileIn T ≃ ↥T.toFinset := {
    toFun := fun t => ⟨t.val, List.mem_toFinset.mpr t.property⟩
    invFun := fun t => ⟨t.val, List.mem_toFinset.mp t.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  exact (Fintype.card_congr e).trans (Fintype.card_coe _)

/-- The full bit-channel reduction with a numerical binary-exponent coefficient. -/
theorem exists_connected_tile_quasipolynomial_explicit_bound (T : LeanWang.TileSet) :
    ∃ P : Tile 3, P ≠ [] ∧ FaceConnected P ∧
      (LeanWang.TilesPlane T ↔ TranslationTiling.Tiles P) ∧
      cubeCount P ≤ 2 ^ (10 ^ 60 * (Nat.log 2 (T.toFinset.card + 2) + 1) *
        (Nat.log 2 (Nat.log 2 (T.toFinset.card + 2) + 2) + 1)) := by
  letI : Fintype (LeanWang.TileIn T) := Fintype.ofFinite _
  let l := Nat.log 2 (T.toFinset.card + 2) + 1
  have hl : 0 < l := by dsimp [l]; omega
  have hcard : Fintype.card (LeanWang.TileIn T) ≤ 2 ^ l := by
    rw [tileIn_card]
    exact (by omega : T.toFinset.card ≤ T.toFinset.card + 2).trans
      (Nat.lt_pow_succ_log_self (by decide : 1 < 2) _).le
  obtain ⟨code, hc⟩ := BitChannels.exists_bit_code (LeanWang.TileIn T) l hcard
  obtain ⟨P, hP, hconn, hiff, hcubes⟩ :=
    FiniteCompiler.Size.exists_connected_tile_channel_bound_of_degrees
      FiniteCompiler.BitSystem.alphabet Sudoku.Width (10 ^ 32) (10 ^ 6)
      FiniteCompiler.Size.bit_parameterBase_explicit_degree
      FiniteCompiler.Size.geometryPolynomial_explicit_degree
      (FiniteCompiler.BitSystem.system code hl) T rfl
      (FiniteCompiler.BitSystem.slope_bound code hl)
      (fun E => FiniteCompiler.BitSystem.finite_system_iff_wang code hc hl E)
  have hlog := linear_channel_cap_le_exp_log_explicit Sudoku.Width
    (12 * 10 ^ 32 * 10 ^ 6) l (by omega)
  have hcoeff : (Sudoku.Width + 4) * (12 * 10 ^ 32 * 10 ^ 6) * (Sudoku.Width + 2) ≤
      10 ^ 60 := by norm_num [Sudoku.Width, Sudoku.p, Sudoku.q]
  have hexp := Nat.mul_le_mul_right (l * (Nat.log 2 (l + 1) + 1)) hcoeff
  have hbound := hcubes.trans (hlog.trans (Nat.pow_le_pow_right (by decide)
    (by simpa only [Nat.mul_assoc] using hexp)))
  refine ⟨P, hP, hconn, hiff, ?_⟩
  simpa only [l, Nat.mul_assoc, Nat.add_assoc] using hbound

/-- The same numerical estimate as a power of the number of tiles plus two. -/
theorem exists_connected_tile_quasipolynomial_explicit_power_bound (T : LeanWang.TileSet) :
    ∃ P : Tile 3, P ≠ [] ∧ FaceConnected P ∧
      (LeanWang.TilesPlane T ↔ TranslationTiling.Tiles P) ∧
      cubeCount P ≤ (T.toFinset.card + 2) ^
        (2 * 10 ^ 60 * (Nat.log 2 (Nat.log 2 (T.toFinset.card + 2) + 2) + 1)) := by
  obtain ⟨P, hP, hconn, hiff, hcubes⟩ := exists_connected_tile_quasipolynomial_explicit_bound T
  exact ⟨P, hP, hconn, hiff, hcubes.trans (exp_iterated_log_le_power (10 ^ 60) T.toFinset.card)⟩

/-- The coefficient is uniform in the number of distinct tiles, including zero. -/
theorem exists_connected_tile_quasipolynomial_bound :
    ∃ K : ℕ, ∀ T : LeanWang.TileSet,
      ∃ P : Tile 3, P ≠ [] ∧ FaceConnected P ∧
        (LeanWang.TilesPlane T ↔ TranslationTiling.Tiles P) ∧
        cubeCount P ≤ 2 ^ (K * (Nat.log 2 (T.toFinset.card + 2) + 1) *
          (Nat.log 2 (Nat.log 2 (T.toFinset.card + 2) + 2) + 1)) :=
  ⟨10 ^ 60, exists_connected_tile_quasipolynomial_explicit_bound⟩

/-- A numerical one-tile consequence of the full bit-channel construction. -/
theorem exists_connected_tile_one_quasipolynomial_bound (T : LeanWang.TileSet)
    (hT : T.toFinset.card = 1) :
    ∃ P : Tile 3, P ≠ [] ∧ FaceConnected P ∧
      (LeanWang.TilesPlane T ↔ TranslationTiling.Tiles P) ∧
      cubeCount P ≤ 2 ^ (4 * 10 ^ 60) := by
  obtain ⟨P, hP, hconn, hiff, hcubes⟩ := exists_connected_tile_quasipolynomial_explicit_bound T
  have hexp : 10 ^ 60 * (Nat.log 2 (1 + 2) + 1) *
      (Nat.log 2 (Nat.log 2 (1 + 2) + 2) + 1) = 4 * 10 ^ 60 := by norm_num [Nat.log]
  rw [hT, hexp] at hcubes
  exact ⟨P, hP, hconn, hiff, hcubes⟩

end
end TranslationTiling.Compiler.Size
