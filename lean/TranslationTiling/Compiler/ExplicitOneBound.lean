import TranslationTiling.Compiler.SmallOneParameters
import TranslationTiling.Compiler.DirectTestCount
import TranslationTiling.Compiler.ClosedGeometryBound
import TranslationTiling.Compiler.SimpleSizeBound

set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 1024

/-! # An explicit singly exponential one-tile bound

Polynomial bounds on the fixed useful primes, together with direct equation
counts, give `2^(10^100)` cubes for one distinct Wang tile. This specializes
the full reduction, without deciding the one-tile Wang problem separately.
-/

namespace TranslationTiling.Compiler.Size

open scoped Classical BigOperators
noncomputable section

private theorem two_exp_mono {a b : ℕ} (h : a ≤ b) : 2 ^ a ≤ 2 ^ b :=
  Nat.pow_le_pow_right (by decide) h

private theorem mul_exp_le {x y a b : ℕ} (hx : x ≤ 2 ^ a) (hy : y ≤ 2 ^ b) :
    x * y ≤ 2 ^ (a + b) := by
  simpa only [pow_add] using Nat.mul_le_mul hx hy

private theorem pow_exp_le {x a : ℕ} (hx : x ≤ 2 ^ a) (k : ℕ) :
    x ^ k ≤ 2 ^ (a * k) := by
  simpa only [pow_mul] using Nat.pow_le_pow_left hx k

private theorem add_exp_le {x y a b : ℕ} (hx : x ≤ 2 ^ a) (hy : y ≤ 2 ^ b) :
    x + y ≤ 2 ^ (max a b + 1) := by
  have hx' := hx.trans (two_exp_mono (le_max_left a b))
  have hy' := hy.trans (two_exp_mono (le_max_right a b))
  rw [pow_succ]
  omega

/-- Stacking and geometry cost only a constant factor in a common binary exponent. -/
theorem stack_geometry_exp {H V s e : ℕ} (he : 1024 ≤ e)
    (hH : H ≤ 2 ^ e) (hV : V ≤ 2 ^ e) (hs : s ≤ 2 ^ e) :
    geometryCap H (V * (2 * (8 * s ^ 5 + V + 3))) ≤ 2 ^ (100 * e) := by
  let M := V * (2 * (8 * s ^ 5 + V + 3))
  let S := 2 * (1000 * (2 * H + M + 1)) + 3
  have hM : M ≤ 2 ^ (7 * e) := by
    have h := mul_exp_le hV (mul_exp_le (by decide : 2 ≤ 2 ^ 1)
      (add_exp_le (add_exp_le (mul_exp_le (by decide : 8 ≤ 2 ^ 3)
        (pow_exp_le hs 5)) hV) (by decide : 3 ≤ 2 ^ 2)))
    exact h.trans (two_exp_mono (by omega))
  have hS : S ≤ 2 ^ (8 * e) := by
    have h := add_exp_le (mul_exp_le (by decide : 2 ≤ 2 ^ 1)
      (mul_exp_le (by decide : 1000 ≤ 2 ^ 10)
        (add_exp_le (add_exp_le (mul_exp_le (by decide : 2 ≤ 2 ^ 1) hH) hM)
          (by decide : 1 ≤ 2 ^ 0)))) (by decide : 3 ≤ 2 ^ 2)
    exact h.trans (two_exp_mono (by omega))
  have hcube := mul_exp_le (pow_exp_le hS 3)
    (pow_exp_le (add_exp_le (mul_exp_le (by decide : 3 ≤ 2 ^ 2)
      (pow_exp_le hS 3)) (by decide : 6 ≤ 2 ^ 3)) 3)
  exact hcube.trans (two_exp_mono (by omega))

theorem exists_one_parameterBudget (T : LeanWang.TileSet) (hT : T.length = 1) :
    ∃ E : EncodingParameters T, ParameterBudget E (2 ^ (10 ^ 8)) ∧
      (∀ i, E.a i ≤ 10 ^ 40 ∧ E.b i ≤ 10 ^ 40) ∧
      channelCount ≤ 2 ^ (10 ^ 8) ∧ labelsBound T.length ≤ 2 ^ (10 ^ 8) := by
  obtain ⟨E, hu, hp⟩ := exists_small_one_parameters T hT
  have hsmall : 10 ^ 40 ≤ 2 ^ (10 ^ 8) :=
    (by norm_num : 10 ^ 40 ≤ 2 ^ 1000).trans (two_exp_mono (by norm_num))
  have hN : residueModulus ≤ 10 ^ 40 := by
    norm_num [residueModulus_eq, Sudoku.Width, Sudoku.p, Sudoku.q]
  have hC : channelCount ≤ 10 ^ 40 := by
    norm_num [channelCount_eq, residueModulus_eq, Sudoku.Width, Sudoku.p, Sudoku.q]
  have hlabels : labelsBound T.length ≤ 10 ^ 40 := by
    norm_num [hT, labelsBound, arithmeticAlphabet, Sudoku.p, Sudoku.q]
  have hr (i : Channel T) : E.r i ≤ 2 ^ (10 ^ 8) := by
    have hc : Fintype.card (Label T i) ≤ 46621 := by
      simpa only [hT, labelsBound, arithmeticAlphabet, Sudoku.p, Sudoku.q] using label_card_le T i
    have hprime (j : Label T i) : E.digitPrime i j ≤ 2 ^ 1000 :=
      (hp i j).trans (by norm_num)
    rw [E.r_eq_prod]
    calc
      _ ≤ ∏ _j : Label T i, 2 ^ 1000 := Finset.prod_le_prod (fun j _ => hprime j)
      _ = (2 ^ 1000) ^ Fintype.card (Label T i) := by simp
      _ ≤ 2 ^ (1000 * Fintype.card (Label T i)) := pow_exp_le le_rfl _
      _ ≤ 2 ^ (1000 * 46621) := two_exp_mono (Nat.mul_le_mul_left 1000 hc)
      _ ≤ _ := two_exp_mono (by norm_num)
  refine ⟨E, ⟨?_, hN.trans hsmall, hr, fun i => (hu i).1.trans hsmall,
    fun i => (hu i).2.trans hsmall⟩, hu, hC.trans hsmall, hlabels.trans hsmall⟩
  exact (by norm_num : 2 ≤ 10 ^ 40).trans hsmall

/-- Propagate binary-exponent budgets while keeping the large powers symbolic. -/
theorem exists_connected_tile_of_exp_budget {T : LeanWang.TileSet} {E : EncodingParameters T}
    {b u k e : ℕ} (hb : ParameterBudget E b)
    (hu : ∀ i, E.a i ≤ u ∧ E.b i ≤ u) (hC : channelCount ≤ b)
    (hL : labelsBound T.length ≤ b) (hk : 1 ≤ k) (hbase : b ≤ 2 ^ k)
    (he : 1024 ≤ e) (hcountExp : k * testCountExponentFor u ≤ e)
    (hhor : 100 * k ≤ e) (hfinite : k * (4 * channelCount + 2) ≤ e) :
    ∃ P : Tile 3, P ≠ [] ∧ FaceConnected P ∧
      (LeanWang.TilesPlane T ↔ TranslationTiling.Tiles P) ∧
      cubeCount P ≤ 2 ^ (100 * e) := by
  have hcount : (testTiles E).card ≤ 2 ^ e :=
    (testTiles_card_le_direct hb hu hC hL).trans
      ((pow_exp_le hbase _).trans (two_exp_mono hcountExp))
  obtain ⟨m, hm, hcap, F, hF, hcorrect, hcoord⟩ :=
    exists_cyclic_tile_of_card_le hb (2 ^ e) hcount
  obtain ⟨P, hP, hconn, hiff, hcubes⟩ :=
    exists_bounded_connected_tile hm hcap F hF hcorrect hcoord
  have hH : horizontalCap b ≤ 2 ^ e :=
    (horizontal_exp hk hbase).trans (two_exp_mono hhor)
  have hV : finiteCap b ≤ 2 ^ e :=
    (pow_exp_le hbase _).trans (two_exp_mono hfinite)
  exact ⟨P, hP, hconn, hiff, hcubes.trans (stack_geometry_exp he hH hV le_rfl)⟩

/-- The explicit bound specializes the full construction to one distinct tile. -/
theorem exists_connected_tile_one_explicit_bound (T : LeanWang.TileSet)
    (hT : T.toFinset.card = 1) :
    ∃ P : Tile 3, P ≠ [] ∧ FaceConnected P ∧
      (LeanWang.TilesPlane T ↔ TranslationTiling.Tiles P) ∧
      cubeCount P ≤ 2 ^ (10 ^ 100) := by
  have hlen : T.dedup.length = 1 := by simpa only [List.card_toFinset] using hT
  obtain ⟨E, hb, hu, hC, hL⟩ := exists_one_parameterBudget T.dedup hlen
  obtain ⟨P, hP, hconn, hiff, hcubes⟩ :=
    exists_connected_tile_of_exp_budget (k := 10 ^ 8) (e := 10 ^ 98)
      hb hu hC hL (by norm_num) le_rfl (by norm_num)
      (by norm_num [testCountExponentFor, cycleCountExponentFor, channelCount_eq,
        residueModulus_eq, Sudoku.Width, Sudoku.p, Sudoku.q])
      (by norm_num)
      (by norm_num [channelCount_eq, residueModulus_eq, Sudoku.Width, Sudoku.p, Sudoku.q])
  have hexp : 100 * 10 ^ 98 = 10 ^ 100 := by norm_num
  rw [hexp] at hcubes
  have hd : LeanWang.TilesPlane T ↔ LeanWang.TilesPlane T.dedup :=
    LeanWang.tilesPlane_congr (by intro t; simp)
  exact ⟨P, hP, hconn, hd.trans hiff, hcubes⟩

end
end TranslationTiling.Compiler.Size
