import TranslationTiling.Compiler.ExplicitOneBound
import Mathlib.Data.Nat.Log

set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 1024

/-! # Explicit constants in the size bound

The small useful-prime table works for every input size. It gives the uniform
bound `(n+2)^(10^101*(n+1))`, and a binary-exponent coefficient of `10^100`.
-/

namespace TranslationTiling.Compiler.Size

open scoped Classical BigOperators
noncomputable section

theorem exists_small_parameters (T : LeanWang.TileSet) :
    ∃ E : EncodingParameters T,
      (∀ i, E.a i ≤ 10 ^ 40 ∧ E.b i ≤ 10 ^ 40) ∧
      ∀ i j, E.digitPrime i j ≤ 10 ^ 164 * (T.length + 2) ^ 2 := by
  obtain ⟨u, huinj, hu, hseed, hseedlarge⟩ := exists_small_useful
  let Tags := Σ i : Channel T, Label T i
  let ix : Tags ≃ Fin (Fintype.card Tags) := Fintype.equivFin Tags
  let g (j : Tags) := Nat.nth Nat.Prime (primeThreshold (10 ^ 40) + (ix j).val)
  apply exists_parameters_of_bounded_families T (10 ^ 40) _
    u huinj hu hseed hseedlarge g (fun _ => Nat.prime_nth_prime _)
  · intro j
    have := Nat.add_two_le_nth_prime (primeThreshold (10 ^ 40) + (ix j).val)
    change primeThreshold (10 ^ 40) <
      Nat.nth Nat.Prime (primeThreshold (10 ^ 40) + (ix j).val)
    omega
  · intro i j hij
    apply ix.injective
    apply Fin.ext
    have h := (Nat.nth_strictMono Nat.infinite_setOfPred_prime).injective hij
    change primeThreshold (10 ^ 40) + (ix i).val =
      primeThreshold (10 ^ 40) + (ix j).val at h
    omega
  · intro j
    have hcard : Fintype.card Tags ≤ channelCount * labelsBound T.length := by
      rw [Fintype.card_sigma]
      calc
        _ ≤ ∑ i : Channel T, labelsBound T.length :=
          Finset.sum_le_sum (fun i _ => label_card_le T i)
        _ = _ := by simp [channelCount]
    have hrank := (ix j).isLt
    have h : 8 * (primeThreshold (10 ^ 40) + (ix j).val + 1) ≤
        10 ^ 82 * (T.length + 2) := by
      norm_num [primeThreshold, channelCount_eq, residueModulus_eq, Sudoku.Width,
        Sudoku.p, Sudoku.q, labelsBound, arithmeticAlphabet] at hcard ⊢
      omega
    apply (nth_prime_le_square _).trans
    have hh := Nat.pow_le_pow_left h 2
    convert hh using 1; ring

theorem exists_small_parameterBudget (T : LeanWang.TileSet) :
    ∃ E : EncodingParameters T,
      ParameterBudget E ((T.length + 2) ^ (10 ^ 8 * (T.length + 1))) ∧
      (∀ i, E.a i ≤ 10 ^ 40 ∧ E.b i ≤ 10 ^ 40) ∧
      channelCount ≤ (T.length + 2) ^ (10 ^ 8 * (T.length + 1)) ∧
      labelsBound T.length ≤ (T.length + 2) ^ (10 ^ 8 * (T.length + 1)) := by
  obtain ⟨E, hu, hp⟩ := exists_small_parameters T
  let x := T.length + 2
  let b := x ^ (10 ^ 8 * (T.length + 1))
  have hx : 2 ≤ x := by dsimp [x]; omega
  have hpow : x ^ 1000 ≤ b :=
    Nat.pow_le_pow_right (by omega) (by dsimp [x]; omega)
  have hsmall : 10 ^ 40 ≤ b :=
    (by norm_num : 10 ^ 40 ≤ 2 ^ 1000).trans
      ((Nat.pow_le_pow_left hx 1000).trans hpow)
  have hN : residueModulus ≤ 10 ^ 40 := by
    norm_num [residueModulus_eq, Sudoku.Width, Sudoku.p, Sudoku.q]
  have hC : channelCount ≤ 10 ^ 40 := by
    norm_num [channelCount_eq, residueModulus_eq, Sudoku.Width, Sudoku.p, Sudoku.q]
  have hlabels : labelsBound T.length ≤ b := by
    have hcoef : 46621 ≤ x ^ 999 :=
      (by norm_num : 46621 ≤ 2 ^ 999).trans (Nat.pow_le_pow_left hx 999)
    calc
      _ ≤ 46621 * x := by
        dsimp [x]; norm_num [labelsBound, arithmeticAlphabet, Sudoku.p, Sudoku.q]; omega
      _ ≤ x ^ 999 * x := Nat.mul_le_mul_right x hcoef
      _ = x ^ 1000 := by rw [← pow_succ]
      _ ≤ b := hpow
  have hr (i : Channel T) : E.r i ≤ b := by
    have hc := label_card_le T i
    have hexp : 1000 * Fintype.card (Label T i) ≤ 10 ^ 8 * (T.length + 1) := by
      norm_num [labelsBound, arithmeticAlphabet, Sudoku.p, Sudoku.q] at hc
      omega
    have hprime (j : Label T i) : E.digitPrime i j ≤ x ^ 1000 := by
      calc
        _ ≤ 10 ^ 164 * x ^ 2 := hp i j
        _ ≤ x ^ 998 * x ^ 2 := Nat.mul_le_mul_right _
          ((by norm_num : 10 ^ 164 ≤ 2 ^ 998).trans (Nat.pow_le_pow_left hx 998))
        _ = x ^ 1000 := by rw [← pow_add]
    rw [E.r_eq_prod]
    calc
      _ ≤ ∏ _j : Label T i, x ^ 1000 := Finset.prod_le_prod (fun j _ => hprime j)
      _ = (x ^ 1000) ^ Fintype.card (Label T i) := by simp
      _ = x ^ (1000 * Fintype.card (Label T i)) := by rw [pow_mul]
      _ ≤ b := Nat.pow_le_pow_right (by omega) hexp
  refine ⟨E, ⟨?_, hN.trans hsmall, hr, fun i => (hu i).1.trans hsmall,
    fun i => (hu i).2.trans hsmall⟩, hu, hC.trans hsmall, hlabels⟩
  exact (by norm_num : 2 ≤ 10 ^ 40).trans hsmall

/-- An explicit binary-exponent coefficient, including all geometric steps. -/
theorem exists_connected_tile_explicit_exp_log_bound (T : LeanWang.TileSet) :
    ∃ P : Tile 3, P ≠ [] ∧ FaceConnected P ∧
      (LeanWang.TilesPlane T ↔ TranslationTiling.Tiles P) ∧
      cubeCount P ≤ 2 ^ (10 ^ 100 * (T.toFinset.card + 1) *
        (Nat.log 2 (T.toFinset.card + 2) + 1)) := by
  obtain ⟨E, hb, hu, hC, hL⟩ := exists_small_parameterBudget T.dedup
  let n := T.dedup.length
  let l := Nat.log 2 (n + 2) + 1
  let f := (n + 1) * l
  have hf : 1 ≤ f := by dsimp [f, l]; nlinarith
  have hbase : (n + 2) ^ (10 ^ 8 * (n + 1)) ≤ 2 ^ (10 ^ 8 * f) := by
    have h := (Nat.lt_pow_succ_log_self (by decide : 1 < 2) (n + 2)).le
    apply (Nat.pow_le_pow_left h (10 ^ 8 * (n + 1))).trans
    rw [← pow_mul]
    exact le_of_eq (by dsimp [f, l]; congr 1; ring)
  have hcount : 10 ^ 8 * testCountExponentFor (10 ^ 40) ≤ 10 ^ 98 := by
    norm_num [testCountExponentFor, cycleCountExponentFor, channelCount_eq,
      residueModulus_eq, Sudoku.Width, Sudoku.p, Sudoku.q]
  have hfinite : 10 ^ 8 * (4 * channelCount + 2) ≤ 10 ^ 98 := by
    norm_num [channelCount_eq, residueModulus_eq, Sudoku.Width, Sudoku.p, Sudoku.q]
  obtain ⟨P, hP, hconn, hiff, hcubes⟩ :=
    exists_connected_tile_of_exp_budget (k := 10 ^ 8 * f) (e := 10 ^ 98 * f)
      hb hu hC hL (by nlinarith) hbase (by nlinarith)
      (by nlinarith [Nat.mul_le_mul_right f hcount])
      (by nlinarith)
      (by nlinarith [Nat.mul_le_mul_right f hfinite])
  have hexp : 100 * (10 ^ 98 * f) = 10 ^ 100 * (n + 1) * l := by
    dsimp [f]; ring
  rw [hexp] at hcubes
  have hd : LeanWang.TilesPlane T ↔ LeanWang.TilesPlane T.dedup :=
    LeanWang.tilesPlane_congr (by intro t; simp)
  refine ⟨P, hP, hconn, hd.trans hiff, ?_⟩
  simpa only [n, l, List.card_toFinset] using hcubes

/-- In the power bound, the universal constant can be taken to be `10^101`. -/
theorem exists_connected_tile_explicit_power_bound (T : LeanWang.TileSet) :
    ∃ P : Tile 3, P ≠ [] ∧ FaceConnected P ∧
      (LeanWang.TilesPlane T ↔ TranslationTiling.Tiles P) ∧
      cubeCount P ≤ (T.toFinset.card + 2) ^ (10 ^ 101 * (T.toFinset.card + 1)) := by
  obtain ⟨P, hP, hconn, hiff, hcubes⟩ := exists_connected_tile_explicit_exp_log_bound T
  let n := T.toFinset.card
  have hx : 2 ≤ n + 2 := by omega
  have hlog : 2 ^ (Nat.log 2 (n + 2) + 1) ≤ (n + 2) ^ 2 := by
    rw [pow_succ, pow_two]
    exact Nat.mul_le_mul (Nat.pow_log_le_self 2 (by omega)) hx
  refine ⟨P, hP, hconn, hiff, hcubes.trans ?_⟩
  calc
    _ = (2 ^ (Nat.log 2 (n + 2) + 1)) ^ (10 ^ 100 * (n + 1)) := by
      rw [← pow_mul]; congr 1; ring
    _ ≤ ((n + 2) ^ 2) ^ (10 ^ 100 * (n + 1)) := Nat.pow_le_pow_left hlog _
    _ = (n + 2) ^ (2 * (10 ^ 100 * (n + 1))) := by rw [← pow_mul]
    _ ≤ _ := Nat.pow_le_pow_right (by omega) (by nlinarith)

end
end TranslationTiling.Compiler.Size
