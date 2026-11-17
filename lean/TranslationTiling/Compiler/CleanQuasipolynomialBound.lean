import TranslationTiling.Compiler.QuasipolynomialBound
import Mathlib.Analysis.SpecialFunctions.Log.Base

set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

namespace TranslationTiling.Compiler.Size

noncomputable section

/-- Absorb the shifted integer logarithms into a single iterated logarithm. -/
theorem shifted_power_le_clean (k n : ℕ) :
    (n + 2) ^ (2 * k * (Nat.log 2 (Nat.log 2 (n + 2) + 2) + 1)) ≤
      (n + 4) ^ (10 * k * Nat.log 2 (Nat.log 2 (n + 4))) := by
  have hb : 2 ≤ Nat.log 2 (n + 4) :=
    Nat.le_log_of_pow_le (by decide) (by norm_num)
  have hc : 1 ≤ Nat.log 2 (Nat.log 2 (n + 4)) :=
    Nat.le_log_of_pow_le (by decide) (by simpa using hb)
  have hshift : Nat.log 2 (n + 2) + 2 ≤ Nat.log 2 (n + 4) * 2 := by
    have h := Nat.log_mono_right (b := 2) (by omega : n + 2 ≤ n + 4)
    omega
  have hlog := Nat.log_mono_right (b := 2) hshift
  rw [Nat.log_mul_base (by decide) (by omega)] at hlog
  have hexp : 2 * k * (Nat.log 2 (Nat.log 2 (n + 2) + 2) + 1) ≤
      10 * k * Nat.log 2 (Nat.log 2 (n + 4)) := by
    have h : Nat.log 2 (Nat.log 2 (n + 2) + 2) + 1 ≤
        3 * Nat.log 2 (Nat.log 2 (n + 4)) := by omega
    have hm := Nat.mul_le_mul_left (2 * k) h
    nlinarith
  exact (Nat.pow_le_pow_left (by omega : n + 2 ≤ n + 4) _).trans
    (Nat.pow_le_pow_right (by omega) hexp)

/-- Absorb the shifted integer logarithms into a single iterated logarithm. -/
theorem shifted_power_le_clean_six (k n : ℕ) :
    (n + 2) ^ (2 * k * (Nat.log 2 (Nat.log 2 (n + 2) + 2) + 1)) ≤
      (n + 4) ^ (6 * k * Nat.log 2 (Nat.log 2 (n + 4))) := by
  have hb : 2 ≤ Nat.log 2 (n + 4) :=
    Nat.le_log_of_pow_le (by decide) (by norm_num)
  have hc : 1 ≤ Nat.log 2 (Nat.log 2 (n + 4)) :=
    Nat.le_log_of_pow_le (by decide) (by simpa using hb)
  have hshift : Nat.log 2 (n + 2) + 2 ≤ Nat.log 2 (n + 4) * 2 := by
    have h := Nat.log_mono_right (b := 2) (by omega : n + 2 ≤ n + 4)
    omega
  have hlog := Nat.log_mono_right (b := 2) hshift
  rw [Nat.log_mul_base (by decide) (by omega)] at hlog
  have hexp : 2 * k * (Nat.log 2 (Nat.log 2 (n + 2) + 2) + 1) ≤
      6 * k * Nat.log 2 (Nat.log 2 (n + 4)) := by
    have h : Nat.log 2 (Nat.log 2 (n + 2) + 2) + 1 ≤
        3 * Nat.log 2 (Nat.log 2 (n + 4)) := by omega
    have hm := Nat.mul_le_mul_left (2 * k) h
    nlinarith
  exact (Nat.pow_le_pow_left (by omega : n + 2 ≤ n + 4) _).trans
    (Nat.pow_le_pow_right (by omega) hexp)

/-- Treat the few small inputs directly to sharpen the logarithm conversion. -/
theorem exp_iterated_log_le_clean_four (k n : ℕ) :
    2 ^ (k * (Nat.log 2 (n + 2) + 1) * (Nat.log 2 (Nat.log 2 (n + 2) + 2) + 1)) ≤
      (n + 4) ^ (4 * k * Nat.log 2 (Nat.log 2 (n + 4))) := by
  by_cases hn : n < 12
  · have hbase : 2 ^ ((Nat.log 2 (n + 2) + 1) * (Nat.log 2 (Nat.log 2 (n + 2) + 2) + 1)) ≤
        (n + 4) ^ (4 * Nat.log 2 (Nat.log 2 (n + 4))) := by
      interval_cases n <;> decide
    calc
      _ = (2 ^ ((Nat.log 2 (n + 2) + 1) * (Nat.log 2 (Nat.log 2 (n + 2) + 2) + 1))) ^ k := by
        rw [← pow_mul]; congr 1; ring
      _ ≤ ((n + 4) ^ (4 * Nat.log 2 (Nat.log 2 (n + 4)))) ^ k := Nat.pow_le_pow_left hbase _
      _ = _ := by rw [← pow_mul]; congr 1; ring
  · have hb : 4 ≤ Nat.log 2 (n + 4) := Nat.le_log_of_pow_le (by decide) (by norm_num; omega)
    have hc : 2 ≤ Nat.log 2 (Nat.log 2 (n + 4)) :=
      Nat.le_log_of_pow_le (by decide) (by simpa using hb)
    have hshift : Nat.log 2 (n + 2) + 2 ≤ Nat.log 2 (n + 4) * 2 := by
      have h := Nat.log_mono_right (b := 2) (by omega : n + 2 ≤ n + 4)
      omega
    have hlog := Nat.log_mono_right (b := 2) hshift
    rw [Nat.log_mul_base (by decide) (by omega)] at hlog
    apply (exp_iterated_log_le_power k n).trans
    apply (Nat.pow_le_pow_left (by omega : n + 2 ≤ n + 4) _).trans
    apply Nat.pow_le_pow_right (by omega)
    have hJ : Nat.log 2 (Nat.log 2 (n + 2) + 2) + 1 ≤
        2 * Nat.log 2 (Nat.log 2 (n + 4)) := by omega
    nlinarith [Nat.mul_le_mul_left (2 * k) hJ]

/-- The separated parameters give a clean coefficient of ten to the eleventh. -/
theorem ternary_exp_le_clean (n : ℕ) :
    2 ^ ((2 * 10 ^ 10) * (Nat.log 2 (n + 2) + 1) *
      (Nat.log 2 (Nat.log 2 (n + 2) + 2) + 1)) ≤
      (n + 4) ^ (10 ^ 11 * Nat.log 2 (Nat.log 2 (n + 4))) := by
  apply (exp_iterated_log_le_clean_four (2 * 10 ^ 10) n).trans
  apply Nat.pow_le_pow_right (by omega)
  exact Nat.mul_le_mul_right _ (by norm_num : 4 * (2 * 10 ^ 10) ≤ 10 ^ 11)

/-- Passing to ordinary real logarithms removes all rounding operations. -/
theorem clean_power_le_real_loglog (k n : ℕ) :
    (((n + 4) ^ (10 * k * Nat.log 2 (Nat.log 2 (n + 4))) : ℕ) : ℝ) ≤
      ((n : ℝ) + 4) ^ (((10 * k : ℕ) : ℝ) *
        Real.logb 2 (Real.logb 2 ((n : ℝ) + 4))) := by
  have hb : 2 ≤ Nat.log 2 (n + 4) :=
    Nat.le_log_of_pow_le (by decide) (by norm_num)
  have hinner : (Nat.log 2 (n + 4) : ℝ) ≤ Real.logb 2 ((n : ℝ) + 4) := by
    simpa only [Nat.cast_add, Nat.cast_ofNat] using Real.natLog_le_logb (n + 4) 2
  have hlog : (Nat.log 2 (Nat.log 2 (n + 4)) : ℝ) ≤
      Real.logb 2 (Real.logb 2 ((n : ℝ) + 4)) :=
    (Real.natLog_le_logb _ 2).trans
      (Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
        (by exact_mod_cast (by omega : 0 < Nat.log 2 (n + 4))) hinner)
  calc
    _ = ((n : ℝ) + 4) ^ ((10 * k * Nat.log 2 (Nat.log 2 (n + 4)) : ℕ) : ℝ) := by
      rw [Real.rpow_natCast]
      push_cast
      rfl
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le
      (by have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith)
      (by push_cast; exact mul_le_mul_of_nonneg_left hlog (by positivity))

/-- A numerical quasipolynomial bound with ordinary real logarithms and no floors. -/
theorem exists_connected_tile_clean_quasipolynomial_bound (T : LeanWang.TileSet) :
    ∃ P : Tile 3, P ≠ [] ∧ FaceConnected P ∧
      (LeanWang.TilesPlane T ↔ TranslationTiling.Tiles P) ∧
      (cubeCount P : ℝ) ≤ ((T.toFinset.card : ℝ) + 4) ^
        ((8000 : ℝ) * Real.logb 2 (Real.logb 2 ((T.toFinset.card : ℝ) + 4))) := by
  obtain ⟨hn,hc,ht,hb⟩ := FiniteCompiler.Effective.mixedCompile_facts T.dedup
  have hd : LeanWang.TilesPlane T ↔ LeanWang.TilesPlane T.dedup :=
    LeanWang.tilesPlane_congr (by intro t; simp)
  refine ⟨FiniteCompiler.Effective.mixedCompile T.dedup,hn,hc,hd.trans ht,?_⟩
  have hcard : (cubeCount (FiniteCompiler.Effective.mixedCompile T.dedup):ℝ) ≤
      ((FiniteCompiler.Effective.mixedCompile T.dedup).length:ℝ) := by
    exact_mod_cast List.toFinset_card_le (FiniteCompiler.Effective.mixedCompile T.dedup)
  apply hcard.trans
  simpa only [List.card_toFinset] using hb

end
end TranslationTiling.Compiler.Size
