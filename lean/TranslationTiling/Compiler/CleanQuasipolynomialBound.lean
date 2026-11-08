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
        ((10 : ℝ) ^ 61 * Real.logb 2 (Real.logb 2 ((T.toFinset.card : ℝ) + 4))) := by
  obtain ⟨P, hP, hconn, hiff, hcubes⟩ := exists_connected_tile_quasipolynomial_explicit_power_bound T
  have hnat := hcubes.trans (shifted_power_le_clean (10 ^ 60) T.toFinset.card)
  have hcast : (cubeCount P : ℝ) ≤
      (((T.toFinset.card + 4) ^ (10 * 10 ^ 60 * Nat.log 2 (Nat.log 2 (T.toFinset.card + 4))) : ℕ) : ℝ) :=
    by exact_mod_cast hnat
  have hbound := hcast.trans (clean_power_le_real_loglog (10 ^ 60) T.toFinset.card)
  have hcoeff : 10 * 10 ^ 60 = 10 ^ 61 := by norm_num
  rw [hcoeff] at hbound
  refine ⟨P, hP, hconn, hiff, ?_⟩
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using hbound

end
end TranslationTiling.Compiler.Size
