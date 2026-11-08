import TranslationTiling.Compiler.PowerBounds
import Mathlib.Data.Nat.Log

namespace TranslationTiling.Compiler.Size

/-- The degree and binary-exponent coefficient are explicit. -/
theorem linear_channel_cap_le_exp_log_explicit (N d l : ℕ) (hl : 1 ≤ l) :
    (N * l + 2) ^ (d * (N * l + 2)) ≤
      2 ^ ((N + 4) * d * (N + 2) * l * (Nat.log 2 (l + 1) + 1)) := by
  have ha := ((PowerBoundAt.const N).mul PowerBoundAt.id).add (PowerBoundAt.const 2)
  have hC : N * l + 2 ≤ (N + 2) * l := by nlinarith
  have hbase : N * l + 2 ≤ (l + 1) ^ (N + 4) :=
    (by nlinarith : N * l + 2 ≤ N * (l + 1) + 2).trans (ha _ (by omega))
  have hlog : l + 1 ≤ 2 ^ (Nat.log 2 (l + 1) + 1) :=
    (Nat.lt_pow_succ_log_self (by decide : 1 < 2) _).le
  calc
    _ ≤ ((l + 1) ^ (N + 4)) ^ (d * (N * l + 2)) := Nat.pow_le_pow_left hbase _
    _ = (l + 1) ^ ((N + 4) * d * (N * l + 2)) := by simp only [← pow_mul]; congr 1; ring
    _ ≤ (l + 1) ^ ((N + 4) * d * (N + 2) * l) :=
      Nat.pow_le_pow_right (by omega)
        (by nlinarith [Nat.mul_le_mul_left ((N + 4) * d) hC])
    _ ≤ (2 ^ (Nat.log 2 (l + 1) + 1)) ^ ((N + 4) * d * (N + 2) * l) :=
      Nat.pow_le_pow_left hlog _
    _ = _ := by rw [← pow_mul]; congr 1; ring


/-- A bound exponential in `C log C`, with `C` linear in the bit length,
has a binary exponent linear in the bit length times its logarithm. -/
theorem linear_channel_cap_le_exp_log (N d : ℕ) :
    ∃ K : ℕ, ∀ l : ℕ, 1 ≤ l →
      (N * l + 2) ^ (d * (N * l + 2)) ≤
        2 ^ (K * l * (Nat.log 2 (l + 1) + 1)) :=
  ⟨(N + 4) * d * (N + 2), linear_channel_cap_le_exp_log_explicit N d⟩

/-- The numerical conversion used by the end-to-end theorem
`exists_connected_tile_quasipolynomial_bound`. -/
theorem bit_channel_cap_le_iterated_log (N d : ℕ) :
    ∃ K : ℕ, ∀ n : ℕ,
      (N * (Nat.log 2 (n + 2) + 1) + 2) ^
          (d * (N * (Nat.log 2 (n + 2) + 1) + 2)) ≤
        2 ^ (K * (Nat.log 2 (n + 2) + 1) *
          (Nat.log 2 (Nat.log 2 (n + 2) + 2) + 1)) := by
  obtain ⟨K, hK⟩ := linear_channel_cap_le_exp_log N d
  exact ⟨K, fun n => hK _ (by omega)⟩

/-- Convert a binary iterated-log bound to a power bound, keeping the large
numerical coefficient symbolic during the proof. -/
theorem exp_iterated_log_le_power (k n : ℕ) :
    2 ^ (k * (Nat.log 2 (n + 2) + 1) * (Nat.log 2 (Nat.log 2 (n + 2) + 2) + 1)) ≤
      (n + 2) ^ (2 * k * (Nat.log 2 (Nat.log 2 (n + 2) + 2) + 1)) := by
  have hlog : 2 ^ (Nat.log 2 (n + 2) + 1) ≤ (n + 2) ^ 2 := by
    rw [pow_succ, pow_two]
    exact Nat.mul_le_mul (Nat.pow_log_le_self 2 (by omega)) (by omega)
  calc
    _ = (2 ^ (Nat.log 2 (n + 2) + 1)) ^
        (k * (Nat.log 2 (Nat.log 2 (n + 2) + 2) + 1)) := by
      rw [← pow_mul]; congr 1; ring
    _ ≤ ((n + 2) ^ 2) ^
        (k * (Nat.log 2 (Nat.log 2 (n + 2) + 2) + 1)) := Nat.pow_le_pow_left hlog _
    _ = _ := by rw [← pow_mul]; congr 1; ring

end TranslationTiling.Compiler.Size
