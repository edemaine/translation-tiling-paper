import TranslationTiling.Compiler.ClosedPrimeBound
import Mathlib.NumberTheory.Chebyshev

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace TranslationTiling.Compiler.Size

open scoped Classical BigOperators
noncomputable section

/-- A deliberately coarse polynomial bound, sufficient for the size estimate.
Chebyshev's elementary lower bound supplies at least `t` primes below `(8t)²`. -/
theorem le_primeCounting_square (t : ℕ) (ht : 1 ≤ t) :
    t ≤ Nat.primeCounting ((8 * t) ^ 2) := by
  have htR : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hx : (1 : ℝ) < ((8 * t : ℕ) ^ 2 : ℕ) := by
    push_cast
    nlinarith
  have hlog : Real.log (((8 * t : ℕ) ^ 2 : ℕ) : ℝ) ≤ 16 * t := by
    push_cast
    rw [Real.log_pow]
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 8 * t by positivity)
    norm_num at *
    linarith
  have hlog1 : Real.log ((((8 * t : ℕ) ^ 2 : ℕ) + 1 : ℕ) : ℝ) ≤ 16 * t := by
    have hle : ((((8 * t : ℕ) ^ 2 : ℕ) + 1 : ℕ) : ℝ) ≤ (8 * (t : ℝ) + 1) ^ 2 := by
      push_cast
      nlinarith
    have h := Real.log_le_log (by positivity) hle
    rw [Real.log_pow] at h
    have h' := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 8 * t + 1 by positivity)
    norm_num at h
    push_cast
    linarith
  have htwo : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  have hp := Chebyshev.pi_ge ((8 * t) ^ 2)
  have hpos := Real.log_pos hx
  have hmul := (div_le_iff₀ hpos).mp hp
  have hnum : (t : ℝ) * Real.log (((8 * t : ℕ) ^ 2 : ℕ) : ℝ) ≤
      (((8 * t : ℕ) ^ 2 : ℕ) : ℝ) * Real.log 2 -
        Real.log ((((8 * t : ℕ) ^ 2 : ℕ) + 1 : ℕ) : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hlog (by positivity : (0 : ℝ) ≤ t)
    have h' := mul_le_mul_of_nonneg_left htwo
      (by positivity : (0 : ℝ) ≤ (((8 * t : ℕ) ^ 2 : ℕ) : ℝ))
    push_cast at *
    nlinarith
  push_cast at hnum hmul hpos
  exact_mod_cast (mul_le_mul_iff_left₀ hpos).mp (hnum.trans hmul)

/-- Zero-indexed primes admit a quadratic upper bound. -/
theorem nth_prime_le_square (k : ℕ) : Nat.nth Nat.Prime k ≤ (8 * (k + 1)) ^ 2 := by
  have h := le_primeCounting_square (k + 1) (by omega)
  have h' : k < Nat.count Nat.Prime ((8 * (k + 1)) ^ 2 + 1) := h
  exact Nat.le_of_lt_succ (Nat.nth_lt_of_lt_count h')

/-- Its argument will be `n+2`; all coefficients are fixed construction constants. -/
def polynomialPrimeCap (x : ℕ) : ℕ :=
  (8 * (digitStart + channelCount * (arithmeticAlphabet * x + 1) + 2)) ^ 2

theorem exists_polynomial_parameters (T : LeanWang.TileSet) :
    ∃ E : EncodingParameters T,
      (∀ i, E.a i ≤ usefulCap ∧ E.b i ≤ usefulCap) ∧
      ∀ i j, E.digitPrime i j ≤ polynomialPrimeCap (T.length + 2) := by
  let Tags := Σ i : Channel T, Label T i
  let ix : Tags ≃ Fin (Fintype.card Tags) := Fintype.equivFin Tags
  let g (j : Tags) := Nat.nth Nat.Prime (digitStart + (ix j).val)
  apply exists_parameters_of_prime_family T _ g (fun _ => Nat.prime_nth_prime _)
  · intro j
    have := Nat.add_two_le_nth_prime (digitStart + (ix j).val)
    dsimp [g]
    omega
  · intro i j hij
    apply ix.injective
    apply Fin.ext
    have h := (Nat.nth_strictMono Nat.infinite_setOfPred_prime).injective hij
    change digitStart + (ix i).val = digitStart + (ix j).val at h
    omega
  · intro j
    have hcard : Fintype.card Tags ≤ channelCount * labelsBound T.length := by
      rw [Fintype.card_sigma]
      calc
        _ ≤ ∑ i : Channel T, labelsBound T.length :=
          Finset.sum_le_sum (fun i _ => label_card_le T i)
        _ = _ := by simp [channelCount]
    have hrank := (ix j).isLt
    apply (nth_prime_le_square _).trans
    unfold polynomialPrimeCap labelsBound at *
    gcongr <;> nlinarith

end
end TranslationTiling.Compiler.Size
