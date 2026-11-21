import TranslationTiling.Compiler.GuardedLogBound
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Data.Nat.Log

namespace TranslationTiling.Compiler.Size

noncomputable section

/-- A Chebyshev prime budget with integer arithmetic. -/
def guardedPrimeCap (m : ℕ) : ℕ := 4 * m * (Nat.log 2 m + 1)

theorem lg_natLog_le {m : ℕ} (hm : 0 < m) :
    (Nat.log 2 m : ℝ) ≤ Real.logb 2 m := by
  have hp := Nat.pow_log_le_self 2 hm.ne'
  have h := lg_mono (by positivity : 0 < (2 : ℝ) ^ Nat.log 2 m) (show (2 : ℝ)^Nat.log 2 m ≤ (m : ℝ) by exact_mod_cast hp)
  simpa only [lg_two_pow] using h

theorem guardedPrimeCap_count {m : ℕ} (hm : 16 ≤ m) :
    m ≤ Nat.primeCounting (guardedPrimeCap m) := by
  let s := Nat.log 2 m + 1
  let Q := guardedPrimeCap m
  have hs : 4 ≤ s := by
    have h := (Nat.le_log_iff_pow_le (by decide : 1 < 2) (by omega : m ≠ 0)).mpr
      (show 2^4 ≤ m by norm_num; exact hm)
    dsimp [s]
    omega
  have hms : m ≤ 2^s := (Nat.lt_pow_succ_log_self (by decide) m).le
  have hs' (u : ℕ) (hu : 4 ≤ u) : 4*u ≤ 2^u := by
    induction u, hu using Nat.le_induction with
    | base => decide
    | succ u hu ih =>
      rw [pow_succ]
      omega
  have hQ : Q ≤ 2^(2*s) := by
    rw [mul_comm 2 s, pow_mul, pow_two]
    change 4*m*s ≤ _
    calc
      _ = (4*s)*m := by ring
      _ ≤ _ := Nat.mul_le_mul (hs' s hs) hms
  have h2 : 2 ≤ Q := by
    change 2 ≤ 4*m*s
    nlinarith
  have hQ' : 0 < (Q : ℝ) := by exact_mod_cast (show 0<Q by omega)
  have hlog : 0 < Real.logb 2 Q := Real.logb_pos (by norm_num) (by exact_mod_cast (show 1<Q by omega))
  have hlogU := lg_mono hQ' (show (Q : ℝ) ≤ (2 : ℝ)^(2*s) by exact_mod_cast hQ)
  rw [lg_two_pow, Nat.cast_mul, Nat.cast_ofNat] at hlogU
  have hplus := lg_mono (show 0 < (Q : ℝ)+1 by positivity)
    (show (Q : ℝ)+1 ≤ (Q : ℝ)^2 by
      have h2' : (2 : ℝ) ≤ Q := by exact_mod_cast h2
      nlinarith)
  rw [Real.logb_pow, Nat.cast_ofNat] at hplus
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogQ : 0 < Real.log (Q : ℝ) := Real.log_pos (by exact_mod_cast (show 1<Q by omega))
  have hcount := (div_le_iff₀ hlogQ).mp (Chebyshev.pi_ge Q)
  push_cast at hcount
  have hnum : (Q : ℝ) ≤ (Nat.primeCounting Q : ℝ)*Real.logb 2 Q +
      Real.logb 2 ((Q : ℝ)+1) := by
    unfold Real.logb
    rw [← mul_div_assoc, ← add_div, le_div_iff₀ hlog2]
    linarith only [hcount]
  have hstep : (Q : ℝ) ≤ (Nat.primeCounting Q + 2 : ℝ) * Real.logb 2 Q := by
    linarith only [hnum,hplus]
  have hmul := mul_le_mul_of_nonneg_left hlogU
    (show 0 ≤ (Nat.primeCounting Q + 2 : ℝ) by positivity)
  have hv : (Q : ℝ) = 4 * (m : ℝ) * (s : ℝ) := by
    simp only [Q, guardedPrimeCap, Nat.cast_mul, Nat.cast_ofNat, s]
  have hsr : (4 : ℝ) ≤ s := by exact_mod_cast hs
  change m ≤ Nat.primeCounting Q
  by_contra hn
  have hc : (Nat.primeCounting Q : ℝ) + 2 < 2 * (m : ℝ) := by
    have hn' : Nat.primeCounting Q + 2 < 2*m := by omega
    exact_mod_cast hn'
  have hh := mul_lt_mul_of_pos_right hc (show (0 : ℝ) < 2*s by linarith)
  nlinarith only [hstep, hmul, hv, hh]

end
end TranslationTiling.Compiler.Size
