import TranslationTiling.Compiler.GuardedLogBound
import TranslationTiling.FiniteCompiler.SlotWords

namespace TranslationTiling.Compiler.Size

open FiniteCompiler.SlotWords

/-- A digit of length `4*t` carries at least `8*t - lg(4*t+1)` bits. -/
theorem slot_radix_log_lower (t : ℕ) :
    8*(t : ℝ) - Real.logb 2 (4*(t : ℝ)+1) ≤
      Real.logb 2 (Fintype.card (Word (4*t) (3*t) 3)) := by
  let R := Fintype.card (Word (4*t) (3*t) 3)
  have h := four_pow_le_weighted t
  change 4^(4*t) ≤ (4*t+1)*R at h
  have hR : 0 < R := by
    by_contra! hzero
    have hpos : 0 < 4^(4*t) := by positivity
    simp [Nat.eq_zero_of_le_zero hzero] at h
  have hlog := lg_mono (show 0 < (4 : ℝ)^(4*t) by positivity)
    (show (4 : ℝ)^(4*t) ≤ (4*(t : ℝ)+1)*(R : ℝ) by exact_mod_cast h)
  rw [show (4 : ℝ) = 2^2 by norm_num, ← pow_mul,lg_two_pow,
    Real.logb_mul (by positivity) (by exact_mod_cast hR.ne')] at hlog
  push_cast at hlog
  norm_num at hlog
  change _ ≤ Real.logb 2 (R : ℝ)
  linarith

end TranslationTiling.Compiler.Size
