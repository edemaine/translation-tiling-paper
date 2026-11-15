import TranslationTiling.FiniteCompiler.Effective.MixedInput
import Mathlib.Analysis.SpecialFunctions.Log.Base

namespace TranslationTiling.Compiler.Size
open FiniteCompiler.Effective
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

private theorem logb_two_pow (k : ℕ) : Real.logb 2 ((2:ℝ)^k) = k := by
  rw [Real.logb_pow]
  norm_num [Real.logb_self_eq_one]

private theorem pow_le_log_bound {x : ℝ} (hx : 0 < x) (a b : ℕ)
    (h : (2:ℝ)^a ≤ x^b) : (a : ℝ) ≤ b * Real.logb 2 x := by
  have hl := Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2) (by positivity : 0 < (2:ℝ)^a) h
  simpa [Real.logb_pow,Real.logb_self_eq_one] using hl

theorem mixedWidth_lower {n : ℕ} (hn : 0 < n) : 12 ≤ mixedWidth n := by
  have hp : 3^9 ≤ Sudoku.p*Sudoku.q*n := by
    have h := Nat.mul_le_mul_left (Sudoku.p*Sudoku.q) hn
    norm_num [Sudoku.p,Sudoku.q] at *
    omega
  have hl := Nat.le_log_of_pow_le (by decide : 1<3) hp
  unfold mixedWidth mixedPayloadWidth
  omega

theorem mixedWidth_one : mixedWidth 1 = 12 := by decide

/-- A direct conversion avoids multiplying the integer-log rounding losses. -/
theorem mixedWidth_le_log {n : ℕ} (hn : 0 < n) :
    (mixedWidth n : ℝ) ≤ (21/4:ℝ) * Real.logb 2 ((n:ℝ)+4) := by
  let t := Real.logb 2 ((n:ℝ)+4)
  have h5 : (23:ℝ) ≤ 10 * Real.logb 2 5 := pow_le_log_bound (by norm_num) 23 10 (by norm_num)
  have ht5 : Real.logb 2 5 ≤ t := Real.logb_le_logb_of_le (by norm_num) (by norm_num)
    (by exact_mod_cast (by omega : 5 ≤ n+4))
  by_cases hsmall : n < 4
  · interval_cases n
    · rw [mixedWidth_one]; norm_num only [Nat.cast_ofNat]; nlinarith
    · have hw : mixedWidth 2 = 13 := by decide
      rw [hw]
      have h6 : (5:ℝ) ≤ 2 * Real.logb 2 6 := pow_le_log_bound (by norm_num) 5 2 (by norm_num)
      norm_num only [Nat.cast_ofNat]
      nlinarith
    · have hw : mixedWidth 3 = 13 := by decide
      rw [hw]
      have h6 : (5:ℝ) ≤ 2 * Real.logb 2 6 := pow_le_log_bound (by norm_num) 5 2 (by norm_num)
      have ht6 : Real.logb 2 6 ≤ Real.logb 2 7 := Real.logb_le_logb_of_le (by norm_num) (by norm_num) (by norm_num)
      norm_num only [Nat.cast_ofNat]
      nlinarith
  · have ht : 3 ≤ t := by
      have he := pow_le_log_bound (by positivity : 0 < (n:ℝ)+4) 3 1 (by norm_num; exact_mod_cast (by omega : 8 ≤ n+4))
      dsimp [t]
      simpa using he
    have hnreal : (0:ℝ) < n := by exact_mod_cast hn
    have hnlog : Real.logb 2 (n:ℝ) ≤ t := Real.logb_le_logb_of_le (by norm_num) hnreal (by linarith)
    have h2 : (Nat.log 2 n : ℝ) ≤ t := (Real.natLog_le_logb n 2).trans hnlog
    have hp : 0 < Sudoku.p*Sudoku.q*n := by positivity
    have h3nat : 3 ^ Nat.log 3 (Sudoku.p*Sudoku.q*n) ≤ Sudoku.p*Sudoku.q*n := Nat.pow_log_le_self 3 (by omega)
    have h3real : (3:ℝ) ^ Nat.log 3 (Sudoku.p*Sudoku.q*n) ≤ (Sudoku.p*Sudoku.q:ℕ) * (n:ℝ) := by exact_mod_cast h3nat
    have h3log := Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2) (by positivity : 0 < (3:ℝ)^Nat.log 3 (Sudoku.p*Sudoku.q*n)) h3real
    rw [Real.logb_pow,Real.logb_mul (by norm_num [Sudoku.p,Sudoku.q]) (by positivity)] at h3log
    have h3base : (3:ℝ) ≤ 2 * Real.logb 2 3 := pow_le_log_bound (by norm_num) 3 2 (by norm_num)
    have harith : Real.logb 2 ((Sudoku.p*Sudoku.q:ℕ):ℝ) ≤ 16 := by
      apply (Real.logb_le_logb_of_le (by norm_num) (by norm_num [Sudoku.p,Sudoku.q])
        (show ((Sudoku.p*Sudoku.q:ℕ):ℝ) ≤ (2:ℝ)^16 by norm_num [Sudoku.p,Sudoku.q])).trans
      exact (logb_two_pow 16).le
    have h3 : 3 * (Nat.log 3 (Sudoku.p*Sudoku.q*n) : ℝ) ≤ 32+2*t := by
      nlinarith [mul_le_mul_of_nonneg_left h3base (Nat.cast_nonneg (Nat.log 3 (Sudoku.p*Sudoku.q*n)))]
    unfold mixedWidth mixedPayloadWidth
    push_cast
    change max ((Nat.log 2 n:ℝ)+1) ((Nat.log 3 (Sudoku.p*Sudoku.q*n):ℝ)+1) + 2 ≤ (21/4:ℝ)*t
    have hm : max ((Nat.log 2 n:ℝ)+1) ((Nat.log 3 (Sudoku.p*Sudoku.q*n):ℝ)+1) ≤ (21/4:ℝ)*t-2 :=
      max_le (by nlinarith only [h2,ht]) (by
        have helper (u v : ℝ) (hv : 3 ≤ v) (hu : 3*u ≤ 32+2*v) : u+1 ≤ (21/4:ℝ)*v-2 := by linarith
        exact helper _ _ ht h3)
    linarith

/-- The iterated logarithm is uniformly bounded away from one on positive inputs. -/
theorem mixed_loglog_lower {n : ℕ} (hn : 0 < n) :
    (6/5:ℝ) ≤ Real.logb 2 (Real.logb 2 ((n:ℝ)+4)) := by
  have h5 : (23:ℝ) ≤ 10 * Real.logb 2 5 := pow_le_log_bound (by norm_num) 23 10 (by norm_num)
  have h23 : (6:ℝ) ≤ 5 * Real.logb 2 (23/10:ℝ) := pow_le_log_bound (by norm_num) 6 5 (by norm_num)
  have ht : Real.logb 2 5 ≤ Real.logb 2 ((n:ℝ)+4) := Real.logb_le_logb_of_le (by norm_num) (by norm_num)
    (by exact_mod_cast (by omega : 5 ≤ n+4))
  have hh := Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2) (by norm_num : (0:ℝ)<23/10)
    (show (23/10:ℝ) ≤ Real.logb 2 ((n:ℝ)+4) by linarith)
  linarith

theorem channel_cap_real_bound (d k : ℕ)
    (hcoeff : (d:ℝ)*((21/4:ℝ)*Sudoku.Width+1)*16 ≤ k)
    {n : ℕ} (hn : 0<n) :
    (((Sudoku.Width * mixedWidth n + 2) ^ (d*(Sudoku.Width*mixedWidth n+2)) : ℕ):ℝ) ≤
      ((n:ℝ)+4) ^ ((k:ℝ) * Real.logb 2 (Real.logb 2 ((n:ℝ)+4))) := by
  let C := Sudoku.Width*mixedWidth n+2
  let t := Real.logb 2 ((n:ℝ)+4)
  let g := Real.logb 2 t
  let a : ℝ := (21/4:ℝ)*Sudoku.Width+1
  have ht : 2 ≤ t := by
    have h := pow_le_log_bound (by positivity : 0 < (n:ℝ)+4) 2 1 (by simpa only [pow_one,show (2:ℝ)^2 = 4 by norm_num] using (show (4:ℝ) ≤ (n:ℝ)+4 by have := Nat.cast_nonneg (α := ℝ) n; linarith))
    simpa [t] using h
  have hg : (6/5:ℝ) ≤ g := mixed_loglog_lower hn
  have hC : (C:ℝ) ≤ a*t := by
    have hw := mixedWidth_le_log hn
    dsimp [C,a,t]
    push_cast
    nlinarith
  have hCpos : (0:ℝ) < C := by dsimp [C]; positivity
  have ha : a ≤ (2:ℝ)^18 := by norm_num [a,Sudoku.Width,Sudoku.q]
  have hlog : Real.logb 2 (C:ℝ) ≤ 16*g := by
    have hlog := Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2) hCpos
      (hC.trans (mul_le_mul_of_nonneg_right ha (by linarith)))
    rw [Real.logb_mul (by positivity) (by linarith),logb_two_pow] at hlog
    dsimp [g] at *
    linarith
  have hc1 : 1 ≤ (C:ℝ) := by
    have hnat : 1 ≤ C := by dsimp [C]; omega
    exact_mod_cast hnat
  have he : (d:ℝ)*(C:ℝ)*Real.logb 2 (C:ℝ) ≤ (k:ℝ)*t*g := by
    have hclog : 0 ≤ Real.logb 2 (C:ℝ) := Real.logb_nonneg (by norm_num) hc1
    have hmul := mul_le_mul hC hlog hclog (by dsimp [a]; positivity : 0 ≤ a*t)
    have hconst : (d:ℝ)*a*16 ≤ (k:ℝ) := hcoeff
    have hc := mul_le_mul_of_nonneg_left hmul (Nat.cast_nonneg d)
    have hb := mul_le_mul_of_nonneg_right hconst (show 0 ≤ t*g by positivity)
    nlinarith only [hc,hb]
  change ((C ^ (d*C):ℕ):ℝ) ≤ _
  rw [Nat.cast_pow]
  apply (Real.logb_le_logb (by norm_num : (1:ℝ)<2) (by positivity) (by positivity)).mp
  rw [Real.logb_pow,Real.logb_rpow_eq_mul_logb_of_pos (by positivity : 0 < (n:ℝ)+4)]
  push_cast
  dsimp [t,g] at he
  nlinarith


theorem mixed_channel_cap_real_bound {n : ℕ} (hn : 0<n) :
    (((Sudoku.Width*mixedWidth n+2)^(1772*(Sudoku.Width*mixedWidth n+2)):ℕ):ℝ) ≤
      ((n:ℝ)+4)^((10:ℝ)^10*Real.logb 2 (Real.logb 2 ((n:ℝ)+4))) := by
  have h := channel_cap_real_bound 1772 (10^10) (by norm_num [Sudoku.Width,Sudoku.q]) hn
  norm_num only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] at h ⊢
  exact h

theorem sharp_channel_cap_real_bound {n : ℕ} (hn : 0<n) :
    (((Sudoku.Width*mixedWidth n+2)^(103*(Sudoku.Width*mixedWidth n+2)):ℕ):ℝ) ≤
      ((n:ℝ)+4)^((5*(10:ℝ)^8)*Real.logb 2 (Real.logb 2 ((n:ℝ)+4))) := by
  have h := channel_cap_real_bound 103 (5*10^8) (by norm_num [Sudoku.Width,Sudoku.q]) hn
  norm_num only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] at h ⊢
  exact h

end
end TranslationTiling.Compiler.Size
