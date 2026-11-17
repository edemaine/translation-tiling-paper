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

theorem mixedWidth_lower {n : ℕ} (hn : 0 < n) : 6 ≤ mixedWidth n := mixedWidth_six hn

theorem mixedWidth_one : mixedWidth 1 = 6 := by decide

/-- A direct conversion avoids multiplying the integer-log rounding losses. -/
theorem mixedWidth_le_log {n : ℕ} (hn : 0 < n) :
    (mixedWidth n : ℝ) ≤ (11/4:ℝ) * Real.logb 2 ((n:ℝ)+4) := by
  let t := Real.logb 2 ((n:ℝ)+4)
  by_cases hsmall : n < 7
  · interval_cases n
    · rw [show mixedWidth 1=6 by decide]
      norm_num only [Nat.cast_ofNat]
      have h := pow_le_log_bound (by norm_num) 24 11 (by norm_num : (2:ℝ)^24≤5^11)
      norm_num at h ⊢
      linarith
    · rw [show mixedWidth 2=6 by decide]
      norm_num only [Nat.cast_ofNat]
      have h := pow_le_log_bound (by norm_num) 28 11 (by norm_num : (2:ℝ)^28≤6^11)
      norm_num at h ⊢
      linarith
    · rw [show mixedWidth 3=7 by decide]
      norm_num only [Nat.cast_ofNat]
      have h := pow_le_log_bound (by norm_num) 28 11 (by norm_num : (2:ℝ)^28≤7^11)
      norm_num at h ⊢
      linarith
    · rw [show mixedWidth 4=7 by decide]
      norm_num only [Nat.cast_ofNat]
      have h := pow_le_log_bound (by norm_num) 32 11 (by norm_num : (2:ℝ)^32≤8^11)
      norm_num at h ⊢
      linarith
    · rw [show mixedWidth 5=7 by decide]
      norm_num only [Nat.cast_ofNat]
      have h := pow_le_log_bound (by norm_num) 32 11 (by norm_num : (2:ℝ)^32≤9^11)
      norm_num at h ⊢
      linarith
    · rw [show mixedWidth 6=7 by decide]
      norm_num only [Nat.cast_ofNat]
      have h := pow_le_log_bound (by norm_num) 32 11 (by norm_num : (2:ℝ)^32≤10^11)
      norm_num at h ⊢
      linarith
  · have ht : 10/3 ≤ t := by
      have hnp : (11:ℝ)≤(n:ℝ)+4 := by exact_mod_cast (by omega : 11≤n+4)
      have he := pow_le_log_bound (by positivity : 0 < (n:ℝ)+4) 10 3
        ((by norm_num : (2:ℝ)^10≤11^3).trans (pow_le_pow_left₀ (by norm_num) hnp 3))
      dsimp [t]
      norm_num only [Nat.cast_ofNat] at he
      linarith
    have hnreal : (0:ℝ) < n := by exact_mod_cast hn
    have hnlog : Real.logb 2 (n:ℝ) ≤ t := Real.logb_le_logb_of_le (by norm_num) hnreal (by linarith)
    have h2 : (Nat.log 2 n : ℝ) ≤ t := (Real.natLog_le_logb n 2).trans hnlog
    have hp : 0 < 2*Sudoku.p*Sudoku.q*n := by positivity
    have h3nat : 3 ^ Nat.log 3 (2*Sudoku.p*Sudoku.q*n) ≤ 2*Sudoku.p*Sudoku.q*n := Nat.pow_log_le_self 3 (by omega)
    have h3real : (3:ℝ) ^ Nat.log 3 (2*Sudoku.p*Sudoku.q*n) ≤ (2*Sudoku.p*Sudoku.q:ℕ) * (n:ℝ) := by exact_mod_cast h3nat
    have h3log := Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2) (by positivity : 0 < (3:ℝ)^Nat.log 3 (2*Sudoku.p*Sudoku.q*n)) h3real
    rw [Real.logb_pow,Real.logb_mul (by norm_num [Sudoku.p,Sudoku.q]) (by positivity)] at h3log
    have h3base : (19:ℝ) ≤ 12 * Real.logb 2 3 := pow_le_log_bound (by norm_num) 19 12 (by norm_num)
    have harith : Real.logb 2 ((2*Sudoku.p*Sudoku.q:ℕ):ℝ) ≤ (75/8:ℝ) := by
      have hh := Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2)
        (by norm_num [Sudoku.p,Sudoku.q] : (0:ℝ)<((2*Sudoku.p*Sudoku.q:ℕ):ℝ)^8)
        (show (((2*Sudoku.p*Sudoku.q:ℕ):ℝ)^8)≤(2:ℝ)^75 by norm_num [Sudoku.p,Sudoku.q])
      rw [Real.logb_pow,logb_two_pow] at hh
      norm_num at hh
      linarith
    have h3 : 19 * (Nat.log 3 (2*Sudoku.p*Sudoku.q*n) : ℝ) ≤ (225/2:ℝ)+12*t := by
      have hu := mul_le_mul_of_nonneg_left h3base (Nat.cast_nonneg (α:=ℝ) (Nat.log 3 (2*Sudoku.p*Sudoku.q*n)))
      have hh := mul_le_mul_of_nonneg_left h3log (by norm_num : (0:ℝ)≤12)
      norm_num [Sudoku.p,Sudoku.q] at hu hh harith hnlog ⊢
      nlinarith only [hu,hh,harith,hnlog]
    unfold mixedWidth mixedPayloadWidth
    push_cast
    change max ((Nat.log 2 n:ℝ)+1) ((Nat.log 3 (2*Sudoku.p*Sudoku.q*n):ℝ)+1) ≤ (11/4:ℝ)*t
    apply max_le
    · linarith only [h2,ht]
    · linarith only [h3,ht]

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

/-- Two rational power comparisons sharpen the small-input log-log constant. -/
theorem mixed_loglog_lower_sharp {n : ℕ} (hn : 0<n) :
    (121/100:ℝ)≤Real.logb 2 (Real.logb 2 ((n:ℝ)+4)) := by
  have h5 := pow_le_log_bound (by norm_num : (0:ℝ)<5) 58 25 (by norm_num : (2:ℝ)^58≤5^25)
  have h58 := pow_le_log_bound (by norm_num : (0:ℝ)<58/25) 121 100 (by norm_num : (2:ℝ)^121≤(58/25)^100)
  have ht := Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2) (by norm_num : (0:ℝ)<5)
    (show (5:ℝ)≤(n:ℝ)+4 by exact_mod_cast (by omega : 5≤n+4))
  have hh := Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2) (by norm_num : (0:ℝ)<58/25)
    (show (58/25:ℝ)≤Real.logb 2 ((n:ℝ)+4) by norm_num at h5; linarith)
  norm_num at h58
  linarith

set_option exponentiation.threshold 2000 in
theorem channel_cap_real_bound (d k : ℕ)
    (hcoeff : (d:ℝ)*((7/2:ℝ)*Sudoku.Width+1)*(1987/242:ℝ) ≤ k)
    {n : ℕ} (hn : 0<n) :
    (((Sudoku.Width * mixedWidth n + 2) ^ (d*(Sudoku.Width*mixedWidth n+2)) : ℕ):ℝ) ≤
      ((n:ℝ)+4) ^ ((k:ℝ) * Real.logb 2 (Real.logb 2 ((n:ℝ)+4))) := by
  let C := Sudoku.Width*mixedWidth n+2
  let t := Real.logb 2 ((n:ℝ)+4)
  let g := Real.logb 2 t
  let a : ℝ := (7/2:ℝ)*Sudoku.Width+1
  have ht : 2 ≤ t := by
    have h := pow_le_log_bound (by positivity : 0 < (n:ℝ)+4) 2 1 (by simpa only [pow_one,show (2:ℝ)^2 = 4 by norm_num] using (show (4:ℝ) ≤ (n:ℝ)+4 by have := Nat.cast_nonneg (α := ℝ) n; linarith))
    simpa [t] using h
  have hg : (121/100:ℝ) ≤ g := mixed_loglog_lower_sharp hn
  have hC : (C:ℝ) ≤ a*t := by
    have hw := mixedWidth_le_log hn
    dsimp [C,a,t]
    push_cast
    nlinarith
  have hCpos : (0:ℝ) < C := by dsimp [C]; positivity
  have ha : Real.logb 2 a ≤ 349/40 := by
    have hh := Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2) (by norm_num [a,Sudoku.Width,Sudoku.q] : (0:ℝ)<a^40)
      (show a^40≤(2:ℝ)^349 by norm_num [a,Sudoku.Width,Sudoku.q])
    rw [Real.logb_pow,logb_two_pow] at hh
    norm_num at hh
    linarith
  have hlog : Real.logb 2 (C:ℝ) ≤ (1987/242:ℝ)*g := by
    have hh := Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2) hCpos hC
    rw [Real.logb_mul (by norm_num [a,Sudoku.Width,Sudoku.q]) (by linarith)] at hh
    change Real.logb 2 (C:ℝ)≤(1987/242:ℝ)*Real.logb 2 t
    dsimp [g] at hg
    have helper (u v w : ℝ) (hu : u≤(349/40:ℝ)) (hv : (121/100:ℝ)≤v) (hw : w≤u+v) : w≤(1987/242:ℝ)*v := by linarith
    exact helper _ _ _ ha hg hh
  have hc1 : 1 ≤ (C:ℝ) := by
    have hnat : 1 ≤ C := by dsimp [C]; omega
    exact_mod_cast hnat
  have he : (d:ℝ)*(C:ℝ)*Real.logb 2 (C:ℝ) ≤ (k:ℝ)*t*g := by
    have hclog : 0 ≤ Real.logb 2 (C:ℝ) := Real.logb_nonneg (by norm_num) hc1
    have hmul := mul_le_mul hC hlog hclog (by dsimp [a]; positivity : 0 ≤ a*t)
    have hconst : (d:ℝ)*a*(1987/242:ℝ) ≤ (k:ℝ) := hcoeff
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

set_option exponentiation.threshold 2000 in
theorem channel_product_le_binary (N C e f k : ℕ) (hN : N≤C^e*3^f)
    (hbase : C^100≤2^991) (hexp : 991*e+160*f≤100*k) : N≤2^k := by
  apply (Nat.pow_le_pow_iff_left (by decide : 100≠0)).mp
  calc
    N^100 ≤ (C^e*3^f)^100 := Nat.pow_le_pow_left hN _
    _ = (C^100)^e*(3^5)^(20*f) := by simp only [mul_pow,←pow_mul]; ring_nf
    _ ≤ (2^991)^e*(2^8)^(20*f) := Nat.mul_le_mul (Nat.pow_le_pow_left hbase _) (Nat.pow_le_pow_left (by norm_num : 3^5≤2^8) _)
    _ = 2^(991*e+160*f) := by simp only [←pow_mul,←pow_add]; congr 1; ring
    _ ≤ 2^(k*100) := Nat.pow_le_pow_right (by decide) (by omega)
    _ = (2^k)^100 := pow_mul _ _ _

set_option exponentiation.threshold 2000 in
theorem dyadic_channel_product_le_binary (N C e f k : ℕ) (hN : N≤C^e*3^f)
    (hbase : C≤2^8) (hexp : 40*e+8*f≤5*k) : N≤2^k := by
  apply (Nat.pow_le_pow_iff_left (by decide : 5≠0)).mp
  calc
    N^5 ≤ (C^e*3^f)^5 := Nat.pow_le_pow_left hN _
    _ = C^(5*e)*(3^5)^f := by simp only [mul_pow,←pow_mul]; congr 1 <;> ring
    _ ≤ (2^8)^(5*e)*(2^8)^f := Nat.mul_le_mul
      (Nat.pow_le_pow_left hbase _) (Nat.pow_le_pow_left (by norm_num : 3^5≤2^8) _)
    _ = 2^(40*e+8*f) := by simp only [←pow_mul,←pow_add]; congr 1; ring
    _ ≤ 2^(k*5) := Nat.pow_le_pow_right (by decide) (by omega)
    _ = (2^k)^5 := pow_mul _ _ _

set_option exponentiation.threshold 2000 in
theorem sharp_channel_cap_real_bound {n N : ℕ} (hn : 0<n)
    (hN : N≤(max (Sudoku.Width*mixedWidth n+2) 256)^(33*(Sudoku.Width*mixedWidth n)+466)*3^(4*(Sudoku.Width*mixedWidth n)+4)) :
    (N:ℝ)≤((n:ℝ)+4)^((1.75*(10:ℝ)^4)*Real.logb 2 (Real.logb 2 ((n:ℝ)+4))) := by
  let w := Sudoku.Width*mixedWidth n
  let P := max (w+2) 256
  let t := Real.logb 2 ((n:ℝ)+4)
  let g := Real.logb 2 t
  have hP : 256≤P := le_max_right _ _
  have ht : (65/28:ℝ)≤t := by
    have h5 := pow_le_log_bound (by norm_num : (0:ℝ)<5) 65 28 (by norm_num : (2:ℝ)^65≤5^28)
    have hh := Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2) (by norm_num : (0:ℝ)<5)
      (show (5:ℝ)≤(n:ℝ)+4 by exact_mod_cast (by omega : 5≤n+4))
    dsimp [t]
    norm_num at h5
    linarith
  have hg : (243/200:ℝ)≤g := by
    have hh := pow_le_log_bound (by norm_num : (0:ℝ)<65/28) 243 200 (by norm_num : (2:ℝ)^243≤(65/28)^200)
    have hm := Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2) (by norm_num : (0:ℝ)<65/28) ht
    dsimp [g]
    norm_num at hh
    linarith
  have hw : (w:ℝ)≤77*t := by
    have hh := mixedWidth_le_log hn
    dsimp [w,t]
    norm_num only [Sudoku.Width,Sudoku.q,Nat.cast_mul,Nat.cast_ofNat]
    nlinarith
  have hPpos : (0:ℝ)<P := by exact_mod_cast (by omega : 0<P)
  have he : ((33*w+466:ℕ):ℝ)*Real.logb 2 (P:ℝ)+((4*w+4:ℕ):ℝ)*Real.logb 2 3≤17500*t*g := by
    by_cases hone : n=1
    · have hwone : w=168 := by simp [w,hone,mixedWidth_one,Sudoku.Width,Sudoku.q]
      have hPone : P=256 := by simp [P,hwone]
      have hl : Real.logb 2 (P:ℝ)≤8 := by
        rw [hPone]
        have hh := logb_two_pow 8
        norm_num at hh ⊢
        exact hh.le
      have hl3 : Real.logb 2 3≤8/5 := by
        have hh := Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2) (by norm_num : (0:ℝ)<3^5) (show (3:ℝ)^5≤(2:ℝ)^8 by norm_num)
        rw [Real.logb_pow,logb_two_pow] at hh
        norm_num at hh
        linarith
      have htg := mul_le_mul ht hg (by norm_num : (0:ℝ)≤243/200) (by linarith : 0≤t)
      rw [hwone]
      norm_num only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
      nlinarith only [hl,hl3,htg]
    · have ht' : (31/12:ℝ)≤t := by
        have hh := pow_le_log_bound (by positivity : 0<(n:ℝ)+4) 31 12
          ((by norm_num : (2:ℝ)^31≤6^12).trans
            (pow_le_pow_left₀ (by norm_num) (show (6:ℝ)≤(n:ℝ)+4 by exact_mod_cast (by omega : 6≤n+4)) 12))
        dsimp [t]
        norm_num at hh
        linarith
      have hg' : (4/3:ℝ)≤g := by
        have hh := pow_le_log_bound (by norm_num : (0:ℝ)<31/12) 4 3 (by norm_num)
        have hm := Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2) (by norm_num : (0:ℝ)<31/12) ht'
        dsimp [g]
        norm_num at hh
        linarith
      have hPreal : (P:ℝ)≤100*t := by
        dsimp [P]
        push_cast
        exact max_le (by push_cast; linarith) (by linarith)
      have hl100 : Real.logb 2 (100:ℝ)≤20/3 := by
        have hh := Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2)
          (by norm_num : (0:ℝ)<100^3) (show (100:ℝ)^3≤(2:ℝ)^20 by norm_num)
        rw [Real.logb_pow,logb_two_pow] at hh
        norm_num at hh
        linarith
      have hlog : Real.logb 2 (P:ℝ)≤(6:ℝ)*g := by
        have hh := Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2) hPpos hPreal
        rw [Real.logb_mul (by norm_num : (100:ℝ)≠0) (by linarith : t≠0)] at hh
        dsimp [g] at hg' ⊢
        linarith
      have he' : ((34*w+467:ℕ):ℝ)≤(2618+467*12/31:ℝ)*t := by
        push_cast
        linarith
      have hpos : 0≤Real.logb 2 (P:ℝ) := Real.logb_nonneg (by norm_num)
        (by exact_mod_cast (by omega : 1≤P))
      have hh := mul_le_mul he' hlog hpos (by positivity : 0≤(2618+467*12/31:ℝ)*t)
      have hc := mul_le_mul_of_nonneg_right
        (show (2618+467*12/31:ℝ)*6≤17500 by norm_num) (show 0≤t*g by positivity)
      have hthree : 4*Real.logb 2 3≤Real.logb 2 (P:ℝ) := by
        have hbase : (3:ℝ)^4≤(P:ℝ) := by norm_num; exact_mod_cast (by omega : 81≤P)
        have hl := Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2) (by norm_num : (0:ℝ)<3^4) hbase
        simpa only [Real.logb_pow,Nat.cast_ofNat] using hl
      have hmul := mul_le_mul_of_nonneg_right hthree (show (0:ℝ)≤w+1 by positivity)
      push_cast at hh ⊢
      nlinarith only [hh,hc,hmul]
  have hpow : ((P^(33*w+466)*3^(4*w+4):ℕ):ℝ)≤((n:ℝ)+4)^((1.75*(10:ℝ)^4)*g) := by
    push_cast
    apply (Real.logb_le_logb (by norm_num : (1:ℝ)<2) (by positivity) (by positivity)).mp
    rw [Real.logb_mul (by positivity) (by positivity),Real.logb_pow,Real.logb_pow,
      Real.logb_rpow_eq_mul_logb_of_pos (by positivity : 0<(n:ℝ)+4)]
    change _≤(1.75*(10:ℝ)^4)*g*t
    nlinarith only [he]
  exact (show (N:ℝ)≤((P^(33*w+466)*3^(4*w+4):ℕ):ℝ) by exact_mod_cast hN).trans hpow

end
end TranslationTiling.Compiler.Size
