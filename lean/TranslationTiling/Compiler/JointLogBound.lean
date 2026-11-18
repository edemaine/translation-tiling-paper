import TranslationTiling.FiniteCompiler.MixedCompiler
import TranslationTiling.FiniteCompiler.Effective.JointCode
import TranslationTiling.FiniteCompiler.Effective.SmallParameters
import Mathlib.Analysis.SpecialFunctions.Log.Base

namespace TranslationTiling.Compiler.Size
open FiniteCompiler.Effective
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 2000

private theorem logb_two_pow (k : ℕ) : Real.logb 2 ((2:ℝ)^k)=k := by
  rw [Real.logb_pow]
  norm_num [Real.logb_self_eq_one]

private theorem pow_le_log_bound {x : ℝ} (hx : 0<x) (a b : ℕ)
    (h : (2:ℝ)^a≤x^b) : (a:ℝ)≤b*Real.logb 2 x := by
  have hl := Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2) (by positivity : 0<(2:ℝ)^a) h
  simpa [Real.logb_pow,Real.logb_self_eq_one] using hl

private theorem lg_three_lower : (3/2:ℝ)≤Real.logb 2 3 := by
  have h := pow_le_log_bound (by norm_num : (0:ℝ)<3) 3 2 (by norm_num)
  norm_num at h
  linarith

private theorem lg_three_upper : Real.logb 2 3≤(8/5:ℝ) := by
  have h := Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2)
    (by norm_num : (0:ℝ)<3^5) (show (3:ℝ)^5≤(2:ℝ)^8 by norm_num)
  rw [Real.logb_pow,logb_two_pow] at h
  norm_num at h
  linarith

theorem jointWidth_le_log {n : ℕ} (hn : 0<n) :
    (jointWidth n:ℝ)≤(2/3:ℝ)*Real.logb 2 ((n:ℝ)+4)+4 := by
  have hn0 : 8*n≠0 := by omega
  have hk : jointWidth n=Nat.log 3 (8*n)+2 := by
    unfold jointWidth
    rw [show 24*n=(8*n)*3 by omega,Nat.log_mul_base (by decide) hn0]
  have hp : 3^Nat.log 3 (8*n)≤8*n := Nat.pow_log_le_self 3 hn0
  have hl := Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2)
    (by positivity : 0<(3:ℝ)^Nat.log 3 (8*n)) (show (3:ℝ)^Nat.log 3 (8*n)≤8*(n:ℝ) by exact_mod_cast hp)
  rw [Real.logb_pow,Real.logb_mul (by norm_num) (by positivity)] at hl
  have h8 : Real.logb 2 (8:ℝ)=3 := by have hh := logb_two_pow 3; norm_num at hh ⊢; exact hh
  rw [h8] at hl
  have hmul := mul_le_mul_of_nonneg_left lg_three_lower
    (Nat.cast_nonneg (α:=ℝ) (Nat.log 3 (8*n)))
  have hlog := Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2)
    (by exact_mod_cast hn : (0:ℝ)<n) (show (n:ℝ)≤(n:ℝ)+4 by linarith)
  rw [hk]
  push_cast
  nlinarith only [hl,hmul,hlog]

private theorem t_lower {n : ℕ} {a b : ℕ} (hb : 0<b) (h : (2:ℝ)^a≤((n:ℝ)+4)^b) :
    (a:ℝ)/b≤Real.logb 2 ((n:ℝ)+4) := by
  have hh := pow_le_log_bound (by positivity : 0<(n:ℝ)+4) a b h
  apply (div_le_iff₀ (by exact_mod_cast hb : (0:ℝ)<b)).mpr
  nlinarith only [hh]

private theorem g_lower {n : ℕ} {u : ℝ} (hu : 0<u)
    (ht : u≤Real.logb 2 ((n:ℝ)+4)) (a b : ℕ) (hb : 0<b)
    (h : (2:ℝ)^a≤u^b) :
    (a:ℝ)/b≤Real.logb 2 (Real.logb 2 ((n:ℝ)+4)) := by
  have hh := pow_le_log_bound hu a b h
  have hm := Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2) hu ht
  apply (div_le_iff₀ (by exact_mod_cast hb : (0:ℝ)<b)).mpr
  nlinarith only [hh,hm]

theorem joint_channel_cap_real_bound {n N : ℕ} (hn : 0<n)
    (hN : N≤(max (Sudoku.Width*jointWidth n+2) 256)^(33*(Sudoku.Width*jointWidth n)+466)*
      3^(4*(Sudoku.Width*jointWidth n)+4)) :
    (N:ℝ)≤((n:ℝ)+4)^(6000*Real.logb 2 (Real.logb 2 ((n:ℝ)+4))) := by
  let w := Sudoku.Width*jointWidth n
  let P := max (w+2) 256
  let t := Real.logb 2 ((n:ℝ)+4)
  let g := Real.logb 2 t
  have hP : 256≤P := le_max_right _ _
  have hPpos : (0:ℝ)<P := by exact_mod_cast (by omega : 0<P)
  have htpos : 0<t := Real.logb_pos (by norm_num) (by have := Nat.cast_nonneg (α:=ℝ) n; linarith)
  have he : ((33*w+466:ℕ):ℝ)*Real.logb 2 (P:ℝ)+((4*w+4:ℕ):ℝ)*Real.logb 2 3≤6000*t*g := by
    push_cast
    by_cases hsmall : n<12
    · have hcases : (n=1 ∧ jointWidth n=3) ∨
          (2≤n ∧ n≤3 ∧ jointWidth n=4) ∨
          (4≤n ∧ n≤10 ∧ jointWidth n=5) ∨ (n=11 ∧ jointWidth n=6) := by
        interval_cases n <;> decide
      have hup (k : ℕ) (hk : jointWidth n=k) (hk' : k≤6) :
          ((33*w+466:ℕ):ℝ)*Real.logb 2 (P:ℝ)+((4*w+4:ℕ):ℝ)*Real.logb 2 3≤
            ((21632*k+18672:ℕ):ℝ)/5 := by
        have hw : w=16*k := by simp [w,hk,Sudoku.Width,Sudoku.q]
        have hp : P=256 := by dsimp [P]; omega
        have hl : Real.logb 2 (P:ℝ)=8 := by rw [hp]; have hh := logb_two_pow 8; norm_num at hh ⊢; exact hh
        rw [hl,hw]
        have hm := mul_le_mul_of_nonneg_left lg_three_upper (show (0:ℝ)≤4*(16*k)+4 by positivity)
        push_cast at hm ⊢
        nlinarith only [hm]
      rcases hcases with ⟨rfl,hk⟩ | ⟨hn2,_,hk⟩ | ⟨hn4,_,hk⟩ | ⟨rfl,hk⟩
      · have ht : (65/28:ℝ)≤t := t_lower (by decide) (by norm_num)
        have hg : (243/200:ℝ)≤g := g_lower (by norm_num) ht 243 200 (by decide) (by norm_num)
        have htg := mul_le_mul ht hg (by norm_num : (0:ℝ)≤243/200) htpos.le
        have hu := hup 3 hk (by omega)
        norm_num at hu
        nlinarith only [hu,htg]
      · have ht : (31/12:ℝ)≤t := t_lower (by decide)
          ((by norm_num : (2:ℝ)^31≤6^12).trans
            (pow_le_pow_left₀ (by norm_num) (show (6:ℝ)≤(n:ℝ)+4 by exact_mod_cast (by omega : 6≤n+4)) 12))
        have hg : (34/25:ℝ)≤g := g_lower (by norm_num) ht 34 25 (by decide) (by norm_num)
        have htg := mul_le_mul ht hg (by norm_num : (0:ℝ)≤34/25) htpos.le
        have hu := hup 4 hk (by omega)
        norm_num at hu
        nlinarith only [hu,htg]
      · have ht : (3:ℝ)≤t := by
          have h := t_lower (n:=n) (a:=3) (b:=1) (by decide)
            (by norm_num; exact_mod_cast (by omega : 8≤n+4))
          simpa using h
        have hg : (3/2:ℝ)≤g := g_lower (by norm_num) ht 3 2 (by decide) (by norm_num)
        have htg := mul_le_mul ht hg (by norm_num : (0:ℝ)≤3/2) htpos.le
        have hu := hup 5 hk (by omega)
        norm_num at hu
        nlinarith only [hu,htg]
      · have ht : (7/2:ℝ)≤t := t_lower (by decide) (by norm_num)
        have ht3 : (3:ℝ)≤t := by linarith
        have hg : (3/2:ℝ)≤g := g_lower (by norm_num) ht3 3 2 (by decide) (by norm_num)
        have htg := mul_le_mul ht hg (by norm_num : (0:ℝ)≤3/2) htpos.le
        have hu := hup 6 hk (by omega)
        norm_num at hu
        nlinarith only [hu,htg]
    · have ht : (4:ℝ)≤t := by
        have h := t_lower (n:=n) (a:=4) (b:=1) (by decide)
          (by norm_num; exact_mod_cast (by omega : 16≤n+4))
        simpa using h
      have hg : (2:ℝ)≤g := by
        have h := g_lower (by norm_num : (0:ℝ)<4) ht 2 1 (by decide) (by norm_num)
        simpa using h
      have hw : (w:ℝ)≤(80/3:ℝ)*t := by
        have h := jointWidth_le_log hn
        dsimp [w,t]
        norm_num only [Sudoku.Width,Sudoku.q,Nat.cast_mul,Nat.cast_ofNat]
        dsimp [t] at ht
        nlinarith
      have hPreal : (P:ℝ)≤64*t := by
        dsimp [P]
        push_cast
        exact max_le (by push_cast; linarith) (by linarith)
      have hl64 : Real.logb 2 (64:ℝ)=6 := by have hh := logb_two_pow 6; norm_num at hh ⊢; exact hh
      have hlog : Real.logb 2 (P:ℝ)≤4*g := by
        have h := Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2) hPpos hPreal
        rw [Real.logb_mul (by norm_num : (64:ℝ)≠0) (by linarith : t≠0),hl64] at h
        dsimp [g] at hg ⊢
        linarith
      have hloglo : (8:ℝ)≤Real.logb 2 (P:ℝ) := by
        have h := Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2) (by norm_num : (0:ℝ)<256)
          (show (256:ℝ)≤P by exact_mod_cast hP)
        have heq : Real.logb 2 (256:ℝ)=8 := by have hh := logb_two_pow 8; norm_num at hh ⊢; exact hh
        rwa [heq] at h
      have hthree : 4*Real.logb 2 3≤Real.logb 2 (P:ℝ) := by linarith [lg_three_upper]
      have hextra := mul_le_mul_of_nonneg_right hthree (show (0:ℝ)≤w+1 by positivity)
      have ha : ((34*w+467:ℕ):ℝ)≤(34*(80/3)+467/4:ℝ)*t := by push_cast; linarith
      have hh := mul_le_mul ha hlog (by linarith : 0≤Real.logb 2 (P:ℝ)) (by positivity : 0≤(34*(80/3)+467/4:ℝ)*t)
      have hc := mul_le_mul_of_nonneg_right (show (34*(80/3)+467/4:ℝ)*4≤6000 by norm_num)
        (show 0≤t*g by positivity)
      push_cast at hh ⊢
      nlinarith only [hh,hc,hextra]
  have hpow : ((P^(33*w+466)*3^(4*w+4):ℕ):ℝ)≤((n:ℝ)+4)^(6000*g) := by
    push_cast
    apply (Real.logb_le_logb (by norm_num : (1:ℝ)<2) (by positivity) (by positivity)).mp
    rw [Real.logb_mul (by positivity) (by positivity),Real.logb_pow,Real.logb_pow,
      Real.logb_rpow_eq_mul_logb_of_pos (by positivity : 0<(n:ℝ)+4)]
    change _≤6000*g*t
    nlinarith only [he]
  exact (show (N:ℝ)≤((P^(33*w+466)*3^(4*w+4):ℕ):ℝ) by exact_mod_cast hN).trans hpow

theorem dyadic_compact_real_bound {n N e : ℕ} (hN : N≤2^e)
    (he : (e:ℝ)≤2200*Real.logb 2 ((n:ℝ)+4)*Real.logb 2 (Real.logb 2 ((n:ℝ)+4))) :
    (N:ℝ)≤((n:ℝ)+4)^(2200*Real.logb 2 (Real.logb 2 ((n:ℝ)+4))) := by
  apply (show (N:ℝ)≤(2:ℝ)^e by exact_mod_cast hN).trans
  apply (Real.logb_le_logb (by norm_num : (1:ℝ)<2) (by positivity) (by positivity)).mp
  rw [logb_two_pow,Real.logb_rpow_eq_mul_logb_of_pos (by positivity : 0<(n:ℝ)+4)]
  nlinarith only [he]

theorem joint_compact_bulk_real_bound {n N : ℕ} (hn : 92≤n)
    (hN : N≤(max (Sudoku.Width*jointWidth n+2) 256)^(33*(Sudoku.Width*jointWidth n)+98)*
      3^(4*(Sudoku.Width*jointWidth n)+4)) :
    (N:ℝ)≤((n:ℝ)+4)^(2200*Real.logb 2 (Real.logb 2 ((n:ℝ)+4))) := by
  let w := Sudoku.Width*jointWidth n
  let P := max (w+2) 256
  let t := Real.logb 2 ((n:ℝ)+4)
  let g := Real.logb 2 t
  have hP : 256≤P := le_max_right _ _
  have hPpos : (0:ℝ)<P := by exact_mod_cast (by omega : 0<P)
  have ht : (13/2:ℝ)≤t := by
    have hh := t_lower (n:=n) (a:=13) (b:=2) (by decide)
      ((by norm_num : (2:ℝ)^13≤96^2).trans
        (pow_le_pow_left₀ (by norm_num) (show (96:ℝ)≤(n:ℝ)+4 by exact_mod_cast (by omega : 96≤n+4)) 2))
    simpa using hh
  have hg : (8/3:ℝ)≤g := g_lower (by norm_num) ht 8 3 (by decide) (by norm_num)
  have hw : (w:ℝ)≤(800/39:ℝ)*t := by
    have hh := jointWidth_le_log (by omega : 0<n)
    dsimp [w]
    norm_num only [Sudoku.Width,Sudoku.q,Nat.cast_mul,Nat.cast_ofNat]
    dsimp [t] at ht ⊢
    nlinarith
  have hp : (P:ℝ)≤(512/13:ℝ)*t := by
    dsimp [P]; push_cast
    exact max_le (by push_cast; linarith) (by linarith)
  have hconst : Real.logb 2 (512/13:ℝ)≤(16/3:ℝ) := by
    have hh := Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2)
      (by norm_num : (0:ℝ)<(512/13:ℝ)^3) (show (512/13:ℝ)^3≤(2:ℝ)^16 by norm_num)
    rw [Real.logb_pow,logb_two_pow] at hh
    norm_num at hh
    linarith
  have hlog : Real.logb 2 (P:ℝ)≤(3:ℝ)*g := by
    have hh := Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2) hPpos hp
    rw [Real.logb_mul (by norm_num : (512/13:ℝ)≠0) (by linarith : t≠0)] at hh
    change Real.logb 2 (P:ℝ)≤_ at hh
    dsimp [g] at hg ⊢
    linarith
  have hloglo : (8:ℝ)≤Real.logb 2 (P:ℝ) := by
    have hh := Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2) (by norm_num : (0:ℝ)<256)
      (show (256:ℝ)≤P by exact_mod_cast hP)
    have heq : Real.logb 2 (256:ℝ)=8 := by have hh := logb_two_pow 8; norm_num at hh ⊢; exact hh
    rwa [heq] at hh
  have hthree : 4*Real.logb 2 3≤Real.logb 2 (P:ℝ) := by linarith [lg_three_upper]
  have hextra := mul_le_mul_of_nonneg_right hthree (show (0:ℝ)≤w+1 by positivity)
  have ha : ((34*w+99:ℕ):ℝ)≤(34*(800/39)+198/13:ℝ)*t := by push_cast; linarith
  have hh := mul_le_mul ha hlog (by linarith : 0≤Real.logb 2 (P:ℝ))
    (by positivity : 0≤(34*(800/39)+198/13:ℝ)*t)
  have hc := mul_le_mul_of_nonneg_right
    (show (34*(800/39)+198/13:ℝ)*3≤2200 by norm_num) (show 0≤t*g by positivity)
  have he : ((33*w+98:ℕ):ℝ)*Real.logb 2 (P:ℝ)+((4*w+4:ℕ):ℝ)*Real.logb 2 3≤2200*t*g := by
    push_cast at hh ⊢
    nlinarith only [hh,hc,hextra]
  apply (show (N:ℝ)≤((P^(33*w+98)*3^(4*w+4):ℕ):ℝ) by exact_mod_cast hN).trans
  push_cast
  apply (Real.logb_le_logb (by norm_num : (1:ℝ)<2) (by positivity) (by positivity)).mp
  rw [Real.logb_mul (by positivity) (by positivity),Real.logb_pow,Real.logb_pow,
    Real.logb_rpow_eq_mul_logb_of_pos (by positivity : 0<(n:ℝ)+4)]
  change _≤2200*g*t
  nlinarith only [he]

theorem joint_compact_small_exponent {n : ℕ} (hn : 3≤n) (hn4 : n≠4) (hn5 : n≠5) (i : Fin 5)
    (hi : jointWidth n=3+i.val) :
    (SmallProfiles.exponent i:ℝ)≤2200*Real.logb 2 ((n:ℝ)+4)*
      Real.logb 2 (Real.logb 2 ((n:ℝ)+4)) := by
  let t := Real.logb 2 ((n:ℝ)+4)
  let g := Real.logb 2 t
  have htpos : 0<t := Real.logb_pos (by norm_num) (by have := Nat.cast_nonneg (α:=ℝ) n; linarith)
  fin_cases i
  · change jointWidth n=3+0 at hi
    have hm : jointWidth 3≤jointWidth n :=
      Nat.add_le_add_right (Nat.log_mono_right (Nat.mul_le_mul_left 24 hn)) 1
    have hc : jointWidth 3=4 := by decide
    omega
  · change jointWidth n=3+1 at hi
    have hn' : 3≤n := hn
    have ht : (14/5:ℝ)≤t := by
      have hh := t_lower (n:=n) (a:=14) (b:=5) (by decide)
        ((by norm_num : (2:ℝ)^14≤(3+4)^5).trans
          (pow_le_pow_left₀ (by norm_num) (show (3+4:ℝ)≤(n:ℝ)+4 by exact_mod_cast Nat.add_le_add_right hn' 4) 5))
      simpa [t] using hh
    have hg : (297/200:ℝ)≤g := g_lower (by norm_num) ht 297 200 (by decide) (by norm_num)
    have hh := mul_le_mul ht hg (by norm_num : (0:ℝ)≤297/200) htpos.le
    norm_num [SmallProfiles.exponent] at *
    nlinarith only [hh]
  · change jointWidth n=3+2 at hi
    have hn' : 4≤n := by
      by_contra h
      have hm : jointWidth n≤jointWidth (4-1) :=
        Nat.add_le_add_right (Nat.log_mono_right
          (Nat.mul_le_mul_left 24 (show n≤4-1 by omega))) 1
      have hc : jointWidth (4-1)<3+2 := by decide
      omega
    have hn6 : 6≤n := by omega
    have ht : (33/10:ℝ)≤t := by
      have hh := t_lower (n:=n) (a:=33) (b:=10) (by decide)
        ((by norm_num : (2:ℝ)^33≤(6+4)^10).trans
          (pow_le_pow_left₀ (by norm_num) (show (6+4:ℝ)≤(n:ℝ)+4 by exact_mod_cast Nat.add_le_add_right hn6 4) 10))
      simpa [t] using hh
    have hg : (17/10:ℝ)≤g := g_lower (by norm_num) ht 17 10 (by decide) (by norm_num)
    have hh := mul_le_mul ht hg (by norm_num : (0:ℝ)≤17/10) htpos.le
    norm_num [SmallProfiles.exponent] at *
    nlinarith only [hh]
  · change jointWidth n=3+3 at hi
    have hn' : 11≤n := by
      by_contra h
      have hm : jointWidth n≤jointWidth (11-1) :=
        Nat.add_le_add_right (Nat.log_mono_right
          (Nat.mul_le_mul_left 24 (show n≤11-1 by omega))) 1
      have hc : jointWidth (11-1)<3+3 := by decide
      omega
    have ht : (39/10:ℝ)≤t := by
      have hh := t_lower (n:=n) (a:=39) (b:=10) (by decide)
        ((by norm_num : (2:ℝ)^39≤(11+4)^10).trans
          (pow_le_pow_left₀ (by norm_num) (show (11+4:ℝ)≤(n:ℝ)+4 by exact_mod_cast Nat.add_le_add_right hn' 4) 10))
      simpa [t] using hh
    have hg : (49/25:ℝ)≤g := g_lower (by norm_num) ht 49 25 (by decide) (by norm_num)
    have hh := mul_le_mul ht hg (by norm_num : (0:ℝ)≤49/25) htpos.le
    norm_num [SmallProfiles.exponent] at *
    nlinarith only [hh]
  · change jointWidth n=3+4 at hi
    have hn' : 31≤n := by
      by_contra h
      have hm : jointWidth n≤jointWidth (31-1) :=
        Nat.add_le_add_right (Nat.log_mono_right
          (Nat.mul_le_mul_left 24 (show n≤31-1 by omega))) 1
      have hc : jointWidth (31-1)<3+4 := by decide
      omega
    have ht : (5/1:ℝ)≤t := by
      have hh := t_lower (n:=n) (a:=5) (b:=1) (by decide)
        ((by norm_num : (2:ℝ)^5≤(31+4)^1).trans
          (pow_le_pow_left₀ (by norm_num) (show (31+4:ℝ)≤(n:ℝ)+4 by exact_mod_cast Nat.add_le_add_right hn' 4) 1))
      simpa [t] using hh
    have hg : (23/10:ℝ)≤g := g_lower (by norm_num) ht 23 10 (by decide) (by norm_num)
    have hh := mul_le_mul ht hg (by norm_num : (0:ℝ)≤23/10) htpos.le
    norm_num [SmallProfiles.exponent] at *
    nlinarith only [hh]


theorem single_compact_exponent : (250:ℝ)≤2200*Real.logb 2 ((1:ℝ)+4)*Real.logb 2 (Real.logb 2 ((1:ℝ)+4)) := by
  have ht : (2:ℝ)≤Real.logb 2 ((1:ℝ)+4) := by
    have hh := t_lower (n:=1) (a:=2) (b:=1) (by decide) (by norm_num)
    simpa using hh
  have hg : (1:ℝ)≤Real.logb 2 (Real.logb 2 ((1:ℝ)+4)) := by
    have ht' : (2:ℝ)≤Real.logb 2 (((1:ℕ):ℝ)+4) := by simpa only [Nat.cast_one] using ht
    have hh := g_lower (n:=1) (by norm_num : (0:ℝ)<2) ht' 1 1 (by decide) (by norm_num)
    simpa only [Nat.cast_one,Nat.cast_ofNat,div_one] using hh
  have hh := mul_le_mul ht hg (by norm_num : (0:ℝ)≤1) (by linarith : (0:ℝ)≤Real.logb 2 ((1:ℝ)+4))
  nlinarith only [hh]

theorem mixed_compact_exponent (k : Fin 3) {n : ℕ}
    (hn : n=FiniteCompiler.MixedCompiler.Profiles.count k) :
    (FiniteCompiler.MixedCompiler.Profiles.exponent k:ℝ)≤2200*Real.logb 2 ((n:ℝ)+4)*
      Real.logb 2 (Real.logb 2 ((n:ℝ)+4)) := by
  subst n
  fin_cases k
  · change (7736:ℝ)≤2200*Real.logb 2 ((2:ℝ)+4)*Real.logb 2 (Real.logb 2 ((2:ℝ)+4))
    have ht : (137/53:ℝ)≤Real.logb 2 ((2:ℝ)+4) := by
      simpa only [Nat.cast_ofNat,Nat.cast_one,div_one] using (t_lower (n:=2) (a:=137) (b:=53) (by decide) (by norm_num))
    have hg : (63/46:ℝ)≤Real.logb 2 (Real.logb 2 ((2:ℝ)+4)) :=
      g_lower (n:=2) (by norm_num) ht 63 46 (by decide) (by norm_num)
    have hh := mul_le_mul ht hg (by norm_num : (0:ℝ)≤63/46) (le_trans (by norm_num : (0:ℝ)≤137/53) ht)
    norm_num at hh ⊢
    nlinarith only [hh]
  · change (9460:ℝ)≤2200*Real.logb 2 ((4:ℝ)+4)*Real.logb 2 (Real.logb 2 ((4:ℝ)+4))
    have ht : (3/1:ℝ)≤Real.logb 2 ((4:ℝ)+4) := by
      simpa only [Nat.cast_ofNat,Nat.cast_one,div_one] using (t_lower (n:=4) (a:=3) (b:=1) (by decide) (by norm_num))
    have hg : (19/12:ℝ)≤Real.logb 2 (Real.logb 2 ((4:ℝ)+4)) :=
      g_lower (n:=4) (by norm_num) ht 19 12 (by decide) (by norm_num)
    have hh := mul_le_mul ht hg (by norm_num : (0:ℝ)≤19/12) (le_trans (by norm_num : (0:ℝ)≤3/1) ht)
    norm_num at hh ⊢
    nlinarith only [hh]
  · change (10019:ℝ)≤2200*Real.logb 2 ((5:ℝ)+4)*Real.logb 2 (Real.logb 2 ((5:ℝ)+4))
    have ht : (31/10:ℝ)≤Real.logb 2 ((5:ℝ)+4) := by
      simpa only [Nat.cast_ofNat,Nat.cast_one,div_one] using (t_lower (n:=5) (a:=31) (b:=10) (by decide) (by norm_num))
    have hg : (8/5:ℝ)≤Real.logb 2 (Real.logb 2 ((5:ℝ)+4)) :=
      g_lower (n:=5) (by norm_num) ht 8 5 (by decide) (by norm_num)
    have hh := mul_le_mul ht hg (by norm_num : (0:ℝ)≤8/5) (le_trans (by norm_num : (0:ℝ)≤31/10) ht)
    norm_num at hh ⊢
    nlinarith only [hh]

end
end TranslationTiling.Compiler.Size
