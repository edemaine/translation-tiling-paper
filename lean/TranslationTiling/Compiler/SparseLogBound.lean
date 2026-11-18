import TranslationTiling.FiniteCompiler.SparseSmallCompiler
import TranslationTiling.FiniteCompiler.SparseTernaryCode
import Mathlib.Analysis.SpecialFunctions.Log.Base

namespace TranslationTiling.Compiler.Size
open FiniteCompiler.Effective
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
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

theorem sparseWidth_le_log {n : ℕ} (hn : 0<n) :
    (FiniteCompiler.SparseTernary.width n:ℝ)≤2*Real.logb 2 ((n:ℝ)+4)+66 := by
  have hp := Nat.pow_log_le_self 3 (by omega : n≠0)
  have hl := Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2)
    (by positivity : 0<(3:ℝ)^Nat.log 3 n)
    (show (3:ℝ)^Nat.log 3 n≤n by exact_mod_cast hp)
  rw [Real.logb_pow] at hl
  have hm := mul_le_mul_of_nonneg_left lg_three_lower (Nat.cast_nonneg (α:=ℝ) (Nat.log 3 n))
  have hlog := Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2)
    (by exact_mod_cast hn : (0:ℝ)<n) (show (n:ℝ)≤(n:ℝ)+4 by linarith)
  have hw := FiniteCompiler.SparseTernary.width_upper n
  unfold FiniteCompiler.SparseTernary.tileWidth at hw
  have hw' : (FiniteCompiler.SparseTernary.width n:ℝ)≤48+3*((Nat.log 3 n:ℝ)+1)+15 := by exact_mod_cast hw
  nlinarith only [hl,hm,hlog,hw']

theorem sparse_dyadic_real_bound {n N e : ℕ} (hN : N≤2^e)
    (he : (e:ℝ)≤1350*Real.logb 2 ((n:ℝ)+4)*Real.logb 2 (Real.logb 2 ((n:ℝ)+4))) :
    (N:ℝ)≤((n:ℝ)+4)^(1350*Real.logb 2 (Real.logb 2 ((n:ℝ)+4))) := by
  apply (show (N:ℝ)≤(2:ℝ)^e by exact_mod_cast hN).trans
  apply (Real.logb_le_logb (by norm_num : (1:ℝ)<2) (by positivity) (by positivity)).mp
  rw [logb_two_pow,Real.logb_rpow_eq_mul_logb_of_pos (by positivity : 0<(n:ℝ)+4)]
  nlinarith only [he]

theorem sparse_bulk_real_bound {n N : ℕ} (hn : 252≤n)
    (hN : N≤(max (FiniteCompiler.SparseTernary.width n+2) 256)^(33*(FiniteCompiler.SparseTernary.width n)+98)*
      3^(4*(FiniteCompiler.SparseTernary.width n)+4)) :
    (N:ℝ)≤((n:ℝ)+4)^(1350*Real.logb 2 (Real.logb 2 ((n:ℝ)+4))) := by
  let w := FiniteCompiler.SparseTernary.width n
  let P := max (w+2) 256
  let t := Real.logb 2 ((n:ℝ)+4)
  let g := Real.logb 2 t
  have hP : 256≤P := le_max_right _ _
  have hPpos : (0:ℝ)<P := by exact_mod_cast (by omega : 0<P)
  have ht : (8:ℝ)≤t := by
    have hh := t_lower (n:=n) (a:=8) (b:=1) (by decide)
      (by norm_num; exact_mod_cast (by omega : 256≤n+4))
    simpa using hh
  have hg : (3:ℝ)≤g := by
    have hh := g_lower (n:=n) (by norm_num : (0:ℝ)<8) ht 3 1 (by decide) (by norm_num)
    simpa using hh
  have hw : (w:ℝ)≤(41/4:ℝ)*t := by
    have hh := sparseWidth_le_log (by omega : 0<n)
    dsimp [w,t] at *
    linarith
  have hp : (P:ℝ)≤32*t := by
    dsimp [P]; push_cast
    exact max_le (by push_cast; linarith) (by linarith)
  have hl32 : Real.logb 2 (32:ℝ)=5 := by
    have hh := logb_two_pow 5
    norm_num at hh ⊢
    exact hh
  have hlog : Real.logb 2 (P:ℝ)≤(8/3:ℝ)*g := by
    have hh := Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2) hPpos hp
    rw [Real.logb_mul (by norm_num : (32:ℝ)≠0) (by linarith : t≠0),hl32] at hh
    dsimp [g] at hg ⊢
    linarith
  have hloglo : (8:ℝ)≤Real.logb 2 (P:ℝ) := by
    have hh := Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2) (by norm_num : (0:ℝ)<256)
      (show (256:ℝ)≤P by exact_mod_cast hP)
    have heq : Real.logb 2 (256:ℝ)=8 := by have hh := logb_two_pow 8; norm_num at hh ⊢; exact hh
    rwa [heq] at hh
  have hthree : 4*Real.logb 2 3≤Real.logb 2 (P:ℝ) := by linarith [lg_three_upper]
  have hextra := mul_le_mul_of_nonneg_right hthree (show (0:ℝ)≤w+1 by positivity)
  have ha : ((34*w+99:ℕ):ℝ)≤(34*(41/4)+99/8:ℝ)*t := by push_cast; linarith
  have hh := mul_le_mul ha hlog (by linarith : 0≤Real.logb 2 (P:ℝ))
    (by positivity : 0≤(34*(41/4)+99/8:ℝ)*t)
  have hc := mul_le_mul_of_nonneg_right
    (show (34*(41/4)+99/8:ℝ)*(8/3)≤1350 by norm_num) (show 0≤t*g by positivity)
  have he : ((33*w+98:ℕ):ℝ)*Real.logb 2 (P:ℝ)+((4*w+4:ℕ):ℝ)*Real.logb 2 3≤1350*t*g := by
    push_cast at hh ⊢
    nlinarith only [hh,hc,hextra]
  apply (show (N:ℝ)≤((P^(33*w+98)*3^(4*w+4):ℕ):ℝ) by exact_mod_cast hN).trans
  push_cast
  apply (Real.logb_le_logb (by norm_num : (1:ℝ)<2) (by positivity) (by positivity)).mp
  rw [Real.logb_mul (by positivity) (by positivity),Real.logb_pow,Real.logb_pow,
    Real.logb_rpow_eq_mul_logb_of_pos (by positivity : 0<(n:ℝ)+4)]
  change _≤1350*g*t
  nlinarith only [he]


theorem sparse_small_exponent (k : Fin 7) {n : ℕ}
    (hlen : n=FiniteCompiler.SparseSmallCompiler.Profiles.count k) :
    (FiniteCompiler.SparseSmallCompiler.Profiles.exponent k:ℝ)≤
      1350*Real.logb 2 ((n:ℝ)+4)*Real.logb 2 (Real.logb 2 ((n:ℝ)+4)) := by
  fin_cases k
  · subst n
    change (6300:ℝ)≤1350*Real.logb 2 ((4:ℝ)+4)*Real.logb 2 (Real.logb 2 ((4:ℝ)+4))
    have ht : (3/1:ℝ)≤Real.logb 2 ((4:ℝ)+4) := by
      simpa using (t_lower (n:=4) (a:=3) (b:=1) (by decide) (by norm_num))
    have hg := g_lower (n:=4) (by norm_num : (0:ℝ)<3/1) ht 19 12 (by decide) (by norm_num)
    have hm := mul_le_mul ht hg (by norm_num : (0:ℝ)≤19/12) (Real.logb_pos (by norm_num : (1:ℝ)<2) (by norm_num : (1:ℝ)<(4:ℝ)+4)).le
    norm_num at hm ⊢
    nlinarith only [hm]
  · subst n
    change (6400:ℝ)≤1350*Real.logb 2 ((5:ℝ)+4)*Real.logb 2 (Real.logb 2 ((5:ℝ)+4))
    have ht : (31/10:ℝ)≤Real.logb 2 ((5:ℝ)+4) := by
      simpa using (t_lower (n:=5) (a:=31) (b:=10) (by decide) (by norm_num))
    have hg := g_lower (n:=5) (by norm_num : (0:ℝ)<31/10) ht 163 100 (by decide) (by norm_num)
    have hm := mul_le_mul ht hg (by norm_num : (0:ℝ)≤163/100) (Real.logb_pos (by norm_num : (1:ℝ)<2) (by norm_num : (1:ℝ)<(5:ℝ)+4)).le
    norm_num at hm ⊢
    nlinarith only [hm]
  · subst n
    change (6500:ℝ)≤1350*Real.logb 2 ((6:ℝ)+4)*Real.logb 2 (Real.logb 2 ((6:ℝ)+4))
    have ht : (33/10:ℝ)≤Real.logb 2 ((6:ℝ)+4) := by
      simpa using (t_lower (n:=6) (a:=33) (b:=10) (by decide) (by norm_num))
    have hg := g_lower (n:=6) (by norm_num : (0:ℝ)<33/10) ht 17 10 (by decide) (by norm_num)
    have hm := mul_le_mul ht hg (by norm_num : (0:ℝ)≤17/10) (Real.logb_pos (by norm_num : (1:ℝ)<2) (by norm_num : (1:ℝ)<(6:ℝ)+4)).le
    norm_num at hm ⊢
    nlinarith only [hm]
  · subst n
    change (7000:ℝ)≤1350*Real.logb 2 ((7:ℝ)+4)*Real.logb 2 (Real.logb 2 ((7:ℝ)+4))
    have ht : (17/5:ℝ)≤Real.logb 2 ((7:ℝ)+4) := by
      simpa using (t_lower (n:=7) (a:=17) (b:=5) (by decide) (by norm_num))
    have hg := g_lower (n:=7) (by norm_num : (0:ℝ)<17/5) ht 7 4 (by decide) (by norm_num)
    have hm := mul_le_mul ht hg (by norm_num : (0:ℝ)≤7/4) (Real.logb_pos (by norm_num : (1:ℝ)<2) (by norm_num : (1:ℝ)<(7:ℝ)+4)).le
    norm_num at hm ⊢
    nlinarith only [hm]
  · subst n
    change (7000:ℝ)≤1350*Real.logb 2 ((8:ℝ)+4)*Real.logb 2 (Real.logb 2 ((8:ℝ)+4))
    have ht : (17/5:ℝ)≤Real.logb 2 ((8:ℝ)+4) := by
      simpa using (t_lower (n:=8) (a:=17) (b:=5) (by decide) (by norm_num))
    have hg := g_lower (n:=8) (by norm_num : (0:ℝ)<17/5) ht 7 4 (by decide) (by norm_num)
    have hm := mul_le_mul ht hg (by norm_num : (0:ℝ)≤7/4) (Real.logb_pos (by norm_num : (1:ℝ)<2) (by norm_num : (1:ℝ)<(8:ℝ)+4)).le
    norm_num at hm ⊢
    nlinarith only [hm]
  · subst n
    change (7000:ℝ)≤1350*Real.logb 2 ((9:ℝ)+4)*Real.logb 2 (Real.logb 2 ((9:ℝ)+4))
    have ht : (17/5:ℝ)≤Real.logb 2 ((9:ℝ)+4) := by
      simpa using (t_lower (n:=9) (a:=17) (b:=5) (by decide) (by norm_num))
    have hg := g_lower (n:=9) (by norm_num : (0:ℝ)<17/5) ht 7 4 (by decide) (by norm_num)
    have hm := mul_le_mul ht hg (by norm_num : (0:ℝ)≤7/4) (Real.logb_pos (by norm_num : (1:ℝ)<2) (by norm_num : (1:ℝ)<(9:ℝ)+4)).le
    norm_num at hm ⊢
    nlinarith only [hm]
  · subst n
    change (7000:ℝ)≤1350*Real.logb 2 ((10:ℝ)+4)*Real.logb 2 (Real.logb 2 ((10:ℝ)+4))
    have ht : (17/5:ℝ)≤Real.logb 2 ((10:ℝ)+4) := by
      simpa using (t_lower (n:=10) (a:=17) (b:=5) (by decide) (by norm_num))
    have hg := g_lower (n:=10) (by norm_num : (0:ℝ)<17/5) ht 7 4 (by decide) (by norm_num)
    have hm := mul_le_mul ht hg (by norm_num : (0:ℝ)≤7/4) (Real.logb_pos (by norm_num : (1:ℝ)<2) (by norm_num : (1:ℝ)<(10:ℝ)+4)).le
    norm_num at hm ⊢
    nlinarith only [hm]

theorem sparse_medium_exponent {n : ℕ} (hn : 11≤n) :
    (9124:ℝ)≤1350*Real.logb 2 ((n:ℝ)+4)*Real.logb 2 (Real.logb 2 ((n:ℝ)+4)) := by
  have ht : (39/10:ℝ)≤Real.logb 2 ((n:ℝ)+4) := t_lower (n:=n) (a:=39) (b:=10) (by decide)
    ((by norm_num : (2:ℝ)^39≤15^10).trans
      (pow_le_pow_left₀ (by norm_num) (show (15:ℝ)≤(n:ℝ)+4 by exact_mod_cast (by omega : 15≤n+4)) 10))
  have hg := g_lower (n:=n) (by norm_num : (0:ℝ)<39/10) ht 49 25 (by decide) (by norm_num)
  have hm := mul_le_mul ht hg (by norm_num : (0:ℝ)≤49/25) (by linarith : (0:ℝ)≤Real.logb 2 ((n:ℝ)+4))
  norm_num at hm
  nlinarith only [hm]

theorem sparse_later_exponent {n : ℕ} (hn : 243≤n) :
    (11678:ℝ)≤1350*Real.logb 2 ((n:ℝ)+4)*Real.logb 2 (Real.logb 2 ((n:ℝ)+4)) := by
  have ht : (7:ℝ)≤Real.logb 2 ((n:ℝ)+4) := by
    have hh := t_lower (n:=n) (a:=7) (b:=1) (by decide)
      (by norm_num; exact_mod_cast (by omega : 128≤n+4))
    simpa using hh
  have hg : (2:ℝ)≤Real.logb 2 (Real.logb 2 ((n:ℝ)+4)) := by
    have hh := g_lower (n:=n) (by norm_num : (0:ℝ)<7) ht 2 1 (by decide) (by norm_num)
    simpa using hh
  have hm := mul_le_mul ht hg (by norm_num : (0:ℝ)≤2) (by linarith : (0:ℝ)≤Real.logb 2 ((n:ℝ)+4))
  nlinarith only [hm]

theorem sparse_tiny_exponent (n : ℕ) :
    (250:ℝ)≤1350*Real.logb 2 ((n:ℝ)+4)*Real.logb 2 (Real.logb 2 ((n:ℝ)+4)) := by
  have ht : (2:ℝ)≤Real.logb 2 ((n:ℝ)+4) := by
    have hh := t_lower (n:=n) (a:=2) (b:=1) (by decide)
      (by norm_num)
    simpa using hh
  have hg : (1:ℝ)≤Real.logb 2 (Real.logb 2 ((n:ℝ)+4)) := by
    have hh := g_lower (n:=n) (by norm_num : (0:ℝ)<2) ht 1 1 (by decide) (by norm_num)
    simpa using hh
  have hm := mul_le_mul ht hg (by norm_num : (0:ℝ)≤1) (by linarith : (0:ℝ)≤Real.logb 2 ((n:ℝ)+4))
  nlinarith only [hm]

 theorem sparse_width64 {n : ℕ} (hn : 11≤n) (hhi : n≤242) : FiniteCompiler.SparseTernary.width n=64 := by
  have hlo := Nat.log_mono_right (b:=3) hn
  have hhi' := Nat.log_mono_right (b:=3) hhi
  norm_num at hlo hhi'
  unfold FiniteCompiler.SparseTernary.width FiniteCompiler.SparseTernary.tileWidth
  omega

 theorem sparse_width80 {n : ℕ} (hn : 243≤n) (hhi : n≤251) : FiniteCompiler.SparseTernary.width n=80 := by
  have hlo := Nat.log_mono_right (b:=3) hn
  have hhi' := Nat.log_mono_right (b:=3) hhi
  norm_num at hlo hhi'
  unfold FiniteCompiler.SparseTernary.width FiniteCompiler.SparseTernary.tileWidth
  omega

end
end TranslationTiling.Compiler.Size
