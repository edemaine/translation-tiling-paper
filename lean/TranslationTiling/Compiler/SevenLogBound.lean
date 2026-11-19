import TranslationTiling.Compiler.PairLogBound
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

theorem seven_dyadic_real_bound {n N e : ℕ} (hN : N≤2^e)
    (he : (e:ℝ)≤700*Real.logb 2 ((n:ℝ)+4)*Real.logb 2 (Real.logb 2 ((n:ℝ)+4))) :
    (N:ℝ)≤((n:ℝ)+4)^(700*Real.logb 2 (Real.logb 2 ((n:ℝ)+4))) := by
  apply (show (N:ℝ)≤(2:ℝ)^e by exact_mod_cast hN).trans
  apply (Real.logb_le_logb (by norm_num : (1:ℝ)<2) (by positivity) (by positivity)).mp
  rw [logb_two_pow,Real.logb_rpow_eq_mul_logb_of_pos (by positivity : 0<(n:ℝ)+4)]
  nlinarith only [he]

theorem seven_bulk_real_bound {n N : ℕ} (hn : 8188≤n)
    (hN : N≤(max (FiniteCompiler.SparseTernary.width n+2) 256)^(33*(FiniteCompiler.SparseTernary.width n)+98)*
      3^(4*(FiniteCompiler.SparseTernary.width n)+4)) :
    (N:ℝ)≤((n:ℝ)+4)^(700*Real.logb 2 (Real.logb 2 ((n:ℝ)+4))) := by
  let w := FiniteCompiler.SparseTernary.width n
  let P := max (w+2) 256
  let t := Real.logb 2 ((n:ℝ)+4)
  let g := Real.logb 2 t
  have hP : 256≤P := le_max_right _ _
  have hPpos : (0:ℝ)<P := by exact_mod_cast (by omega : 0<P)
  have ht : (13:ℝ)≤t := by
    have hh := t_lower (n:=n) (a:=13) (b:=1) (by decide)
      (by norm_num; exact_mod_cast (by omega : 8192≤n+4))
    simpa using hh
  have hg : (3:ℝ)≤g := by
    have hh := g_lower (n:=n) (by norm_num : (0:ℝ)<13) ht 3 1 (by decide) (by norm_num)
    simpa using hh
  have hw : (w:ℝ)≤(92/13:ℝ)*t := by
    have hh := pairWidth_le_log (by omega : 0<n)
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
  have ha : ((34*w+99:ℕ):ℝ)≤(34*(92/13)+99/13:ℝ)*t := by push_cast; linarith
  have hh := mul_le_mul ha hlog (by linarith : 0≤Real.logb 2 (P:ℝ))
    (by positivity : 0≤(34*(92/13)+99/13:ℝ)*t)
  have hc := mul_le_mul_of_nonneg_right
    (show (34*(92/13)+99/13:ℝ)*(8/3)≤700 by norm_num) (show 0≤t*g by positivity)
  have he : ((33*w+98:ℕ):ℝ)*Real.logb 2 (P:ℝ)+((4*w+4:ℕ):ℝ)*Real.logb 2 3≤700*t*g := by
    push_cast at hh ⊢
    nlinarith only [hh,hc,hextra]
  apply (show (N:ℝ)≤((P^(33*w+98)*3^(4*w+4):ℕ):ℝ) by exact_mod_cast hN).trans
  push_cast
  apply (Real.logb_le_logb (by norm_num : (1:ℝ)<2) (by positivity) (by positivity)).mp
  rw [Real.logb_mul (by positivity) (by positivity),Real.logb_pow,Real.logb_pow,
    Real.logb_rpow_eq_mul_logb_of_pos (by positivity : 0<(n:ℝ)+4)]
  change _≤700*g*t
  nlinarith only [he]



theorem seven_exponent {n m e a b c d : ℕ} (hn : m≤n) (hb : 0<b) (hd : 0<d)
    (ht : (2:ℝ)^a≤((m:ℝ)+4)^b) (hg : (2:ℝ)^c≤((a:ℝ)/b)^d)
    (ha : (0:ℝ)<(a:ℝ)/b) (he : (e:ℝ)≤700*((a:ℝ)/b)*((c:ℝ)/d)) :
    (e:ℝ)≤700*Real.logb 2 ((n:ℝ)+4)*Real.logb 2 (Real.logb 2 ((n:ℝ)+4)) := by
  have hmt : (m:ℝ)+4≤(n:ℝ)+4 := by exact_mod_cast Nat.add_le_add_right hn 4
  have ht' := t_lower (n:=n) (a:=a) (b:=b) hb (ht.trans (pow_le_pow_left₀ (by positivity) hmt _))
  have hg' := g_lower ha ht' c d hd hg
  have hp := mul_le_mul ht' hg' (by positivity : (0:ℝ)≤(c:ℝ)/d) (ha.le.trans ht')
  nlinarith only [he,hp]

theorem seven_width80 {n : ℕ} (hn : 243≤n) (hhi : n≤8187) :
    FiniteCompiler.SparseTernary.width n=80 := by
  have hlo := Nat.log_mono_right (b:=3) hn
  have hhi' := Nat.log_mono_right (b:=3) hhi
  norm_num at hlo hhi'
  unfold FiniteCompiler.SparseTernary.width FiniteCompiler.SparseTernary.tileWidth
  omega

end
end TranslationTiling.Compiler.Size
