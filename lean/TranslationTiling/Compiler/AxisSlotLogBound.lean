import TranslationTiling.Compiler.AxisSlotBound
import TranslationTiling.Compiler.AxisSlotWide
import TranslationTiling.Compiler.SlotLogBound

namespace TranslationTiling.Compiler.Size

open FiniteCompiler.Packed AxisParameters
open FiniteCompiler.SharedCoordinates FiniteCompiler.Effective
set_option maxRecDepth 20000
attribute [local irreducible] axisPrimeCap axisFallbackCap slotSearchCap

private theorem axisPrimeCap_pos (m S : ℕ) : 0 < axisPrimeCap m S := by
  have hA : 2048 ≤ axisFallbackCap m := by rw [axisFallbackCap]; exact threshold_le_slotSearchCap ..
  unfold axisPrimeCap slotWindowCap
  have hpos : 0 < (axisFallbackCap m)^2 := by positivity
  exact Nat.mul_pos (by decide) (hpos.trans_le (le_max_left ..))

private theorem axisFallbackCap_pos (m : ℕ) : 0 < axisFallbackCap m := by
  rw [axisFallbackCap]
  exact (by decide : 0 < SlotParameters.slotBasePrimeCap).trans_le (threshold_le_slotSearchCap ..)

theorem axisPrimeCap_scale (m S : ℕ) {u g : ℝ} (hg : 48 ≤ g)
    (hU : 64 ≤ u) (hu : Real.logb 2 u = g)
    (hS : (S:ℝ) ≤ u) (hA : 16*(axisFallbackCap m : ℝ)^2 ≤ u) :
    (axisPrimeCap m S : ℝ) ≤ 256*u*g := by
  let T := 5*S+4*(axisFallbackCap m)^2+16
  have hT : 0 < T := by dsimp [T]; omega
  have hTc : (T:ℝ) ≤ 6*u := by
    dsimp [T]
    push_cast
    linarith
  have hlog := (lg_natLog_le hT).trans (lg_mono (by exact_mod_cast hT) hTc)
  rw [Real.logb_mul (by norm_num) (by linarith : u ≠ 0),hu] at hlog
  have hl6 : Real.logb 2 6 ≤ 3 := by
    have h := lg_mono (by norm_num : 0 < (6:ℝ)) (by norm_num : (6:ℝ) ≤ 2^(3:ℕ))
    rwa [lg_two_pow] at h
  have hgc : (guardedPrimeCap T : ℝ) ≤ 24*u*(g+4) := by
    unfold guardedPrimeCap
    push_cast
    have h := mul_le_mul hTc (show (Nat.log 2 T : ℝ)+1 ≤ g+4 by linarith)
      (by positivity) (by linarith : 0 ≤ 6*u)
    nlinarith only [h]
  unfold axisPrimeCap slotWindowCap
  change (↑(8*max ((axisFallbackCap m)^2) (guardedPrimeCap T)) : ℝ) ≤ _
  push_cast
  have hmax : max ((axisFallbackCap m : ℝ)^2) (guardedPrimeCap T : ℝ) ≤ 32*u*g := by
    apply max_le
    · have h := mul_le_mul_of_nonneg_left hg (show 0 ≤ u by linarith)
      nlinarith only [h,hA,show 0 ≤ u by linarith]
    · have h := mul_le_mul_of_nonneg_left hg (show 0 ≤ u by linarith)
      nlinarith only [h,hgc]
  linarith

theorem axisRadius_log_bound (P m w : ℕ) {u g l : ℝ} (hg : 48 ≤ g)
    (hm : (m:ℝ)+1 ≤ g^2) (hP0 : 0 < P)
    (hP : Real.logb 2 (P:ℝ) ≤ g+l+8) (hL : l+8 ≤ g/3)
    (hu : 1000*g^3 ≤ u) :
    2*Real.logb 2 ((axisRadius P m w : ℝ)+1) ≤ u := by
  let H := axisRadius P m w
  have hc : fourValueRadius 0 ≤ 2^68 := by decide
  have hp : (P:ℝ)^ (9*(m+1-w)) ≤ (P:ℝ)^(9*(m+1)) :=
    pow_le_pow_right₀ (by exact_mod_cast hP0) (Nat.mul_le_mul_left _ (Nat.sub_le ..))
  have hh : (H:ℝ) ≤ max ((2:ℝ)^68) ((P:ℝ)^(9*(m+1))) := by
    unfold H axisRadius
    push_cast
    exact max_le_max (by exact_mod_cast hc) hp
  have hpos : 1 ≤ H := (by decide : 1 ≤ fourValueRadius 0).trans (le_max_left ..)
  have h1 : Real.logb 2 (H:ℝ) ≤ 12*g^3 := by
    rcases max_cases ((2:ℝ)^68) ((P:ℝ)^(9*(m+1))) with ⟨ha,-⟩ | ⟨ha,-⟩
    · have h := lg_mono (by exact_mod_cast hpos) (hh.trans_eq ha)
      rw [lg_two_pow] at h
      have hg' : (48:ℝ)^3 ≤ g^3 := pow_le_pow_left₀ (by norm_num) hg _
      exact h.trans (by norm_num at hg' ⊢; linarith only [hg'])
    · have h := lg_mono (by exact_mod_cast hpos) (hh.trans_eq ha)
      rw [Real.logb_pow] at h
      push_cast at h
      have ha' := mul_le_mul_of_nonneg_left (show Real.logb 2 (P:ℝ) ≤ 4*g/3 by linarith)
        (show 0 ≤ 9*((m:ℝ)+1) by positivity)
      have hb' := mul_le_mul_of_nonneg_right hm (show 0 ≤ 12*g by linarith)
      nlinarith only [h,ha',hb']
  have hz : (0:ℝ) < H := by exact_mod_cast hpos
  have h2 := lg_mono (by positivity : 0 < (H:ℝ)+1) (show (H:ℝ)+1 ≤ 2*H by exact_mod_cast
    (show H+1 ≤ 2*H by omega))
  rw [Real.logb_mul (by norm_num) hz.ne', Real.logb_self_eq_one (by norm_num)] at h2
  have hg' : (48:ℝ)^3 ≤ g^3 := pow_le_pow_left₀ (by norm_num) hg _
  exact by linarith only [h1,h2,hu,hg']


private theorem axis_radix_upper {m w : ℕ} (h : w ≤ m) : axisRadix m w ≤ 7^m := by
  have hsum : (7 : ℕ)^m = ∑ i ∈ Finset.range (m+1), m.choose i*6^i := by
    simpa [mul_comm] using (add_pow (6 : ℕ) 1 m)
  rw [hsum]
  exact Finset.single_le_sum (f := fun i => m.choose i*6^i)
    (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (by omega))

private theorem axis_capacity_upper {n t : ℕ} (hn : 0 < n) (ht : 0 < t) :
    (axisRadix (7*t) (6*t))^axisPackedDigits n t ≤ n*7^(7*t) := by
  let D := axisRadix (7*t) (6*t)
  let k := axisPackedDigits n t
  have hD := axisRadix_one_lt ht
  have h₁ : D^(k-1) ≤ n := by
    have hk : k-1 = Nat.clog D n-1 := by unfold k axisPackedDigits D; omega
    by_cases h : 1 < n
    · rw [hk]
      exact (Nat.pow_pred_clog_lt_self hD h).le
    · have hn₁ : n = 1 := by omega
      simp [hk,hn₁]
  have h := axis_radix_upper (m := 7*t) (w := 6*t) (by omega)
  have hk : 0 < k := (by decide : 0 < 1).trans_le (le_max_left ..)
  change D^k ≤ _
  calc
    _ = D^(k-1)*D := by rw [← pow_succ]; congr 1; omega
    _ ≤ _ := Nat.mul_le_mul h₁ h

theorem axisDeck_log_bound {n t P : ℕ} (hn : 4 ≤ n) (ht : 0 < t)
    {u g : ℝ} (hg : 48 ≤ g)
    (hU : u = Real.logb 2 ((n:ℝ)+4)) (hu : Real.logb 2 u = g)
    (hbig : 1000*g^3 ≤ u)
    (hS : 2*(axisPackedDigits n t : ℝ)*(7*(t:ℝ)) ≤ u)
    (hm : 7*(t:ℝ)+1 ≤ g^2)
    (hP0 : 0 < P) (hP : Real.logb 2 (P:ℝ) ≤ 4*g/3) :
    let m := 7*t
    let k := axisPackedDigits n t
    let X := SlotParameters.stackTestCap P (axisDeckCap k m ((axisRadix m (6*t))^k))
    Real.logb 2 (X:ℝ) ≤ 3*u := by
  let k := axisPackedDigits n t
  let m := 7*t
  let D := (axisRadix m (6*t))^k
  let x : ℝ := (n:ℝ)+4
  have hx : 0 < x := by dsimp [x]; positivity
  have hm0 : 0 < m := by dsimp [m]; omega
  have hk0 : 0 < k := (by decide : 0 < 1).trans_le (le_max_left ..)
  have hS' : (2:ℝ)*k*m ≤ u := by norm_num [k,m]; linarith
  have hmr : (1:ℝ) ≤ m := by exact_mod_cast hm0
  have hkr : (1:ℝ) ≤ k := by exact_mod_cast hk0
  have hku : 2*(k:ℝ) ≤ u := by
    have h := mul_nonneg (show 0 ≤ (k:ℝ) by positivity) (sub_nonneg.mpr hmr)
    nlinarith only [hS',h]
  have hmu : (m:ℝ) ≤ u := by
    have h := mul_nonneg (show 0 ≤ (m:ℝ) by positivity) (sub_nonneg.mpr hkr)
    nlinarith only [hS',h,show 0 ≤ (m:ℝ) by positivity]
  have hg2 : g^2 ≤ g^3 := pow_le_pow_right₀ (by linarith) (by decide)
  have htmp : (48:ℝ)^2 ≤ g^2 := pow_le_pow_left₀ (by norm_num) hg _
  have hu64 : 64 ≤ u := by linarith only [hbig,hg2,htmp]
  have hu0 : 0 < u := by linarith
  change u = Real.logb 2 x at hU
  have hlog {y : ℝ} (hy : 0 < y) (hh : Real.logb 2 y ≤ u) : y ≤ x :=
    (Real.logb_le_logb (by norm_num) hy hx).mp (hh.trans_eq hU)
  have hpoly : (2530+arithmeticBaseline.length+20*(2*k*m+8*m)+(6*k*m+4*m)*(21+2*k*m+8*m+k) : ℕ)
      ≤ 1024*u^2 := by
    have h₁ : 20*(2*(k:ℝ)*m+8*m) ≤ 180*u := by linarith
    have h₂ : (6*(k:ℝ)*m+4*m)*(21+2*k*m+8*m+k) ≤ 77*u^2 := by
      have hl : 6*(k:ℝ)*m+4*m ≤ 7*u := by linarith
      have hr : 21+2*(k:ℝ)*m+8*m+k ≤ 11*u := by linarith
      convert mul_le_mul hl hr (by positivity) (by linarith : 0 ≤ 7*u) using 1
      ring
    have hlen : arithmeticBaseline.length = 424 := by decide +kernel
    rw [hlen]
    push_cast
    have hh : u ≤ u^2 := by nlinarith only [mul_nonneg hu0.le (show 0 ≤ u-1 by linarith)]
    have hh' : (64:ℝ)^2 ≤ u^2 := pow_le_pow_left₀ (by norm_num) hu64 _
    nlinarith only [h₁,h₂,hh,hh']
  have hpolyx : 1024*u^2 ≤ x := by
    apply hlog (by positivity)
    rw [Real.logb_mul (by norm_num) (by positivity),Real.logb_pow,hu,
      show Real.logb 2 1024=10 by rw [← show (2:ℝ)^10=1024 by norm_num,lg_two_pow]; norm_num]
    have hg' : g ≤ g^2 := by nlinarith only [mul_nonneg (show 0 ≤ g by linarith) (show 0 ≤ g-1 by linarith)]
    norm_num
    linarith only [hbig,hg2,htmp,hg']
  have hmm : (m:ℝ)+1 ≤ g^2 := by simpa [m] using hm
  have hax : (2*(k:ℝ))*(2:ℝ)^m ≤ x := by
    refine (mul_le_mul_of_nonneg_right hku (by positivity)).trans (hlog (by positivity) ?_)
    rw [Real.logb_mul hu0.ne' (by positivity),lg_two_pow,hu]
    have hg' : g ≤ g^2 := by nlinarith only [mul_nonneg (show 0 ≤ g by linarith) (show 0 ≤ g-1 by linarith)]
    linarith only [hbig,hg2,htmp,hg',hmm]
  have hp2 : (2:ℝ)^(6*m+8) ≤ x := by
    apply hlog (by positivity)
    rw [lg_two_pow]
    push_cast
    linarith only [hbig,hg2,htmp,hmm]
  have hD : (D:ℝ) ≤ (n:ℝ)*(7:ℝ)^m := by
    exact_mod_cast axis_capacity_upper (by omega : 0 < n) ht
  have hd2 : 72*(D:ℝ)^2 ≤ x^3/2 := by
    calc
      _ ≤ 72*(x*(7:ℝ)^m)^2 := by gcongr; exact hD.trans (by dsimp [x]; gcongr; linarith)
      _ ≤ (x^2/2)*(2:ℝ)^(6*m+8) := by
        have h : ((7:ℝ)^m)^2 ≤ (2:ℝ)^(6*m) := by
          calc
            _ = ((7:ℝ)^2)^m := by rw [← pow_mul,← pow_mul,Nat.mul_comm m 2]
            _ ≤ ((2:ℝ)^6)^m := pow_le_pow_left₀ (by positivity) (by norm_num) m
            _ = _ := (pow_mul (2:ℝ) 6 m).symm
        rw [mul_pow,pow_add,show (2:ℝ)^8=256 by norm_num]
        nlinarith only [mul_le_mul_of_nonneg_left h (sq_nonneg x),
          show (0:ℝ)≤x^2*2^(6*m) by positivity]
      _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_left hp2 (show 0 ≤ x^2/2 by positivity)]
  have hx2 : 2 ≤ x := by dsimp [x]; linarith [Nat.cast_nonneg (α := ℝ) n]
  have hdc : (axisDeckCap k m D : ℝ) ≤ x^3 := by
    unfold axisDeckCap
    have hh : (2:ℝ)*x ≤ x^3/2 := by
      nlinarith only [mul_nonneg hx.le (sub_nonneg.mpr (pow_le_pow_left₀ (show (0:ℝ)≤2 by norm_num) hx2 2))]
    have hpc := hpoly.trans hpolyx
    simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] at hpc ⊢
    exact (add_le_add (add_le_add hpc hax) hd2).trans (by linarith only [hh])
  have hp : (P:ℝ) ≤ x := by
    apply hlog (by exact_mod_cast hP0)
    have hg' : g ≤ g^2 := by nlinarith only [mul_nonneg (show 0 ≤ g by linarith) (show 0 ≤ g-1 by linarith)]
    linarith only [hP,hbig,hg2,htmp,hg']
  have hw : (2313:ℝ) ≤ x := by
    refine (by norm_num : (2313:ℝ) ≤ 2^(12:ℕ)).trans (hlog (by positivity) ?_)
    rw [lg_two_pow]
    norm_num
    linarith
  let X := SlotParameters.stackTestCap P (axisDeckCap k m D)
  have hX : (X:ℝ) ≤ x^3 := by
    change (↑(max 2313 (max P _)) : ℝ) ≤ _
    simp only [Nat.cast_max,Nat.cast_ofNat]
    have h : x ≤ x^3 := by
      simpa using pow_le_pow_right₀ (by linarith : (1:ℝ) ≤ x) (by decide : 1 ≤ 3)
    exact max_le (hw.trans h) (max_le (hp.trans h) hdc)
  have h := lg_mono (by exact_mod_cast ((by decide : 0 < 2313).trans_le
    (le_max_left 2313 (max P (axisDeckCap k m D))))) hX
  rw [Real.logb_pow,← hU] at h
  norm_num at h
  exact h


open FiniteCompiler in
theorem axisEstimate_log {n : ℕ} (hn : 4 ≤ n) (hb : 48 ≤ axisInputLog n) :
    let t := axisLengthParameter n
    let u := Real.logb 2 ((n:ℝ)+4)
    let g := Real.logb 2 u
    let l := Real.logb 2 g
    Real.logb 2 (axisEstimate (axisPackedDigits n t) (7*t) (6*t) : ℝ) ≤
      u*(4.986901*(g+l)+64) := by
  let t := axisLengthParameter n
  let k := axisPackedDigits n t
  let m := 7*t
  let S := 2*k*m
  let A := axisFallbackCap m
  let P := axisPrimeCap m S
  let H := axisRadius P m (6*t)
  let X := SlotParameters.stackTestCap P (axisDeckCap k m ((axisRadix m (6*t))^k))
  let u := Real.logb 2 ((n:ℝ)+4)
  let g := Real.logb 2 u
  let l := Real.logb 2 g
  have ht : 0 < t := (by decide : 0 < 1).trans_le (le_max_left ..)
  obtain ⟨hg,hl,hmlo,hmhi⟩ := axis_width_bounds n hn hb
  change 48 ≤ g at hg
  change 5 ≤ l at hl
  have hg' : (48:ℝ)^3 ≤ g^3 := pow_le_pow_left₀ (by norm_num) hg _
  obtain ⟨hfb,hug⟩ := axis_fallback_room n hn hb
  change 16*(A:ℝ)^2 ≤ u at hfb
  change 1000*g^3 ≤ u at hug
  have hu : 64 ≤ u := by linarith only [hug,hg']
  have hpos : 0 ≤ u := by linarith
  have ⟨hrem,hL⟩ := axis_log_remainders (g := g) (l := l) rfl hg
  have hₙ : Real.logb 2 (n:ℝ) ≤ u := lg_mono (by exact_mod_cast (show 0 < n by omega)) (by linarith)
  obtain ⟨hS,hcount⟩ := axis_factor_count (by omega : 0 < n) ht hg hl hpos hmlo hmhi hL
    (show Real.logb 2 g=l from rfl) hₙ hug
  have hSu : (S:ℝ) ≤ u := by simpa only [S,m,k,Nat.cast_mul,Nat.cast_ofNat] using hS
  have hP0 := axisPrimeCap_pos m S
  have hA0 := axisFallbackCap_pos m
  have ha : (1:ℝ) ≤ A := by exact_mod_cast hA0
  have hpr : (P:ℝ) ≤ 256*u*g := axisPrimeCap_scale m S hg hu rfl hSu hfb
  have hlgP := lg_mono (by exact_mod_cast hP0) hpr
  rw [Real.logb_mul (by positivity) (by linarith : g ≠ 0),
    Real.logb_mul (by norm_num) (by linarith : u ≠ 0),
    show Real.logb 2 256 = 8 by rw [← show (2:ℝ)^8=256 by norm_num,lg_two_pow]; norm_num] at hlgP
  change Real.logb 2 (P:ℝ) ≤ 8+g+l at hlgP
  have hplog : Real.logb 2 (P:ℝ) ≤ g+l+8 := by linarith only [hlgP]
  have hlogA : Real.logb 2 (A:ℝ) ≤ g := by
    have hAr : (A:ℝ) ≤ u := by
      have h := mul_nonneg (show (0:ℝ) ≤ A by positivity) (sub_nonneg.mpr ha)
      nlinarith only [h,hfb,show (0:ℝ) ≤ (A:ℝ)^2 by positivity]
    exact lg_mono (by linarith) hAr
  have hmreal : (m:ℝ) ≤ g*l := by simpa only [m,Nat.cast_mul,Nat.cast_ofNat] using hmhi
  have hm2 : (m:ℝ)+1 ≤ g^2 := by
    have hh := mul_le_mul_of_nonneg_left hL (show 0 ≤ g by linarith)
    have hgg : (48:ℝ)^2 ≤ g^2 := pow_le_pow_left₀ (by norm_num) hg _
    nlinarith only [hmreal,hh,hgg]
  have hmg : (m:ℝ)*g ≤ g^3 := by
    nlinarith only [mul_le_mul_of_nonneg_right hm2 (show 0 ≤ g by linarith),show 0 ≤ g by linarith]
  have hAlog : 8*(m:ℝ)*Real.logb 2 (A:ℝ) ≤ u := by
    nlinarith only [mul_le_mul_of_nonneg_left hlogA (show 0 ≤ 8*(m:ℝ) by positivity),
      hmg,hug,show (0:ℝ) ≤ g^3 by positivity]
  have hH : 2*Real.logb 2 ((H:ℝ)+1) ≤ u :=
    axisRadius_log_bound P m (6*t) hg hm2 hP0 hplog hrem hug
  have hX : Real.logb 2 (X:ℝ) ≤ 3*u :=
    axisDeck_log_bound hn ht hg rfl rfl hug hS
      (by simpa only [m,Nat.cast_mul,Nat.cast_ofNat] using hm2) hP0 (by linarith only [hplog,hrem])
  let c := 14/Real.logb 2 7
  have hc : c ≤ (4.986901:ℝ) := axis_coefficient_le_decimal
  have hc5 : c ≤ 5 := hc.trans (by norm_num)
  have hs' : 7*(S:ℝ) ≤ c*u+(6/g)*u+14*(m:ℝ) := by
    simpa only [S,m,k,Nat.cast_mul,Nat.cast_ofNat,c] using hcount
  have hf : (6/g)*(g+l+8) ≤ 8 := by
    have hh := mul_le_mul_of_nonneg_left (show g+l+8 ≤ 4*g/3 by linarith only [hrem])
      (show 0 ≤ 6/g by positivity)
    have he : 6/g*(4*g/3)=8 := by field_simp [show g ≠ 0 by linarith]; norm_num
    exact hh.trans_eq he
  have hr : 14*(m:ℝ)*(g+l+8) ≤ u := by
    have hh := mul_le_mul_of_nonneg_left (show g+l+8 ≤ 4*g/3 by linarith only [hrem])
      (show 0 ≤ 14*(m:ℝ) by positivity)
    nlinarith only [hh,hmg,hug,show (0:ℝ) ≤ g^3 by positivity]
  have hbig := mul_le_mul hs' hplog
    (Real.logb_nonneg (by norm_num) (by exact_mod_cast hP0))
    (show 0 ≤ c*u+6/g*u+14*(m:ℝ) by linarith only [hs',show 0 ≤ 7*(S:ℝ) by positivity])
  have hf' := mul_le_mul_of_nonneg_right hf hpos
  have hc' := mul_le_mul_of_nonneg_left hc (show 0 ≤ u*(g+l) by positivity)
  have hc'' := mul_le_mul_of_nonneg_right hc5 hpos
  have hsum : 7*(S:ℝ)*Real.logb 2 (P:ℝ) ≤ u*(4.986901*(g+l)+49) := by
    nlinarith only [hbig,hf',hc',hc'',hr]
  let N := order (fourValueLayout 0)
  have hN : 0 < (N:ℝ) := by exact_mod_cast fourValueOrder_pos 0
  have hNc : (10:ℝ)^35*N ≤ (2:ℝ)^2010 := by
    have hb : N ≤ 2^1893 := by
      dsimp only [N]
      rw [fourValueLayout_order]
      simpa only [Nat.mul_zero,pow_zero,Nat.mul_one] using fourValueRows_order_bound 0
    have h : 10^35*N ≤ (2:ℕ)^117*2^1893 := Nat.mul_le_mul (by decide) hb
    rw [← pow_add] at h
    exact_mod_cast h
  have hz := lg_mono (show 0 < (10:ℝ)^35*N by positivity) hNc
  rw [lg_two_pow] at hz
  norm_num at hz
  have hX0 : 0 < (X:ℝ) := by
    exact_mod_cast ((by decide : 0 < 2313).trans_le (le_max_left ..) : 0 < X)
  have hprod := slot_log_bound_factors (show 0 < (10:ℝ)^35*N by positivity)
    (show 0 < (P:ℝ) by exact_mod_cast hP0) (show 0 < (A:ℝ) by exact_mod_cast hA0)
    hX0 (show 0 < (H:ℝ)+1 by positivity) (7*S) (8*m)
  change Real.logb 2 (axisEstimate k m (6*t):ℝ) ≤ _
  have he : (axisEstimate k m (6*t):ℝ) = (10:ℝ)^35*N*((P:ℝ)^(7*S)*(A:ℝ)^(8*m))*(X:ℝ)^3*((H:ℝ)+1)^2 := by
    simp only [axisEstimate,Nat.cast_mul,Nat.cast_add,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_one]
    change (10:ℝ)^35*(N*((P:ℝ)^(7*S)*(A:ℝ)^(8*m)))*X^3*(H+1)^2 = _
    ring
  rw [he,hprod]
  push_cast
  linarith only [hz,hug,hg',hsum,hAlog,hX,hH]

end TranslationTiling.Compiler.Size
