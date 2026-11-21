import TranslationTiling.Compiler.GuardedParameters
import TranslationTiling.FiniteCompiler.StripVolume
import TranslationTiling.FiniteCompiler.Effective.ReservedStack

namespace TranslationTiling.Compiler.Size

open Compiler.StripLift FiniteCompiler.Effective Rails.Strips

noncomputable section

set_option maxHeartbeats 2000000
set_option Elab.async false
set_option exponentiation.threshold 20000

def guardedRadius (k : ℕ) : ℕ := 2 * (guardedPairCap k)^2 * (guardedDigitCap k)^6

theorem guard_digit_budget {n : ℕ} (hn : 3^21 < n) :
    guardedDigitCap (guardedTrits n) ≤ (n+4)^2 := by
  let t := Real.logb 2 ((n : ℝ)+4)
  let g := Real.logb 2 t
  have ht : 32 ≤ t := guarded_t_lower hn
  have hg : 5 ≤ g := guarded_g_lower ht
  have hg' : g ≤ 5*(t/32) := by
    have h := lg_ratio (t := t) (b := 5) (by decide) (by norm_num; exact ht)
    norm_num at h
    exact h
  have hgg : Real.logb 2 g ≤ g := by
    have h := lg_ratio (t := g) (b := 2) (by decide) (by norm_num; linarith)
    norm_num at h
    linarith
  have hun := (guarded_prime_logs hn).1.2
  change Real.logb 2 (guardedDigitCap (guardedTrits n)) ≤ 2*g+3*Real.logb 2 g+18 at hun
  have hpos : 0 < guardedDigitCap (guardedTrits n) :=
    Nat.zero_le _ |>.trans_lt (guardedDigitCap_gt (guardedTrits_ge hn))
  suffices h : (guardedDigitCap (guardedTrits n) : ℝ) ≤ ((n : ℝ)+4)^2 by exact_mod_cast h
  apply (Real.logb_le_logb (by norm_num : (1 : ℝ)<2) (by exact_mod_cast hpos) (by positivity)).mp
  rw [Real.logb_pow, Nat.cast_ofNat]
  change _ ≤ 2*t
  linarith

theorem guard_stack_budget {n : ℕ} (hn : 3^21 < n) :
    guardedDigitCap (guardedTrits n) + 3 ≤ 2*(guardedTests n)^2 := by
  have h := guard_digit_budget hn
  have h4 : 4 ≤ (n+4)^2 := by nlinarith
  unfold guardedTests
  nlinarith only [h, h4, Nat.mul_le_mul_right ((n+4)^2) h4]

theorem log_guard_stack {n : ℕ} (hn : 3^21 < n) :
    Real.logb 2 (reservedCap (guardedTests n) (guardedDigitCap (guardedTrits n))) ≤
      4*Real.logb 2 ((n : ℝ)+4)+Real.logb 2 (Real.logb 2 ((n : ℝ)+4))+27 := by
  let X := guardedTests n
  let P := guardedDigitCap (guardedTrits n)
  let t := Real.logb 2 ((n : ℝ)+4)
  let g := Real.logb 2 t
  have ht : 32 ≤ t := guarded_t_lower hn
  have hX : 0 < X := by unfold X guardedTests; positivity
  have hL := guard_stack_budget hn
  have hXlog : Real.logb 2 X = 10+2*t := by
    have he : (X : ℝ) = (2 : ℝ)^10*((n : ℝ)+4)^2 := by
      unfold X guardedTests
      push_cast
      norm_num
    rw [he, Real.logb_mul (by positivity) (by positivity), lg_two_pow, Real.logb_pow]
    norm_num [t]
  have hdiff : (Stacking.differenceLog X : ℝ) ≤ 2*t+12 := by
    have h := lg_natLog_le (show 0 < 2*X by positivity)
    push_cast at h
    rw [Real.logb_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity),
      Real.logb_self_eq_one (by norm_num), hXlog] at h
    unfold Stacking.differenceLog
    push_cast
    linarith
  have hcap : (reservedCap X P : ℝ) ≤ (2 : ℝ)^7 * (t*(X : ℝ)^2) := by
    have hp : (P : ℝ)+3 ≤ 2*(X : ℝ)^2 := by exact_mod_cast hL
    have hprod := mul_le_mul_of_nonneg_right hdiff (show 0 ≤ (X : ℝ)^2 by positivity)
    have htprod := mul_le_mul_of_nonneg_right ht (show 0 ≤ (X : ℝ)^2 by positivity)
    unfold reservedCap reservedThreshold
    push_cast
    norm_num
    nlinarith only [hp, hprod, htprod, Nat.cast_nonneg (α := ℝ) X]
  have hlog := lg_mono (show 0 < (reservedCap X P : ℝ) by unfold reservedCap reservedThreshold; positivity) hcap
  rw [Real.logb_mul (by positivity) (by positivity), lg_two_pow,
    Real.logb_mul (by linarith : t ≠ 0) (by positivity), Real.logb_pow, hXlog] at hlog
  norm_num at hlog
  change _ ≤ 4*t+g+27
  linarith

theorem guarded_slots_le {k : ℕ} (hk : 20 ≤ k) :
    countCapAt 35 (fun _ => guardedRadius k) ≤ 2^30 * (guardedPairCap k)^2 * (guardedDigitCap k)^6 := by
  let H := guardedRadius k
  have hx := (guardedPairCaps_ge hk).1
  have hy := guardedDigitCap_gt hk
  have hy' : 0 < guardedDigitCap k := Nat.zero_le _ |>.trans_lt hy
  have hH : 1 ≤ H := by
    have hx' : 0 < guardedPairCap k := (by decide : 0 < 16).trans_le hx
    unfold H guardedRadius
    exact Nat.mul_pos (Nat.mul_pos (by decide) (pow_pos hx' _)) (pow_pos hy' _)
  have hr : 2*radius H+1 ≤ 1333*H := by unfold radius; omega
  have hc : ((List.range 17).map (fun s => 2*widthAt 35 s+1)).sum ≤ 400000 := by decide
  have ht : 1333*400000 ≤ (2 : ℕ)^29 := by decide
  calc
    _ = (2*radius H+1)*((List.range 17).map (fun s => 2*widthAt 35 s+1)).sum := by
      unfold countCapAt
      exact List.sum_map_mul_left (l := List.range 17) (f := fun s => 2*widthAt 35 s+1) (r := 2*radius H+1)
    _ ≤ (1333*H)*400000 := Nat.mul_le_mul hr hc
    _ = (1333*400000)*H := by ac_rfl
    _ ≤ 2^29*H := Nat.mul_le_mul_right _ ht
    _ = _ := by unfold H guardedRadius; ring

theorem guarded_shell_bound {R J L A : ℕ} (hR : 0 < R) (hA : 0 < A) :
    mssPieceCap*(J*L)*(216*(4*A+7*(railHeight (3*R+1)+2)+1)*(4*A+1)) ≤
      2^49*(R*J)*L*A^2 := by
  have hB : railHeight (3*R+1)+2 ≤ 1207*R := by unfold railHeight; omega
  have hA1 : A ≤ A*R := Nat.le_mul_of_pos_right _ hR
  have hR1 : R ≤ A*R := Nat.le_mul_of_pos_left _ hA
  have hAR : 1 ≤ A*R := Nat.mul_pos hA hR
  have h₁ : 4*A+7*(railHeight (3*R+1)+2)+1 ≤ 2^14*(A*R) := by norm_num; omega
  have h₂ : 4*A+1 ≤ 2^3*A := by norm_num; omega
  calc
    _ ≤ (2^24*(J*L))*(2^8*(2^14*(A*R))*(2^3*A)) := by
      exact Nat.mul_le_mul (Nat.mul_le_mul_right _ (by decide))
        (Nat.mul_le_mul (Nat.mul_le_mul (by decide) h₁) h₂)
    _ = _ := by ring

theorem guarded_volume_bound {n R J : ℕ} (hn : 3^21 < n) (hR : 0 < R)
    (hRJ : R*J ≤ 2^76 * (guardedDigitCap (guardedTrits n))^(180+12*guardedTrits n) *
      (guardedPairCap (guardedTrits n))^(36+4*guardedTrits n)) :
    (↑(reservedVolumeCap 35 (fun _ => guardedRadius (guardedTrits n)) R J
      (reservedCap (guardedTests n) (guardedDigitCap (guardedTrits n)))) : ℝ) ≤ guardedBound n := by
  let k := guardedTrits n
  let x := guardedPairCap k
  let y := guardedDigitCap k
  let X := guardedTests n
  let L := reservedCap X y
  let A := 2^30*x^2*y^6
  let N := 2^49*(2^76*y^(180+12*k)*x^(36+4*k))*L*A^2
  let t := Real.logb 2 ((n : ℝ)+4)
  let g := Real.logb 2 t
  let l := Real.logb 2 g
  have hk : 20 ≤ k := guardedTrits_ge hn
  have hx : 0 < x := lt_of_lt_of_le (by decide) (guardedPairCaps_ge hk).1
  have hy : 0 < y := Nat.zero_le _ |>.trans_lt (guardedDigitCap_gt hk)
  have hL : 0 < L := by unfold L reservedCap reservedThreshold; positivity
  have hA : 0 < A := by unfold A; positivity
  have hN : 0 < N := by unfold N; positivity
  have hV : reservedVolumeCap 35 (fun _ => guardedRadius k) R J L ≤ N := by
    unfold reservedVolumeCap
    refine le_trans ?_ ((guarded_shell_bound (J := J) (L := L) hR hA).trans ?_)
    · have ha := guarded_slots_le hk
      change countCapAt 35 (fun _ => guardedRadius k) ≤ A at ha
      exact Nat.mul_le_mul_left _ (Nat.mul_le_mul
        (Nat.mul_le_mul_left 216 (Nat.add_le_add_right (Nat.add_le_add_right
          (Nat.mul_le_mul_left 4 ha) _) _))
        (Nat.add_le_add_right (Nat.mul_le_mul_left 4 ha) _))
    · exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hRJ))
  refine (show (↑(reservedVolumeCap 35 (fun _ => guardedRadius k) R J L) : ℝ) ≤ N by
    exact_mod_cast hV).trans (guarded_bound_log hN ?_)
  change Real.logb 2 (N : ℝ) ≤ t*((88331/5000 : ℝ)*g+561)
  have ht : 32 ≤ t := guarded_t_lower hn
  have hg : 5 ≤ g := guarded_g_lower ht
  have hl : 0 ≤ l := Real.logb_nonneg (by norm_num) (by linarith)
  have hxr : 0 < (x : ℝ) := by exact_mod_cast hx
  have hyr : 0 < (y : ℝ) := by exact_mod_cast hy
  have hLr : 0 < (L : ℝ) := by exact_mod_cast hL
  have hLg : Real.logb 2 L ≤ 4*t+g+27 := log_guard_stack hn
  have hkr : (k : ℝ) ≤ (359/569 : ℝ)*t+1 :=
    guardedTrits_log ((by decide : 1 < 3^21).trans hn)
  have hAlog : Real.logb 2 A = 30+2*Real.logb 2 x+6*Real.logb 2 y := by
    unfold A
    push_cast
    rw [Real.logb_mul (by positivity) (by positivity),
      Real.logb_mul (by positivity) (by positivity),show (1073741824 : ℝ) = (2 : ℝ)^30 by norm_num,lg_two_pow,
      Real.logb_pow,Real.logb_pow]
    norm_num
  have hJlog : Real.logb 2 ((2^76*y^(180+12*k)*x^(36+4*k) : ℕ) : ℝ) =
      76+(180+12*(k : ℝ))*Real.logb 2 y+(36+4*(k : ℝ))*Real.logb 2 x := by
    push_cast
    rw [Real.logb_mul (by positivity) (by positivity),
      Real.logb_mul (by positivity) (by positivity),show (75557863725914323419136 : ℝ) = (2 : ℝ)^76 by norm_num,lg_two_pow,
      Real.logb_pow,Real.logb_pow]
    push_cast
    rfl
  have hNlog : Real.logb 2 N = 185+Real.logb 2 L+
      ((40+4*(k : ℝ))*Real.logb 2 x + (192+12*(k : ℝ))*Real.logb 2 y) := by
    let J' := 2^76*y^(180+12*k)*x^(36+4*k)
    have hJ' : 0 < (J' : ℝ) := by unfold J'; push_cast; positivity
    have hAr : 0 < (A : ℝ) := by exact_mod_cast hA
    change Real.logb 2 ((2^49*J'*L*A^2 : ℕ) : ℝ) = _
    push_cast
    rw [Real.logb_mul (by positivity) (by positivity),
      Real.logb_mul (by positivity) (by positivity),
      Real.logb_mul (by positivity) (by positivity),show (562949953421312 : ℝ) = (2 : ℝ)^49 by norm_num,lg_two_pow,
      Real.logb_pow, hAlog]
    rw [show Real.logb 2 J' = _ from hJlog]
    push_cast
    ring
  have hest {a b : ℝ} (ha : Real.logb 2 x ≤ g+l+a)
      (hb : Real.logb 2 y ≤ 2*g+3*l+b) (hab : 0 ≤ 4*a+12*b) :
      Real.logb 2 N ≤ (28*g+40*l+4*a+12*b)*((359/569 : ℝ)*t+1) +
        425*g+616*l+(40*a+192*b+212)+4*t := by
    have hm := mul_le_mul_of_nonneg_left ha (show 0 ≤ 40+4*(k : ℝ) by positivity)
    have hn := mul_le_mul_of_nonneg_left hb (show 0 ≤ 192+12*(k : ℝ) by positivity)
    have hr := mul_le_mul_of_nonneg_left hkr (show 0 ≤ 28*g+40*l+4*a+12*b by linarith)
    nlinarith only [hm, hn, hr, hNlog, hLg]
  apply guarded_volume_log ht
  · intro _
    obtain ⟨⟨ha,hb⟩,_⟩ := guarded_prime_logs hn
    have h := hest ha hb (by norm_num)
    change _ ≤ (28*g+40*l+240)*((359/569 : ℝ)*t+1)+425*g+616*l+3908+4*t
    linarith
  · intro hg'
    obtain ⟨ha,hb⟩ := (guarded_prime_logs hn).2 hg'
    have h := hest ha hb (by norm_num)
    change _ ≤ (28*g+40*l+172)*((359/569 : ℝ)*t+1)+425*g+616*l+2868+4*t
    linarith

end
end TranslationTiling.Compiler.Size
