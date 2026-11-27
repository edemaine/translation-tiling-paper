import TranslationTiling.Compiler.AxisSlotEstimate
import TranslationTiling.Compiler.SlotWideEstimate

namespace TranslationTiling.Compiler.Size

open FiniteCompiler.Packed FiniteCompiler.Packed.AxisParameters
open FiniteCompiler.SharedCoordinates FiniteCompiler.Effective

private theorem log_lt_natLog_succ {n : ℕ} (hn : 0 < n) :
    Real.logb 2 (n : ℝ) < (Nat.log 2 n : ℝ)+1 := by
  have hp : (n : ℝ) < (2 : ℝ)^(Nat.log 2 n+1) := by
    exact_mod_cast Nat.lt_pow_succ_log_self (by decide : 1 < (2 : ℕ)) n
  have hh := Real.logb_lt_logb (by norm_num : (1 : ℝ)<2) (Nat.cast_pos.mpr hn) hp
  simpa only [lg_two_pow,Nat.cast_add,Nat.cast_one] using hh

def axisInputLog (n : ℕ) := Nat.log 2 (Nat.log 2 n)

theorem axis_log_comparison (n : ℕ) (hn : 4 ≤ n) :
    let u := Real.logb 2 ((n : ℝ)+4)
    let g := Real.logb 2 u
    let b := axisInputLog n
    (b : ℝ) ≤ g ∧ g < (b : ℝ)+2 := by
  let a := Nat.log 2 n
  let b := Nat.log 2 a
  let u := Real.logb 2 ((n : ℝ)+4)
  let g := Real.logb 2 u
  have ha : 0 < a := (Nat.le_log_iff_pow_le (by decide) (by omega)).mpr (by omega)
  have hₙ : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hlog : (a : ℝ) ≤ Real.logb 2 (n : ℝ) := Real.natLog_le_logb _ _
  have hu : (a : ℝ) ≤ u := hlog.trans (lg_mono hₙ (by linarith))
  refine ⟨(Real.natLog_le_logb a 2).trans (lg_mono (Nat.cast_pos.mpr ha) hu),?_⟩
  have ha' := log_lt_natLog_succ (by omega : 0 < n)
  have ha'' : (a : ℝ)+1 ≤ (2 : ℝ)^(b+1) := by
    exact_mod_cast Nat.lt_pow_succ_log_self (by decide : 1 < (2 : ℕ)) a
  have hpos : 0 < Real.logb 2 (n : ℝ) := (Nat.cast_pos.mpr ha).trans_le hlog
  have hb' := Real.logb_lt_logb (by norm_num : (1 : ℝ)<2) hpos (ha'.trans_le ha'')
  rw [lg_two_pow,Nat.cast_add,Nat.cast_one] at hb'
  have hr : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hsmall := lg_mono (show 0 < (n : ℝ)+4 by positivity)
    (show (n : ℝ)+4 ≤ 2*n by linarith)
  rw [Real.logb_mul (by norm_num) hₙ.ne',Real.logb_self_eq_one (by norm_num)] at hsmall
  have hbig := lg_mono (show 0 < u from (Nat.cast_pos.mpr ha).trans_le hu)
    (show u ≤ 2*Real.logb 2 (n : ℝ) by
      exact hsmall.trans (by linarith [show (1 : ℝ) ≤ a by exact_mod_cast ha]))
  rw [Real.logb_mul (by norm_num) hpos.ne',Real.logb_self_eq_one (by norm_num)] at hbig
  change g < (b : ℝ)+2
  linarith only [hbig,hb']

theorem axis_width_bounds (n : ℕ) (hn : 4 ≤ n) (hb0 : 48 ≤ axisInputLog n) :
    let u := Real.logb 2 ((n : ℝ)+4)
    let g := Real.logb 2 u
    let l := Real.logb 2 g
    let m := 7*(axisLengthParameter n : ℝ)
    48 ≤ g ∧ 5 ≤ l ∧ (2/3 : ℝ)*g*l ≤ m ∧ m ≤ g*l := by
  let b := axisInputLog n
  let j := Nat.log 2 b
  let u := Real.logb 2 ((n : ℝ)+4)
  let g := Real.logb 2 u
  let l := Real.logb 2 g
  let m := 7*(axisLengthParameter n : ℝ)
  have ⟨hb,hb'⟩ := axis_log_comparison n hn
  change (b : ℝ) ≤ g at hb
  change g < (b : ℝ)+2 at hb'
  have hb48 : (48:ℝ) ≤ b := by exact_mod_cast hb0
  have hg48 := hb48.trans hb
  have hj5 : 5 ≤ j := (Nat.le_log_iff_pow_le (by decide) (by omega : b ≠ 0)).mpr (by omega)
  have hj5' : (5:ℝ) ≤ j := by exact_mod_cast hj5
  have hj : (j : ℝ) ≤ l := (Real.natLog_le_logb b 2).trans
    (lg_mono (by linarith) hb)
  have hbp : (b : ℝ)+1 ≤ (2 : ℝ)^(j+1) := by
    exact_mod_cast Nat.lt_pow_succ_log_self (by decide : 1 < (2 : ℕ)) b
  have hg' : g ≤ (2 : ℝ)^(j+2) := by
    rw [show j+2 = (j+1)+1 by omega,pow_succ]
    linarith
  have hl' := lg_mono (by linarith : 0 < g) hg'
  rw [lg_two_pow,Nat.cast_add,Nat.cast_ofNat] at hl'
  have hgj : g ≤ (25/24 : ℝ)*b := by linarith
  have hlj : l ≤ (7/5 : ℝ)*j := by linarith
  have hbj : 240 ≤ b*j := (by decide : 240 ≤ 48*5).trans (Nat.mul_le_mul hb0 hj5)
  have hwidth : axisLengthParameter n = b*j/7 := by
    change max 1 (b*j/7) = b*j/7
    exact max_eq_right (by omega)
  have hm : m ≤ (b : ℝ)*j := by
    have ht : 7*axisLengthParameter n ≤ b*j := by omega
    dsimp [m]
    exact_mod_cast ht
  have hm' : (39/40 : ℝ)*b*j ≤ m := by
    have ht : b*j ≤ 7*axisLengthParameter n+6 := by omega
    have ht' : (b : ℝ)*j ≤ m+6 := by dsimp [m]; exact_mod_cast ht
    have hb' : (240 : ℝ) ≤ (b : ℝ)*j := by exact_mod_cast hbj
    nlinarith only [ht',hb']
  have hgl := mul_le_mul hgj hlj (show 0 ≤ l by linarith) (by positivity : 0 ≤ (25/24 : ℝ)*b)
  exact ⟨hg48,hj5'.trans hj,by nlinarith only [hgl,hm'],
    hm.trans (mul_le_mul hb hj (by positivity) (by linarith))⟩


private theorem axisBaseGrowth : ∀ b ≥ 48, 2^14*b^6 ≤ (2 : ℕ)^b := by
  intro b hb
  induction b,hb using Nat.le_induction with
  | base => decide
  | succ b hb ih =>
    have hx : 17*(b+1) ≤ 18*b := by omega
    have hpow := Nat.pow_le_pow_left hx 6
    rw [mul_pow,mul_pow] at hpow
    have hy : (18:ℕ)^6 ≤ 2*17^6 := by decide
    have h2 := Nat.mul_le_mul_right (b^6) hy
    have hs : (b+1)^6 ≤ 2*b^6 := by
      have h : 17^6*(b+1)^6 ≤ 17^6*(2*b^6) := by
        convert hpow.trans h2 using 1
        ring
      exact Nat.le_of_mul_le_mul_left h (by decide)
    rw [pow_succ]
    have hf := Nat.mul_le_mul_left (2^14) hs
    exact hf.trans (by omega)

private theorem axisLogEighth {b : ℕ} (hb : 48 ≤ b) : 8*Nat.log 2 b ≤ b := by
  let j := Nat.log 2 b
  by_cases h : j ≤ 5
  · omega
  have haux : ∀ i ≥ 6, 8*i ≤ (2:ℕ)^i := by
    intro i hi
    induction i,hi using Nat.le_induction with
    | base => decide
    | succ i hi ih => rw [pow_succ]; omega
  exact (haux _ (by omega)).trans (Nat.pow_log_le_self 2 (by omega))

private theorem axisLogRoom {j : ℕ} (hj : 5 ≤ j) : 18*j ≤ (2:ℕ)^(3*j) := by
  induction j,hj using Nat.le_induction with
  | base => decide
  | succ j hj ih =>
    rw [show 3*(j+1) = 3*j+3 by omega,pow_add]
    norm_num
    omega

theorem axis_fallback_room (n : ℕ) (hn : 4 ≤ n) (hb0 : 48 ≤ axisInputLog n) :
    let u := Real.logb 2 ((n : ℝ)+4)
    let g := Real.logb 2 u
    let m := 7*axisLengthParameter n
    (16*(axisFallbackCap m : ℝ)^2 ≤ u) ∧ 1000*g^3 ≤ u := by
  let b := axisInputLog n
  let j := Nat.log 2 b
  let m := 7*axisLengthParameter n
  let A := axisFallbackCap m
  let u := Real.logb 2 ((n : ℝ)+4)
  let g := Real.logb 2 u
  have ⟨hbg,hg'⟩ := axis_log_comparison n hn
  change (b : ℝ) ≤ g at hbg
  change g < (b : ℝ)+2 at hg'
  have hbr : (48:ℝ) ≤ b := by exact_mod_cast hb0
  have hg0 : 0 ≤ g := by linarith
  have hu : 0 < u := by
    apply Real.logb_pos (by norm_num)
    have hnr : (4:ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have h2b : (2:ℝ)^b ≤ u :=
    (Real.logb_le_logb (by norm_num : (1:ℝ)<2) (by positivity) hu).mp
      (by rwa [lg_two_pow])
  have hj5 : 5 ≤ j := (Nat.le_log_iff_pow_le (by decide) (by omega : b ≠ 0)).mpr (by omega)
  have hbj : 240 ≤ b*j := (by decide : 240 ≤ 48*5).trans (Nat.mul_le_mul hb0 hj5)
  have hm : m ≤ b*j := by
    change 7*max 1 (b*j/7) ≤ b*j
    rw [max_eq_right (by omega)]
    omega
  let d := 8*m+16
  have hd : 0 < d := by dsimp [d]; omega
  have hd' : d ≤ 9*(b*j) := by dsimp [d]; omega
  have hblt : b < 2^(j+1) := Nat.lt_pow_succ_log_self (by decide) _
  have hroom : 9*(b*j) < (2:ℕ)^(4*j) := by
    calc
      _ < 9*(2^(j+1)*j) := Nat.mul_lt_mul_of_pos_left
        (Nat.mul_lt_mul_of_pos_right hblt (by omega)) (by decide)
      _ = 2^j*(18*j) := by rw [pow_succ]; ring
      _ ≤ 2^j*2^(3*j) := Nat.mul_le_mul_left _ (axisLogRoom hj5)
      _ = _ := by rw [← pow_add]; congr 1; omega
  have hl : Nat.log 2 d+1 ≤ 4*j := by
    have h := (Nat.log_lt_iff_lt_pow (by decide : 1 < (2 : ℕ)) hd.ne').mpr (hd'.trans_lt hroom)
    omega
  have hcap : guardedPrimeCap d ≤ 144*(b*j)*j := by
    unfold guardedPrimeCap
    calc
      _ ≤ 4*(9*(b*j))*(4*j) := Nat.mul_le_mul (Nat.mul_le_mul_left _ hd') hl
      _ = _ := by ring
  have hA : A ≤ 2048*b*j^2 := by
    apply (slotSearchCap_le_window (t := SlotParameters.slotBasePrimeCap) (c := 8*m) (by decide)).trans
    unfold slotWindowCap
    change 8*max 2048 (guardedPrimeCap d) ≤ _
    have hmax : max 2048 (guardedPrimeCap d) ≤ 256*(b*j)*j := by
      apply max_le
      · exact (by decide : 2048 ≤ 256*240*5).trans (Nat.mul_le_mul (Nat.mul_le_mul_left _ hbj) hj5)
      · exact hcap.trans (Nat.mul_le_mul_right _
          (Nat.mul_le_mul_right _ (by decide : 144 ≤ 256)))
    calc
      _ ≤ 8*(256*(b*j)*j) := Nat.mul_le_mul_left _ hmax
      _ = _ := by ring
  have hAj : A ≤ 32*b^3 := by
    apply Nat.le_of_mul_le_mul_left (c := 64) _ (by decide)
    have hjb := Nat.pow_le_pow_left (axisLogEighth hb0) 2
    rw [mul_pow] at hjb
    have h := Nat.mul_le_mul_left (2048*b) hjb
    calc
      _ ≤ 64*(2048*b*j^2) := Nat.mul_le_mul_left _ hA
      _ = (2048*b)*(8^2*j^2) := by ring
      _ ≤ (2048*b)*b^2 := h
      _ = _ := by ring
  have hbase : (2:ℝ)^14*(b : ℝ)^6 ≤ u :=
    (show (2:ℝ)^14*(b : ℝ)^6 ≤ (2:ℝ)^b by exact_mod_cast axisBaseGrowth b hb0).trans h2b
  refine ⟨?_,?_⟩
  · have ha : (A:ℝ) ≤ 32*(b:ℝ)^3 := by exact_mod_cast hAj
    change 16*(A:ℝ)^2 ≤ u
    calc
      _ ≤ 16*(32*(b:ℝ)^3)^2 := by gcongr
      _ = (2:ℝ)^14*(b:ℝ)^6 := by ring
      _ ≤ u := hbase
  · have hgb : g ≤ 2*(b:ℝ) := by linarith
    calc
      _ ≤ 1000*(2*(b:ℝ))^3 := by gcongr
      _ ≤ (2:ℝ)^14*(b:ℝ)^6 := by
        have h := pow_le_pow_right₀ (by linarith : (1:ℝ) ≤ b) (show 3 ≤ 6 by decide)
        norm_num at *
        linarith only [h,show 0 ≤ (b:ℝ)^3 by positivity]
      _ ≤ u := hbase


theorem axis_log_remainders {g l : ℝ} (hll : Real.logb 2 g = l) (hg : 48 ≤ g) : l+8 ≤ g/3 ∧ l ≤ g/6 := by
  have hpow : (2:ℝ)^5 ≤ g := by norm_num; linarith
  have h := lg_ratio (b := 5) (by decide) hpow
  rw [hll] at h
  norm_num at h
  exact ⟨by linarith,by linarith⟩

theorem axis_factor_count {n t : ℕ} (hn : 0 < n) (ht : 0 < t)
    {G U L : ℝ} (hg : 48 ≤ G) (hL : 5 ≤ L) (hu : 0 ≤ U)
    (hmlo : (2/3:ℝ)*G*L ≤ 7*(t:ℝ))
    (hmhi : 7*(t:ℝ) ≤ G*L) (hLg : L ≤ G/6) (hLdef : Real.logb 2 G = L)
    (hU : Real.logb 2 (n:ℝ) ≤ U) (hUbig : 1000*G^3 ≤ U) :
    let m := 7*(t:ℝ)
    let S := 2*(axisPackedDigits n t : ℝ)*m
    let c := 14/Real.logb 2 7
    S ≤ U ∧ 7*S ≤ c*U+(6/G)*U+14*m := by
  let m := 7*(t:ℝ)
  let k := (axisPackedDigits n t : ℝ)
  let j : ℝ := ((axisPackedDigits n t-1 : ℕ) : ℝ)
  let rate := Real.logb 2 7
  let f := Real.logb 2 (m+1)/m
  let c := 14/rate
  have hm : 0 < m := by dsimp [m]; positivity
  have hg0 : 0 < G := by linarith
  have hrate : (14:ℝ)/5 ≤ rate :=
    lg_lower (by decide) (by norm_num : (2:ℝ)^14 ≤ 7^5) (by norm_num)
  have hf0 : 0 ≤ f := div_nonneg (Real.logb_nonneg (by norm_num) (by linarith)) hm.le
  have hm2 : m+1 ≤ G^2 := by
    have h := mul_le_mul_of_nonneg_left hLg hg0.le
    change m ≤ G*L at hmhi
    nlinarith only [h,hmhi,show G^2 ≥ 48^2 from pow_le_pow_left₀ (by norm_num) hg 2]
  have hlog := lg_mono (by positivity : 0 < m+1) hm2
  rw [Real.logb_pow,hLdef] at hlog
  norm_num at hlog
  have hf : f ≤ 3/G := by
    apply (div_le_div_iff₀ hm hg0).mpr
    have h := mul_le_mul_of_nonneg_right hlog hg0.le
    change (2/3:ℝ)*G*L ≤ m at hmlo
    nlinarith only [h,hmlo]
  have hfe : f ≤ 1/16 := hf.trans ((div_le_iff₀ hg0).mpr (by linarith))
  have hratef : (27:ℝ)/10 ≤ rate-f := by linarith
  have hratef0 : 0 < rate-f := by linarith
  have hcap := axis_digit_log_bound hn ht
  change j*(m*rate-Real.logb 2 (m+1)) ≤ _ at hcap
  have hfrac : m*f = Real.logb 2 (m+1) := by
    change m*(Real.logb 2 (m+1)/m) = _
    field_simp
  have hmain : j*m*(rate-f) ≤ U := by
    have h : j*m*(rate-f) = j*(m*rate-Real.logb 2 (m+1)) := by
      rw [← hfrac]
      ring
    rw [h]
    exact hcap.trans hU
  have hposj : 0 ≤ j := by dsimp [j]; positivity
  have hsub : j*m ≤ U/(rate-f) := (le_div_iff₀ hratef0).mpr hmain
  have hk : k = j+1 := by
    have h : axisPackedDigits n t = (axisPackedDigits n t-1)+1 := by
      have h₁ : 1 ≤ axisPackedDigits n t := le_max_left ..
      omega
    simpa only [k,j,Nat.cast_add,Nat.cast_one] using congrArg (fun p : ℕ => (p:ℝ)) h
  have hmU : 2*m ≤ U/4 := by
    have hg' : G^2 ≤ G^3 := pow_le_pow_right₀ (by linarith) (by decide)
    nlinarith only [hm2, hg',hUbig, show (0:ℝ) ≤ G^2 by positivity]
  have hfrac' : U/(rate-f) ≤ 10*U/27 := by
    apply (div_le_iff₀ hratef0).mpr
    nlinarith only [mul_le_mul_of_nonneg_left hratef hu]
  have hc : c ≤ 5 := (axis_coefficient_le_decimal).trans (by norm_num)
  have hc0 : 0 ≤ c := div_nonneg (by norm_num) (by linarith)
  have herror : c*f/(rate-f) ≤ 6/G := by
    apply (div_le_div_iff₀ hratef0 hg0).mpr
    have h1 : f*G ≤ 3 := (le_div_iff₀ hg0).mp hf
    have h2 : c*(f*G) ≤ 5*3 := mul_le_mul hc h1 (mul_nonneg hf0 hg0.le) (by norm_num)
    nlinarith only [h2,hratef]
  have hident : 14*U/(rate-f) = c*U+(c*f/(rate-f))*U := by
    dsimp only [c]
    field_simp [show rate ≠ 0 by linarith,hratef0.ne']
    ring
  change 2*k*m ≤ U ∧ 7*(2*k*m) ≤ c*U+(6/G)*U+14*m
  rw [hk]
  constructor
  · nlinarith only [hsub.trans hfrac',hmU,hu]
  · calc
      _ ≤ 14*(U/(rate-f))+14*m := by linarith only [hsub]
      _ = c*U+(c*f/(rate-f))*U+14*m := by rw [← hident]; ring
      _ ≤ _ := by linarith only [mul_le_mul_of_nonneg_right herror hu]

end TranslationTiling.Compiler.Size
