import TranslationTiling.Compiler.SlotComputability
import TranslationTiling.FiniteCompiler.Effective.SlotSmallPrimeCertificates

namespace TranslationTiling.Compiler.Size

open FiniteCompiler.Packed FiniteCompiler.Packed.SlotParameters
open FiniteCompiler.SharedCoordinates FiniteCompiler.Effective

noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 3000000
attribute [local irreducible] slotSearchCap

private theorem dyadic_le {i j : ℕ} (h : i ≤ j) : (2 : ℝ)^i ≤ (2 : ℝ)^j :=
  pow_le_pow_right₀ (by norm_num) h

private theorem dyadic_log_le {x : ℝ} (hx : 0 < x) {i : ℕ} (h : x ≤ (2 : ℝ)^i) :
    Real.logb 2 x ≤ i := by simpa only [lg_two_pow] using lg_mono hx h

private theorem arithmetic_order_le : order (fourValueLayout 0) ≤ 2^1893 := by
  rw [fourValueLayout_order]
  simpa only [Nat.mul_zero,pow_zero,Nat.mul_one] using fourValueRows_order_bound 0

private theorem arithmetic_count_le : arithmeticBaseline.length ≤ 1000 := by
  decide +kernel

private theorem lg_two_times {x : ℝ} (hx : 0 < x) :
    Real.logb 2 (2*x) = 1+Real.logb 2 x := by
  rw [Real.logb_mul (by norm_num) hx.ne',Real.logb_self_eq_one (by norm_num)]

private theorem lg_dyadic_absorb {x : ℝ} (hx : 0 < x) {a p K : ℕ}
    (ha : (a : ℝ) ≤ Real.logb 2 x)
    (h : ∀ j ≥ a, (j+1)^p ≤ K*2^j) :
    Real.logb 2 x ^ p ≤ K*x := by
  let z := Real.logb 2 x
  let j := ⌊z⌋₊
  have hz : 0 ≤ z := (Nat.cast_nonneg a).trans ha
  have hj : a ≤ j := Nat.le_floor ha
  have hlo : (j : ℝ) ≤ z := Nat.floor_le hz
  have hhi : z ≤ (j : ℝ)+1 := (Nat.lt_floor_add_one z).le
  have hp : (2 : ℝ)^j ≤ x :=
    (Real.logb_le_logb (by norm_num : (1 : ℝ) < 2) (by positivity) hx).mp
      (by rwa [lg_two_pow])
  have h' : ((j : ℝ)+1)^p ≤ (K : ℝ)*2^j := by exact_mod_cast h j hj
  exact ((pow_le_pow_left₀ hz hhi _).trans h').trans
    (mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg _))

private theorem log_squared_le {x : ℝ} (hx : 0 < x) (h : 2 ≤ Real.logb 2 x) :
    Real.logb 2 x ^ 2 ≤ 3*x := by
  apply lg_dyadic_absorb hx (a := 2) (K := 3) (by simpa using h)
  intro j hj
  induction j, hj using Nat.le_induction with
  | base => decide
  | succ j hj ih =>
    rw [pow_succ 2 j]
    have hs : (j+2)^2 ≤ 2*(j+1)^2 := by nlinarith
    rw [show j+1+1 = j+2 by omega]
    omega

private theorem log_cubed_le {x : ℝ} (hx : 0 < x) (h : 4 ≤ Real.logb 2 x) :
    Real.logb 2 x ^ 3 ≤ 8*x := by
  apply lg_dyadic_absorb hx (a := 4) (K := 8) (by simpa using h)
  intro j hj
  induction j, hj using Nat.le_induction with
  | base => decide
  | succ j hj ih =>
    rw [pow_succ 2 j]
    have hs : (j+2)^3 ≤ 2*(j+1)^3 := by
      have h : 5*(j+2) ≤ 6*(j+1) := by omega
      have hp := Nat.pow_le_pow_left h 3
      rw [mul_pow,mul_pow] at hp
      omega
    rw [show j+1+1 = j+2 by omega]
    omega

private theorem lg_nat_lt_succ {n : ℕ} (hn : 0 < n) :
    Real.logb 2 (n : ℝ) < (Nat.log 2 n : ℝ)+1 := by
  have hp : (n : ℝ) < (2 : ℝ)^(Nat.log 2 n+1) := by
    exact_mod_cast Nat.lt_pow_succ_log_self (by decide : 1 < (2 : ℕ)) n
  have hh := Real.logb_lt_logb (by norm_num : (1 : ℝ)<2) (Nat.cast_pos.mpr hn) hp
  simpa only [lg_two_pow,Nat.cast_add,Nat.cast_one] using hh

private theorem wide_width {n : ℕ} (hn : 65536 ≤ n) :
    let u := Real.logb 2 ((n : ℝ)+4)
    let g := Real.logb 2 u
    let l := Real.logb 2 g
    let m := 4*(wideSlotLength n : ℝ)
    16 ≤ u ∧ 4 ≤ g ∧ 2 ≤ l ∧ 4 ≤ m ∧ m ≤ g*l ∧ g*l ≤ 6*m := by
  let u := Real.logb 2 ((n : ℝ)+4)
  let g := Real.logb 2 u
  let l := Real.logb 2 g
  let a := Nat.log 2 n
  let b := Nat.log 2 a
  let j := Nat.log 2 b
  let m := 4*(wideSlotLength n : ℝ)
  have ha : 16 ≤ a := (Nat.le_log_iff_pow_le (by decide) (by omega)).mpr hn
  have hb : 4 ≤ b := (Nat.le_log_iff_pow_le (by decide) (by omega)).mpr ha
  have hj : 2 ≤ j := (Nat.le_log_iff_pow_le (by decide) (by omega)).mpr hb
  have hnr : (65536 : ℝ) ≤ n := by exact_mod_cast hn
  have hu₀ : (a : ℝ) ≤ Real.logb 2 (n : ℝ) := Real.natLog_le_logb _ _
  have ha₀ : (16 : ℝ) ≤ a := by exact_mod_cast ha
  have hu : (a : ℝ) ≤ u :=
    hu₀.trans (lg_mono (by positivity : 0 < (n : ℝ)) (by linarith : (n : ℝ) ≤ n+4))
  have h16 : 16 ≤ u := (show (16 : ℝ) ≤ a by exact_mod_cast ha).trans hu
  have hbg : (b : ℝ) ≤ g := (Real.natLog_le_logb a 2).trans
    (lg_mono (Nat.cast_pos.mpr (by omega : 0 < a)) hu)
  have h4 : 4 ≤ g := (show (4 : ℝ) ≤ b by exact_mod_cast hb).trans hbg
  have hjl : (j : ℝ) ≤ l := (Real.natLog_le_logb b 2).trans
    (lg_mono (Nat.cast_pos.mpr (by omega : 0 < b)) hbg)
  have h2 : 2 ≤ l := (show (2 : ℝ) ≤ j by exact_mod_cast hj).trans hjl
  have hg₀ : Real.logb 2 (Real.logb 2 (n : ℝ)) < (b : ℝ)+1 := by
    have ha' : Real.logb 2 (n : ℝ) < (a : ℝ)+1 := lg_nat_lt_succ (by omega)
    have hap : (a : ℝ)+1 ≤ (2 : ℝ)^(b+1) := by
      exact_mod_cast (Nat.lt_pow_succ_log_self (by decide : 1 < (2 : ℕ)) a)
    have h := Real.logb_lt_logb (by norm_num : (1 : ℝ)<2)
      (by linarith : 0 < Real.logb 2 (n : ℝ)) (ha'.trans_le hap)
    simpa only [lg_two_pow,Nat.cast_add,Nat.cast_one] using h
  have hg : g ≤ (3/2 : ℝ)*b := by
    have h := lg_mono (by positivity : 0 < (n : ℝ)+4) (show (n : ℝ)+4 ≤ 2*n by linarith)
    rw [lg_two_times (by positivity)] at h
    have hg' := lg_mono (by linarith : 0 < u)
      (show u ≤ 2*Real.logb 2 (n : ℝ) by linarith)
    rw [lg_two_times (by linarith)] at hg'
    linarith only [hg',hg₀,show (4 : ℝ) ≤ b by exact_mod_cast hb]
  have hl : l ≤ 2*(j : ℝ) := by
    have hbp : (b : ℝ) ≤ (2 : ℝ)^(j+1) := by
      exact_mod_cast (Nat.lt_pow_succ_log_self (by decide : 1 < (2 : ℕ)) b).le
    have h := lg_mono (by linarith : 0 < g) (show g ≤ (2 : ℝ)^(j+2) by
      rw [show j+2 = (j+1)+1 by omega,pow_succ]
      linarith)
    rw [lg_two_pow,Nat.cast_add,Nat.cast_ofNat] at h
    linarith only [h,show (2 : ℝ) ≤ j by exact_mod_cast hj]
  have hbj : 8 ≤ b*j := (by decide : 8 ≤ 4*2).trans (Nat.mul_le_mul hb hj)
  have hm : 4*wideSlotLength n = 4*(b*j/4) := by
    change 4*max 1 (b*j/4) = _
    rw [max_eq_right (by omega)]
  have hm₁ : m ≤ (b : ℝ)*j := by
    have h : 4*wideSlotLength n ≤ b*j := by omega
    dsimp [m]
    exact_mod_cast h
  have hm₂ : (b : ℝ)*j ≤ 2*m := by
    have h : b*j ≤ 2*(4*wideSlotLength n) := by omega
    dsimp [m]
    exact_mod_cast h
  have hm₀ : 4 ≤ m := by
    dsimp [m]
    exact_mod_cast (show 4 ≤ 4*wideSlotLength n by omega)
  refine ⟨h16,h4,h2,hm₀,hm₁.trans (mul_le_mul hbg hjl (Nat.cast_nonneg _) (by linarith)),?_⟩
  have h := mul_le_mul hg hl (by linarith : 0 ≤ l)
    (show 0 ≤ (3/2 : ℝ)*b by positivity)
  nlinarith only [h,hm₂]

private theorem cap_le_from_log {d : ℕ} {x L : ℝ} (hd : 0 < d)
    (hx : (d : ℝ) ≤ x) (hL : Real.logb 2 x+1 ≤ L) :
    (guardedPrimeCap d : ℝ) ≤ 4*x*L := by
  have hp : 0 < (d : ℝ) := Nat.cast_pos.mpr hd
  have hl := (lg_natLog_le hd).trans (lg_mono hp hx)
  unfold guardedPrimeCap
  push_cast
  exact mul_le_mul (mul_le_mul_of_nonneg_left hx (by norm_num))
    (by linarith) (by positivity) (by linarith)

private theorem widePrimeCaps {k m : ℕ} {u g l : ℝ}
    (hu : 16 ≤ u) (hg : 4 ≤ g) (hl : 2 ≤ l)
    (hgu : g ≤ u/4) (hl2 : l^2 ≤ 3*g) (hm : 4 ≤ m)
    (hml : (m : ℝ) ≤ g*l) (hkm : (k : ℝ)*m ≤ 2*u)
    (hgl : Real.logb 2 u = g) (hll : Real.logb 2 g = l)
    (hh : Real.logb 2 l ≤ l) :
    (fallbackCap m : ℝ) ≤ 2^10*g*l^2 ∧
    (separateMarkerCap k m : ℝ) ≤ 2^13*u*g ∧
    (separateLowCap k m : ℝ) ≤ 2^26*u*g^2*l^2 := by
  let A := fallbackCap m
  let B := separateMarkerCap k m
  have hu₀ : 0 < u := by linarith
  have hg₀ : 0 < g := by linarith
  have hl₀ : 0 < l := by linarith
  have hm' : (4 : ℝ) ≤ m := by exact_mod_cast hm
  have hA₀ : 2048 ≤ A := threshold_le_slotSearchCap ..
  have hB₀ : A ≤ B := threshold_le_slotSearchCap ..
  have hApos : (0 : ℝ) ≤ A := by positivity
  have hBpos : (0 : ℝ) ≤ B := by positivity
  have hmlog : Real.logb 2 (m : ℝ) ≤ 2*l := by
    have h := lg_mono (by linarith : 0 < (m : ℝ)) hml
    rw [Real.logb_mul (by linarith) (by linarith),hll] at h
    linarith
  have ha₁ : (guardedPrimeCap (4*m+16) : ℝ) ≤ 128*g*l^2 := by
    have h := cap_le_from_log (d := 4*m+16) (x := 8*(m : ℝ)) (L := 4*l)
      (by omega) (by push_cast; linarith) (by
        rw [Real.logb_mul (by norm_num) (by linarith),
          show Real.logb 2 8 = 3 by rw [show (8:ℝ)=2^3 by norm_num,lg_two_pow]; norm_num]
        linarith)
    have hp := mul_le_mul_of_nonneg_right hml (show 0 ≤ 128*l by linarith)
    nlinarith only [h,hp]
  have ha₂ : (2048 : ℝ) ≤ 128*g*l^2 := by
    have hp := mul_le_mul (show (4 : ℝ) ≤ g by linarith)
      (show 4 ≤ l^2 by nlinarith [mul_nonneg (sub_nonneg.mpr hl) (show 0 ≤ l+2 by linarith)])
      (by norm_num) (by linarith)
    nlinarith only [hp]
  have hA : (A : ℝ) ≤ 2^10*g*l^2 := by
    apply (Nat.cast_le.mpr (slotSearchCap_le_window (t := slotBasePrimeCap) (c := 4*m)
      (by decide))).trans
    unfold slotWindowCap
    push_cast
    have h := max_le ha₂ ha₁
    norm_num only [slotBasePrimeCap,Nat.cast_ofNat] at h ⊢
    linarith only [h]
  have haU : (A : ℝ) ≤ 768*u*g := by
    have h := mul_le_mul_of_nonneg_left (show l^2 ≤ 3*u/4 by linarith)
      (show 0 ≤ (2 : ℝ)^10*g by positivity)
    norm_num only [show (2 : ℝ)^10 = 1024 by norm_num] at h hA
    nlinarith only [h,hA]
  have hb₁ : (guardedPrimeCap (6*k*m+16) : ℝ) ≤ 117*u*g := by
    have hlog := lg_mono (by norm_num : (0 : ℝ) < 13) (show (13 : ℝ) ≤ 2^4 by norm_num)
    rw [lg_two_pow] at hlog
    have h := cap_le_from_log (d := 6*k*m+16) (x := 13*u) (L := (9/4)*g)
      (by omega) (by push_cast; nlinarith only [hkm,hu]) (by
        rw [Real.logb_mul (by norm_num) (by linarith),hgl]
        norm_num at hlog
        linarith)
    nlinarith only [h]
  have hB : (B : ℝ) ≤ 2^13*u*g := by
    apply (Nat.cast_le.mpr (slotSearchCap_le_window (t := A) (c := 6*k*m) (by omega))).trans
    unfold slotWindowCap
    push_cast
    have h := max_le haU (hb₁.trans (by nlinarith [mul_nonneg (show 0 ≤ u by linarith) (show 0 ≤ g by linarith)]))
    norm_num
    linarith only [h,mul_nonneg (show 0 ≤ u by linarith) (show 0 ≤ g by linarith)]
  have hc₁ : (guardedPrimeCap (2*k*m+16) : ℝ) ≤ 40*u*g := by
    have hlog := lg_mono (by norm_num : (0 : ℝ) < 5) (show (5 : ℝ) ≤ 2^3 by norm_num)
    rw [lg_two_pow] at hlog
    have h := cap_le_from_log (d := 2*k*m+16) (x := 5*u) (L := 2*g)
      (by omega) (by push_cast; nlinarith only [hkm,hu]) (by
        rw [Real.logb_mul (by norm_num) (by linarith),hgl]
        norm_num at hlog
        linarith)
    nlinarith only [h]
  have hcAB : (A : ℝ)*B ≤ 2^23*u*g^2*l^2 := by
    have h := mul_le_mul hA hB hBpos (by positivity)
    norm_num only [show (2 : ℝ)^10 = 1024 by norm_num,
      show (2 : ℝ)^13 = 8192 by norm_num, show (2 : ℝ)^23 = 8388608 by norm_num] at h ⊢
    nlinarith only [h]
  refine ⟨hA,hB,?_⟩
  have ht : 512 ≤ A*B :=
    (by decide : 512 ≤ 2048*2048).trans (Nat.mul_le_mul hA₀ (hA₀.trans hB₀))
  apply (Nat.cast_le.mpr (slotSearchCap_le_window (t := A*B) (c := 2*k*m) ht)).trans
  unfold slotWindowCap
  push_cast
  have hgl' : 1 ≤ g*l^2 := by
    have hprod := mul_le_mul (show (1 : ℝ) ≤ g by linarith)
      (show 1 ≤ l^2 by nlinarith) (by norm_num) (by linarith)
    simpa using hprod
  have hh₁ := mul_le_mul_of_nonneg_left hgl' (show 0 ≤ u*g by positivity)
  have hpos : 0 ≤ u*g := by positivity
  have hc' : 40*u*g ≤ 2^23*u*g^2*l^2 := by
    norm_num
    nlinarith only [hh₁,hpos]
  have hc := max_le hcAB (hc₁.trans hc')
  norm_num
  linarith only [hc]

private theorem width_log_le (m : ℕ) (hm : 4 ≤ m) :
    Real.logb 2 ((m : ℝ)+1) ≤ (2/3)*(m : ℝ) := by
  have h : (m+1)^3 ≤ 2^(2*m) := by
    induction m, hm using Nat.le_induction with
    | base => decide
    | succ j hj ih =>
      rw [show 2*(j+1) = 2*j+2 by omega,pow_add]
      have h : 5*(j+2) ≤ 6*(j+1) := by omega
      have hp := Nat.pow_le_pow_left h 3
      rw [mul_pow,mul_pow] at hp
      norm_num at hp ⊢
      rw [show j+1+1 = j+2 by omega]
      omega
  have h' : ((m : ℝ)+1)^3 ≤ (2 : ℝ)^(2*m) := by exact_mod_cast h
  have e := lg_mono (by positivity) h'
  rw [Real.logb_pow,lg_two_pow,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_ofNat] at e
  linarith

private theorem matched_wide_caps {k m : ℕ} {u g l : ℝ}
    (hu : 16 ≤ u) (hg : 4 ≤ g) (hg2 : g^2 ≤ u) (hg3 : g^3 ≤ 8*u)
    (hl2 : l^2 ≤ 3*g) (hs : (k : ℝ)*m ≤ 2*u)
    (hA : (fallbackCap m : ℝ) ≤ 2^10*g*l^2) (hgu : Real.logb 2 u = g) :
    (matchedSlotCap k m : ℝ) ≤ 2^30*u*g := by
  have hg₀ : 0 ≤ g := by linarith
  have hu₀ : 0 ≤ u := by linarith
  have hA' : (fallbackCap m : ℝ) ≤ 3072*u := by
    have h := mul_le_mul_of_nonneg_left hl2 (show 0 ≤ (2 : ℝ)^10*g by positivity)
    norm_num only [show (2 : ℝ)^10 = 1024 by norm_num] at h hA
    nlinarith only [h,hA,hg2]
  have hcount : ((matchedSlotCount k m+16 : ℕ) : ℝ) ≤ 2^14*u := by
    unfold matchedSlotCount
    push_cast
    norm_num
    nlinarith only [hA',hs,hu]
  have hcountlog : Real.logb 2 ((2 : ℝ)^14*u)+1 ≤ 5*g := by
    rw [Real.logb_mul (by positivity) (by linarith), lg_two_pow,hgu]
    norm_num
    linarith
  have hG := cap_le_from_log (by omega : 0 < matchedSlotCount k m+16) hcount hcountlog
  have hA2 : (fallbackCap m : ℝ)^2 ≤ 2^27*u*g := by
    have h' : (fallbackCap m : ℝ) ≤ 3072*g^2 := by
      have h := mul_le_mul_of_nonneg_left hl2 (show 0 ≤ (2 : ℝ)^10*g by positivity)
      norm_num only [show (2 : ℝ)^10 = 1024 by norm_num] at h hA
      nlinarith only [h,hA]
    calc
      _ ≤ (3072*g^2)^2 := by gcongr
      _ = 9437184*g^3*g := by ring
      _ ≤ 9437184*(8*u)*g :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hg3 (by norm_num)) hg₀
      _ ≤ _ := by nlinarith only [mul_nonneg hu₀ hg₀]
  have hG' : (guardedPrimeCap (matchedSlotCount k m+16) : ℝ) ≤ 2^27*u*g := by
    apply hG.trans
    norm_num
    nlinarith only [mul_nonneg hu₀ hg₀]
  unfold matchedSlotCap slotWindowCap
  push_cast
  have h := mul_le_mul_of_nonneg_left (max_le hA2 hG') (show (0 : ℝ) ≤ 8 by norm_num)
  exact h.trans_eq (by ring)

private theorem wide_mode {n : ℕ} (hn : 65536 ≤ n) :
    24 ≤ 4*wideSlotLength n ↔ 2^256 ≤ n := by
  let v := Nat.log 2 n
  let b := Nat.log 2 v
  have hv : 16 ≤ v := (Nat.le_log_iff_pow_le (by decide) (by omega)).mpr hn
  have h₁ : 8 ≤ b ↔ 2^256 ≤ n := by
    change 8 ≤ Nat.log 2 v ↔ _
    rw [Nat.le_log_iff_pow_le (by decide) (by omega : v ≠ 0)]
    change 256 ≤ Nat.log 2 n ↔ _
    exact Nat.le_log_iff_pow_le (by decide) (by omega)
  rw [← h₁]
  constructor
  · intro h
    by_contra! hh
    have ht : Nat.log 2 b ≤ 2 := (Nat.log_mono_right (by omega : b ≤ 7)).trans (by decide)
    have hp := Nat.mul_le_mul (show b ≤ 7 by omega) ht
    change 24 ≤ 4*max 1 (b*Nat.log 2 b/4) at h
    omega
  · intro hb
    have ht : 3 ≤ Nat.log 2 b := (Nat.le_log_iff_pow_le (by decide) (by omega)).mpr hb
    have h := Nat.mul_le_mul hb ht
    change 24 ≤ 4*max 1 (b*Nat.log 2 b/4)
    omega

private theorem lg_cubed_large {u : ℝ} (hu : 0 < u) (hg : 16 ≤ Real.logb 2 u) :
    8*(Real.logb 2 u)^3 ≤ u := by
  let g := Real.logb 2 u
  let j := ⌊g⌋₊
  have hj : 16 ≤ j := Nat.le_floor hg
  have h : ∀ i ≥ 16, 8*(i+1)^3 ≤ 2^i := by
    intro i hi
    induction i,hi using Nat.le_induction with
    | base => decide
    | succ i hi ih =>
        rw [pow_succ]
        have hs : 8*(i+1+1)^3 ≤ 2*(8*(i+1)^3) := by
          nlinarith only [hi,Nat.mul_le_mul_right i hi,Nat.mul_le_mul_right (i*i) hi]
        exact hs.trans (by omega)
  have h₁ : (j : ℝ) ≤ g := Nat.floor_le (by linarith)
  have h₂ : g ≤ (j : ℝ)+1 := (Nat.lt_floor_add_one _).le
  have hp : (2 : ℝ)^j ≤ u :=
    (Real.logb_le_logb (by norm_num : (1 : ℝ) < 2) (by positivity) hu).mp (by rwa [lg_two_pow])
  have hc : 8*((j:ℝ)+1)^3 ≤ (2:ℝ)^j := by exact_mod_cast h j hj
  exact ((mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) h₂ 3) (by norm_num)).trans hc).trans hp

private theorem wideFraction_le_eighth {m : ℕ} (hm : 64≤m) :
    Real.logb 2 ((m:ℝ)+1)/(m:ℝ) ≤ 1/8 := by
  let j := m/8
  have hj : 8≤j := by dsimp [j]; omega
  have h : ∀ i ≥ 8, 8*(i+1) ≤ 2^i := by
    intro i hi
    induction i,hi using Nat.le_induction with
    | base => decide
    | succ i hi ih => rw [pow_succ]; omega
  have hc : (m:ℝ)+1 ≤ (2:ℝ)^j := by
    exact_mod_cast (show m+1≤2^j from (show m+1≤8*(j+1) by dsimp [j]; omega).trans (h j hj))
  have hl := dyadic_log_le (by positivity) hc
  have hm' : (8:ℝ)*j ≤ m := by exact_mod_cast (show 8*j≤m by dsimp [j]; omega)
  exact (div_le_iff₀ (by exact_mod_cast (by omega : 0<m))).mpr (by linarith)

private def moderateWidth (b : ℕ) := 4*(b*Nat.log 2 b/4)
private def moderateRadixLog (b : ℕ) :=
  Nat.log 2 (slotRadix (moderateWidth b) (3*(b*Nat.log 2 b/4)))
private def moderateA (b : ℕ) :=
  if b=4 then 3104 else slotWindowCap 2048 (4*moderateWidth b)
private def moderateB (b k : ℕ) :=
  let m := moderateWidth b
  let A := moderateA b
  if 24 ≤ m then slotWindowCap (A^2) (8*k*m+3*A) else slotWindowCap A (6*k*m)
private def moderateC (b k : ℕ) :=
  let m := moderateWidth b
  if 24 ≤ m then moderateB b k else slotWindowCap (moderateA b*moderateB b k) (2*k*m)

private def moderateMaximum (b : ℕ) :=
  1+(2^(b+1)-1)/moderateRadixLog b

private def moderateBase (b : ℕ) :=
  let k := moderateMaximum b
  let m := moderateWidth b
  let a := Nat.clog 2 (moderateA b)
  let c := Nat.clog 2 (moderateC b k)
  let d := Nat.clog 2 (moderateB b k)
  let h := max 68 ((m/4+1)*(c+3*d+2*a))
  2181+4*m*a+2*(h+1)

private def moderateSlope (b : ℕ) :=
  let k := moderateMaximum b
  2*moderateWidth b*(2*Nat.clog 2 (moderateC b k)+3*Nat.clog 2 (moderateB b k))

private def moderateOffset (b : ℕ) : ℕ := if b = 4 then 330 else 246

private def moderateRate (b : ℕ) := moderateOffset b - 18 + 5*b+5*Nat.log 2 b

private def moderateCheck (b k : ℕ) : Prop :=
  moderateBase b+moderateSlope b*k ≤
    1322+moderateRate b*max (2^b) ((k-1)*moderateRadixLog b)

private instance (b k : ℕ) : Decidable (moderateCheck b k) := by
  unfold moderateCheck
  infer_instance

private theorem moderateCheck_cert (b : ℕ) (hb : 4≤b) (hb' : b<48) :
    let d := moderateRadixLog b
    let j := 1+2^b/d
    0<d ∧ moderateCheck b j ∧ moderateCheck b (j+1) ∧
      moderateSlope b ≤ moderateRate b*d := by
  interval_cases b <;> decide +kernel

private theorem moderateCheck_of {b : ℕ} (hb : 4≤b) (hb' : b<48) (k : ℕ) :
    moderateCheck b k := by
  let d := moderateRadixLog b
  let j := 1+2^b/d
  obtain ⟨hd,hl,hr,hs⟩ := moderateCheck_cert b hb hb'
  change 0<d at hd
  change moderateCheck b j at hl
  change moderateCheck b (j+1) at hr
  change moderateSlope b ≤ moderateRate b*d at hs
  unfold moderateCheck at *
  by_cases hk : k≤j
  · have h : (j-1)*d≤2^b := by
      have hm := Nat.div_mul_le_self (2^b) d
      change (1+2^b/d-1)*d≤2^b
      simpa only [Nat.add_sub_cancel_left] using hm
    rw [max_eq_left h] at hl
    exact ((Nat.add_le_add_left (Nat.mul_le_mul_left _ hk) _).trans hl).trans
      (Nat.add_le_add_left (Nat.mul_le_mul_left _ (le_max_left ..)) _)
  · have hj : 2^b≤(j+1-1)*d := by
      have h := (Nat.div_lt_iff_lt_mul hd).mp (show 2^b/d<j by dsimp [j]; omega)
      simpa only [Nat.add_sub_cancel] using h.le
    rw [max_eq_right hj,Nat.add_sub_cancel] at hr
    have he : j+1 ≤ k := by omega
    obtain ⟨i,rfl⟩ := Nat.exists_eq_add_of_le he
    have hi : (j+1+i-1)*d=(j+i)*d := by
      rw [show j+1+i=j+i+1 by ac_rfl,Nat.add_sub_cancel]
    refine le_trans ?_ (Nat.add_le_add_left (Nat.mul_le_mul_left _ (le_max_right ..)) _)
    rw [hi]
    calc
      _ = (moderateBase b+moderateSlope b*(j+1))+moderateSlope b*i := by ring
      _ ≤ (1322+moderateRate b*(j*d))+(moderateRate b*d)*i :=
        Nat.add_le_add hr (Nat.mul_le_mul_right _ hs)
      _ = _ := by ring

private theorem slotWindowCap_mono {t c t' c' : ℕ} (ht : t ≤ t') (hc : c ≤ c') :
    slotWindowCap t c ≤ slotWindowCap t' c' := by
  unfold slotWindowCap guardedPrimeCap
  gcongr

private theorem moderateCaps (b k : ℕ) (hb : 4≤b) :
    fallbackCap (moderateWidth b) ≤ moderateA b ∧
    markerCap k (moderateWidth b) ≤ moderateB b k ∧
    SlotParameters.lowCap k (moderateWidth b) ≤ moderateC b k := by
  let m := moderateWidth b
  let A := fallbackCap m
  let B := separateMarkerCap k m
  have ha : A≤moderateA b := by
    by_cases he : b=4
    · subst b
      simp only [A,m,moderateA,show moderateWidth 4=8 by decide,
        fallbackCap,show slotBasePrimeCap=2048 by decide,show 4*8=32 by decide,slotSearchCap_2048_32,ite_true,le_rfl]
    · exact (slotSearchCap_le_window (by decide : 512≤slotBasePrimeCap)).trans_eq
        (by simp only [moderateA,ite_eq_right he]; rfl)
  have ha0 : 2048≤A := threshold_le_slotSearchCap ..
  have hb0 : A≤B := threshold_le_slotSearchCap ..
  refine ⟨ha,?_⟩
  by_cases hh : 24≤moderateWidth b
  · have hm : matchedSlotCap k m≤moderateB b k := by
      simp only [moderateB,matchedSlotCap,matchedSlotCount,ite_eq_left hh]
      exact slotWindowCap_mono (Nat.pow_le_pow_left ha _) (Nat.add_le_add_left (Nat.mul_le_mul_left 3 ha) _)
    simpa only [markerCap,SlotParameters.lowCap,moderateC,ite_eq_left hh] using And.intro hm hm
  · have hm : B≤moderateB b k := by
      exact (slotSearchCap_le_window (by omega : 512≤A)).trans (by
        simp only [moderateB,ite_eq_right hh]
        exact slotWindowCap_mono ha le_rfl)
    have hp : 512 ≤ A*B :=
      (by decide : 512≤2048*2048).trans (Nat.mul_le_mul ha0 (ha0.trans hb0))
    have hC : separateLowCap k m≤moderateC b k := by
      exact (slotSearchCap_le_window hp).trans (by
        simp only [moderateC,ite_eq_right hh]
        exact slotWindowCap_mono (Nat.mul_le_mul ha hm) le_rfl)
    simpa only [markerCap,SlotParameters.lowCap,ite_eq_right hh] using And.intro hm hC

private theorem wideDyadicFloors {n : ℕ} (hn : 65536≤n) :
    let b := Nat.log 2 (Nat.log 2 n)
    let u := Real.logb 2 ((n:ℝ)+4)
    let g := Real.logb 2 u
    let l := Real.logb 2 g
    4≤b ∧ (2:ℝ)^b≤u ∧ (b:ℝ)≤g ∧ (Nat.log 2 b:ℝ)≤l := by
  let b := Nat.log 2 (Nat.log 2 n)
  let u := Real.logb 2 ((n:ℝ)+4)
  let g := Real.logb 2 u
  have hn₀ : 0<n := by omega
  have hp : 16≤Nat.log 2 n := (Nat.le_log_iff_pow_le (by decide) (by omega)).mpr hn
  have hb : 4≤b := (Nat.le_log_iff_pow_le (by decide) (by omega)).mpr hp
  have hu : (2:ℝ)^b≤u := by
    have h : (2:ℝ)^b ≤ Nat.log 2 n := by exact_mod_cast Nat.pow_log_le_self 2 (by omega : Nat.log 2 n ≠ 0)
    exact (h.trans (lg_natLog_le hn₀)).trans (lg_mono (by positivity : 0<(n:ℝ)) (by linarith : (n:ℝ)≤(n:ℝ)+4))
  have hg : (b:ℝ)≤g := by
    simpa only [lg_two_pow] using lg_mono (by positivity : 0 < (2:ℝ)^b) hu
  have hl : (Nat.log 2 b:ℝ)≤Real.logb 2 g :=
    (lg_natLog_le (by omega : 0<b)).trans (lg_mono (by positivity) hg)
  exact ⟨hb,hu,hg,hl⟩

private theorem moderateBudget {n : ℕ} (hn : 65536≤n)
    (hb' : Nat.log 2 (Nat.log 2 n)<48) :
    let b := Nat.log 2 (Nat.log 2 n)
    let u := Real.logb 2 ((n:ℝ)+4)
    let k := slotPackedDigits n (wideSlotLength n)
    let v := max (2^b) ((k-1)*moderateRadixLog b)
    v ≤ u ∧ k ≤ moderateMaximum b ∧ moderateCheck b k := by
  let b := Nat.log 2 (Nat.log 2 n)
  let t := wideSlotLength n
  let R := slotRadix (4*t) (3*t)
  let k := slotPackedDigits n t
  let d := moderateRadixLog b
  obtain ⟨hb,hu,_,_⟩ := wideDyadicFloors hn
  have hd := (moderateCheck_cert b hb hb').1
  change 0<d at hd
  have ht : t=b*Nat.log 2 b/4 := by
    have h : 1≤Nat.log 2 b := (Nat.le_log_iff_pow_le (by decide) (by omega : b≠0)).mpr (by norm_num; omega)
    have hh := Nat.mul_le_mul (show 4≤b from hb) h
    change max 1 (b*Nat.log 2 b/4) = b*Nat.log 2 b/4
    exact max_eq_right (by omega)
  have hdR : d=Nat.log 2 R := by
    simp only [d,moderateRadixLog,moderateWidth,R,ht]
  have hR : 1<R := by
    rw [hdR] at hd
    by_contra! he
    interval_cases R <;> simp at hd
  have hpow : R^(k-1)≤n := by
    by_cases hk : k≤1
    · rw [Nat.sub_eq_zero_of_le hk,pow_zero]
      omega
    · have hk' : k=Nat.clog R n := max_eq_right (by unfold k slotPackedDigits at hk; omega)
      have hcl : ¬ Nat.clog R n≤k-1 := by omega
      have h := mt (Nat.clog_le_iff_le_pow hR).mpr hcl
      omega
  have hpow' : 2^((k-1)*d)≤n := by
    rw [mul_comm, pow_mul]
    exact (Nat.pow_le_pow_left (by rw [hdR]; exact Nat.pow_log_le_self _ (by omega)) _).trans hpow
  have hlog := (Nat.le_log_iff_pow_le (by decide : 1<2) (by omega : n≠0)).mpr hpow'
  have hk₂ : (k-1)*d<2^(b+1) := hlog.trans_lt (Nat.lt_pow_succ_log_self (by decide) _)
  have hk₃ : k≤1+(2^(b+1)-1)/d := by
    have h := (Nat.le_div_iff_mul_le hd).mpr (show (k-1)*d≤2^(b+1)-1 by omega)
    omega
  refine ⟨?_,?_⟩
  · rw [Nat.cast_max,Nat.cast_pow,Nat.cast_ofNat]
    refine max_le hu (?_ : (((k-1)*d:ℕ):ℝ)≤_)
    exact (Nat.cast_le.mpr hlog).trans ((lg_natLog_le (by omega : 0<n)).trans
      (lg_mono (by positivity : 0<(n:ℝ)) (by linarith : (n:ℝ)≤(n:ℝ)+4)))
  · exact ⟨hk₃,moderateCheck_of hb hb' k⟩

theorem slotRefinedEstimate_log_at {n : ℕ} (hn : 65536 ≤ n) :
    let u := Real.logb 2 ((n : ℝ)+4)
    let g := Real.logb 2 u
    let l := Real.logb 2 g
    let t := wideSlotLength n
    let k := slotPackedDigits n t
    let b := Nat.log 2 (Nat.log 2 n)
    Real.logb 2 (slotRefinedEstimate k (4*t) (3*t) : ℝ) ≤
      1322+u*(5*g+5*l+(if 5 ≤ b ∧ b < 48 then 246 else 330)) := by
  let x := (n : ℝ)+4
  let u := Real.logb 2 x
  let g := Real.logb 2 u
  let l := Real.logb 2 g
  let h := Real.logb 2 l
  let t := wideSlotLength n
  let k := slotPackedDigits n t
  let m := 4*t
  let v := Real.logb 2 ((m : ℝ)+1)
  let f := v/(m : ℝ)
  let s := 10*(k : ℝ)*(m : ℝ)
  obtain ⟨hu,hg,hl,hm₀,hml,hgm⟩ := wide_width hn
  have ht : 0 < t := (by decide : 0 < 1).trans_le (le_max_left ..)
  have hm₄ : 4 ≤ m := by unfold m; omega
  have hm : (4 : ℝ) ≤ m := by exact_mod_cast hm₄
  have hm' : (m : ℝ) = 4*(t : ℝ) := by simp [m]
  rw [← hm'] at hml hgm
  change (m : ℝ) ≤ g*l at hml
  change g*l ≤ 6*(m : ℝ) at hgm
  change 16 ≤ u at hu
  change 4 ≤ g at hg
  change 2 ≤ l at hl
  have hu₀ : 0 < u := by linarith
  have hg₀ : 0 < g := by linarith
  have hl₀ : 0 < l := by linarith
  have hgu : g ≤ u/4 := by
    have h := lg_ratio (b := 4) (by decide) (by norm_num; exact hu : (2 : ℝ)^4 ≤ u)
    norm_num at h
    exact (by change Real.logb 2 u ≤ _; linarith only [h])
  have hlg : l ≤ g/2 := by
    have h := lg_ratio (b := 2) (by decide) (by norm_num; exact hg : (2 : ℝ)^2 ≤ g)
    norm_num at h
    exact (by change Real.logb 2 g ≤ _; linarith only [h])
  have hh : h ≤ l := by
    have h' : h ≤ l := by
      by_cases h₄ : (4 : ℝ) ≤ l
      · have hh := lg_ratio (b := 2) (by decide) (by norm_num; exact h₄ : (2 : ℝ)^2 ≤ l)
        norm_num at hh
        change Real.logb 2 l ≤ _
        linarith
      · have hh := lg_mono (by linarith : 0 < l) (show l ≤ (2 : ℝ)^2 by norm_num; linarith)
        rw [lg_two_pow] at hh
        norm_num at hh
        change Real.logb 2 l ≤ _
        linarith
    exact h'
  have hh₀ : 0 ≤ h := Real.logb_nonneg (by norm_num) (by linarith)
  have hl2 : l^2 ≤ 3*g := log_squared_le (by linarith) hl
  have hg3 : g^3 ≤ 8*u := log_cubed_le (by linarith) hg
  have hg2 : g^2 ≤ u := by
    apply (Real.logb_le_logb (by norm_num : (1 : ℝ)<2)
      (by positivity : 0 < g^2) (by linarith : 0 < u)).mp
    rw [Real.logb_pow]
    change (2 : ℝ)*l ≤ g
    linarith
  have hmu : (m : ℝ) ≤ u/2 := by
    have he := mul_le_mul_of_nonneg_left hlg (show 0 ≤ g by linarith)
    nlinarith only [hml,he,hg2]
  have hmg : (m : ℝ)*g ≤ 4*u := by
    have he := mul_le_mul_of_nonneg_right hml (show 0 ≤ g by linarith)
    have hf := mul_le_mul_of_nonneg_left hlg (show 0 ≤ g^2 by positivity)
    nlinarith only [he,hf,hg3]
  have hml' : (m : ℝ)*l ≤ 2*u := by
    have he := mul_le_mul_of_nonneg_left hlg (show 0 ≤ (m : ℝ) by positivity)
    nlinarith only [he,hmg]
  have hv : v ≤ 2*l+1 := by
    have he := lg_mono (by positivity : 0 < (m : ℝ)+1) (show (m : ℝ)+1 ≤ 2*((m : ℝ)) by linarith)
    rw [lg_two_times (by linarith)] at he
    have hh' := lg_mono (by linarith : 0 < (m : ℝ)) hml
    rw [Real.logb_mul (by linarith) (by linarith)] at hh'
    change Real.logb 2 (m : ℝ) ≤ l+h at hh'
    linarith only [he,hh',hh]
  have hf₀ : 0 ≤ f := div_nonneg
    (Real.logb_nonneg (by norm_num) (by linarith : 1 ≤ (m : ℝ)+1)) (by positivity)
  have hf : f ≤ 2/3 := (div_le_iff₀ (by linarith : 0 < (m : ℝ))).mpr (width_log_le m hm₄)
  have hfm : f*(m : ℝ) = v := div_mul_cancel₀ _ (by linarith)
  have hfg : f*g ≤ 15 := by
    have he := mul_le_mul_of_nonneg_left hgm hf₀
    by_contra! hcon
    have hcon' := mul_lt_mul_of_pos_right hcon (show 0 < l by linarith)
    nlinarith only [he,hfm,hv,hl,hcon']
  have hfl : f*l ≤ 15/2 := by
    have he := mul_le_mul_of_nonneg_left hlg hf₀
    nlinarith only [he,hfg]
  let j := (k-1 : ℕ)
  have hj : (j : ℝ)*(2*(m : ℝ)-v) ≤ u := by
    have he := slot_digit_log_bound (n := n) (t := t) (by omega) ht
    have hu' := lg_mono (by positivity : 0 < (n : ℝ)) (show (n : ℝ) ≤ x by dsimp [x]; linarith)
    apply le_trans _ hu'
    convert he using 1
    dsimp [j,k,m,v]
    push_cast
    ring
  have hs₀ : s = 10*(j : ℝ)*(m : ℝ)+10*m := by
    have hk : k = j+1 := by
      have : 1 ≤ k := le_max_left ..
      unfold j
      omega
    dsimp [s]
    push_cast [hk]
    ring
  have hj' : (10*(j : ℝ)*(m : ℝ))*(2-f) ≤ 10*u := by
    have he := mul_le_mul_of_nonneg_left hj (show (0 : ℝ) ≤ 10 by norm_num)
    have hf' := congrArg (fun q : ℝ => 10*(j : ℝ)*q) hfm
    nlinarith only [he,hf']
  have hs : s ≤ (25/2)*u := by
    have he := mul_le_mul_of_nonneg_left (show 4/3 ≤ 2-f by linarith)
      (show 0 ≤ 10*(j : ℝ)*(m : ℝ) by positivity)
    nlinarith only [he,hj',hs₀,hmu]
  have hsc : s ≤ (5+4*f)*u+10*m := by
    have he : 10 ≤ (5+4*f)*(2-f) := by
      have h := mul_nonneg hf₀ (show 0 ≤ 3-4*f by linarith)
      nlinarith only [h]
    have he' := mul_le_mul_of_nonneg_right he (show 0 ≤ u by linarith)
    have hx : 10*(j : ℝ)*(m : ℝ) ≤ (5+4*f)*u := by
      apply le_of_mul_le_mul_right _ (show 0 < 2-f by linarith)
      nlinarith only [hj',he']
    linarith only [hs₀,hx]
  have hkm : (k : ℝ)*m ≤ 2*u := by unfold s at hs; linarith
  obtain ⟨hA,hBsep,hCsep⟩ := widePrimeCaps hu hg hl hgu hl2 hm₄ hml hkm rfl rfl hh
  let A := fallbackCap m
  let B := markerCap k m
  let C := SlotParameters.lowCap k m
  let Q := slotPrimeCap k m
  let P := slotStackPrimeCap Q
  let X := stackTestCap P (slotDeckCap k m ((slotRadix m (3*t))^k))
  let H := slotAssemblyRadius k m (3*t)
  let N := order (fourValueLayout 0)
  have hx : 0 < x := by dsimp [x]; positivity
  have hk : 1 ≤ k := le_max_left ..
  have hm₁ : 1 ≤ m := by omega
  have hA₀ := fallbackCap_pos m
  have hAB := fallbackCap_le_markerCap k m
  have hB₀ := hA₀.trans_le hAB
  have hBC : B ≤ C := markerCap_le_lowCap k m
  have hC₀ := hB₀.trans_le hBC
  have hmatched := matched_wide_caps hu hg hg2 hg3 hl2 hkm hA rfl
  have hxu : 2*u ≤ x := by
    have h := lg_ratio (b := 2) (by decide) (show (2 : ℝ)^2 ≤ x by dsimp [x]; linarith)
    norm_num at h
    linarith only [h]
  have hkmx : k*m ≤ n+4 := by
    have h : (k : ℝ)*(m : ℝ) ≤ (n : ℝ)+4 := hkm.trans hxu
    exact_mod_cast h
  have hkx := (Nat.le_mul_of_pos_right k hm₁).trans hkmx
  have hmx := (Nat.le_mul_of_pos_left m hk).trans hkmx
  have h2m : 2^m ≤ n+4 := by
    have h : (2 : ℝ)^m ≤ x := by
      apply (Real.logb_le_logb (by norm_num : (1 : ℝ)<2) (by positivity) hx).mp
      rw [lg_two_pow]
      linarith only [hm,hmu,hu]
    dsimp [x] at h
    exact_mod_cast h
  have hD : (slotRadix m (3*t))^k ≤ (n+4)^3 := by
    have hh := slot_digit_capacity_upper (by omega : 0 < n) ht
    change (slotRadix m (3*t))^k ≤ n*4^m at hh
    calc
      _ ≤ n*4^m := hh
      _ = n*(2^m)^2 := by rw [show (4:ℕ) = 2^2 by decide, ← pow_mul, Nat.mul_comm 2 m, pow_mul]
      _ ≤ (n+4)*(n+4)^2 := Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left h2m _)
      _ = (n+4)^3 := by ring
  have hn₆ : 1 ≤ x^6 := one_le_pow₀ (by dsimp [x]; linarith)
  have hgb : g ≤ x := by linarith only [hgu,hxu,hu]
  have hQN : (Q : ℝ) ≤ (2 : ℝ)^57*x^6 := by
    change (↑(max A (max B C)) : ℝ) ≤ _
    rw [max_eq_right (hAB.trans (le_max_left ..)),max_eq_right hBC]
    change (SlotParameters.lowCap k m : ℝ) ≤ _
    unfold SlotParameters.lowCap
    split
    · calc
        _ ≤ (2 : ℝ)^30*u*g := hmatched
        _ ≤ (2 : ℝ)^57*x*x := by
          have hux : u ≤ x := by linarith
          exact mul_le_mul
            (mul_le_mul_of_nonneg_right (dyadic_le (by decide : 30 ≤ 57)) hu₀.le |>.trans
              (mul_le_mul_of_nonneg_left hux (by positivity))) hgb hg₀.le (by positivity)
        _ ≤ _ := by
          rw [mul_assoc,← pow_two]
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact pow_le_pow_right₀ (by dsimp [x]; linarith) (by decide)
    · calc
        _ ≤ (2 : ℝ)^26*u*g^2*l^2 := hCsep
        _ ≤ (2 : ℝ)^26*x*x^2*x^2 := by
          gcongr <;> linarith only [hxu,hu,hlg,hgb]
        _ ≤ _ := by
          have h₁ : (2 : ℝ)^26 ≤ (2 : ℝ)^57 := dyadic_le (by decide)
          have h₂ : x^5 ≤ x^6 := pow_le_pow_right₀ (by dsimp [x]; linarith) (by decide)
          convert mul_le_mul h₁ h₂ (by positivity) (by positivity) using 1
          ring
  have hN : N ≤ 2^1893 := arithmetic_order_le
  have hNr : (N : ℝ) ≤ (2 : ℝ)^1893 := by exact_mod_cast hN
  have hX : (X : ℝ) ≤ (2 : ℝ)^57*x^6 := by
    have hd := slot_deck_cap_polynomial k m ((slotRadix m (3*t))^k) (n+4)
      (by omega) hkx hmx hkmx h2m hD
    have hd' : (slotDeckCap k m ((slotRadix m (3*t))^k) : ℝ) ≤
        (4000+(arithmeticBaseline.length : ℝ))*x^6 := by dsimp [x]; exact_mod_cast hd
    have h₅ : (5000 : ℝ) ≤ (2 : ℝ)^57 :=
      (by norm_num : (5000 : ℝ) ≤ 2^13).trans (dyadic_le (by decide))
    have hc {z : ℝ} (hz : z ≤ (2 : ℝ)^57) : z ≤ (2 : ℝ)^57*x^6 :=
      hz.trans (by simpa using mul_le_mul_of_nonneg_left hn₆ (show 0 ≤ (2:ℝ)^57 by positivity))
    unfold X stackTestCap P slotStackPrimeCap
    simp only [Nat.cast_max,Nat.cast_ofNat]
    apply max_le _ (max_le (max_le _ (max_le _ hQN)) _)
    · exact hc ((by norm_num : (2313 : ℝ) ≤ 5000).trans h₅)
    · exact hc ((by norm_num : (4 : ℝ) ≤ 5000).trans h₅)
    · exact hc (by norm_num [slotBasePrimeCap])
    · exact hd'.trans (mul_le_mul_of_nonneg_right
        (by have h : (arithmeticBaseline.length : ℝ) ≤ 1000 := by exact_mod_cast arithmetic_count_le
            exact (show 4000+(arithmeticBaseline.length : ℝ) ≤ 5000 by linarith only [h]).trans h₅) (by positivity))
  have hX0 : 0 < X := (by decide : 0 < 2313).trans_le (le_max_left ..)
  have hXL : Real.logb 2 (X : ℝ) ≤ 57+6*u := by
    have h := lg_mono (show 0 < (X : ℝ) by exact_mod_cast hX0) hX
    rw [Real.logb_mul (by positivity) (by positivity),lg_two_pow,Real.logb_pow] at h
    exact h
  have ha : 0 < (A : ℝ) := by exact_mod_cast hA₀
  have hb : 0 < (B : ℝ) := by exact_mod_cast hB₀
  have hc : 0 < (C : ℝ) := by exact_mod_cast hC₀
  have hxa : Real.logb 2 (A : ℝ) ≤ 10+l+2*h := by
    have he := lg_mono ha hA
    rw [Real.logb_mul (by positivity) (by positivity),Real.logb_mul (by positivity) (by positivity),
      lg_two_pow,Real.logb_pow] at he
    exact_mod_cast he
  have hlogs :
      if 24 ≤ m then
        Real.logb 2 (B : ℝ) ≤ 30+g+l ∧ Real.logb 2 (C : ℝ) ≤ 30+g+l
      else
        Real.logb 2 (B : ℝ) ≤ 13+g+l ∧ Real.logb 2 (C : ℝ) ≤ 26+g+2*l+2*h := by
    by_cases hm' : 24 ≤ m
    · rw [ite_eq_left hm']
      have he {p : ℝ} (hp : 0 < p) (hbound : p ≤ 2^30*u*g) :
          Real.logb 2 p ≤ 30+g+l := by
        have h' := lg_mono hp hbound
        rw [Real.logb_mul (by positivity) (by positivity),Real.logb_mul (by positivity) (by positivity),
          lg_two_pow] at h'
        exact_mod_cast h'
      exact ⟨he hb (by simpa only [B,markerCap,ite_eq_left hm'] using hmatched),
        he hc (by simpa only [C,SlotParameters.lowCap,ite_eq_left hm'] using hmatched)⟩
    · rw [ite_eq_right hm']
      have hB : (B : ℝ) ≤ 2^13*u*g := by simpa only [B,markerCap,ite_eq_right hm'] using hBsep
      have hC : (C : ℝ) ≤ 2^26*u*g^2*l^2 := by simpa only [C,SlotParameters.lowCap,ite_eq_right hm'] using hCsep
      constructor
      · have he := lg_mono hb hB
        rw [Real.logb_mul (by positivity) (by positivity),Real.logb_mul (by positivity) (by positivity),
          lg_two_pow] at he
        exact_mod_cast he
      · have he := lg_mono hc hC
        rw [Real.logb_mul (by positivity) (by positivity),Real.logb_mul (by positivity) (by positivity),
          Real.logb_mul (by positivity) (by positivity),lg_two_pow,Real.logb_pow,Real.logb_pow] at he
        exact_mod_cast he
  let W := (C : ℝ)^2*(B : ℝ)^3
  have hW : Real.logb 2 W = 2*Real.logb 2 (C : ℝ)+3*Real.logb 2 (B : ℝ) := by
    unfold W
    rw [Real.logb_mul (by positivity) (by positivity),Real.logb_pow,Real.logb_pow]
    norm_num
  let Z := (C : ℝ)*(B : ℝ)^3*(A : ℝ)^2
  let r := min m (m+1-3*t)
  have hZ : Real.logb 2 Z = Real.logb 2 (C : ℝ)+3*Real.logb 2 (B : ℝ)+2*Real.logb 2 (A : ℝ) := by
    unfold Z
    rw [Real.logb_mul (by positivity) (by positivity),Real.logb_mul (by positivity) (by positivity),
      Real.logb_pow,Real.logb_pow]
    norm_num
  have hr : 2*(r : ℝ) ≤ m := by
    have hn' : 2*r ≤ m := by
      have h := min_le_right m (m+1-3*t)
      unfold r m at *
      omega
    exact_mod_cast hn'
  have hZ₁ : 1 ≤ Z := by
    have ha' : 1 ≤ (A : ℝ) := by exact_mod_cast (show 1 ≤ A by omega)
    have hb' : 1 ≤ (B : ℝ) := by exact_mod_cast hB₀
    have hc' : 1 ≤ (C : ℝ) := by exact_mod_cast hC₀
    exact one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le hc' (one_le_pow₀ hb')) (one_le_pow₀ ha')
  have hH : (H : ℝ)+1 ≤ (2 : ℝ)^70*Z^r := by
    have h : (fourValueRadius 0 : ℝ) = 2^68 := by
      rw [show fourValueRadius 0 = 2^68 by decide]
      norm_num
    have hZr : 1 ≤ Z^r := one_le_pow₀ hZ₁
    change (↑(max (fourValueRadius 0) (slotOffsetFactorCap k m^r)) : ℝ)+1 ≤ _
    rw [slotOffsetFactorCap,ite_eq_right (by omega : ¬ (k = 1 ∧ m = 1)),
      ite_eq_right (by omega : ¬ (k = 2 ∧ m = 1))]
    simp only [Nat.cast_max,Nat.cast_pow,Nat.cast_mul,h,← max_add_add_right]
    change max ((2 : ℝ)^68+1) (Z^r+1) ≤ _
    norm_num
    constructor <;> linarith
  have hN : N ≤ 2^1893 := arithmetic_order_le
  have hNr : (N : ℝ) ≤ (2 : ℝ)^1893 := by exact_mod_cast hN
  have hN₀ : 0 < (N : ℝ) := by exact_mod_cast fourValueOrder_pos 0
  have hconst : Real.logb 2 (10^35*(N : ℝ)) ≤ 2010 := by
    apply dyadic_log_le (i := 2010) (by positivity)
    rw [show 2010 = 117+1893 by decide,pow_add]
    exact mul_le_mul (by norm_num : (10 : ℝ)^35 ≤ 2^117) hNr (by positivity) (by positivity)
  have hsize : (slotRefinedEstimate k m (3*t) : ℝ) =
      (10^35*(N : ℝ))*(W^(2*k*m)*(A : ℝ)^(4*m))*(X : ℝ)^3*((H : ℝ)+1)^2 := by
    simp only [slotRefinedEstimate, Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_ofNat,
      Nat.cast_one, W, A, B, C, H, N, X, Q, P]
    ring
  have he := slot_log_bound_factors (c := 10^35*(N : ℝ)) (by positivity)
    (show 0 < W by positivity) ha (show 0 < (X : ℝ) by exact_mod_cast hX0)
    (by positivity : 0 < (H : ℝ)+1) (2*k*m) (4*m)
  let C₀ : ℝ := if 5 ≤ Nat.log 2 (Nat.log 2 n) ∧ Nat.log 2 (Nat.log 2 n) < 48 then 246 else 330
  change Real.logb 2 (slotRefinedEstimate k m (3*t) : ℝ) ≤ 1322+u*(5*g+5*l+C₀)
  rw [hsize,he]
  push_cast
  let b := Nat.log 2 (Nat.log 2 n)
  obtain ⟨hb₄,hub,hgb,hlb⟩ := wideDyadicFloors hn
  have hbB := hb
  by_cases hb : b<48
  · obtain ⟨hv,hkM,hcheck⟩ := moderateBudget hn hb
    have ht' : t=b*Nat.log 2 b/4 := by
      have hol : 1≤Nat.log 2 b := (Nat.le_log_iff_pow_le (by decide) (by omega : b≠0)).mpr (by norm_num; omega)
      have := Nat.mul_le_mul (show 4≤b from hb₄) hol
      change max 1 (b*Nat.log 2 b/4) = b*Nat.log 2 b/4
      exact max_eq_right (by omega)
    have hm' : m=moderateWidth b := by simp only [m,ht',moderateWidth]
    let K := moderateMaximum b
    obtain ⟨ha',hb',hc'⟩ := moderateCaps b k hb₄
    have hkK : k≤K := hkM
    have monoB : moderateB b k ≤ moderateB b K := by
      by_cases h : 24≤moderateWidth b
      · simp only [moderateB,ite_eq_left h]
        exact slotWindowCap_mono le_rfl (by gcongr)
      · simp only [moderateB,ite_eq_right h]
        exact slotWindowCap_mono le_rfl (by gcongr)
    have monoC : moderateC b k ≤ moderateC b K := by
      by_cases h : 24≤moderateWidth b
      · simpa only [moderateC,ite_eq_left h] using monoB
      · simp only [moderateC,ite_eq_right h]
        exact slotWindowCap_mono (Nat.mul_le_mul_left _ monoB) (by gcongr)
    rw [←hm'] at ha' hb' hc'
    let da := Nat.clog 2 (moderateA b)
    let db := Nat.clog 2 (moderateB b K)
    let dc := Nat.clog 2 (moderateC b K)
    let dh := max 68 ((m/4+1)*(dc+3*db+2*da))
    let v := max (2^b) ((k-1)*moderateRadixLog b)
    have ceiling (a : ℕ) : a ≤ 2^Nat.clog 2 a :=
      (Nat.clog_le_iff_le_pow (by decide)).mp le_rfl
    have ha₂ : A≤2^da := ha'.trans (ceiling _)
    have hb₂ : B≤2^db := hb'.trans (monoB.trans (ceiling _))
    have hc₂ : C≤2^dc := hc'.trans (monoC.trans (ceiling _))
    have hAL := dyadic_log_le ha (by exact_mod_cast ha₂)
    have hBL := dyadic_log_le hbB (by exact_mod_cast hb₂)
    have hCL := dyadic_log_le hc (by exact_mod_cast hc₂)
    have hWL : Real.logb 2 W ≤ 2*(dc:ℝ)+3*(db:ℝ) := by rw [hW]; linarith
    have hH₂ : H ≤ 2^dh := by
      change max (fourValueRadius 0) (slotOffsetFactorCap k m^r) ≤ _
      rw [show fourValueRadius 0 = 2^68 by decide]
      apply max_le (Nat.pow_le_pow_right (by decide) (le_max_left ..))
      have hz := (slotOffsetFactorCap_le k m).trans
        (Nat.mul_le_mul (Nat.mul_le_mul hc₂ (Nat.pow_le_pow_left hb₂ 3)) (Nat.pow_le_pow_left ha₂ 2))
      change slotOffsetFactorCap k m ≤ 2^dc*(2^db)^3*(2^da)^2 at hz
      rw [←pow_mul,←pow_mul,←pow_add,←pow_add,mul_comm db 3,mul_comm da 2] at hz
      have hr' : r ≤ m/4+1 := by
        have hx := min_le_right m (m+1-3*t)
        unfold r m at *
        omega
      apply (Nat.pow_le_pow_left hz r).trans
      rw [←pow_mul,mul_comm]
      exact Nat.pow_le_pow_right (by decide) ((Nat.mul_le_mul_right _ hr').trans (le_max_right ..))
    have hH₃ : (H:ℝ)+1 ≤ (2:ℝ)^(dh+1) := by
      have h₁ : (H:ℝ)≤(2:ℝ)^dh := by exact_mod_cast hH₂
      have h₂ : (1:ℝ)≤(2:ℝ)^dh := one_le_pow₀ (by norm_num)
      rw [pow_succ]
      linarith
    have hHL := dyadic_log_le (by positivity : 0<(H:ℝ)+1) hH₃
    have hoff : 18 ≤ moderateOffset b := by unfold moderateOffset; split <;> decide
    have hCeq : C₀ = moderateOffset b := by
      change (if 5 ≤ b ∧ b < 48 then (246:ℝ) else 330) = _
      by_cases he : b = 4
      · simp [moderateOffset,he]
      · simp [moderateOffset,he,show 5 ≤ b ∧ b < 48 from ⟨by omega,hb⟩]
    have hnum : (2181:ℝ)+2*(k:ℝ)*m*(2*(dc:ℝ)+3*(db:ℝ))+4*(m:ℝ)*da+18*v+2*((dh:ℝ)+1) ≤
        1322+((moderateOffset b:ℝ)+5*(b:ℝ)+5*(Nat.log 2 b:ℝ))*v := by
      have h' : 2181+2*k*m*(2*dc+3*db)+4*m*da+18*v+2*(dh+1) ≤
          1322+(moderateOffset b+5*b+5*Nat.log 2 b)*v := by
        change moderateCheck b k at hcheck
        unfold moderateCheck moderateBase moderateSlope moderateRate at hcheck
        rw [←hm'] at hcheck
        change 2181+4*m*da+2*(dh+1)+(2*m*(2*dc+3*db))*k ≤
          1322+(moderateOffset b-18+5*b+5*Nat.log 2 b)*v at hcheck
        calc
          _ = (2181+4*m*da+2*(dh+1)+(2*m*(2*dc+3*db))*k)+18*v := by ring
          _ ≤ (1322+(moderateOffset b-18+5*b+5*Nat.log 2 b)*v)+18*v :=
            Nat.add_le_add_right hcheck _
          _ = 1322+(moderateOffset b-18+5*b+5*Nat.log 2 b+18)*v := by ring
          _ = _ := by rw [show moderateOffset b-18+5*b+5*Nat.log 2 b+18 =
            moderateOffset b+5*b+5*Nat.log 2 b by omega]
      exact_mod_cast h'
    have hV : (v:ℝ)≤u := hv
    have hfix : (moderateOffset b:ℝ)+5*(b:ℝ)+5*(Nat.log 2 b:ℝ)-18 ≤ C₀+5*g+5*l-18 := by
      rw [hCeq]; linarith
    have ho : (18:ℝ) ≤ C₀ := by rw [hCeq]; exact_mod_cast hoff
    have ht := mul_le_mul hfix hV (by positivity) (by linarith : 0≤C₀+5*g+5*l-18)
    have hw := mul_le_mul_of_nonneg_left hWL (show 0≤2*(k:ℝ)*m by positivity)
    have ha := mul_le_mul_of_nonneg_left hAL (show 0≤4*(m:ℝ) by positivity)
    push_cast at hHL
    nlinarith only [ht,hnum,hw,ha,hHL,hXL,hconst]
  · have hCB : C₀ = 330 := if_neg (by change ¬ (5 ≤ b ∧ b < 48); omega)
    rw [hCB]
    have hb : 16 ≤ b := by omega
    have hu16 : (2:ℝ)^16 ≤ u := (dyadic_le hb).trans hub
    have hg16 : 16 ≤ g := (by exact_mod_cast hb : (16:ℝ) ≤ b).trans hgb
    have hl4 : 4 ≤ l := (by exact_mod_cast
      (Nat.le_log_iff_pow_le (by decide : 1<2) (by omega : b≠0)).mpr hb : (4:ℝ) ≤ Nat.log 2 b).trans hlb
    have hm64 : 64≤m := by
      have hj : 4≤Nat.log 2 b := (Nat.le_log_iff_pow_le (by decide) (by omega : b≠0)).mpr hb
      have hm' := Nat.mul_le_mul hb hj
      change 64 ≤ 4*max 1 (b * Nat.log 2 b / 4)
      omega
    have hstrong := lg_cubed_large hu₀ hg16
    change 8*g^3 ≤ u at hstrong
    have hmg' : (m:ℝ)*g≤u/16 := by
      have h₁ := mul_le_mul_of_nonneg_right hml hg₀.le
      have h₂ := mul_le_mul_of_nonneg_right hlg (show 0≤g^2 by positivity)
      nlinarith only [h₁,h₂,hstrong]
    have hmu' : (m:ℝ)≤u/256 := by
      nlinarith only [hmg',mul_le_mul_of_nonneg_left hg16 (show 0≤(m:ℝ) by positivity)]
    have hml'' : (m:ℝ)*l≤u/32 := by
      nlinarith only [hmg',mul_le_mul_of_nonneg_left hlg (show 0≤(m:ℝ) by positivity)]
    have hf' : f ≤ 1/8 := wideFraction_le_eighth hm64
    have hs' : s≤6*u := by
      have h₁ := mul_le_mul_of_nonneg_right hf' hu₀.le
      nlinarith only [h₁,hsc,hmu',hu₀]
    have hsg' : s*g≤5*u*g+61*u := by
      have h₁ := mul_le_mul_of_nonneg_right hsc hg₀.le
      have h₂ := mul_le_mul_of_nonneg_right hfg (show 0 ≤ 4*u by linarith)
      nlinarith only [h₁,h₂,hmg',hu₀]
    have hsl' : s*l≤5*u*l+31*u := by
      have h₁ := mul_le_mul_of_nonneg_right hsc hl₀.le
      have h₂ := mul_le_mul_of_nonneg_right hfl (show 0 ≤ 4*u by linarith)
      nlinarith only [h₁,h₂,hml'',hu₀]
    have hm' : 24 ≤ m := by omega
    rw [ite_eq_left hm'] at hlogs
    obtain ⟨hBL,hCL⟩ := hlogs
    have hWlarge : (2*(k:ℝ)*(m:ℝ))*Real.logb 2 W ≤ u*(5*g+5*l+272) := by
      rw [show (2:ℝ)*k*m=s/5 by unfold s; ring,hW]
      have h₁ : 2*Real.logb 2 (C:ℝ)+3*Real.logb 2 (B:ℝ)≤5*(30+g+l) := by linarith
      have h₂ := mul_le_mul_of_nonneg_left h₁ (show 0≤s/5 by dsimp [s]; positivity)
      nlinarith only [h₂,hs',hsg',hsl']
    have hAlarge : 4*(m:ℝ)*Real.logb 2 (A:ℝ)≤u := by
      have h₁ := mul_le_mul_of_nonneg_left hxa (show 0≤(m:ℝ) by positivity)
      have h₂ := mul_le_mul_of_nonneg_left hh (show 0≤(m:ℝ) by positivity)
      nlinarith only [h₁,h₂,hmu',hml'',hu₀]
    have hHlarge : 2*Real.logb 2 ((H:ℝ)+1)≤2*u := by
      have he := lg_mono (by positivity : 0 < (H:ℝ)+1) hH
      rw [Real.logb_mul (by positivity) (by positivity),lg_two_pow,Real.logb_pow] at he
      have hz₀ := Real.logb_nonneg (by norm_num : (1:ℝ)<2) hZ₁
      have h₁ := mul_le_mul_of_nonneg_right hr hz₀
      have hz : Real.logb 2 Z≤140+4*g+10*l := by rw [hZ]; linarith
      have h₂ := mul_le_mul_of_nonneg_left hz (show 0≤(m:ℝ) by positivity)
      simp only [Nat.cast_ofNat] at he
      have hu65536 : 65536≤u := by simpa only [show (2:ℝ)^16=65536 by norm_num] using hu16
      nlinarith only [he,h₁,h₂,hmu',hmg',hml'',hu65536]
    have hu65536 : 65536≤u := by simpa only [show (2:ℝ)^16=65536 by norm_num] using hu16
    nlinarith only [hWlarge,hAlarge,hHlarge,hXL,hconst,hu65536]



theorem slotRefinedEstimate_log {n : ℕ} (hn : 65536 ≤ n) :
    let u := Real.logb 2 ((n : ℝ)+4)
    let g := Real.logb 2 u
    let l := Real.logb 2 g
    let t := wideSlotLength n
    let k := slotPackedDigits n t
    Real.logb 2 (slotRefinedEstimate k (4*t) (3*t) : ℝ) ≤ 1322+u*(5*g+5*l+330) := by
  dsimp only
  apply (slotRefinedEstimate_log_at hn).trans
  gcongr
  · exact Real.logb_nonneg (by norm_num) (by linarith [Nat.cast_nonneg (α := ℝ) n])
  · split <;> norm_num

end
end TranslationTiling.Compiler.Size
