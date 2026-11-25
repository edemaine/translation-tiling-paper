import TranslationTiling.Compiler.SlotComputability
import TranslationTiling.FiniteCompiler.Effective.PackedTotalCompiler

namespace TranslationTiling.Compiler.Size

open FiniteCompiler.Packed FiniteCompiler.Packed.SlotParameters
open FiniteCompiler.SharedCoordinates FiniteCompiler.Effective

noncomputable section

set_option maxHeartbeats 2500000
set_option maxRecDepth 10000

/-- The explicit size bound for the constant-weight compiler. Its
leading two iterated-logarithmic coefficients are five and sixty-five. -/
def slotExplicitBound (n : ℕ) : ℝ :=
  let x := (n : ℝ) + 4
  let g := Real.logb 2 (Real.logb 2 x)
  max (x^(5*g+65*Real.logb 2 g) * (n : ℝ)^(2700 : ℕ)) (2^(2065 : ℕ))

private theorem dyadic_le {i j : ℕ} (h : i ≤ j) : (2 : ℝ)^i ≤ (2 : ℝ)^j :=
  pow_le_pow_right₀ (by norm_num) h

private theorem dyadic_log_le {x : ℝ} (hx : 0 < x) {i : ℕ} (h : x ≤ (2 : ℝ)^i) :
    Real.logb 2 x ≤ i := by simpa only [lg_two_pow] using lg_mono hx h

private theorem arithmetic_order_le : order (fourValueLayout 0) ≤ 2^1893 := by
  rw [fourValueLayout_order]
  simpa only [Nat.mul_zero,pow_zero,Nat.mul_one] using fourValueRows_order_bound 0

/-- The width and digit count give the leading coefficient without
charging the fixed prime-cap constant to the third logarithm. -/
private theorem large_slot_count {n : ℕ} (hn : 65536 ≤ n) :
    let u := Real.logb 2 ((n : ℝ)+4)
    let g := Real.logb 2 u
    let l := Real.logb 2 g
    let t := slotLengthParameter n
    let m := 4*(t : ℝ)
    let s := 10*(slotPackedDigits n t : ℝ)*m
    m ≤ g ∧ g ≤ u/4 ∧ g^2 ≤ u ∧
      s ≤ (25/2)*u ∧ s*g ≤ u*(5*g+15*l+25) := by
  let u := Real.logb 2 ((n : ℝ)+4)
  let g := Real.logb 2 u
  let l := Real.logb 2 g
  let t := slotLengthParameter n
  let m := 4*(t : ℝ)
  let s := 10*(slotPackedDigits n t : ℝ)*m
  let u₀ := Real.logb 2 (n : ℝ)
  let g₀ := Real.logb 2 u₀
  have hpow : (2 : ℝ)^16 ≤ (n : ℝ) := by
    norm_num
    exact_mod_cast hn
  have hu₀ : 16 ≤ u₀ := by
    have h := lg_mono (by positivity) hpow
    rwa [lg_two_pow] at h
  have hle : u₀ ≤ u := lg_mono (by positivity) (by norm_num)
  have hu : 16 ≤ u := hu₀.trans hle
  have hgu : g ≤ u/4 := by
    have h := lg_ratio (b := 4) (by decide) (by norm_num; exact hu : (2 : ℝ)^4 ≤ u)
    change _ ≤ _ at h
    norm_num at h
    exact (by change Real.logb 2 u ≤ _; linarith only [h])
  have hg₀ : 4 ≤ g₀ := by
    have h := lg_mono (by positivity) (by norm_num; exact hu₀ : (2 : ℝ)^4 ≤ u₀)
    rwa [lg_two_pow] at h
  have hg₀g : g₀ ≤ g := lg_mono (by linarith) hle
  have hg : 4 ≤ g := hg₀.trans hg₀g
  have hlg : l ≤ g/2 := by
    have h := lg_ratio (b := 2) (by decide) (by norm_num; exact hg : (2 : ℝ)^2 ≤ g)
    norm_num at h
    exact (by change Real.logb 2 g ≤ _; linarith only [h])
  have hg2 : g^2 ≤ u := by
    apply (Real.logb_le_logb (by norm_num : (1 : ℝ)<2)
      (by positivity : 0 < g^2) (by linarith : 0 < u)).mp
    rw [Real.logb_pow]
    change (2 : ℝ)*l ≤ g
    linarith
  have hgg : g ≤ g₀+1 := by
    have hn' : (n : ℝ)+4 ≤ 2*(n : ℝ) := by
      have h : (65536 : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    have h := lg_mono (by positivity : 0 < (n : ℝ)+4) hn'
    rw [Real.logb_mul (by norm_num) (by positivity),Real.logb_self_eq_one (by norm_num)] at h
    have h₁ : u ≤ 2*u₀ := by change u ≤ 1+u₀ at h; linarith
    have h₂ := lg_mono (by linarith : 0 < u) h₁
    rw [Real.logb_mul (by norm_num) (by linarith),Real.logb_self_eq_one (by norm_num)] at h₂
    linarith only [h₂]
  obtain ⟨hmlo,hmhi⟩ := slot_width_additive (by omega : 2 ≤ n)
  change g₀ < m+5 at hmlo
  change m ≤ max 4 g₀ at hmhi
  rw [max_eq_right hg₀] at hmhi
  have hm : m ≤ g := hmhi.trans hg₀g
  have ht : 0 < t := (by decide : 0 < 1).trans_le (le_max_left ..)
  have hm₄ : 4 ≤ m := by
    have h : (1 : ℝ) ≤ t := by exact_mod_cast ht
    change 4 ≤ 4*(t : ℝ)
    linarith
  let v := Real.logb 2 (m+1)
  have hv0 : 0 ≤ v := Real.logb_nonneg (by norm_num) (by linarith)
  have hv1 : v ≤ 1+l := by
    have h := lg_mono (by linarith : 0 < m+1) (show m+1 ≤ 2*g by linarith)
    rw [Real.logb_mul (by norm_num) (by linarith),Real.logb_self_eq_one (by norm_num)] at h
    exact h
  have hvm : v ≤ m := by
    have hp (j : ℕ) : j+1 ≤ 2^j := by
      induction j with
      | zero => decide
      | succ j ih => rw [pow_succ]; omega
    have h := lg_mono (by linarith : 0 < m+1)
      (show m+1 ≤ (2 : ℝ)^(4*t) by dsimp [m]; exact_mod_cast hp (4*t))
    rw [lg_two_pow] at h
    push_cast at h
    exact h
  have hm0 : 0 < m := by linarith
  have hvdiv : 0 ≤ v/m := by positivity
  have hcount : s ≤ 5*u*(1+v/m)+10*m := by
    have h := slot_factor_count (n := n) (t := t) (by omega) ht
    change s ≤ 5*u₀*(1+v/m)+40*(t : ℝ) at h
    rw [show 40*(t : ℝ) = 10*m by unfold m; ring] at h
    exact h.trans (by gcongr)
  have hdiv : v/m ≤ 1 := (div_le_iff₀ hm0).mpr (by simpa using hvm)
  have hcoarse : s ≤ (25/2)*u := by
    have h := mul_le_mul_of_nonneg_left (show 1+v/m ≤ 2 by linarith) (show 0 ≤ 5*u by linarith)
    linarith only [h,hcount,hm,hgu]
  have hgdiv : g/m ≤ 3 := (div_le_iff₀ hm0).mpr (by linarith)
  have hvterm : v/m*g ≤ 3*(1+l) := by
    rw [div_mul_eq_mul_div,mul_div_assoc]
    exact (mul_le_mul_of_nonneg_left hgdiv hv0).trans (by linarith only [hv1])
  have hmg : m*g ≤ u := (mul_le_mul_of_nonneg_right hm (by linarith)).trans (by rwa [← pow_two])
  have hmul := mul_le_mul_of_nonneg_right hcount (show 0 ≤ g by linarith)
  have hcorr := mul_le_mul_of_nonneg_left hvterm (show 0 ≤ 5*u by linarith)
  exact ⟨hm,hgu,hg2,hcoarse,by nlinarith only [hmul,hcorr,hmg]⟩

private theorem arithmetic_count_le : arithmeticBaseline.length ≤ 1000 := by
  decide +kernel

private theorem arithmetic_radius_le : fourValueRadius 0 + 2 ≤ 2^150 := by
  decide +kernel

private theorem explicit_main_log {n : ℕ} (hn : 65536 ≤ n) :
    let u := Real.logb 2 ((n : ℝ)+4)
    let g := Real.logb 2 u
    let l := Real.logb 2 g
    let t := slotLengthParameter n
    let k := slotPackedDigits n t
    Real.logb 2 (slotSizeBound k (4*t) (3*t) : ℝ) ≤ u*(5*g+65*l+2000) := by
  let x := (n : ℝ)+4
  let u := Real.logb 2 x
  let g := Real.logb 2 u
  let l := Real.logb 2 g
  let t := slotLengthParameter n
  let k := slotPackedDigits n t
  let m := 4*t
  let s := 10*(k : ℝ)*(m : ℝ)
  let N := order (fourValueLayout 0)
  let A := fallbackCap m
  let Q := slotPrimeCap k m
  let P := slotStackPrimeCap Q
  let X := stackTestCap P (slotDeckCap k m ((slotRadix m (3*t))^k))
  let H := slotRadius Q m
  let F := (fourValueRadius 0 : ℝ)+2
  let C : ℝ := 2^56
  have hx : 0 < x := by dsimp [x]; positivity
  have hu : 16 ≤ u := by
    have h : (2 : ℝ)^16 ≤ x := by
      have hN : (65536 : ℝ) ≤ n := by exact_mod_cast hn
      dsimp [x]
      norm_num
      linarith
    simpa only [lg_two_pow,Nat.cast_ofNat] using lg_mono (by positivity) h
  have hg : 4 ≤ g := by
    have h := lg_mono (by positivity) (show (2 : ℝ)^4 ≤ u by norm_num; exact hu)
    rwa [lg_two_pow] at h
  have hl0 : 0 ≤ l := Real.logb_nonneg (by norm_num) (by linarith)
  have hlg : l ≤ g := by
    have h := lg_ratio (b := 2) (by decide) (show (2 : ℝ)^2 ≤ g by norm_num; exact hg)
    norm_num at h
    linarith only [h,hg]
  have hC : 1 ≤ C := one_le_pow₀ (by norm_num)
  obtain ⟨hm,hgu,hg2,hs,hsg⟩ := large_slot_count hn
  have hmcast : (m : ℝ) = 4*(t : ℝ) := by simp [m]
  change 4*(t : ℝ) ≤ g at hm
  change 10*(k : ℝ)*(4*(t : ℝ)) ≤ _ at hs
  change 10*(k : ℝ)*(4*(t : ℝ))*g ≤ _ at hsg
  rw [← hmcast] at hm hs hsg
  change (m : ℝ) ≤ g at hm
  change g ≤ u/4 at hgu
  change g^2 ≤ u at hg2
  change s ≤ (25/2)*u at hs
  change s*g ≤ u*(5*g+15*l+25) at hsg
  have ht : 0 < t := (by decide : 0 < 1).trans_le (le_max_left ..)
  have hk : 1 ≤ k := le_max_left ..
  have hm₁ : 1 ≤ m := by unfold m; omega
  have hkm : (k : ℝ)*(m : ℝ) ≤ 2*u := by dsimp [s] at hs; linarith
  obtain ⟨ha,hmark,hlow⟩ := slot_prime_caps_scale_explicit k m u g
    (by linarith) (by linarith) hg2 le_rfl hlg hm hkm
  have hQ1 : (Q : ℝ) ≤ C*u*g^4 := by
    change (↑(max (fallbackCap m) (max (markerCap k m) (SlotParameters.lowCap k m))) : ℝ) ≤ _
    simp only [Nat.cast_max]
    apply max_le _ (max_le hmark hlow)
    apply ha.trans
    have hg' : g^2 ≤ g^4 := pow_le_pow_right₀ (by linarith) (by decide)
    have hCu : C ≤ C*u := by
      simpa using mul_le_mul_of_nonneg_left (show 1 ≤ u by linarith) (show 0 ≤ C by positivity)
    exact (mul_le_mul_of_nonneg_left hg' (show 0 ≤ C by positivity)).trans
      (mul_le_mul_of_nonneg_right hCu (by positivity))
  have hAq : A ≤ Q := le_max_left ..
  have hA0 : 0 < A := by unfold A fallbackCap guardedPrimeCap; positivity
  have hQ0 : 0 < Q := hA0.trans_le hAq
  have hQ' : 0 < (Q : ℝ) := by exact_mod_cast hQ0
  have hQL : Real.logb 2 (Q : ℝ) ≤ 56+g+4*l := by
    have h := lg_mono hQ' hQ1
    rw [Real.logb_mul (by positivity) (by positivity),
      Real.logb_mul (by positivity) (by positivity),lg_two_pow,Real.logb_pow] at h
    exact h
  have hmnonneg := Nat.cast_nonneg (α := ℝ) m
  have hmg : (m : ℝ)*g ≤ u :=
    (mul_le_mul_of_nonneg_right hm (by linarith : 0 ≤ g)).trans (by rwa [← pow_two])
  have hmQ : (m : ℝ)*Real.logb 2 (Q : ℝ) ≤ 19*u := by
    have h₁ := mul_le_mul_of_nonneg_left hQL hmnonneg
    have h₂ := mul_le_mul_of_nonneg_left hlg hmnonneg
    nlinarith only [h₁,h₂,hmg,hm,hgu]
  have hAA : (m : ℝ)*Real.logb 2 (A : ℝ) ≤ 19*u :=
    (mul_le_mul_of_nonneg_left
      (lg_mono (show 0 < (A : ℝ) by exact_mod_cast hA0)
        (show (A : ℝ) ≤ (Q : ℝ) by exact_mod_cast hAq)) hmnonneg).trans hmQ
  have hmain : s*Real.logb 2 (Q : ℝ) ≤ u*(5*g+65*l+725) := by
    have h := mul_le_mul_of_nonneg_left hQL (show 0 ≤ s by dsimp [s]; positivity)
    have h' := mul_le_mul_of_nonneg_right hs (show 0 ≤ 56+4*l by linarith)
    nlinarith only [h,h',hsg]
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
      linarith only [hm,hgu,hu]
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
    calc
      _ ≤ C*u*g^4 := hQ1
      _ ≤ C*x*x^4 := by gcongr; linarith only [hxu,hu]
      _ = C*x^5 := by rw [pow_succ' x 4,mul_assoc]
      _ ≤ (2 : ℝ)^57*x^6 :=
        mul_le_mul (dyadic_le (by decide)) (pow_le_pow_right₀ (by dsimp [x]; linarith) (by decide))
          (by positivity) (by positivity)
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
  have hH : ((H : ℝ)+1) ≤ F*(Q : ℝ)^(11*m) := by
    have hq : 1 ≤ (Q : ℝ)^(11*m) := one_le_pow₀ (by exact_mod_cast hQ0)
    unfold H slotRadius
    simp only [Nat.cast_max,Nat.cast_pow]
    rw [← max_add_add_right]
    apply max_le
    · dsimp [F]
      nlinarith only [hq, mul_le_mul_of_nonneg_left hq
        (show 0 ≤ (fourValueRadius 0 : ℝ)+2 by positivity)]
    · dsimp [F]
      nlinarith only [hq,mul_nonneg (Nat.cast_nonneg (α := ℝ) (fourValueRadius 0))
        (show 0 ≤ (Q : ℝ)^(11*m) by positivity)]
  have hF : Real.logb 2 F ≤ 150 :=
    dyadic_log_le (by dsimp [F]; positivity) (by dsimp [F]; exact_mod_cast arithmetic_radius_le)
  have hHL : Real.logb 2 ((H : ℝ)+1) ≤ 150+11*19*u := by
    have h := lg_mono (by positivity : 0 < (H : ℝ)+1) hH
    rw [Real.logb_mul (by positivity) (by positivity), Real.logb_pow] at h
    push_cast at h
    nlinarith only [h,hmQ,hF]
  have hN0 : 0 < (N : ℝ) := by exact_mod_cast fourValueOrder_pos 0
  have hZ : Real.logb 2 (10^35*(N : ℝ)) ≤ 2010 := by
    apply dyadic_log_le (i := 2010) (by positivity)
    rw [show 2010 = 117+1893 by decide,pow_add]
    exact mul_le_mul (by norm_num : (10 : ℝ)^35 ≤ 2^117) hNr (by positivity) (by positivity)
  have hform : Real.logb 2 (slotSizeBound k m (3*t) : ℝ) =
      Real.logb 2 (10^35*(N : ℝ)) + s*Real.logb 2 (Q : ℝ) +
        4*(m : ℝ)*Real.logb 2 (A : ℝ) +
        3*Real.logb 2 (X : ℝ)+2*Real.logb 2 ((H : ℝ)+1) := by
    have hsz : (slotSizeBound k m (3*t) : ℝ) =
        (10^35*(N : ℝ))*((Q : ℝ)^(10*k*m)*(A : ℝ)^(4*m))*(X : ℝ)^3*((H : ℝ)+1)^2 := by
      change ((10^35*(N*(Q^(10*k*m)*A^(4*m)))*X^3*(H+1)^2 : ℕ) : ℝ) = _
      simp only [Nat.cast_mul,Nat.cast_pow,Nat.cast_add,Nat.cast_ofNat,Nat.cast_one]
      ring
    rw [hsz]
    have h := slot_log_bound_factors (c := 10^35*(N : ℝ)) (by positivity)
      hQ' (show 0 < (A : ℝ) by exact_mod_cast hA0) (show 0 < (X : ℝ) by exact_mod_cast hX0)
      (by positivity : 0 < (H : ℝ)+1) (10*k*m) (4*m)
    simpa only [s,Nat.cast_mul,Nat.cast_ofNat] using h
  change Real.logb 2 (slotSizeBound k m (3*t) : ℝ) ≤ u*(5*g+65*l+2000)
  rw [hform]
  nlinarith only [hZ,hmain,hAA,hXL,hHL,hu]

set_option maxRecDepth 40000 in
private theorem width_four_numerical {k : ℕ} (hk₁ : 1 ≤ k) (hk : k ≤ 3) :
    (4*Rails.Strips.countCapAt 35 (fun _ => slotAssemblyRadius k 4 3)+4229 ≤ 2^811) ∧
      (k = 1 → slotShortEstimate k 4 3 ≤ 2^4250) ∧ slotShortEstimate k 4 3 ≤ 2^6800 := by
  have h : k = 1 ∨ k = 2 ∨ k = 3 := by omega
  rcases h with rfl | rfl | rfl <;> decide +kernel

private theorem small_slot_width {n : ℕ} (hn : n < 65536) :
    slotLengthParameter n = 1 := by
  have h : Nat.log 2 n ≤ 15 :=
    (Nat.log_mono_right (by omega : n ≤ 65535)).trans (by decide)
  have h' : Nat.log 2 (Nat.log 2 n) ≤ 3 :=
    (Nat.log_mono_right h).trans (by decide)
  unfold slotLengthParameter
  omega

private theorem slot_digits_at_four {n k : ℕ} (hk : 1 ≤ k) (hn : n ≤ 108^k)
    (hl : k = 1 ∨ 108^(k-1) < n) :
    slotPackedDigits n 1 = k := by
  change max 1 (Nat.clog 108 n) = k
  have h : Nat.clog 108 n ≤ k := (Nat.clog_le_iff_le_pow (by decide)).mpr hn
  have h' : k ≤ max 1 (Nat.clog 108 n) := by
    rcases hl with rfl | hl
    · exact le_max_left ..
    · have : ¬ Nat.clog 108 n ≤ k-1 := by
        intro hc
        exact hl.not_ge ((Nat.clog_le_iff_le_pow (by decide)).mp hc)
      omega
  exact le_antisymm (max_le hk h) h'

private theorem slot_size_positive {k m w : ℕ} : 0 < slotSizeBound k m w := by
  have hN := fourValueOrder_pos 0
  have hA : 0 < fallbackCap m := by unfold fallbackCap guardedPrimeCap; positivity
  have hQ : 0 < slotPrimeCap k m := hA.trans_le (le_max_left ..)
  have hX : 0 < stackTestCap (slotStackPrimeCap (slotPrimeCap k m)) (slotDeckCap k m ((slotRadix m w)^k)) :=
    (by decide : 0 < 2313).trans_le (le_max_left ..)
  unfold slotSizeBound
  positivity

private theorem le_explicit_of_log {n : ℕ} {B : ℝ} (hn : 2 ≤ n) (hB : 0 < B)
    (h : let x := (n : ℝ)+4
         let u := Real.logb 2 x
         let g := Real.logb 2 u
         Real.logb 2 B ≤ u*(5*g+65*Real.logb 2 g)+2700*Real.logb 2 (n : ℝ)) :
    B ≤ slotExplicitBound n := by
  have hx : 0 < (n : ℝ)+4 := by positivity
  have hₙ : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  apply le_trans _ (le_max_left _ _)
  apply (Real.logb_le_logb (by norm_num : (1 : ℝ)<2) hB (by positivity)).mp
  rw [Real.logb_mul (Real.rpow_pos_of_pos hx _).ne' (by positivity),
    Real.logb_rpow_eq_mul_logb_of_pos hx, Real.logb_pow]
  simpa only [Nat.cast_ofNat,mul_comm] using h

theorem slot_size_bound_explicit {n : ℕ} (hn : 65536 ≤ n) :
    let t := slotLengthParameter n
    let k := slotPackedDigits n t
    (slotSizeBound k (4*t) (3*t) : ℝ) ≤ slotExplicitBound n := by
  apply le_explicit_of_log (by omega) (by exact_mod_cast slot_size_positive)
  let u := Real.logb 2 ((n : ℝ)+4)
  let v := Real.logb 2 (n : ℝ)
  let g := Real.logb 2 u
  let l := Real.logb 2 g
  have hn' : (65536 : ℝ) ≤ n := by exact_mod_cast hn
  have hv : 16 ≤ v := by
    have h := lg_mono (by positivity : 0 < (2 : ℝ)^16)
      (show (2 : ℝ)^16 ≤ n by rwa [show (2 : ℝ)^16 = 65536 by norm_num])
    rwa [lg_two_pow] at h
  have huv : u ≤ 1+v := by
    have h := lg_mono (by positivity : 0 < (n : ℝ)+4) (show (n : ℝ)+4 ≤ 2*(n : ℝ) by linarith)
    rw [Real.logb_mul (by norm_num) (by positivity), Real.logb_self_eq_one (by norm_num)] at h
    exact h
  have h := explicit_main_log hn
  change _ ≤ u*(5*g+65*l+2000) at h
  exact h.trans (by nlinarith only [huv,hv])

private theorem small_compiler_log {T : LeanWang.TileSet} (hn : 2 ≤ T.length)
    (hlt : T.length < 65536) (hB : 0 < ((compileSlot T).length : ℝ)) :
    let n := (T.length : ℝ)
    let u := Real.logb 2 (n+4)
    let g := Real.logb 2 u
    Real.logb 2 ((compileSlot T).length : ℝ) ≤ u*(5*g+65*Real.logb 2 g)+2700*Real.logb 2 n := by
  let n := (T.length : ℝ)
  let u := Real.logb 2 (n+4)
  let g := Real.logb 2 u
  let l := Real.logb 2 g
  let v := Real.logb 2 n
  have hn' : (2 : ℝ) ≤ n := by
    change (2 : ℝ) ≤ (T.length : ℝ)
    exact_mod_cast hn
  have hv : 1 ≤ v := by
    have h := lg_mono (by norm_num : 0 < (2 : ℝ)) hn'
    rwa [Real.logb_self_eq_one (by norm_num)] at h
  have hu : (5 : ℝ)/2 ≤ u := by
    apply lg_lower (a := 5) (b := 2) (by decide) _ (by linarith : 0 < n+4)
    exact (by norm_num : (2 : ℝ)^5 ≤ 6^2).trans (pow_le_pow_left₀ (by norm_num) (by linarith) _)
  have hg : (5 : ℝ)/4 ≤ g := by
    apply lg_lower (a := 5) (b := 4) (by decide) _ (by linarith : 0 < u)
    exact (by norm_num : (2 : ℝ)^5 ≤ ((5 : ℝ)/2)^4).trans
      (pow_le_pow_left₀ (by norm_num) hu _)
  have hl : (1 : ℝ)/4 ≤ l := by
    have hpow : (2 : ℝ)^1 ≤ g^4 := (by norm_num : (2 : ℝ)^1 ≤ ((5 : ℝ)/4)^4).trans
      (pow_le_pow_left₀ (by norm_num) hg _)
    simpa only [Nat.cast_one, Nat.cast_ofNat] using
      (lg_lower (a := 1) (b := 4) (by decide) hpow (by linarith : 0 < g))
  have hmain : 50 ≤ u*(5*g+65*l) := by
    have h := mul_le_mul hu (show (45 : ℝ)/2 ≤ 5*g+65*l by linarith) (by norm_num) (by linarith)
    linarith
  change _ ≤ u*(5*g+65*l)+2700*v
  by_cases hs : T.length ≤ 3
  · have h : (compileSlot T).length ≤ 2^2750 :=
      (compileSlot_smallWidth T hn hs).trans (by decide +kernel)
    exact (dyadic_log_le (i := 2750) hB (by exact_mod_cast h)).trans
      (by norm_num only [Nat.cast_ofNat]; linarith)
  · have ht := small_slot_width hlt
    let k := slotPackedDigits T.length 1
    have hk₁ (h : T.length ≤ 108) : k = 1 :=
      slot_digits_at_four (by decide) (by simpa using h) (Or.inl rfl)
    have hk₂ (h : 108 < T.length) : k = 2 ∨ k = 3 := by
      by_cases h₂ : T.length ≤ 11664
      · exact Or.inl (slot_digits_at_four (by decide) h₂ (Or.inr (by omega)))
      · exact Or.inr (slot_digits_at_four (by decide) (by omega) (Or.inr (by omega)))
    have hk : k = 1 ∨ k = 2 ∨ k = 3 := by
      by_cases h₁ : T.length ≤ 108
      · exact Or.inl (hk₁ h₁)
      · exact Or.inr (hk₂ (by omega))
    obtain ⟨hH,hshort₁,hshort⟩ := width_four_numerical (by omega : 1 ≤ k) (by omega)
    have hb := compileSlot_widthFour T (by omega) ht hH
    by_cases h₁ : T.length ≤ 108
    · have h : (compileSlot T).length ≤ 2^4250 := hb.trans (hshort₁ (hk₁ h₁))
      have hv₂ : 2 ≤ v := by
        have hn₄ : (4 : ℝ) ≤ n := by
          change (4 : ℝ) ≤ (T.length : ℝ)
          exact_mod_cast (show 4 ≤ T.length by omega)
        have hv' := lg_mono (by norm_num : 0 < (2 : ℝ)^2) (show (2 : ℝ)^2 ≤ n by norm_num; exact hn₄)
        rwa [lg_two_pow] at hv'
      exact (dyadic_log_le (i := 4250) hB (by exact_mod_cast h)).trans
        (by norm_num only [Nat.cast_ofNat]; linarith)
    · have h : (compileSlot T).length ≤ 2^6800 := hb.trans hshort
      have hv₃ : 3 ≤ v := by
        have hn₈ : (8 : ℝ) ≤ n := by
          change (8 : ℝ) ≤ (T.length : ℝ)
          exact_mod_cast (show 8 ≤ T.length by omega)
        have hv' := lg_mono (by norm_num : 0 < (2 : ℝ)^3) (show (2 : ℝ)^3 ≤ n by norm_num; exact hn₈)
        rwa [lg_two_pow] at hv'
      exact (dyadic_log_le (i := 6800) hB (by exact_mod_cast h)).trans
        (by norm_num only [Nat.cast_ofNat]; linarith)

/-- The uniform computable compiler meets the explicit bound. -/
theorem compileSlot_explicit (T : LeanWang.TileSet) (hn : 0 < T.length) :
    (compileSlot T).length ≤ slotExplicitBound T.length := by
  by_cases h : T.length = 1
  · have hb : ((compileSlot T).length : ℝ) ≤ ((2^2065 : ℕ) : ℝ) :=
      Nat.cast_le.mpr (compileSlot_one T h)
    rw [Nat.cast_pow,Nat.cast_ofNat] at hb
    exact hb.trans (le_max_right _ _)
  · by_cases hlarge : 65536 ≤ T.length
    · have hb := (compileSlot_correct T hn).2.2.2
      exact (Nat.cast_le.mpr hb).trans (slot_size_bound_explicit hlarge)
    · have hp : 0 < ((compileSlot T).length : ℝ) := by
        exact_mod_cast List.length_pos_iff.mpr (compileSlot_correct T hn).1
      exact le_explicit_of_log (by omega) hp (small_compiler_log (by omega) (by omega) hp)

/-- Totalize the compiler by encoding the empty alphabet as a single Wang tile
that cannot tile the plane. -/
def compileSlotTotal (T : LeanWang.TileSet) : Tile 3 :=
  compileSlot (nonemptyInput T)

theorem compileSlotTotal_computable : Computable compileSlotTotal :=
  compileSlot_computable.comp nonemptyInput_primrec.to_comp

theorem compileSlotTotal_facts (T : LeanWang.TileSet) :
    compileSlotTotal T ≠ [] ∧ FaceConnected (compileSlotTotal T) ∧
      (LeanWang.TilesPlane T ↔ TranslationTiling.Tiles (compileSlotTotal T)) ∧
      ((compileSlotTotal T).length : ℝ) ≤ slotExplicitBound T.length := by
  have hlen := nonemptyInput_length T
  have hp : 0 < (nonemptyInput T).length := by
    rw [hlen]
    exact Nat.zero_lt_one.trans_le (le_max_left _ _)
  obtain ⟨hne,hconn,hiff,_⟩ := compileSlot_correct (nonemptyInput T) hp
  refine ⟨hne,hconn,(nonemptyInput_tiles T).symm.trans hiff,?_⟩
  by_cases h : T.length = 0
  · have h₁ : (nonemptyInput T).length = 1 := by simpa only [h,max_eq_left (by decide : 0 ≤ 1)] using hlen
    have hb : ((compileSlotTotal T).length : ℝ) ≤ ((2^2065 : ℕ) : ℝ) :=
      Nat.cast_le.mpr (compileSlot_one _ h₁)
    rw [Nat.cast_pow,Nat.cast_ofNat] at hb
    exact hb.trans (le_max_right _ _)
  · have h₁ : (nonemptyInput T).length = T.length :=
      hlen.trans (max_eq_right (Nat.one_le_iff_ne_zero.mpr h))
    have hb := compileSlot_explicit (nonemptyInput T) hp
    rw [h₁] at hb
    exact hb

/-- The public formula absorbs the polynomial factor into the exponent
of the shifted base and retains the sharp bound for at most one tile. -/
def slotPublicBound (n : ℕ) : ℝ :=
  if n ≤ 1 then 2^2065 else
  ((n : ℝ)+4)^(5*Real.logb 2 (Real.logb 2 ((n : ℝ)+4)) +
    65*Real.logb 2 (Real.logb 2 (Real.logb 2 ((n : ℝ)+4))) + 2700)

theorem compileSlotTotal_public_bound (T : LeanWang.TileSet) :
    ((compileSlotTotal T).length : ℝ) ≤ slotPublicBound T.length := by
  by_cases hn : T.length ≤ 1
  · rw [slotPublicBound,ite_eq_left hn]
    have h : (nonemptyInput T).length = 1 :=
      (nonemptyInput_length T).trans (max_eq_left hn)
    exact_mod_cast compileSlot_one (nonemptyInput T) h
  · rw [slotPublicBound,ite_eq_right hn]
    let n := (T.length : ℝ)
    let x := n+4
    let g := Real.logb 2 (Real.logb 2 x)
    let a := 5*g+65*Real.logb 2 g
    have hn₀ : 0 ≤ n := by dsimp [n]; positivity
    have hx : 0 < x := by dsimp [x]; positivity
    have hx₂ : (2 : ℝ) ≤ x := by dsimp [x]; linarith
    have hg : 1 ≤ g := by
      have h := lg_mono (by positivity : 0 < (2 : ℝ)^2)
        (show (2 : ℝ)^2 ≤ x by norm_num; dsimp [x]; linarith)
      rw [lg_two_pow] at h
      have h' := lg_mono (by positivity : 0 < (2 : ℝ)) h
      rwa [Real.logb_self_eq_one (by norm_num)] at h'
    have ha : 0 ≤ a := by
      dsimp [a]
      linarith [Real.logb_nonneg (by norm_num : (1 : ℝ) < 2) hg]
    apply (compileSlotTotal_facts T).2.2.2.trans
    change max (x^a*n^(2700 : ℕ)) (2^(2065 : ℕ)) ≤ x^(a+2700)
    apply max_le
    · calc
        _ ≤ x^a*x^(2700 : ℕ) := mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ hn₀ (by dsimp [x]; linarith) _) (by positivity)
        _ = _ := by
          rw [← Real.rpow_natCast x 2700, ← Real.rpow_add hx, Nat.cast_ofNat]
    · calc
        _ ≤ x^(2065 : ℕ) := pow_le_pow_left₀ (by norm_num) hx₂ _
        _ = x^(2065 : ℝ) := (Real.rpow_natCast x 2065).symm
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)

end
end TranslationTiling.Compiler.Size
