import TranslationTiling.Compiler.SlotBound
import TranslationTiling.Compiler.SlotCapacity

namespace TranslationTiling.Compiler.Size

open FiniteCompiler.Packed

noncomputable section

private theorem lg_nat_lt_succ {n : ℕ} (hn : 0 < n) :
    Real.logb 2 (n : ℝ) < (Nat.log 2 n : ℝ) + 1 := by
  have hpow : (n : ℝ) < (2 : ℝ) ^ (Nat.log 2 n + 1) := by
    exact_mod_cast Nat.lt_pow_succ_log_self (by decide : 1 < (2 : ℕ)) n
  have hlog := Real.logb_lt_logb (by norm_num : (1 : ℝ) < 2)
    (show 0 < (n : ℝ) by exact_mod_cast hn) hpow
  rw [lg_two_pow, Nat.cast_add, Nat.cast_one] at hlog
  exact hlog

private theorem lg_mul_two {x : ℝ} (hx : 0 < x) :
    Real.logb 2 (2*x) = 1 + Real.logb 2 x := by
  rw [Real.logb_mul (by norm_num) hx.ne', Real.logb_self_eq_one (by norm_num)]

/-- The integer width differs from the second logarithm by at most a
constant, with a minimum width of four. -/
theorem slot_width_additive {n : ℕ} (hn : 2 ≤ n) :
    let g := Real.logb 2 (Real.logb 2 (n : ℝ))
    let m := 4*(slotLengthParameter n : ℝ)
    g < m+5 ∧ m ≤ max 4 g := by
  let a := Nat.log 2 n
  let b := Nat.log 2 a
  let u := Real.logb 2 (n : ℝ)
  let g := Real.logb 2 u
  have hu : 0 < u := Real.logb_pos (by norm_num) (by exact_mod_cast (show 1 < n by omega))
  have ha : 0 < a := Nat.log_pos (by decide) hn
  have hau : (a : ℝ) ≤ u := Real.natLog_le_logb _ _
  have hua : u < (a : ℝ)+1 := lg_nat_lt_succ (by omega)
  have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hga : g ≤ Real.logb 2 (2*(a : ℝ)) := lg_mono hu (by linarith)
  rw [lg_mul_two (by exact_mod_cast ha)] at hga
  have hgb : g < (b : ℝ)+2 := by
    have h := lg_nat_lt_succ ha
    change Real.logb 2 (a : ℝ) < (b : ℝ)+1 at h
    linarith
  have hbg : (b : ℝ) ≤ g :=
    (Real.natLog_le_logb a 2).trans (lg_mono (by exact_mod_cast ha) hau)
  have hlo : b ≤ 4*slotLengthParameter n+3 := by
    change b ≤ 4*max 1 (b/4)+3
    omega
  have hhi : 4*slotLengthParameter n ≤ max 4 b := by
    change 4*max 1 (b/4) ≤ max 4 b
    omega
  have hlr : (b : ℝ) ≤ 4*(slotLengthParameter n : ℝ)+3 := by exact_mod_cast hlo
  have hhr : 4*(slotLengthParameter n : ℝ) ≤ max 4 (b : ℝ) := by exact_mod_cast hhi
  exact ⟨by linarith, hhr.trans (max_le_max_left _ hbg)⟩

/-- The width is within a factor of two of the second logarithm
throughout the range of the asymptotic estimate. -/
theorem slot_width_bounds {n : ℕ} (hn : 2 ≤ n)
    (hg : 16 ≤ Real.logb 2 (Real.logb 2 (n : ℝ))) :
    let g := Real.logb 2 (Real.logb 2 (n : ℝ))
    let m := 4*(slotLengthParameter n : ℝ)
    g/2 ≤ m ∧ m ≤ g := by
  obtain ⟨hl,hh⟩ := slot_width_additive hn
  dsimp only
  exact ⟨by linarith,hh.trans_eq (max_eq_right (by linarith))⟩

/-- Squared iterated-logarithmic widths fit inside the first logarithm
in the range used for the asymptotic bound. -/
theorem slot_log_squared_le {u : ℝ} (hu : 0 < u) (hg : 16 ≤ Real.logb 2 u) :
    (Real.logb 2 u)^2 ≤ u := by
  let g := Real.logb 2 u
  change 16 ≤ g at hg
  have hg' : (2 : ℝ)^4 ≤ g := by norm_num; exact hg
  have h := lg_ratio (b := 4) (by decide) hg'
  norm_num at h
  apply (Real.logb_le_logb (by norm_num : (1 : ℝ) < 2)
    (by change 0 < g^2; positivity) hu).mp
  change Real.logb 2 (g^2) ≤ g
  rw [Real.logb_pow]
  norm_num
  linarith

/-- The radix loss contributes only a third-logarithmic term after
multiplying by the logarithm of the slot prime. -/
theorem slot_leading_log {n : ℕ} (hn : 2 ≤ n)
    (hg : 16 ≤ Real.logb 2 (Real.logb 2 (n : ℝ))) {A : ℝ} (hA : 0 ≤ A) :
    let u := Real.logb 2 (n : ℝ)
    let g := Real.logb 2 u
    let e := 1 + Real.logb 2 g
    let t := slotLengthParameter n
    let m := 4*(t : ℝ)
    let s := 10*(slotPackedDigits n t : ℝ)*m
    s*(g + A*e) ≤ u*(5*g + (30+20*A)*e) := by
  let u := Real.logb 2 (n : ℝ)
  let g := Real.logb 2 u
  let e := 1 + Real.logb 2 g
  let t := slotLengthParameter n
  let m := 4*(t : ℝ)
  let s := 10*(slotPackedDigits n t : ℝ)*m
  let v := Real.logb 2 (m+1)
  change 16 ≤ g at hg
  change s*(g + A*e) ≤ u*(5*g + (30+20*A)*e)
  have hu : 0 < u := Real.logb_pos (by norm_num) (by exact_mod_cast (show 1 < n by omega))
  have ge := slot_width_bounds hn hg
  change g/2 ≤ m ∧ m ≤ g at ge
  have hm : 0 < m := by linarith [ge.1]
  have hg0 : 0 < g := by linarith
  have hsquare : g^2 ≤ u := slot_log_squared_le hu hg
  have heg : 1 ≤ e :=
    le_add_of_nonneg_right (Real.logb_nonneg (by norm_num) (by linarith : 1 ≤ g))
  have hv0 : 0 ≤ v := Real.logb_nonneg (by norm_num) (by linarith : 1 ≤ m+1)
  have hve : v ≤ e := by
    have h := lg_mono (show 0 < m+1 by linarith) (show m+1 ≤ 2*g by linarith [ge.2])
    rwa [lg_mul_two hg0] at h
  have hvm : v ≤ m := by
    have hp (j : ℕ) : j+1 ≤ 2^j := by
      induction j with
      | zero => decide
      | succ j ih => rw [pow_succ]; omega
    have h := lg_mono (x := m+1) (y := (2 : ℝ)^(4*t)) (by linarith)
      (by dsimp [m]; exact_mod_cast hp (4*t))
    rw [lg_two_pow] at h
    push_cast at h
    exact h
  have ht : 0 < t := (by decide : 0 < 1).trans_le (le_max_left ..)
  have hcount : s ≤ 5*u*(1+v/m)+10*m := by
    have h := slot_factor_count (n := n) (t := t) (by omega) ht
    change s ≤ 5*u*(1+v/m)+40*(t : ℝ) at h
    convert h using 1
    dsimp [m]
    ring
  have hgu : g ≤ u := by nlinarith
  have hcoarse : s ≤ 20*u := by
    have hf : v/m ≤ 1 := (div_le_iff₀ hm).mpr (by simpa using hvm)
    have h := mul_le_mul_of_nonneg_left (show 1+v/m ≤ 2 by linarith)
      (show 0 ≤ 5*u by positivity)
    linarith [ge.2]
  have hgquot : g/m ≤ 2 :=
    (div_le_iff₀ hm).mpr (by linarith [ge.1])
  have hvg : v/m*g ≤ 2*e := by
    rw [div_mul_eq_mul_div, mul_div_assoc]
    have hve' : v*2 ≤ 2*e := by linarith only [hve]
    exact (mul_le_mul_of_nonneg_left hgquot hv0).trans hve'
  have hmg : m*g ≤ u :=
    (mul_le_mul_of_nonneg_right ge.2 hg0.le).trans (by rw [← pow_two]; exact hsquare)
  have hmul := mul_le_mul_of_nonneg_right hcount hg0.le
  have hcorr := mul_le_mul_of_nonneg_left hvg (show 0 ≤ 5*u by positivity)
  have hus : u ≤ u*e := by simpa using mul_le_mul_of_nonneg_left heg hu.le
  have hlead : s*g ≤ 5*u*g+20*u*e := by nlinarith only [hmul, hcorr, hmg, hus]
  have htail := mul_le_mul_of_nonneg_right hcoarse
    (mul_nonneg hA (show 0 ≤ e by linarith))
  nlinarith only [hlead, htail, mul_nonneg hu.le (show 0 ≤ e by linarith)]

end

end TranslationTiling.Compiler.Size
