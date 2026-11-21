import TranslationTiling.Compiler.GuardedVolumeBound

namespace TranslationTiling.Compiler.Size

noncomputable section

set_option exponentiation.threshold 20000
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000

/-- The size bound for the guarded reduction with residue-class prime selection. -/
def residueBound (n : ℕ) : ℝ :=
  max (((n : ℝ) + 4) ^ (10 * Real.logb 2 (Real.logb 2 ((n : ℝ) + 4)) +
    19 * Real.logb 2 (Real.logb 2 (Real.logb 2 ((n : ℝ) + 4))) + 557))
    ((2 : ℝ) ^ (2392 : ℕ))

theorem residue_bound_log {n N : ℕ} (hN : 0 < N)
    (h : let t := Real.logb 2 ((n : ℝ) + 4)
         let g := Real.logb 2 t
         Real.logb 2 N ≤ t * (10*g + 19*Real.logb 2 g + 557)) :
    (N : ℝ) ≤ residueBound n := by
  apply le_trans _ (le_max_left _ _)
  apply (Real.logb_le_logb (by norm_num : (1 : ℝ) < 2)
    (by exact_mod_cast hN) (by positivity)).mp
  rwa [Real.logb_rpow_eq_mul_logb_of_pos (by positivity), mul_comm]

theorem residue_bound_dyadic {n e a b c d u v : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (hv : 0 < v)
    (ht : (2 : ℝ)^a ≤ ((n : ℝ)+4)^b)
    (hg : (2 : ℝ)^c ≤ ((a : ℝ)/b)^d)
    (hl : (2 : ℝ)^u ≤ ((c : ℝ)/d)^v)
    (he : (e : ℝ) ≤ ((a : ℝ)/b) * (10*((c : ℝ)/d)+19*((u : ℝ)/v)+557)) :
    ((2^e : ℕ) : ℝ) ≤ residueBound n := by
  have ht' := lg_lower hb ht (by positivity)
  have hg' := (lg_lower hd hg (by positivity)).trans (lg_mono (by positivity) ht')
  have hl' := (lg_lower hv hl (by positivity)).trans (lg_mono (by positivity) hg')
  apply residue_bound_log (by positivity)
  rw [Nat.cast_pow,Nat.cast_ofNat,lg_two_pow]
  exact he.trans (mul_le_mul ht' (by linarith) (by positivity) (le_trans (by positivity) ht'))

def residueDigits (n : ℕ) : ℕ := Nat.log 4 (n-1)+1

theorem residueDigits_pos (n : ℕ) : 0 < residueDigits n := by unfold residueDigits; omega

theorem residueDigits_capacity (n : ℕ) : n ≤ 4^residueDigits n := by
  have h := Nat.lt_pow_succ_log_self (by decide : 1 < 4) (n-1)
  unfold residueDigits
  omega

theorem residueDigits_capacity_le {n : ℕ} (hn : 1 < n) : 4^residueDigits n ≤ 4*n := by
  unfold residueDigits
  rw [pow_succ]
  exact (Nat.mul_le_mul_right 4 (Nat.pow_log_le_self 4 (by omega : n-1 ≠ 0))).trans (by omega)

theorem residueDigits_log {n : ℕ} (hn : 1 < n) :
    (residueDigits n : ℝ) ≤ Real.logb 2 ((n : ℝ)+4)/2+1 := by
  have hpow : (2 : ℝ)^(2*Nat.log 4 (n-1)) ≤ (n : ℝ)+4 := by
    rw [pow_mul,show (2 : ℝ)^2 = 4 by norm_num]
    exact_mod_cast (Nat.pow_log_le_self 4 (by omega : n-1 ≠ 0)).trans
      (by omega : n-1 ≤ n+4)
  have h := lg_mono (by positivity) hpow
  rw [lg_two_pow] at h
  unfold residueDigits
  push_cast at ⊢ h
  linarith

def residueUsefulCap (k : ℕ) := guardedPrimeCap (2*k+134)
def residuePrimeCap (k : ℕ) := guardedPrimeCap (4*residueUsefulCap k+12*k+134)
def residueTests (n : ℕ) := 2048*(n+4)^2
def residueRadius (k : ℕ) := 2^70+2*(residuePrimeCap k)^5*residueUsefulCap k

private theorem primeCap_log {m : ℕ} {z h : ℝ} (hm : 0 < m) (hz : 0 < z) (hh : 0 ≤ h)
    (h₁ : (m : ℝ) ≤ z) (h₂ : Real.logb 2 z + 1 ≤ h) :
    (guardedPrimeCap m : ℝ) ≤ 4*z*h := by
  have hl := (lg_natLog_le hm).trans (lg_mono (by exact_mod_cast hm) h₁)
  unfold guardedPrimeCap
  push_cast
  have hp := mul_le_mul h₁ (show (Nat.log 2 m : ℝ)+1 ≤ h by linarith) (by positivity) hz.le
  linarith

private theorem residue_prime_logs {n : ℕ} (hn : 3^21 < n) :
    let t := Real.logb 2 ((n : ℝ)+4)
    let g := Real.logb 2 t
    let l := Real.logb 2 g
    let k := residueDigits n
    Real.logb 2 (residueUsefulCap k) ≤ g+l+6 ∧
    Real.logb 2 (residuePrimeCap k) ≤ g+2*l+13 := by
  let t := Real.logb 2 ((n : ℝ)+4)
  let g := Real.logb 2 t
  let l := Real.logb 2 g
  let k := residueDigits n
  let m := 2*k+134
  let x := residueUsefulCap k
  let M := 4*x+12*k+134
  let P := residuePrimeCap k
  change Real.logb 2 x ≤ g+l+6 ∧ Real.logb 2 P ≤ g+2*l+13
  have ht : 32 ≤ t := guarded_t_lower hn
  have hg : 5 ≤ g := guarded_g_lower ht
  have hl : l ≤ g/2 := by
    have h := lg_ratio (t := g) (b := 2) (by decide) (by norm_num; linarith)
    norm_num at h
    change Real.logb 2 g ≤ g/2
    linarith
  have hk : (k : ℝ) ≤ t/2+1 := residueDigits_log (by omega)
  have hm : (m : ℝ) ≤ 8*t := by
    dsimp [m]
    push_cast
    linarith
  have hx : 0 < x := by unfold x residueUsefulCap guardedPrimeCap; positivity
  have hP : 0 < P := by unfold P residuePrimeCap guardedPrimeCap; positivity
  have hxle : (x : ℝ) ≤ 64*t*g := by
    have h := primeCap_log (m := m) (z := 8*t) (h := 2*g)
      (by dsimp [m]; omega) (by positivity) (by linarith) hm (by
        rw [show (8:ℝ)=2^3 by norm_num,Real.logb_mul (by positivity) (by linarith : t ≠ 0),lg_two_pow]
        change 3+g+1 ≤ 2*g
        linarith)
    change (x : ℝ) ≤ _ at h
    linarith
  have hM : (M : ℝ) ≤ 512*t*g := by
    dsimp [M]
    push_cast
    nlinarith only [hxle,hk,ht,hg,mul_nonneg (show 0 ≤ t by linarith) (show 0 ≤ g-1 by linarith)]
  have hMlog : Real.logb 2 (512*t*g) + 1 ≤ (7/2)*g := by
    rw [show (512:ℝ)=2^9 by norm_num,
      Real.logb_mul (by positivity) (by linarith : g ≠ 0),
      Real.logb_mul (by positivity) (by linarith : t ≠ 0),lg_two_pow]
    change 9+g+l+1 ≤ (7/2)*g
    linarith
  have hPle : (P : ℝ) ≤ 8192*t*g^2 := by
    have h := primeCap_log (m := M) (z := 512*t*g) (h := (7/2)*g)
      (by dsimp [M]; omega) (by positivity) (by linarith) hM hMlog
    change (P : ℝ) ≤ _ at h
    nlinarith only [h,sq_nonneg g,mul_nonneg (show 0 ≤ t by linarith) (sq_nonneg g)]
  have hxl := lg_mono (by exact_mod_cast hx) hxle
  have hPl := lg_mono (by exact_mod_cast hP) hPle
  rw [show (64:ℝ)=2^6 by norm_num,Real.logb_mul (by positivity) (by linarith : g ≠ 0),
    Real.logb_mul (by positivity) (by linarith : t ≠ 0),lg_two_pow] at hxl
  rw [show (8192:ℝ)=2^13 by norm_num,Real.logb_mul (by positivity) (by positivity),
    Real.logb_mul (by positivity) (by linarith : t ≠ 0),lg_two_pow,Real.logb_pow] at hPl
  exact ⟨by change _ ≤ g+l+6; change _ ≤ 6+g+l at hxl; linarith,
    by change _ ≤ g+2*l+13; change _ ≤ 13+g+2*l at hPl; linarith⟩


open FiniteCompiler.Effective Compiler.StripLift Rails.Strips

theorem residue_stack_budget {n : ℕ} (hn : 3^21 < n) :
    residuePrimeCap (residueDigits n)+3 ≤ (n+4)^2 := by
  let t := Real.logb 2 ((n : ℝ)+4)
  let g := Real.logb 2 t
  let l := Real.logb 2 g
  let P := residuePrimeCap (residueDigits n)
  have ht : 32 ≤ t := guarded_t_lower hn
  have hg : 5 ≤ g := guarded_g_lower ht
  have hl : l ≤ g/2 := by
    have h := lg_ratio (t := g) (b := 2) (by decide) (by norm_num; linarith)
    norm_num at h
    change Real.logb 2 g ≤ g/2
    linarith
  have hgt : g ≤ 5*(t/32) := by
    have h := lg_ratio (t := t) (b := 5) (by decide) (by norm_num; exact ht)
    norm_num at h
    exact h
  have hP : 3 ≤ P := by
    unfold P residuePrimeCap guardedPrimeCap
    let m := 4*residueUsefulCap (residueDigits n)+12*residueDigits n+134
    have hm : 134 ≤ m := by dsimp [m]; omega
    change 3 ≤ 4*m*(Nat.log 2 m+1)
    exact (show 3 ≤ 4*m by omega).trans (Nat.le_mul_of_pos_right _ (by omega))
  have h := (residue_prime_logs hn).2
  change Real.logb 2 P ≤ g+2*l+13 at h
  have hlog : Real.logb 2 ((2:ℝ)*P) ≤ Real.logb 2 (((n : ℝ)+4)^2) := by
    rw [Real.logb_mul (by norm_num) (by exact_mod_cast (by omega : P ≠ 0)),
      Real.logb_self_eq_one (by norm_num),Real.logb_pow]
    change 1+Real.logb 2 P ≤ 2*t
    linarith
  have he := (Real.logb_le_logb (by norm_num : (1 : ℝ)<2)
    (by exact_mod_cast (show 0 < 2*P by omega)) (by positivity)).mp hlog
  have he' : 2*P ≤ (n+4)^2 := by exact_mod_cast he
  omega

private theorem residue_slots_le (k : ℕ)
    (hx : 0 < residueUsefulCap k) (hP : 0 < residuePrimeCap k) :
    countCapAt 35 (fun _ => residueRadius k) ≤
      2^100 * (residuePrimeCap k)^5 * residueUsefulCap k := by
  let H := residueRadius k
  let Z := (residuePrimeCap k)^5 * residueUsefulCap k
  have hZ : 1 ≤ Z := Nat.mul_pos (pow_pos hP _) hx
  have hH : 1 ≤ H := by unfold H residueRadius; omega
  have hr : 2*radius H+1 ≤ 1333*H := by unfold radius; omega
  have hc : ((List.range 17).map (fun s => 2*widthAt 35 s+1)).sum ≤ 400000 := by decide
  have hH' : H ≤ 2^71*Z := by
    unfold H residueRadius
    rw [Nat.mul_assoc]
    change 2^70+2*Z ≤ 2^71*Z
    calc
      _ ≤ 2^70*Z+2*Z := Nat.add_le_add_right (Nat.le_mul_of_pos_right _ hZ) _
      _ = (2^70+2)*Z := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ (by decide)
  calc
    _ = (2*radius H+1)*((List.range 17).map (fun s => 2*widthAt 35 s+1)).sum := by
      unfold countCapAt
      exact List.sum_map_mul_left (l := List.range 17) (f := fun s => 2*widthAt 35 s+1) (r := 2*radius H+1)
    _ ≤ (1333*400000)*H := by
      calc
        _ ≤ (1333*H)*400000 := Nat.mul_le_mul hr hc
        _ = _ := by ac_rfl
    _ ≤ 2^29*H := Nat.mul_le_mul_right _ (by decide)
    _ ≤ 2^100*(residuePrimeCap k)^5*residueUsefulCap k := by
      calc
        _ ≤ 2^29*(2^71*Z) := Nat.mul_le_mul_left _ hH'
        _ = _ := by unfold Z; ring

theorem residue_volume_bound {n R J : ℕ} (hn : 3^21 < n) (hR : 0 < R)
    (hRJ : R*J ≤ 2^1878 * (residuePrimeCap (residueDigits n))^(18*residueDigits n) *
      (residueUsefulCap (residueDigits n))^(2*residueDigits n)) :
    (↑(reservedVolumeCap 35 (fun _ => residueRadius (residueDigits n)) R J
      (reservedCap (residueTests n) (residuePrimeCap (residueDigits n)))) : ℝ) ≤ residueBound n := by
  let k := residueDigits n
  let x := residueUsefulCap k
  let P := residuePrimeCap k
  let X := residueTests n
  let L := reservedCap X P
  let A := 2^100*P^5*x
  let N := 2^49*(2^1878*P^(18*k)*x^(2*k))*L*A^2
  let t := Real.logb 2 ((n : ℝ)+4)
  let g := Real.logb 2 t
  let l := Real.logb 2 g
  have ht : 32 ≤ t := guarded_t_lower hn
  have hg : 5 ≤ g := guarded_g_lower ht
  have hl : l ≤ g/2 := by
    have h := lg_ratio (t := g) (b := 2) (by decide) (by norm_num; linarith)
    norm_num at h
    change Real.logb 2 g ≤ g/2
    linarith
  have hg' : g ≤ 5*(t/32) := by
    have h := lg_ratio (t := t) (b := 5) (by decide) (by norm_num; exact ht)
    norm_num at h
    exact h
  have hl0 : 0 ≤ l := Real.logb_nonneg (by norm_num) (by linarith)
  have hk : (k : ℝ) ≤ t/2+1 := residueDigits_log (by omega)
  have hx : 0 < x := by unfold x residueUsefulCap guardedPrimeCap; positivity
  have hP : 0 < P := by unfold P residuePrimeCap guardedPrimeCap; positivity
  have hL : 0 < L := by unfold L reservedCap reservedThreshold; positivity
  have hA : 0 < A := by unfold A; positivity
  have hN : 0 < N := by unfold N; positivity
  let a₀ := countCapAt 35 (fun _ => residueRadius k)
  have ha₀ : 0 < a₀ := by
    unfold a₀ countCapAt
    rw [List.sum_map_mul_left]
    exact Nat.mul_pos (by positivity) (by decide)
  have ha : a₀ ≤ A := residue_slots_le k hx hP
  have hV : reservedVolumeCap 35 (fun _ => residueRadius k) R J L ≤ N := by
    have hh : 2^49*(R*J)*L ≤ 2^49*(2^1878*P^(18*k)*x^(2*k))*L :=
      Nat.mul_le_mul_right L (Nat.mul_le_mul_left (2^49) hRJ)
    exact (guarded_shell_bound (J := J) (L := L) hR ha₀).trans
      (Nat.mul_le_mul hh (Nat.pow_le_pow_left ha 2))
  refine (show (↑(reservedVolumeCap 35 (fun _ => residueRadius k) R J L) : ℝ) ≤ N by
    exact_mod_cast hV).trans (residue_bound_log hN ?_)
  have hXeq : (X : ℝ) = (2 : ℝ)^11 * ((n : ℝ)+4)^2 := by unfold X residueTests; push_cast; norm_num
  have hXlog : Real.logb 2 X = 11+2*t := by
    rw [hXeq, Real.logb_mul (by positivity) (by positivity), lg_two_pow, Real.logb_pow]
    norm_num [t]
  have hX : 0 < X := by unfold X residueTests; positivity
  have hdiff : (Stacking.differenceLog X : ℝ) ≤ 3*t := by
    have h := lg_natLog_le (show 0 < 2*X by positivity)
    push_cast at h
    rw [Real.logb_mul (by norm_num : (2:ℝ) ≠ 0) (by positivity),
      Real.logb_self_eq_one (by norm_num), hXlog] at h
    unfold Stacking.differenceLog
    push_cast
    linarith
  have hcap : (L : ℝ) ≤ (2 : ℝ)^7 * (t*(X : ℝ)^2) := by
    have hb : (P : ℝ)+3 ≤ 2*(X : ℝ)^2 := by
      have he := residue_stack_budget hn
      have hx' : (n+4)^2 ≤ X := by unfold X residueTests; omega
      have hh : P+3 ≤ 2*X^2 := he.trans (hx'.trans (by nlinarith only [hX]))
      exact_mod_cast hh
    have hd := mul_le_mul_of_nonneg_right hdiff (show 0 ≤ (X : ℝ)^2 by positivity)
    have ht' := mul_le_mul_of_nonneg_right ht (show 0 ≤ (X : ℝ)^2 by positivity)
    unfold L reservedCap reservedThreshold
    push_cast
    nlinarith only [hb,hd,ht']
  have hLl := lg_mono (by exact_mod_cast hL) hcap
  rw [Real.logb_mul (by positivity) (by positivity),lg_two_pow,
    Real.logb_mul (by positivity) (by positivity),Real.logb_pow,hXlog] at hLl
  have hx' : 0 < (x : ℝ) := by exact_mod_cast hx
  have hP' : 0 < (P : ℝ) := by exact_mod_cast hP
  have hL' : 0 < (L : ℝ) := by exact_mod_cast hL
  have hAl : Real.logb 2 A = 100+5*Real.logb 2 P+Real.logb 2 x := by
    dsimp only [A]
    simp only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
    rw [Real.logb_mul (by positivity) hx'.ne',Real.logb_mul (by positivity) (by positivity),
      lg_two_pow,Real.logb_pow]
    norm_num
  have hNl : Real.logb 2 N =
      2127 + Real.logb 2 L + (18*(k : ℝ)+10)*Real.logb 2 P +
      (2*(k : ℝ)+2)*Real.logb 2 x := by
    dsimp only [N]
    simp only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
    rw [Real.logb_mul (by positivity) (by positivity),Real.logb_pow,hAl,
      Real.logb_mul (by positivity) hL'.ne',Real.logb_mul (by positivity) (by positivity),
      lg_two_pow,Real.logb_mul (by positivity) (by positivity),
      Real.logb_mul (by positivity) (by positivity),lg_two_pow,Real.logb_pow,Real.logb_pow]
    push_cast
    ring
  obtain ⟨hxlog,hPlog⟩ := residue_prime_logs hn
  change Real.logb 2 x ≤ g+l+6 at hxlog
  change Real.logb 2 P ≤ g+2*l+13 at hPlog
  have hhx := mul_le_mul_of_nonneg_left hxlog (show 0 ≤ 2*(k : ℝ)+2 by positivity)
  have hhP := mul_le_mul_of_nonneg_left hPlog (show 0 ≤ 18*(k : ℝ)+10 by positivity)
  have hmx := mul_le_mul_of_nonneg_right (show 2*(k : ℝ)+2 ≤ t+4 by linarith) (show 0 ≤ g+l+6 by linarith)
  have hmP := mul_le_mul_of_nonneg_right (show 18*(k : ℝ)+10 ≤ 9*t+28 by linarith) (show 0 ≤ g+2*l+13 by linarith)
  have hLlog : Real.logb 2 L ≤ 29+4*t+g := by
    change _ ≤ 7 + (g + (2:ℝ)*(11+2*t)) at hLl
    linarith
  have hmain : Real.logb 2 N ≤ t*(10*g+19*l+127)+2544+33*g+60*l := by
    linarith only [hNl,hLlog,hhx,hhP,hmx,hmP]
  have hrest : 2544+33*g+60*l ≤ 100*t := by linarith only [ht,hl,hg']
  change Real.logb 2 N ≤ t*(10*g+19*l+557)
  nlinarith only [hmain,hrest,ht]

end
end TranslationTiling.Compiler.Size
