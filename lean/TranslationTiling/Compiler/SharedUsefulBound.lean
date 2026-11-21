import TranslationTiling.Compiler.GuardedFiniteBound

namespace TranslationTiling.Compiler.Size

noncomputable section

set_option exponentiation.threshold 20000
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000

/-- The size bound for the guarded reduction with shared useful primes. -/
def sharedUsefulBound (n : ℕ) : ℝ :=
  max (((n : ℝ) + 4) ^ ((441651/50000 : ℝ) * (Real.logb 2 (Real.logb 2 ((n : ℝ) + 4)) +
    Real.logb 2 (Real.logb 2 (Real.logb 2 ((n : ℝ) + 4)))) + 570))
    ((2 : ℝ) ^ (2392 : ℕ))

theorem shared_useful_bound_log {n N : ℕ} (hN : 0 < N)
    (h : let t := Real.logb 2 ((n : ℝ) + 4)
         let g := Real.logb 2 t
         Real.logb 2 N ≤ t * ((441651/50000 : ℝ)*(g + Real.logb 2 g) + 570)) :
    (N : ℝ) ≤ sharedUsefulBound n := by
  apply le_trans _ (le_max_left _ _)
  apply (Real.logb_le_logb (by norm_num : (1 : ℝ) < 2)
    (by exact_mod_cast hN) (by positivity)).mp
  rwa [Real.logb_rpow_eq_mul_logb_of_pos (by positivity), mul_comm]

theorem shared_useful_bound_dyadic {n e a b c d u v : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (hv : 0 < v)
    (ht : (2 : ℝ)^a ≤ ((n : ℝ)+4)^b)
    (hg : (2 : ℝ)^c ≤ ((a : ℝ)/b)^d)
    (hl : (2 : ℝ)^u ≤ ((c : ℝ)/d)^v)
    (he : (e : ℝ) ≤ ((a : ℝ)/b) * ((441651/50000 : ℝ)*((c : ℝ)/d + (u : ℝ)/v)+570)) :
    ((2^e : ℕ) : ℝ) ≤ sharedUsefulBound n := by
  have ht' := lg_lower hb ht (by positivity)
  have hg' := (lg_lower hd hg (by positivity)).trans (lg_mono (by positivity) ht')
  have hl' := (lg_lower hv hl (by positivity)).trans (lg_mono (by positivity) hg')
  apply shared_useful_bound_log (by positivity)
  rw [Nat.cast_pow,Nat.cast_ofNat,lg_two_pow]
  exact he.trans (mul_le_mul ht' (by linarith) (by positivity) (le_trans (by positivity) ht'))

theorem shared_coefficient : 14 / Real.logb 2 3 ≤ (441651/50000 : ℝ) := by
  have h : (1054 : ℝ)/665 ≤ Real.logb 2 3 := by
    apply lg_lower (a := 1054) (b := 665) (by decide) _ (by norm_num)
    exact_mod_cast (by decide : (2:ℕ)^1054 ≤ 3^665)
  apply (div_le_iff₀ (by linarith)).mpr
  linarith

def sharedPairCap (k : ℕ) : ℕ := guardedPrimeCap (2*k+136)
def sharedPrimeCap (k : ℕ) : ℕ := 1600*sharedPairCap k
def sharedRadius (k : ℕ) : ℕ := 2^70+400*(sharedPrimeCap k)^3*sharedPairCap k

private theorem primeCap_log {m : ℕ} {z h : ℝ} (hm : 0 < m) (hz : 0 < z) (_hh : 0 ≤ h)
    (h₁ : (m : ℝ) ≤ z) (h₂ : Real.logb 2 z + 1 ≤ h) :
    (guardedPrimeCap m : ℝ) ≤ 4*z*h := by
  have hl := (lg_natLog_le hm).trans (lg_mono (by exact_mod_cast hm) h₁)
  unfold guardedPrimeCap
  push_cast
  have hp := mul_le_mul h₁ (show (Nat.log 2 m : ℝ)+1 ≤ h by linarith) (by positivity) hz.le
  linarith

private theorem shared_prime_logs {n : ℕ} (hn : 3^21 < n) :
    let t := Real.logb 2 ((n : ℝ)+4)
    let g := Real.logb 2 t
    let l := Real.logb 2 g
    let k := guardedTrits n
    Real.logb 2 (sharedPairCap k) ≤ g+l+6 ∧
    Real.logb 2 (sharedPrimeCap k) ≤ g+l+17 := by
  let t := Real.logb 2 ((n : ℝ)+4)
  let g := Real.logb 2 t
  let l := Real.logb 2 g
  let k := guardedTrits n
  let m := 2*k+136
  let x := sharedPairCap k
  let P := sharedPrimeCap k
  change Real.logb 2 x ≤ g+l+6 ∧ Real.logb 2 P ≤ g+l+17
  have ht : 32 ≤ t := guarded_t_lower hn
  have hg : 5 ≤ g := guarded_g_lower ht
  have hk : (k : ℝ) ≤ (359/569 : ℝ)*t+1 := guardedTrits_log (by omega)
  have hm : (m : ℝ) ≤ 8*t := by
    dsimp [m]
    push_cast
    linarith
  have hx : 0 < x := by unfold x sharedPairCap guardedPrimeCap; positivity
  have hxle : (x : ℝ) ≤ 64*t*g := by
    have h := primeCap_log (m := m) (z := 8*t) (h := 2*g)
      (by dsimp [m]; omega) (by positivity) (by linarith) hm (by
        rw [show (8:ℝ)=2^3 by norm_num,Real.logb_mul (by positivity) (by linarith : t ≠ 0),lg_two_pow]
        change 3+g+1 ≤ 2*g
        linarith)
    change (x : ℝ) ≤ _ at h
    linarith
  have hxl := lg_mono (by exact_mod_cast hx) hxle
  rw [show (64:ℝ)=2^6 by norm_num,Real.logb_mul (by positivity) (by linarith : g ≠ 0),
    Real.logb_mul (by positivity) (by linarith : t ≠ 0),lg_two_pow] at hxl
  change _ ≤ 6+g+l at hxl
  have hP' : (P : ℝ) ≤ 2^11 * (x : ℝ) := by unfold P sharedPrimeCap; push_cast; nlinarith
  have hp : 0 < P := by unfold P sharedPrimeCap; positivity
  have h := lg_mono (by exact_mod_cast hp) hP'
  rw [Real.logb_mul (by positivity) (by exact_mod_cast hx.ne'),lg_two_pow] at h
  norm_num at h
  exact ⟨by linarith,by linarith⟩

private theorem sharedTrits_log {n : ℕ} (hn : 1 < n) :
    (guardedTrits n : ℝ) ≤ Real.logb 2 ((n : ℝ)+4) / Real.logb 2 3 + 1 := by
  have hp : (3 : ℝ)^Nat.log 3 (n-1) ≤ (n : ℝ)+4 := by
    exact_mod_cast (Nat.pow_log_le_self 3 (by omega : n-1 ≠ 0)).trans
      (by omega : n-1 ≤ n+4)
  have h := lg_mono (by positivity) hp
  rw [Real.logb_pow] at h
  have hb : 0 < Real.logb 2 3 := Real.logb_pos (by norm_num) (by norm_num)
  have h' := (le_div_iff₀ hb).mpr h
  unfold guardedTrits
  push_cast
  linarith

open FiniteCompiler.Effective Compiler.StripLift Rails.Strips

theorem shared_stack_budget {n : ℕ} (hn : 3^21 < n) :
    sharedPrimeCap (guardedTrits n)+3 ≤ (n+4)^2 := by
  let t := Real.logb 2 ((n : ℝ)+4)
  let g := Real.logb 2 t
  let l := Real.logb 2 g
  let P := sharedPrimeCap (guardedTrits n)
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
    have hx : 0 < sharedPairCap (guardedTrits n) := by unfold sharedPairCap guardedPrimeCap; positivity
    unfold P sharedPrimeCap
    omega
  have h := (shared_prime_logs hn).2
  change Real.logb 2 P ≤ g+l+17 at h
  have hlog : Real.logb 2 ((2:ℝ)*P) ≤ Real.logb 2 (((n : ℝ)+4)^2) := by
    rw [Real.logb_mul (by norm_num) (by exact_mod_cast (by omega : P ≠ 0)),
      Real.logb_self_eq_one (by norm_num),Real.logb_pow]
    change 1+Real.logb 2 P ≤ 2*t
    linarith
  have he := (Real.logb_le_logb (by norm_num : (1 : ℝ)<2)
    (by exact_mod_cast (show 0 < 2*P by omega)) (by positivity)).mp hlog
  have he' : 2*P ≤ (n+4)^2 := by exact_mod_cast he
  omega

private theorem shared_slots_le (k : ℕ)
    (hx : 0 < sharedPairCap k) (hP : 0 < sharedPrimeCap k) :
    countCapAt 35 (fun _ => sharedRadius k) ≤
      2^100 * (sharedPrimeCap k)^3 * sharedPairCap k := by
  let H := sharedRadius k
  let Z := (sharedPrimeCap k)^3 * sharedPairCap k
  have hZ : 1 ≤ Z := Nat.mul_pos (pow_pos hP _) hx
  have hH : 1 ≤ H := by unfold H sharedRadius; omega
  have hr : 2*radius H+1 ≤ 1333*H := by unfold radius; omega
  have hc : ((List.range 17).map (fun s => 2*widthAt 35 s+1)).sum ≤ 400000 := by decide
  have hH' : H ≤ 2^71*Z := by
    unfold H sharedRadius
    rw [Nat.mul_assoc]
    change 2^70+400*Z ≤ 2^71*Z
    calc
      _ ≤ 2^70*Z+400*Z := Nat.add_le_add_right (Nat.le_mul_of_pos_right _ hZ) _
      _ = (2^70+400)*Z := by ring
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
    _ ≤ 2^100*(sharedPrimeCap k)^3*sharedPairCap k := by
      calc
        _ ≤ 2^29*(2^71*Z) := Nat.mul_le_mul_left _ hH'
        _ = _ := by unfold Z; ring

theorem shared_volume_bound {n R J : ℕ} (hn : 3^21 < n) (hR : 0 < R)
    (hRJ : R*J ≤ 2^1893 * (sharedPrimeCap (guardedTrits n))^(12*guardedTrits n) *
      (sharedPairCap (guardedTrits n))^(2*guardedTrits n)) :
    (↑(reservedVolumeCap 35 (fun _ => sharedRadius (guardedTrits n)) R J
      (reservedCap (residueTests n) (sharedPrimeCap (guardedTrits n)))) : ℝ) ≤ sharedUsefulBound n := by
  let k := guardedTrits n
  let x := sharedPairCap k
  let P := sharedPrimeCap k
  let X := residueTests n
  let L := reservedCap X P
  let A := 2^100*P^3*x
  let N := 2^49*(2^1893*P^(12*k)*x^(2*k))*L*A^2
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
  let q := Real.logb 2 3
  have hq : (19/12 : ℝ) ≤ q := by
    apply lg_lower (a := 19) (b := 12) (by decide) _ (by norm_num)
    norm_num
  have hq' : 0 < q := by linarith
  have hk : (k : ℝ) ≤ t/q+1 := sharedTrits_log (by omega)
  have hx : 0 < x := by unfold x sharedPairCap guardedPrimeCap; positivity
  have hP : 0 < P := by unfold P sharedPrimeCap sharedPairCap guardedPrimeCap; positivity
  have hL : 0 < L := by unfold L reservedCap reservedThreshold; positivity
  have hA : 0 < A := by unfold A; positivity
  have hN : 0 < N := by unfold N; positivity
  let a₀ := countCapAt 35 (fun _ => sharedRadius k)
  have ha₀ : 0 < a₀ := by
    unfold a₀ countCapAt
    rw [List.sum_map_mul_left]
    exact Nat.mul_pos (by positivity) (by decide)
  have ha : a₀ ≤ A := shared_slots_le k hx hP
  have hV : reservedVolumeCap 35 (fun _ => sharedRadius k) R J L ≤ N := by
    have hh : 2^49*(R*J)*L ≤ 2^49*(2^1893*P^(12*k)*x^(2*k))*L :=
      Nat.mul_le_mul_right L (Nat.mul_le_mul_left (2^49) hRJ)
    exact (guarded_shell_bound (J := J) (L := L) hR ha₀).trans
      (Nat.mul_le_mul hh (Nat.pow_le_pow_left ha 2))
  refine (show (↑(reservedVolumeCap 35 (fun _ => sharedRadius k) R J L) : ℝ) ≤ N by
    exact_mod_cast hV).trans (shared_useful_bound_log hN ?_)
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
      have he := shared_stack_budget hn
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
  have hAl : Real.logb 2 A = 100+3*Real.logb 2 P+Real.logb 2 x := by
    dsimp only [A]
    simp only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
    rw [Real.logb_mul (by positivity) hx'.ne',Real.logb_mul (by positivity) (by positivity),
      lg_two_pow,Real.logb_pow]
    norm_num
  have hNl : Real.logb 2 N =
      2142 + Real.logb 2 L + (12*(k : ℝ)+6)*Real.logb 2 P +
      (2*(k : ℝ)+2)*Real.logb 2 x := by
    dsimp only [N]
    simp only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
    rw [Real.logb_mul (by positivity) (by positivity),Real.logb_pow,hAl,
      Real.logb_mul (by positivity) hL'.ne',Real.logb_mul (by positivity) (by positivity),
      lg_two_pow,Real.logb_mul (by positivity) (by positivity),
      Real.logb_mul (by positivity) (by positivity),lg_two_pow,Real.logb_pow,Real.logb_pow]
    push_cast
    ring
  obtain ⟨hxlog,hPlog⟩ := shared_prime_logs hn
  change Real.logb 2 x ≤ g+l+6 at hxlog
  change Real.logb 2 P ≤ g+l+17 at hPlog
  have hhx := mul_le_mul_of_nonneg_left hxlog (show 0 ≤ 2*(k : ℝ)+2 by positivity)
  have hhP := mul_le_mul_of_nonneg_left hPlog (show 0 ≤ 12*(k : ℝ)+6 by positivity)
  have hmx := mul_le_mul_of_nonneg_right (show 2*(k : ℝ)+2 ≤ 2*(t/q)+4 by linarith) (show 0 ≤ g+l+6 by linarith)
  have hmP := mul_le_mul_of_nonneg_right (show 12*(k : ℝ)+6 ≤ 12*(t/q)+18 by linarith) (show 0 ≤ g+l+17 by linarith)
  have hLlog : Real.logb 2 L ≤ 29+4*t+g := by
    change _ ≤ 7 + (g + (2:ℝ)*(11+2*t)) at hLl
    linarith
  have hmain : Real.logb 2 N ≤
      (t/q)*(14*(g+l)+216)+4*t+2501+23*g+22*l := by
    linarith only [hNl,hLlog,hhx,hhP,hmx,hmP]
  have hrest : 2501+23*g+22*l ≤ (2671/32)*t := by linarith only [ht,hl,hg']
  have hq₂ : 216/q ≤ (2592/19 : ℝ) := by
    apply (div_le_iff₀ hq').mpr
    linarith
  have hq₃ : 14/q ≤ (441651/50000 : ℝ) := shared_coefficient
  have hC := mul_le_mul_of_nonneg_right hq₃ (show 0 ≤ g+l by linarith)
  have hE := mul_le_mul_of_nonneg_right hq₂ (show 0 ≤ t by linarith)
  have he := mul_le_mul_of_nonneg_right hC (show 0 ≤ t by linarith)
  have hsplit : (t/q)*(14*(g+l)+216) = t*((14/q)*(g+l))+(216/q)*t := by ring
  change Real.logb 2 N ≤ t*((441651/50000 : ℝ)*(g+l)+570)
  rw [hsplit] at hmain
  nlinarith only [hmain,hrest,hE,he,ht]

open FiniteCompiler.Packed

theorem guarded_profile_shared_bound (n : ℕ) :
    ((2^(guardedProfile (max 1 n)).exponent : ℕ) : ℝ) ≤ sharedUsefulBound n := by
  have hbudget (d : ℕ) (hd : d ≤ 2392) : ((2^d : ℕ) : ℝ) ≤ sharedUsefulBound n := by
    apply le_trans _ (le_max_right _ _)
    push_cast
    exact pow_le_pow_right₀ (by norm_num) hd
  have hlog (m a b : ℕ) (hm : m ≤ n) (h : (2 : ℝ)^a ≤ ((m : ℝ)+4)^b) :
      (2 : ℝ)^a ≤ ((n : ℝ)+4)^b := by
    exact h.trans (pow_le_pow_left₀ (by positivity) (by exact_mod_cast (Nat.add_le_add_right hm 4)) b)
  unfold guardedProfile
  split_ifs with h1 h12 h15 h36 h243 h19683
  · exact hbudget 2112 (by decide)
  · exact hbudget 2392 (by decide)
  · exact shared_useful_bound_dyadic (a:=94) (b:=23) (c:=67) (d:=33) (u:=51) (v:=50)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (hlog 13 94 23 (by omega) (by norm_num)) (by norm_num) (by norm_num)
      (by change (2438 : ℝ) ≤ _; norm_num)
  · exact shared_useful_bound_dyadic (a:=69) (b:=16) (c:=21) (d:=10) (u:=21) (v:=20)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (hlog 16 69 16 (by omega) (by norm_num)) (by norm_num) (by norm_num)
      (by change (2573 : ℝ) ≤ _; norm_num)
  · exact shared_useful_bound_dyadic (a:=5) (b:=1) (c:=2) (d:=1) (u:=1) (v:=1)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (hlog 37 5 1 (by omega) (by norm_num)) (by norm_num) (by norm_num)
      (by change (2876 : ℝ) ≤ _; norm_num)
  · exact shared_useful_bound_dyadic (a:=7) (b:=1) (c:=2) (d:=1) (u:=1) (v:=1)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (hlog 243 7 1 (by omega) (by norm_num)) (by norm_num) (by norm_num)
      (by change (3594 : ℝ) ≤ _; norm_num)
  · exact shared_useful_bound_dyadic (a:=14) (b:=1) (c:=3) (d:=1) (u:=1) (v:=1)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (hlog 19684 14 1 (by omega) (by norm_num)) (by norm_num) (by norm_num)
      (by change (5954 : ℝ) ≤ _; norm_num)

end
end TranslationTiling.Compiler.Size
