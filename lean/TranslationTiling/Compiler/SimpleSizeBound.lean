import TranslationTiling.Compiler.ClosedFormBound

set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

namespace TranslationTiling.Compiler.Size

open LeanWang
noncomputable section

private theorem exp_mono {a b : ℕ} (h : a ≤ b) : 2 ^ a ≤ 2 ^ b :=
  Nat.pow_le_pow_right (by decide) h

private theorem exp_mul (a b : ℕ) : 2 ^ a * 2 ^ b = 2 ^ (a + b) := (pow_add _ _ _).symm

private theorem exp_power (a b : ℕ) : (2 ^ a) ^ b = 2 ^ (a * b) := (pow_mul _ _ _).symm

private theorem four_power_exp (a b : ℕ) : 4 ^ a * 2 ^ b = 2 ^ (2 * a + b) := by
  change (2 ^ 2) ^ a * 2 ^ b = _
  rw [← pow_mul, exp_mul]

private theorem sum_three_exp {a b c e : ℕ}
    (ha : a ≤ 2 ^ e) (hb : b ≤ 2 ^ e) (hc : c ≤ 2 ^ e) :
    a + b + c ≤ 4 * 2 ^ e := by omega

private theorem add_one_exp {x e : ℕ} (h : x ≤ 2 ^ e) : x + 1 ≤ 2 ^ (e + 1) := by
  rw [pow_succ]
  have hpos : 1 ≤ 2 ^ e := Nat.one_le_two_pow
  omega

private theorem pairCap_exp {x e : ℕ} (h : x ≤ 2 ^ e) : pairCap x ≤ 2 ^ (2 * e + 2) := by
  have hpos : 1 ≤ 2 ^ e := Nat.one_le_two_pow
  have hsq := Nat.mul_le_mul h h
  have he : 2 ^ (2 * e + 2) = 4 * (2 ^ e) ^ 2 := by
    rw [pow_add, show 2 * e = e * 2 by omega, pow_mul]
    ring
  rw [he]
  unfold pairCap
  nlinarith

theorem horizontal_exp {b k : ℕ} (hk : 1 ≤ k) (hb : b ≤ 2 ^ k) :
    horizontalCap b ≤ 2 ^ (100 * k) := by
  have hJ : indexCap b ≤ 2 ^ (16 * k + 30) := by
    have h := pairCap_exp (pairCap_exp (pairCap_exp (pairCap_exp hb)))
    calc
      indexCap b ≤ 2 ^ (2 * (2 * (2 * (2 * k + 2) + 2) + 2) + 2) := h
      _ = _ := by congr 1; omega
  have hJ1 := add_one_exp hJ
  have hb5 : b ^ 5 ≤ 2 ^ (5 * k) := by
    simpa only [exp_power, Nat.mul_comm] using Nat.pow_le_pow_left hb 5
  have hprod : b ^ 5 * (indexCap b + 1) ≤ 2 ^ (21 * k + 31) := by
    calc
      _ ≤ 2 ^ (5 * k) * 2 ^ (16 * k + 30 + 1) := Nat.mul_le_mul hb5 hJ1
      _ = _ := by rw [exp_mul]; congr 1; omega
  have hplus := add_one_exp hprod
  calc
    horizontalCap b ≤ 2 ^ k * 2 ^ (21 * k + 31 + 1) := Nat.mul_le_mul hb hplus
    _ = 2 ^ (22 * k + 32) := by rw [exp_mul]; congr 1; omega
    _ ≤ _ := exp_mono (by omega)

/-- The polynomial geometry at the end is absorbed into one additional
constant in the double-exponential exponent. -/
private theorem final_cost_exp {H V W p : ℕ} (hp : 1024 ≤ p)
    (hH : H ≤ p) (hV : V ≤ p) (hW : W ≤ p) :
    let M := V * (2 * (8 * (2 ^ W) ^ 5 + V + 3))
    let S := 2 * (1000 * (2 * H + M + 1)) + 3
    S ^ 3 * (3 * S ^ 3 + 6) ^ 3 ≤ 2 ^ (500 * p) := by
  let M := V * (2 * (8 * (2 ^ W) ^ 5 + V + 3))
  let S := 2 * (1000 * (2 * H + M + 1)) + 3
  have hself : p ≤ 2 ^ p := Nat.lt_two_pow_self.le
  have hpow : (2 ^ W) ^ 5 ≤ 2 ^ (5 * p) := by
    rw [exp_power]
    exact exp_mono (by omega)
  have hvsmall : V + 3 ≤ 2 ^ (5 * p + 3) := by
    have h := exp_mono (show p + 1 ≤ 5 * p + 3 by omega)
    have h3 : p + 3 ≤ 2 ^ (p + 1) := by
      rw [pow_succ]
      omega
    exact (by omega : V + 3 ≤ p + 3).trans (h3.trans h)
  have hterm : 8 * (2 ^ W) ^ 5 + V + 3 ≤ 2 ^ (5 * p + 4) := by
    have h8 : 8 * (2 ^ W) ^ 5 ≤ 2 ^ (5 * p + 3) := by
      calc
        _ ≤ 8 * 2 ^ (5 * p) := Nat.mul_le_mul_left 8 hpow
        _ = _ := by rw [pow_add]; ring
    have hsum : 8 * (2 ^ W) ^ 5 + (V + 3) ≤ 2 ^ (5 * p + 3) + 2 ^ (5 * p + 3) :=
      Nat.add_le_add h8 hvsmall
    calc
      _ ≤ 2 ^ (5 * p + 3) + 2 ^ (5 * p + 3) := by omega
      _ = 2 ^ (5 * p + 3) * 2 := by omega
      _ = 2 ^ ((5 * p + 3) + 1) := (pow_succ 2 (5 * p + 3)).symm
      _ = _ := rfl
  have hM : M ≤ 2 ^ (20 * p) := by
    calc
      M ≤ 2 ^ p * (2 * 2 ^ (5 * p + 4)) :=
        Nat.mul_le_mul (hV.trans hself) (Nat.mul_le_mul_left 2 hterm)
      _ = 2 ^ (6 * p + 5) := by rw [pow_add, show 6 * p = p + 5 * p by omega, pow_add]; ring
      _ ≤ _ := exp_mono (by omega)
  have hpM : p ≤ 2 ^ (20 * p) := hself.trans (exp_mono (by omega))
  have hone : 1 ≤ 2 ^ (20 * p) := Nat.one_le_two_pow
  have hsum : 2 * H + M + 1 ≤ 2 ^ (20 * p + 2) := by
    rw [pow_add]
    nlinarith
  have hS : S ≤ 2 ^ (40 * p) := by
    have hscale : 2 * (1000 * (2 * H + M + 1)) ≤ 2 ^ (20 * p + 13) := by
      calc
        _ ≤ 2048 * 2 ^ (20 * p + 2) := by nlinarith
        _ = _ := by rw [show 20 * p + 13 = (20 * p + 2) + 11 by omega, pow_add]; ring
    have h3 : 3 ≤ 2 ^ (20 * p + 13) := by
      exact (by decide : 3 ≤ 2 ^ 2).trans (exp_mono (by omega))
    calc
      S ≤ 2 ^ (20 * p + 14) := by
        dsimp [S]
        rw [show 20 * p + 14 = (20 * p + 13) + 1 by omega, pow_succ]
        omega
      _ ≤ _ := exp_mono (by omega)
  have hS3 : S ^ 3 ≤ 2 ^ (120 * p) := by
    calc
      _ ≤ (2 ^ (40 * p)) ^ 3 := Nat.pow_le_pow_left hS 3
      _ = _ := by rw [exp_power]; congr 1; omega
  have hSbig : 6 ≤ 2 ^ (120 * p) :=
    (by decide : 6 ≤ 2 ^ 3).trans (exp_mono (by omega))
  have hinner : 3 * S ^ 3 + 6 ≤ 2 ^ (120 * p + 4) := by
    rw [pow_add]
    nlinarith
  calc
    S ^ 3 * (3 * S ^ 3 + 6) ^ 3 ≤ 2 ^ (120 * p) * (2 ^ (120 * p + 4)) ^ 3 :=
      Nat.mul_le_mul hS3 (Nat.pow_le_pow_left hinner 3)
    _ = 2 ^ (480 * p + 12) := by rw [exp_power, exp_mul]; congr 1; omega
    _ ≤ _ := exp_mono (by omega)

/-- The initial arithmetic parameter budget, separated from stacking and geometry. -/
noncomputable def arithmeticParameterCap (N C A n : ℕ) : ℕ :=
  let U := 4 ^ (2 * C + 1) * (N ^ 2 + 438)
  let L := A * n + 1
  let Q := 4 ^ (C * L + 1) * (U ^ 2 + 2 * U + 438)
  Q ^ L + U + N + 2

/-- Retain the channel count explicitly when converting an initial parameter
budget into a cube bound. This is sharper than the uniform simplification. -/
theorem arithmeticCubeBound_le_of_budget (N C A n k : ℕ) (hk : 1 ≤ k)
    (hb : arithmeticParameterCap N C A n ≤ 2 ^ k) :
    arithmeticCubeBound N C A n ≤ 2 ^ (2 ^ ((4 * C + 210) * k + 9)) := by
  let b := arithmeticParameterCap N C A n
  let H := horizontalCap b
  let V := b ^ (4 * C + 2)
  let W := (2 * H + 1) ^ 2 * V
  let w := (4 * C + 210) * k
  let p := 2 ^ w
  have hH : H ≤ 2 ^ (100 * k) := horizontal_exp hk hb
  have hV : V ≤ 2 ^ ((4 * C + 2) * k) := by
    calc
      _ ≤ (2 ^ k) ^ (4 * C + 2) := Nat.pow_le_pow_left hb _
      _ = _ := (exp_power _ _).trans (congrArg (fun e : ℕ => 2 ^ e) (Nat.mul_comm _ _))
  have hlin : 2 * H + 1 ≤ 2 ^ (100 * k + 2) := by
    have hpos : 1 ≤ 2 ^ (100 * k) := Nat.one_le_two_pow
    rw [pow_add]
    nlinarith only [hH, hpos]
  have hW : W ≤ p := by
    calc
      W ≤ (2 ^ (100 * k + 2)) ^ 2 * 2 ^ ((4 * C + 2) * k) :=
        Nat.mul_le_mul (Nat.pow_le_pow_left hlin 2) hV
      _ = 2 ^ ((100 * k + 2) * 2 + (4 * C + 2) * k) := by rw [exp_power, exp_mul]
      _ ≤ p := exp_mono (by dsimp [w]; nlinarith only [hk])
  have hHp : H ≤ p := hH.trans (exp_mono (by dsimp [w]; nlinarith only [hk]))
  have hVp : V ≤ p := hV.trans (exp_mono (by dsimp [w]; nlinarith only [hk]))
  have hp : 1024 ≤ p :=
    (by decide : 1024 ≤ 2 ^ 10).trans (exp_mono (by dsimp [w]; nlinarith only [hk]))
  calc
    arithmeticCubeBound N C A n ≤ 2 ^ (500 * p) := final_cost_exp hp hHp hVp hW
    _ ≤ 2 ^ (2 ^ (w + 9)) := by
      apply exp_mono
      dsimp [p]
      rw [pow_add]
      change 500 * 2 ^ w ≤ 2 ^ w * 512
      omega

/-- The long arithmetic bound is dominated by a single double exponential.
The hypotheses cover the fixed constants used by the Wang construction. -/
private theorem arithmeticCubeBound_le_doubleExp (N C A n t : ℕ)
    (ht : 1 ≤ t) (hnt : n + 1 ≤ t)
    (hN : N ≤ 10 ^ 10) (hC : C ≤ 10 ^ 10) (hA : A ≤ 10 ^ 5)
    (hNsq : N ^ 2 + 438 ≤ 2 ^ 64) :
    arithmeticCubeBound N C A n ≤ 2 ^ (2 ^ (10 ^ 40 * t ^ 2)) := by
  let u := 4 * C + 66
  let U := 4 ^ (2 * C + 1) * (N ^ 2 + 438)
  let L := A * n + 1
  let Q := 4 ^ (C * L + 1) * (U ^ 2 + 2 * U + 438)
  let b := Q ^ L + U + N + 2
  let k := 10 ^ 22 * t ^ 2
  let H := horizontalCap b
  let V := b ^ (4 * C + 2)
  let W := (2 * H + 1) ^ 2 * V
  let w := 10 ^ 12 * k
  let p := 2 ^ w
  have ht2 : 1 ≤ t ^ 2 := by nlinarith only [ht]
  have hk : 1 ≤ k := by dsimp [k]; nlinarith only [ht2]
  have hL : L ≤ 10 ^ 5 * t := by
    have h := Nat.mul_le_mul_right n hA
    dsimp [L]
    omega
  have hu : u ≤ 10 ^ 12 := by dsimp [u]; nlinarith only [hC]
  have hU : U ≤ 2 ^ u := by
    calc
      U ≤ 4 ^ (2 * C + 1) * 2 ^ 64 := Nat.mul_le_mul_left _ hNsq
      _ = 2 ^ (2 * (2 * C + 1) + 64) := four_power_exp _ _
      _ = _ := by congr 1; dsimp [u]; omega
  have hU438 : 438 ≤ 2 ^ u :=
    (by decide : 438 ≤ 2 ^ 9).trans (exp_mono (by dsimp [u]; omega))
  have hprefactor : U ^ 2 + 2 * U + 438 ≤ 2 ^ (2 * u + 2) := by
    have hsq := Nat.pow_le_pow_left hU 2
    have hself := Nat.le_mul_self (2 ^ u)
    have he : 2 ^ (2 * u + 2) = 4 * (2 ^ u) ^ 2 := by
      rw [pow_add, show 2 * u = u * 2 by omega, pow_mul]
      ring
    rw [he]
    nlinarith only [hsq, hU, hU438, hself]
  have hCL : C * L ≤ 10 ^ 15 * t := by
    calc
      _ ≤ 10 ^ 10 * (10 ^ 5 * t) := Nat.mul_le_mul hC hL
      _ = _ := by ring
  have hQ : Q ≤ 2 ^ (10 ^ 16 * t) := by
    calc
      Q ≤ 4 ^ (C * L + 1) * 2 ^ (2 * u + 2) := Nat.mul_le_mul_left _ hprefactor
      _ = 2 ^ (2 * (C * L + 1) + (2 * u + 2)) := four_power_exp _ _
      _ ≤ _ := exp_mono (by nlinarith only [hCL, hu, ht])
  have hlow : Q ^ L ≤ 2 ^ (10 ^ 21 * t ^ 2) := by
    calc
      _ ≤ (2 ^ (10 ^ 16 * t)) ^ L := Nat.pow_le_pow_left hQ L
      _ = 2 ^ ((10 ^ 16 * t) * L) := exp_power _ _
      _ ≤ _ := by
        apply exp_mono
        calc
          _ ≤ (10 ^ 16 * t) * (10 ^ 5 * t) := Nat.mul_le_mul_left _ hL
          _ = _ := by ring
  have hUlow : U ≤ 2 ^ (10 ^ 21 * t ^ 2) :=
    hU.trans (exp_mono (by nlinarith only [hu, ht2]))
  have hNlow : N + 2 ≤ 2 ^ (10 ^ 21 * t ^ 2) := by
    have hN40 : N + 2 ≤ 2 ^ 40 := by norm_num at hN ⊢; omega
    exact hN40.trans (exp_mono (by nlinarith only [ht2]))
  have hb : b ≤ 2 ^ k := by
    calc
      b = (Q ^ L + U) + (N + 2) := by dsimp [b]; omega
      _ ≤ 4 * 2 ^ (10 ^ 21 * t ^ 2) := sum_three_exp hlow hUlow hNlow
      _ = 2 ^ (10 ^ 21 * t ^ 2 + 2) := by rw [pow_add]; ring
      _ ≤ _ := exp_mono (by dsimp [k]; nlinarith only [ht2])
  have hH : H ≤ 2 ^ (100 * k) := horizontal_exp hk hb
  have hV : V ≤ 2 ^ (10 ^ 11 * k) := by
    calc
      V ≤ (2 ^ k) ^ (4 * C + 2) := Nat.pow_le_pow_left hb _
      _ = 2 ^ (k * (4 * C + 2)) := exp_power _ _
      _ ≤ _ := by
        apply exp_mono
        have hsmall : 4 * C + 2 ≤ 10 ^ 11 := by nlinarith only [hC]
        calc
          k * (4 * C + 2) ≤ k * 10 ^ 11 := Nat.mul_le_mul_left k hsmall
          _ = _ := Nat.mul_comm _ _
  have hlin : 2 * H + 1 ≤ 2 ^ (100 * k + 2) := by
    have hpos : 1 ≤ 2 ^ (100 * k) := Nat.one_le_two_pow
    rw [pow_add]
    nlinarith only [hH, hpos]
  have hW : W ≤ p := by
    calc
      W ≤ (2 ^ (100 * k + 2)) ^ 2 * 2 ^ (10 ^ 11 * k) :=
        Nat.mul_le_mul (Nat.pow_le_pow_left hlin 2) hV
      _ = 2 ^ ((100 * k + 2) * 2 + 10 ^ 11 * k) := by rw [exp_power, exp_mul]
      _ ≤ p := exp_mono (by dsimp [w]; nlinarith only [hk])
  have hHp : H ≤ p := hH.trans (exp_mono (by dsimp [w]; nlinarith only [hk]))
  have hVp : V ≤ p := hV.trans (exp_mono (by dsimp [w]; nlinarith only [hk]))
  have hp : 1024 ≤ p :=
    (by decide : 1024 ≤ 2 ^ 10).trans (exp_mono (by dsimp [w]; nlinarith only [hk]))
  calc
    arithmeticCubeBound N C A n ≤ 2 ^ (500 * p) := final_cost_exp hp hHp hVp hW
    _ ≤ 2 ^ (2 ^ (w + 9)) := by
      apply exp_mono
      dsimp [p]
      rw [pow_add]
      change 500 * 2 ^ w ≤ 2 ^ w * 512
      omega
    _ ≤ _ := by
      apply exp_mono
      apply exp_mono
      dsimp [w, k]
      nlinarith only [ht2]

theorem arithmeticCubeBound_le_simple (N C A n : ℕ)
    (hN : N ≤ 10 ^ 10) (hC : C ≤ 10 ^ 10) (hA : A ≤ 10 ^ 5)
    (hNsq : N ^ 2 + 438 ≤ 2 ^ 64) :
    arithmeticCubeBound N C A n ≤ 2 ^ (2 ^ (10 ^ 40 * (n + 1) ^ 2)) :=
  arithmeticCubeBound_le_doubleExp N C A n (n + 1) (by omega) le_rfl hN hC hA hNsq

/-- A single expression in the number of distinct Wang tiles. -/
def simpleCubeBound (n : ℕ) : ℕ := 2 ^ (2 ^ (10 ^ 40 * (n + 1) ^ 2))

theorem explicitCubeBound_le_simple (n : ℕ) : explicitCubeBound n ≤ simpleCubeBound n := by
  apply arithmeticCubeBound_le_simple <;> norm_num

private theorem one_parameter_budget (N C A k : ℕ) (hk : 10 ^ 19 ≤ k)
    (hN : N ≤ 2213984809) (hC : C ≤ 2213984811) (hA : A ≤ 46620)
    (hNsq : N ^ 2 + 438 ≤ 2 ^ 64) :
    arithmeticParameterCap N C A 1 ≤ 2 ^ k := by
  let u := 4 * C + 66
  let U := 4 ^ (2 * C + 1) * (N ^ 2 + 438)
  let L := A * 1 + 1
  let Q := 4 ^ (C * L + 1) * (U ^ 2 + 2 * U + 438)
  let q := 2 * (C * L + 1) + (2 * u + 2)
  let e := q * L
  have hLpos : 1 ≤ L := by dsimp [L]; omega
  have hL : L ≤ 46621 := by dsimp [L]; omega
  have hu : u ≤ 8855939310 := by dsimp [u]; omega
  have hu40 : 40 ≤ u := by dsimp [u]; omega
  have hU : U ≤ 2 ^ u := by
    calc
      U ≤ 4 ^ (2 * C + 1) * 2 ^ 64 := Nat.mul_le_mul_left _ hNsq
      _ = 2 ^ (2 * (2 * C + 1) + 64) := four_power_exp _ _
      _ = _ := by congr 1; dsimp [u]; omega
  have hU438 : 438 ≤ 2 ^ u :=
    (by decide : 438 ≤ 2 ^ 9).trans (exp_mono (by omega))
  have hprefactor : U ^ 2 + 2 * U + 438 ≤ 2 ^ (2 * u + 2) := by
    have hsq := Nat.pow_le_pow_left hU 2
    have hself := Nat.le_mul_self (2 ^ u)
    have he : 2 ^ (2 * u + 2) = 4 * (2 ^ u) ^ 2 := by
      rw [pow_add, show 2 * u = u * 2 by omega, pow_mul]
      ring
    rw [he]
    nlinarith only [hsq, hU, hU438, hself]
  have hQ : Q ≤ 2 ^ q := by
    calc
      Q ≤ 4 ^ (C * L + 1) * 2 ^ (2 * u + 2) := Nat.mul_le_mul_left _ hprefactor
      _ = _ := four_power_exp _ _
  have hlow : Q ^ L ≤ 2 ^ e :=
    (Nat.pow_le_pow_left hQ L).trans_eq (exp_power q L)
  have hue : u ≤ e := by
    have hq : u ≤ q := by dsimp [q]; omega
    have hmul : q ≤ q * L := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left q hLpos
    exact hq.trans hmul
  have hUlow : U ≤ 2 ^ e := hU.trans (exp_mono hue)
  have hNlow : N + 2 ≤ 2 ^ e := by
    have hN40 : N + 2 ≤ 2 ^ 40 := by norm_num at hN ⊢; omega
    exact hN40.trans (exp_mono (hu40.trans hue))
  have hCL : C * L ≤ 2213984811 * 46621 := Nat.mul_le_mul hC hL
  have hq : q ≤ 207000000000000 := by dsimp [q]; omega
  have he : e ≤ 9700000000000000000 := by
    have h := Nat.mul_le_mul hq hL
    dsimp [e]
    omega
  calc
    arithmeticParameterCap N C A 1 = (Q ^ L + U) + (N + 2) := by
      change Q ^ L + U + N + 2 = _
      omega
    _ ≤ 4 * 2 ^ e := sum_three_exp hlow hUlow hNlow
    _ = 2 ^ (e + 2) := by rw [pow_add]; ring
    _ ≤ _ := exp_mono (by omega)

private theorem arithmetic_one_bound (N C A k e : ℕ) (hk : 10 ^ 19 ≤ k)
    (hN : N ≤ 2213984809) (hC : C ≤ 2213984811) (hA : A ≤ 46620)
    (hNsq : N ^ 2 + 438 ≤ 2 ^ 64) (he : (4 * C + 210) * k + 9 ≤ e) :
    arithmeticCubeBound N C A 1 ≤ 2 ^ (2 ^ e) :=
  (arithmeticCubeBound_le_of_budget N C A 1 k (by omega)
    (one_parameter_budget N C A k hk hN hC hA hNsq)).trans (exp_mono (exp_mono he))

/-- Sharper numerical specialization of the construction's arithmetic bound
for one Wang tile. No test of that tile's tilability is used. -/
theorem explicitCubeBound_one_le : explicitCubeBound 1 ≤ 2 ^ (2 ^ (10 ^ 29)) :=
  arithmetic_one_bound 2213984809 2213984811 46620 (10 ^ 19) (10 ^ 29)
    le_rfl le_rfl le_rfl le_rfl (by norm_num) (by norm_num)

/-- One distinct input Wang tile has an equivalent connected polycube with
at most `2^(2^(10^29))` cubes, using the same bounded-choice construction. -/
theorem exists_connected_tile_one_bound (T : TileSet) (hT : T.toFinset.card = 1) :
    ∃ P : Tile 3, P ≠ [] ∧ FaceConnected P ∧
      (TilesPlane T ↔ TranslationTiling.Tiles P) ∧
      cubeCount P ≤ 2 ^ (2 ^ (10 ^ 29)) := by
  obtain ⟨P, hP, hc, ht, hb⟩ := exists_connected_tile_explicit_bound T
  have hcount : cubeCount P ≤ explicitCubeBound 1 := hT ▸ hb
  exact ⟨P, hP, hc, ht, hcount.trans explicitCubeBound_one_le⟩

theorem exists_connected_tile_simple_bound (T : TileSet) :
    ∃ P : Tile 3, P ≠ [] ∧ FaceConnected P ∧
      (TilesPlane T ↔ TranslationTiling.Tiles P) ∧
      cubeCount P ≤ 2 ^ (2 ^ (10 ^ 40 * (T.toFinset.card + 1) ^ 2)) := by
  obtain ⟨P, hP, hc, ht, hb⟩ := exists_connected_tile_explicit_bound T
  exact ⟨P, hP, hc, ht, hb.trans (explicitCubeBound_le_simple _)⟩

end
end TranslationTiling.Compiler.Size
