import TranslationTiling.Compiler.SevenLogBound
import TranslationTiling.FiniteCompiler.Effective.SparseStrip

namespace TranslationTiling.Compiler.Size

open FiniteCompiler.Effective FiniteCompiler.SparseTernary
noncomputable section

private theorem log_lower {a b : ℕ} {x : ℝ} (_hx : 0 < x) (hb : 0 < b)
    (h : (2 : ℝ)^a ≤ x^b) : (a : ℝ)/b ≤ Real.logb 2 x := by
  have hl := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (by positivity : (0 : ℝ) < 2^a) h
  rw [Real.logb_pow, Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one] at hl
  exact (div_le_iff₀ (by exact_mod_cast hb)).mpr (by linarith)

private theorem log_upper {a b : ℕ} {x : ℝ} (hx : 0 < x) (hb : 0 < b)
    (h : x^b ≤ (2 : ℝ)^a) : Real.logb 2 x ≤ (a : ℝ)/b := by
  have hlog := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (pow_pos hx b) h
  rw [Real.logb_pow, Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one] at hlog
  exact (le_div_iff₀ (by exact_mod_cast hb)).mpr (by linarith)

/-- The consecutive powers of two bracketing the uniform formula at one tile. -/
theorem packed_bound_one :
    (2 : ℝ)^880 < (5 : ℝ)^(312 * Real.logb 2 (Real.logb 2 5)) ∧
    (5 : ℝ)^(312 * Real.logb 2 (Real.logb 2 5)) < (2 : ℝ)^881 := by
  let t := Real.logb 2 (5 : ℝ)
  let g := Real.logb 2 t
  have ht₀ : 202/87 ≤ t :=
    log_lower (a:=202) (b:=87) (by norm_num) (by decide) (by norm_num)
  have ht₁ : t ≤ 137/59 :=
    log_upper (a:=137) (b:=59) (by norm_num) (by decide) (by norm_num)
  have htpos : 0 < t := by linarith
  have hg₀ : 96/79 ≤ g :=
    (log_lower (a:=96) (b:=79) (by norm_num) (by decide) (by norm_num)).trans
      (Real.logb_le_logb_of_le (by norm_num) (by norm_num) ht₀)
  have hg₁ : g ≤ 62/51 :=
    (Real.logb_le_logb_of_le (by norm_num) htpos ht₁).trans
      (log_upper (a:=62) (b:=51) (by norm_num) (by decide) (by norm_num))
  have hp₀ := mul_le_mul ht₀ hg₀ (by norm_num : (0 : ℝ) ≤ 96/79) htpos.le
  have hp₁ := mul_le_mul ht₁ hg₁ (show 0 ≤ g by linarith) (by norm_num : (0 : ℝ) ≤ 137/59)
  have hpow (k : ℕ) : Real.logb 2 ((2 : ℝ)^k) = k := by
    rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one]
  have hr : Real.logb 2 ((5 : ℝ)^(312 * g)) = 312 * g * t :=
    Real.logb_rpow_eq_mul_logb_of_pos (by norm_num)
  constructor
  · apply (Real.logb_lt_logb_iff (by norm_num : (1 : ℝ) < 2) (by positivity) (by positivity)).mp
    change Real.logb 2 ((2 : ℝ)^880) < Real.logb 2 ((5 : ℝ)^(312*g))
    rw [hpow, hr]
    norm_num at hp₀ ⊢
    nlinarith only [hp₀]
  · apply (Real.logb_lt_logb_iff (by norm_num : (1 : ℝ) < 2) (by positivity) (by positivity)).mp
    change Real.logb 2 ((5 : ℝ)^(312*g)) < Real.logb 2 ((2 : ℝ)^881)
    rw [hpow, hr]
    norm_num at hp₁ ⊢
    nlinarith only [hp₁]

theorem packed_exponent {n m e a b c d : ℕ} (hn : m ≤ n) (hb : 0 < b) (hd : 0 < d)
    (ht : (2 : ℝ)^a ≤ ((m : ℝ)+4)^b) (hg : (2 : ℝ)^c ≤ ((a : ℝ)/b)^d)
    (ha : (0 : ℝ) < (a : ℝ)/b) (he : (e : ℝ) ≤ 312*((a : ℝ)/b)*((c : ℝ)/d)) :
    (e : ℝ) ≤ 312*Real.logb 2 ((n : ℝ)+4)*Real.logb 2 (Real.logb 2 ((n : ℝ)+4)) := by
  have hm : (m : ℝ)+4 ≤ (n : ℝ)+4 := by exact_mod_cast Nat.add_le_add_right hn 4
  have ht' := log_lower (a:=a) (by positivity : (0 : ℝ) < (n : ℝ)+4) hb
    (ht.trans (pow_le_pow_left₀ (by positivity) hm _))
  have hg' := (log_lower (a:=c) ha hd hg).trans
    (Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) ha ht')
  have h := mul_le_mul ht' hg' (by positivity : (0 : ℝ) ≤ (c : ℝ)/d) (ha.le.trans ht')
  nlinarith only [he,h]

theorem packed_dyadic_real_bound {n N e : ℕ} (hN : N ≤ 2^e)
    (he : (e : ℝ) ≤ 312*Real.logb 2 ((n : ℝ)+4)*Real.logb 2 (Real.logb 2 ((n : ℝ)+4))) :
    (N : ℝ) ≤ ((n : ℝ)+4)^(312*Real.logb 2 (Real.logb 2 ((n : ℝ)+4))) := by
  apply (show (N : ℝ) ≤ (2 : ℝ)^e by exact_mod_cast hN).trans
  apply (Real.logb_le_logb (by norm_num : (1 : ℝ) < 2) (by positivity) (by positivity)).mp
  rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one, Real.logb_rpow_eq_mul_logb_of_pos (by positivity)]
  nlinarith only [he]

private theorem width_le_eighty {n : ℕ} (hn : n < 59049) : width n ≤ 80 := by
  have h := Nat.log_lt_of_lt_pow' (b:=3) (x:=10) (by decide) hn
  unfold width tileWidth
  omega

private theorem lg_three : Real.logb 2 (3 : ℝ) ≤ 8/5 := by
  have h := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (by positivity : (0 : ℝ) < (3 : ℝ)^5) (show (3 : ℝ)^5 ≤ (2 : ℝ)^8 by norm_num)
  rw [Real.logb_pow, Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one] at h
  norm_num at h
  linarith

private theorem lg_256 : Real.logb 2 (256 : ℝ) = 8 := by
  rw [show (256 : ℝ) = (2 : ℝ)^8 by norm_num, Real.logb_pow]
  norm_num [Real.logb_self_eq_one]

theorem packed_bulk_real_bound {n N : ℕ} (hn : 8188 ≤ n)
    (hN : N ≤ (max (width n+2) 256)^(21*width n+78)*3^(4*width n+4)) :
    (N : ℝ) ≤ ((n : ℝ)+4)^(312*Real.logb 2 (Real.logb 2 ((n : ℝ)+4))) := by
  let w := width n
  let P := max (w+2) 256
  let t := Real.logb 2 ((n : ℝ)+4)
  let g := Real.logb 2 t
  have ht : 13 ≤ t := by
    have h := log_lower (a:=13) (b:=1) (by positivity : (0 : ℝ) < (n : ℝ)+4)
      (by decide) (by norm_num; exact_mod_cast (by omega : 8192 ≤ n+4))
    simpa [t] using h
  have hg : 11/3 ≤ g := by
    exact (log_lower (a:=11) (b:=3) (by norm_num : (0 : ℝ) < 13) (by decide)
      (by norm_num)).trans (Real.logb_le_logb_of_le (by norm_num) (by norm_num) ht)
  have ht0 : 0 < t := by linarith
  have hg0 : 0 < g := by linarith
  have hw0 : (0 : ℝ) ≤ w := Nat.cast_nonneg _
  have hP : 0 < P := lt_of_lt_of_le (by decide) (le_max_right _ _)
  have he : ((21*(w : ℝ)+78)*Real.logb 2 (P : ℝ) +
      (4*(w : ℝ)+4)*Real.logb 2 (3 : ℝ)) ≤ 312*t*g := by
    by_cases hsmall : n < 59049
    · have hw := width_le_eighty hsmall
      have hwr : (w : ℝ) ≤ 80 := by exact_mod_cast hw
      have hp : P = 256 := max_eq_right (by dsimp [w]; omega)
      rw [hp, Nat.cast_ofNat, lg_256]
      have hmul := mul_le_mul ht hg (by norm_num : (0 : ℝ) ≤ 11/3) ht0.le
      have hthird := mul_le_mul
        (show 4*(w : ℝ)+4 ≤ 324 by linarith) lg_three
        (Real.logb_nonneg (by norm_num) (by norm_num))
        (by norm_num : (0 : ℝ) ≤ 324)
      linarith
    · have ht' : 15 ≤ t := by
        have h := log_lower (a:=15) (b:=1) (by positivity : (0 : ℝ) < (n : ℝ)+4)
          (by decide) (by norm_num; exact_mod_cast (by omega : 32768 ≤ n+4))
        simpa [t] using h
      have hg' : 39/10 ≤ g := by
        exact (log_lower (a:=39) (b:=10) (by norm_num : (0 : ℝ) < 15) (by decide)
          (by norm_num)).trans (Real.logb_le_logb_of_le (by norm_num) (by norm_num) ht')
      have hw : (w : ℝ) ≤ 2*t+66 := pairWidth_le_log (by omega)
      have hp : Real.logb 2 (P : ℝ) ≤ (80/39)*g := by
        by_cases h : w+2 ≤ 256
        · have hP' : P = 256 := max_eq_right h
          rw [hP', Nat.cast_ofNat, lg_256]
          linarith
        · have hP' : P = w+2 := max_eq_left (by omega)
          have hle : (P : ℝ) ≤ 8*t := by rw [hP']; push_cast; linarith
          have hl := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
            (by exact_mod_cast hP : (0 : ℝ) < P) hle
          rw [Real.logb_mul (by norm_num : (8 : ℝ) ≠ 0) ht0.ne',
            show (8 : ℝ) = (2 : ℝ)^3 by norm_num, Real.logb_pow] at hl
          norm_num [Real.logb_self_eq_one, ← show g = Real.logb 2 t from rfl] at hl
          linarith
      have hl : (0 : ℝ) ≤ Real.logb 2 (P : ℝ) :=
        Real.logb_nonneg (by norm_num) (by exact_mod_cast (show 1 ≤ P from hP))
      have h1 := mul_le_mul
        (show 21*(w : ℝ)+78 ≤ (21*(2+66/15)+78/15)*t by linarith) hp hl (by positivity)
      have h2 := mul_le_mul
        (show 4*(w : ℝ)+4 ≤ (4*(2+66/15)+4/15)*t by linarith)
        (show Real.logb 2 (3 : ℝ) ≤ (16/39)*g by linarith [lg_three])
        (Real.logb_nonneg (by norm_num) (by norm_num)) (by positivity)
      nlinarith only [h1,h2,mul_nonneg ht0.le hg0.le]
  apply (show (N : ℝ) ≤ (↑(P^(21*w+78)*3^(4*w+4) : ℕ) : ℝ) by exact_mod_cast hN).trans
  push_cast
  apply (Real.logb_le_logb (by norm_num : (1 : ℝ) < 2)
    (by positivity) (by positivity)).mp
  rw [Real.logb_mul (by positivity) (by positivity), Real.logb_pow, Real.logb_pow,
    Real.logb_rpow_eq_mul_logb_of_pos (by positivity)]
  change _ ≤ 312*g*t
  push_cast
  nlinarith only [he]

theorem sparseStripCore_packed_bound (T : LeanWang.TileSet) (hn : 243 ≤ T.length) :
    ((sparseStripCore T).length : ℝ) ≤ ((T.length : ℝ)+4)^
      (312*Real.logb 2 (Real.logb 2 ((T.length : ℝ)+4))) := by
  by_cases hbulk : 8188 ≤ T.length
  · exact packed_bulk_real_bound hbulk (sparseStripCore_channel_bound T (by omega))
  · have hw : (system T).width = 80 := by
      simpa [system, SmallProfiles.width] using seven_width80 hn (by omega : T.length ≤ 8187)
    apply packed_dyadic_real_bound (sparseStripCore_width80 T (by omega) hw)
    exact packed_exponent (m:=243) (a:=55) (b:=7) (c:=53) (d:=18) hn
      (by decide) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end
end TranslationTiling.Compiler.Size
