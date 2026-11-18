import TranslationTiling.SudokuArithmetic.Congruence
import TranslationTiling.SudokuArithmetic.ShortClassification

/-! Arithmetic classification on a short prefix together with the column 2r. -/
namespace TranslationTiling.Sudoku.ShortArithmetic
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

abbrev Column (r : ℕ) := Fin (ShortRule.wordWidth r+1)
def position (r : ℕ) (n : Column r) : ℕ := if n.val<ShortRule.wordWidth r then n.val else 2*r
theorem prefix_width (r : ℕ) : 9≤ShortRule.wordWidth r := by unfold ShortRule.wordWidth; split <;> omega

def atColumn (r n : ℕ) : Column r := if h : n<ShortRule.wordWidth r then ⟨n,by omega⟩ else ⟨ShortRule.wordWidth r,by omega⟩
theorem position_at {r : ℕ} (_hr : r=5 ∨ r=7) (n : ℕ)
    (hn : n<ShortRule.wordWidth r ∨ n=2*r) : position r (atColumn r n)=n := by
  unfold atColumn position
  split
  next h => simp [h]
  next h => simpa using hn.resolve_left h |>.symm

/-- One arithmetic component on the retained column set. -/
def ArithmeticLineRule (r : ℕ) (V : (Column r) → ℤ → (ZMod r)ˣ) : Prop :=
  ∀ d e : ℤ, ∃ a b : ℤ,
    (¬ (r : ℤ) ∣ a ∨ ¬ (r : ℤ) ∣ b) ∧
    ∀ n u, lowValuation r (a * (position r n) + b) = some u → u ≤ threshold r a →
      (V n (d * (position r n) + e)).val = lowDigit r (a * (position r n) + b)

/-- On a primitive line, valuation one can occur only when the slope is a unit. -/
theorem primitive_slope_not_dvd (r : ℕ) (a b n : ℤ)
    (hprim : ¬ (r : ℤ) ∣ a ∨ ¬ (r : ℤ) ∣ b) (ht : (r : ℤ) ∣ a * n + b) :
    ¬ (r : ℤ) ∣ a := by
  intro ha
  have hb : (r : ℤ) ∣ b := by
    have h := dvd_sub ht (dvd_mul_of_dvd_left ha n)
    simpa only [add_sub_cancel_left] using h
  exact hprim.elim (fun h => h ha) (fun h => h hb)

theorem arithmetic_tests (r : ℕ) (V : (Column r) → (ZMod r)ˣ) (a b : ℤ)
    (hprim : ¬ (r : ℤ) ∣ a ∨ ¬ (r : ℤ) ∣ b)
    (hV : ∀ n u, lowValuation r (a * (position r n) + b) = some u → u ≤ threshold r a →
      (V n).val = lowDigit r (a * (position r n) + b)) (n : (Column r)) :
    (¬ (r : ℤ) ∣ a * (position r n) + b → (V n).val = ((a * (position r n) + b : ℤ) : ZMod r)) ∧
    ((r : ℤ) ∣ a * (position r n) + b → ¬ (r : ℤ) ^ 2 ∣ a * (position r n) + b →
      (V n).val = (((a * (position r n) + b) / r : ℤ) : ZMod r)) := by
  constructor
  · intro ht
    have hv : lowValuation r (a * (position r n) + b) = some 0 := by simp [lowValuation, ht]
    simpa only [lowDigit, if_neg ht] using hV n 0 hv (Nat.zero_le _)
  · intro ht ht2
    have ha := primitive_slope_not_dvd r a b (position r n) hprim ht
    have hv : lowValuation r (a * (position r n) + b) = some 1 := by simp [lowValuation, ht, ht2]
    simpa only [lowDigit, if_pos ht] using hV n 1 hv (by simp [threshold, ha])

def smallColumn (r : ℕ) (_hr : r=5 ∨ r=7) (n : ShortRule.Column r) : Column r :=
  ⟨n.val,by have := n.isLt; omega⟩

@[simp] theorem position_smallColumn (r : ℕ) (hr : r=5 ∨ r=7) (n : ShortRule.Column r) :
    position r (smallColumn r hr n)=n.val := by simp [position,smallColumn,n.isLt]

def arithmeticRestriction (r : ℕ) (hr : r=5 ∨ r=7)
    (V : (Column r) → ℤ → (ZMod r)ˣ) : ShortRule.WordArray r :=
  fun n m => V (smallColumn r hr n) m

theorem arithmeticRestriction_lineRule (r : ℕ) (hr : r=5 ∨ r=7)
    (V : (Column r) → ℤ → (ZMod r)ˣ) (hV : ArithmeticLineRule r V) :
    ShortRule.LineRule r (arithmeticRestriction r hr V) := by
  intro d e
  obtain ⟨a, b, hab, ht⟩ := hV d e
  refine ⟨a, b, hab, ?_⟩
  intro n
  simpa only [arithmeticRestriction,position_smallColumn] using arithmetic_tests r (fun n => V n (d * (position r n) + e)) a b hab ht (smallColumn r hr n)

theorem arithmeticRestriction_nonconstant (r : ℕ) (hr : r=5 ∨ r=7)
    (V : (Column r) → ℤ → (ZMod r)ˣ)
    (hV : ∀ n, ∃ m m', V n m ≠ V n m') :
    ShortRule.NonconstantColumns (arithmeticRestriction r hr V) :=
  fun n => hV (smallColumn r hr n)

def FullAffineApproximation {r : ℕ} (V : (Column r) → ℤ → (ZMod r)ˣ)
    (A B C : ZMod r) : Prop :=
  (A ≠ 0 ∨ B ≠ 0 ∨ C ≠ 0) ∧ ∀ (n : (Column r)) (m : ℤ),
    A * ((position r n) : ZMod r) + B * (m : ZMod r) + C ≠ 0 →
    (V n m).val = A * ((position r n) : ZMod r) + B * (m : ZMod r) + C

theorem FullAffineApproximation.restrict {r : ℕ} {V : (Column r) → ℤ → (ZMod r)ˣ}
    {A B C : ZMod r} (h : FullAffineApproximation V A B C) (hr : r=5 ∨ r=7) :
    ShortRule.AffineApproximation (arithmeticRestriction r hr V) A B C :=
  by
    refine ⟨h.1,fun n m hn => ?_⟩
    simpa only [position_smallColumn,ShortRule.affineValue,arithmeticRestriction] using
      h.2 (smallColumn r hr n) m (by simpa only [position_smallColumn,ShortRule.affineValue] using hn)

open ArithmeticRule in
theorem arithmeticLineRule_affine (r : ℕ) (V : (Column r) → ℤ → (ZMod r)ˣ)
    (hV : ArithmeticLineRule r V) (d e : ℤ) :
    ∃ a b : ZMod r, (a ≠ 0 ∨ b ≠ 0) ∧ ∀ n : (Column r),
      a * ((position r n) : ZMod r) + b ≠ 0 →
        (V n (d * (position r n) + e)).val = a * ((position r n) : ZMod r) + b := by
  obtain ⟨a, b, hab, ht⟩ := hV d e
  refine ⟨(a : ZMod r), (b : ZMod r), ?_, ?_⟩
  · simpa only [ne_eq, ZMod.intCast_zmod_eq_zero_iff_dvd] using hab
  · intro n hn
    have hnd : ¬ (r : ℤ) ∣ a * (position r n) + b := by
      intro hd
      apply hn
      have hh := (ZMod.intCast_zmod_eq_zero_iff_dvd (a * (position r n) + b) r).mpr hd
      simpa only [Int.cast_add, Int.cast_mul, Int.cast_natCast] using hh
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_natCast] using
      (arithmetic_tests r (fun n => V n (d * (position r n) + e)) a b hab ht n).1 hnd

/-- The affine approximation on the short prefix extends along horizontal
rows to the isolated column 2r. -/
theorem arithmetic_initial_affine (r : ℕ) (hr : r=5 ∨ r=7)
    (hp : r.Prime) (hlarge : 4 < r) (V : (Column r) → ℤ → (ZMod r)ˣ)
    (hV : ArithmeticLineRule r V) :
    ∃ A B C : ZMod r, FullAffineApproximation V A B C := by
  let : Fact r.Prime := ⟨hp⟩
  obtain ⟨A, B, C, hH⟩ := ShortRule.global_affine_approximation hr
    (arithmeticRestriction_lineRule r hr V hV)
  refine ⟨A, B, C, hH.1, ?_⟩
  intro n m hn
  obtain ⟨a, b, hab, hrow⟩ := arithmeticLineRule_affine r V hV 0 m
  let D := B * (m : ZMod r) + C
  have hAD : A ≠ 0 ∨ D ≠ 0 := by
    by_contra hh
    push Not at hh
    apply hn
    dsimp [D] at hh
    rw [hh.1, zero_mul, zero_add]
    exact hh.2
  let x : Fin 4 → ZMod r := fun i => (i.val : ZMod r)
  have hx : Function.Injective x := by
    simpa only [zero_add, Int.cast_natCast] using
      (ArithmeticRule.four_residues_injective (p := r) (by omega) 0)
  obtain ⟨i, j, hij, hiA, hia, hjA, hja⟩ :=
    ArithmeticRule.two_common_nonzero_of_four x hx A D a b hAD hab
  let c : Fin 4 → ShortRule.Column r := fun k =>
    ⟨k.val,by have := k.isLt; have := prefix_width r; omega⟩
  have agrees (k : Fin 4) (hkA : A * x k + D ≠ 0) (hka : a * x k + b ≠ 0) :
      A * x k + D = a * x k + b := by
    have hleft := hH.2 (c k) m (by simpa only [ShortRule.affineValue, c, x, D,
      add_assoc] using hkA)
    have hright := hrow (smallColumn r hr (c k)) (by simpa only [position_smallColumn, c, x] using hka)
    simp only [arithmeticRestriction] at hleft
    simp only [zero_mul, zero_add] at hright
    have heq := hleft.symm.trans hright
    simpa only [arithmeticRestriction, position_smallColumn, ShortRule.affineValue,
      c, x, D, zero_mul, zero_add, add_assoc] using heq
  obtain ⟨ha, hb⟩ := ArithmeticRule.affine_coefficients_eq_of_two
    (fun heq => hij (hx heq)) (agrees i hiA hia) (agrees j hjA hja)
  have hn' : a * ((position r n) : ZMod r) + b ≠ 0 := by
    rw [← ha, ← hb]
    simpa only [D, add_assoc] using hn
  have hh := hrow n hn'
  simpa only [zero_mul, zero_add, ← ha, ← hb, D, add_assoc] using hh

theorem arithmetic_initial_structure (r : ℕ) (hr : r=5 ∨ r=7)
    (hp : r.Prime) (hlarge : 4 < r) (V : (Column r) → ℤ → (ZMod r)ˣ)
    (hV : ArithmeticLineRule r V) (hcols : ∀ n, ∃ m m', V n m ≠ V n m') :
    ∃ A B C : ZMod r, B ≠ 0 ∧ ∀ (n : (Column r)) (m : ℤ),
      A * ((position r n) : ZMod r) + B * (m : ZMod r) + C ≠ 0 →
      (V n m).val = A * ((position r n) : ZMod r) + B * (m : ZMod r) + C := by
  obtain ⟨A, B, C, hH⟩ := arithmetic_initial_affine r hr hp hlarge V hV
  have hB : B≠0 := by
    intro hB
    have hAC : A≠0 ∨ C≠0 := by simpa [hB] using hH.1
    have pick : ∃ j : Fin 2, A*(j.val:ZMod r)+C≠0 := by
      by_cases hC : C=0
      · exact ⟨1,by simpa [hC] using hAC.resolve_right (not_not.mpr hC)⟩
      · exact ⟨0,by simpa using hC⟩
    obtain ⟨j,hj⟩ := pick
    let n := smallColumn r hr ⟨j.val,by have := j.isLt; have := prefix_width r; omega⟩
    have hn : position r n=j.val := position_smallColumn _ _ _
    obtain ⟨m,m',hne⟩ := hcols n
    apply hne
    apply Units.ext
    have he (m : ℤ) : (V n m).val=A*j.val+C := by
      simpa [hB,hn] using hH.2 n m (by simpa [hB,hn] using hj)
    exact (he m).trans (he m').symm
  exact ⟨A,B,C,hB,hH.2⟩

def arithmeticReparametrize {r : ℕ} (V : (Column r) → ℤ → (ZMod r)ˣ)
    (a u v : ℤ) : (Column r) → ℤ → (ZMod r)ˣ :=
  fun n m => V n (a * m + u * (position r n) + v)

theorem arithmeticReparametrize_lineRule {r : ℕ} {V : (Column r) → ℤ → (ZMod r)ˣ}
    (hV : ArithmeticLineRule r V) (a u v : ℤ) :
    ArithmeticLineRule r (arithmeticReparametrize V a u v) := by
  intro d e
  obtain ⟨b, c, hbc, ht⟩ := hV (a * d + u) (a * e + v)
  refine ⟨b, c, hbc, ?_⟩
  intro n t hn hs
  have he : a * (d * ((position r n) : ℤ) + e) + u * (position r n) + v =
      (a * d + u) * (position r n) + (a * e + v) := by ring
  simpa only [arithmeticReparametrize, he] using ht n t hn hs

theorem FullAffineApproximation.reparametrize {r : ℕ} {V : (Column r) → ℤ → (ZMod r)ˣ}
    {A B C : ZMod r} (hp : r.Prime) (hH : FullAffineApproximation V A B C) (a u v : ℤ)
    (hB : B ≠ 0) (ha : (a : ZMod r) ≠ 0) :
    FullAffineApproximation (arithmeticReparametrize V a u v)
      (A + B * (u : ZMod r)) (B * (a : ZMod r)) (C + B * (v : ZMod r)) := by
  let : Fact r.Prime := ⟨hp⟩
  refine ⟨Or.inr (Or.inl (mul_ne_zero hB ha)), ?_⟩
  intro n m hm
  have he : A * ((position r n) : ZMod r) + B * ((a * m + u * (position r n) + v : ℤ) : ZMod r) + C =
      (A + B * (u : ZMod r)) * (position r n) + (B * (a : ZMod r)) * (m : ZMod r) +
        (C + B * (v : ZMod r)) := by
    push_cast
    ring
  exact (hH.2 n _ (by rwa [he])).trans he

theorem FullAffineApproximation.nonconstant {r : ℕ} (hp : r.Prime)
    (hlarge : 4 < r) {V : (Column r) → ℤ → (ZMod r)ˣ} {A B C : ZMod r}
    (hH : FullAffineApproximation V A B C) (hB : B ≠ 0) :
    ∀ n, ∃ m m', V n m ≠ V n m' := by
  let : Fact r.Prime := ⟨hp⟩
  have h12 : (1 : ZMod r) ≠ 2 := by
    intro he
    have hh := congrArg (fun z : ZMod r => z.val) he
    rw [ZMod.val_one_eq_one_mod, ZMod.val_two_eq_two_mod,
      Nat.mod_eq_of_lt (by omega : 1 < r), Nat.mod_eq_of_lt (by omega : 2 < r)] at hh
    omega
  have h2 : (2 : ZMod r) ≠ 0 := by
    intro he
    exact Nat.not_dvd_of_pos_of_lt (by decide : 0 < 2) (by omega : 2 < r)
      ((ZMod.natCast_eq_zero_iff 2 r).mp he)
  intro n
  have exists_value (t : ZMod r) :
      ∃ m : ℤ, A * ((position r n) : ZMod r) + B * (m : ZMod r) + C = t := by
    obtain ⟨m, hm⟩ := ZMod.intCast_surjective (B⁻¹ * (t - A * ((position r n) : ZMod r) - C))
    refine ⟨m, ?_⟩
    rw [hm, ← mul_assoc, mul_inv_cancel₀ hB, one_mul]
    ring
  obtain ⟨m, hm⟩ := exists_value 1
  obtain ⟨m', hm'⟩ := exists_value 2
  refine ⟨m, m', ?_⟩
  intro he
  have hval := congrArg (fun z : (ZMod r)ˣ => z.val) he
  rw [hH.2 n m (by rw [hm]; exact one_ne_zero), hm,
    hH.2 n m' (by rw [hm']; exact h2), hm'] at hval
  exact h12 hval

theorem normalized_line_coefficients {r : ℕ} (hp : r.Prime) (hlarge : 4 < r)     {V : (Column r) → ℤ → (ZMod r)ˣ} {B : ZMod r}
    (hH : FullAffineApproximation V 0 B 0) (hB : B ≠ 0)
    (d e a b : ℤ) (hab : ¬ (r : ℤ) ∣ a ∨ ¬ (r : ℤ) ∣ b)
    (ht : ∀ n u, lowValuation r (a * (position r n) + b) = some u → u ≤ threshold r a →
      (V n (d * (position r n) + e)).val = lowDigit r (a * (position r n) + b))
    (hde : (d : ZMod r) ≠ 0 ∨ (e : ZMod r) ≠ 0) :
    (a : ZMod r) = B * (d : ZMod r) ∧ (b : ZMod r) = B * (e : ZMod r) := by
  let : Fact r.Prime := ⟨hp⟩
  have hab' : (a : ZMod r) ≠ 0 ∨ (b : ZMod r) ≠ 0 := by
    simpa only [ne_eq, ZMod.intCast_zmod_eq_zero_iff_dvd] using hab
  have hBdBe : B * (d : ZMod r) ≠ 0 ∨ B * (e : ZMod r) ≠ 0 :=
    hde.imp (mul_ne_zero hB) (mul_ne_zero hB)
  let x : Fin 4 → ZMod r := fun i => (i.val : ZMod r)
  have hx : Function.Injective x := by
    simpa only [zero_add, Int.cast_natCast] using
      (ArithmeticRule.four_residues_injective (p := r) (by omega) 0)
  obtain ⟨i, j, hij, hi, hi', hj, hj'⟩ :=
    ArithmeticRule.two_common_nonzero_of_four x hx (a : ZMod r) (b : ZMod r)
      (B * (d : ZMod r)) (B * (e : ZMod r)) hab' hBdBe
  let c : Fin 4 → Column r := fun k => ⟨k.val,by have := k.isLt; have := prefix_width r; omega⟩
  have hc (k : Fin 4) : position r (c k)=k.val := by
    simp [position,c,show k.val<ShortRule.wordWidth r by have := k.isLt; have := prefix_width r; omega]
  have agrees (k : Fin 4) (hk : (a : ZMod r) * x k + (b : ZMod r) ≠ 0)
      (hk' : (B * (d : ZMod r)) * x k + B * (e : ZMod r) ≠ 0) :
      (a : ZMod r) * x k + (b : ZMod r) =
        (B * (d : ZMod r)) * x k + B * (e : ZMod r) := by
    have hn : ¬ (r : ℤ) ∣ a * position r (c k) + b := by
      intro hd
      apply hk
      simpa only [Int.cast_add, Int.cast_mul, Int.cast_natCast, hc, x] using
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ r).mpr hd
    have htest := (arithmetic_tests r _ a b hab ht (c k)).1 hn
    have hform : 0 * (position r (c k) : ZMod r) + B * ((d * position r (c k) + e : ℤ) : ZMod r) + 0 =
        (B * (d : ZMod r)) * x k + B * (e : ZMod r) := by
      simp only [hc, x, zero_mul, zero_add, add_zero, Int.cast_add, Int.cast_mul,
        Int.cast_natCast]
      ring
    have happrox := hH.2 (c k) _ (by rwa [hform])
    have hh : (a : ZMod r) * x k + (b : ZMod r) =
        (V (c k) (d * position r (c k) + e)).val := by
      simpa only [Int.cast_add, Int.cast_mul, Int.cast_natCast, hc, x] using htest.symm
    exact hh.trans (happrox.trans hform)
  exact ArithmeticRule.affine_coefficients_eq_of_two (fun he => hij (hx he))
    (agrees i hi hi') (agrees j hj hj')

/-- Three samples on the zero fibre and two on each of fibres one and two
exclude an affine rescaling whose vertical coefficient vanishes. -/
def NoVerticalConstant (r : ℕ) : Prop :=
  ∀ B A C : ZMod r, B≠0 → (A≠0 ∨ C≠0) →
    (∀ j : Fin 3, ∃ z : ZMod r, ∀ k : Fin 3,
      (j.val=0 ∨ k.val<2) → A*j.val+C≠0 → B*k.val+z≠0 →
      B*k.val+z=A*j.val+C) → False

private theorem noVertical5 : NoVerticalConstant 5 := by
  unfold NoVerticalConstant
  decide +kernel
private theorem noVertical7 : NoVerticalConstant 7 := by
  unfold NoVerticalConstant
  decide +kernel

theorem rescale_vertical_coefficient_ne_zero (r : ℕ) (hr : r=5 ∨ r=7)
    (hp : r.Prime) (hlarge : 4<r) {V : Column r → ℤ → (ZMod r)ˣ}
    (hV : ArithmeticLineRule r V) {B A₁ B₁ C₁ : ZMod r}
    (hB : B≠0) (hH : FullAffineApproximation V 0 B 0)
    (hH₁ : FullAffineApproximation (arithmeticReparametrize V r 0 0) A₁ B₁ C₁) :
    B₁≠0 := by
  letI : Fact r.Prime := ⟨hp⟩
  intro hzero
  have hAC : A₁≠0 ∨ C₁≠0 := by simpa [hzero] using hH₁.1
  have hfield : NoVerticalConstant r := by
    rcases hr with rfl|rfl
    · exact noVertical5
    · exact noVertical7
  apply hfield B A₁ C₁ hB hAC
  intro j
  obtain ⟨a,b,hab,ht⟩ := hV 1 (-(j.val:ℤ))
  obtain ⟨ha,hb⟩ := normalized_line_coefficients hp hlarge hH hB 1 (-(j.val:ℤ)) a b hab ht (Or.inl (by simp))
  simp only [Int.cast_one,mul_one,Int.cast_neg] at ha hb
  have hd : (r:ℤ)∣a*j.val+b := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ r).mp
    simp only [Int.cast_add,Int.cast_mul,Int.cast_natCast,ha,hb]
    ring
  obtain ⟨z,hz⟩ := hd
  refine ⟨(z:ZMod r),fun k hk hc hv => ?_⟩
  let n := atColumn r (j.val+r*k.val)
  have hn : position r n=j.val+r*k.val := by
    apply position_at hr
    rcases hr with rfl|rfl
    all_goals fin_cases j <;> fin_cases k
    all_goals norm_num at hk
    all_goals decide +kernel
  have harg : a*(position r n)+b=(r:ℤ)*(z+a*k.val) := by
    rw [hn]
    push_cast
    linear_combination hz
  have hpred : ¬(r:ℤ)∣z+a*k.val := by
    intro h
    apply hv
    have hh := (ZMod.intCast_zmod_eq_zero_iff_dvd _ r).mpr h
    simpa [Int.cast_add,Int.cast_mul,Int.cast_natCast,ha,add_comm] using hh
  have hr0 : (r:ℤ)≠0 := Int.natCast_ne_zero.mpr hp.ne_zero
  have hsq : ¬(r:ℤ)^2∣a*(position r n)+b := by
    intro h
    apply hpred
    apply (Int.mul_dvd_mul_iff_left hr0).mp
    simpa only [harg,pow_two] using h
  have ht' := (arithmetic_tests r _ a b hab ht n).2 ⟨z+a*k.val,harg⟩ hsq
  rw [harg,Int.mul_ediv_cancel_left _ hr0] at ht'
  have hm : 1*(position r n:ℤ)+-(j.val:ℤ)=(r:ℤ)*k.val := by rw [hn]; push_cast; ring
  rw [hm] at ht'
  have hv' := hH₁.2 n (k.val:ℤ) (by
    simpa [hn,hzero,Nat.cast_add,Nat.cast_mul] using hc)
  have hv'' : (V n ((r:ℤ)*k.val)).val=A₁*j.val+C₁ := by
    simpa [arithmeticReparametrize,hn,hzero,Nat.cast_add,Nat.cast_mul] using hv'
  rw [hv''] at ht'
  simpa [Int.cast_add,Int.cast_mul,Int.cast_natCast,ha,add_comm] using ht'.symm

/-- The vertical coefficient is unchanged when one prime factor is removed. -/
theorem rescale_vertical_coefficient {r : ℕ} (hp : r.Prime) (hlarge : 4 < r)
    (hr : r=5 ∨ r=7) {V : (Column r) → ℤ → (ZMod r)ˣ} (hV : ArithmeticLineRule r V)
    {B A₁ B₁ C₁ : ZMod r} (hB : B ≠ 0) (hH : FullAffineApproximation V 0 B 0)
    (hH₁ : FullAffineApproximation (arithmeticReparametrize V r 0 0) A₁ B₁ C₁) :
    B₁ = B := by
  let : Fact r.Prime := ⟨hp⟩
  have hB₁ : B₁≠0 := rescale_vertical_coefficient_ne_zero r hr hp hlarge hV hB hH hH₁
  have htwo : (2:ZMod r)≠0 := by
    intro h
    have hd := (ZMod.natCast_eq_zero_iff 2 r).mp h
    exact Nat.not_dvd_of_pos_of_lt (by decide) (by omega) hd
  have hshift : ∃ t : ℤ, ∀ k : Fin 3, B₁*((t+k.val:ℤ):ZMod r)+C₁≠0 := by
    obtain ⟨t,ht⟩ := ZMod.intCast_surjective (1-B₁⁻¹*C₁)
    have hbase : B₁*(t:ZMod r)+C₁=B₁ := by
      rw [ht]
      calc
        _ = B₁-(B₁*B₁⁻¹)*C₁+C₁ := by ring
        _ = B₁ := by rw [mul_inv_cancel₀ hB₁]; ring
    refine ⟨t,fun k => ?_⟩
    have hk : ((k.val+1:ℕ):ZMod r)≠0 := by
      intro hz
      have hv := congrArg ZMod.val hz
      rw [ZMod.val_natCast_of_lt (by have := k.isLt; omega),ZMod.val_zero] at hv
      omega
    have he : B₁*((t+k.val:ℤ):ZMod r)+C₁=B₁*((k.val+1:ℕ):ZMod r) := by
      push_cast
      linear_combination hbase
    rw [he]
    exact mul_ne_zero hB₁ hk
  obtain ⟨t,htnonzero⟩ := hshift
  obtain ⟨a,b,hab,ht⟩ := hV 1 ((r:ℤ)*t)
  obtain ⟨ha,hb⟩ := normalized_line_coefficients hp hlarge hH hB 1 ((r:ℤ)*t) a b hab ht (Or.inl (by simp))
  simp only [Int.cast_one,mul_one,Int.cast_mul,Int.cast_natCast,ZMod.natCast_self,zero_mul,mul_zero] at ha hb
  have hbd : (r:ℤ)∣b := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hb
  obtain ⟨z,hz⟩ := hbd
  have ha0 : (a:ZMod r)≠0 := by rwa [ha]
  let c : Fin 3 → Column r := fun k => atColumn r (r*k.val)
  have hc (k : Fin 3) : position r (c k)=r*k.val := by
    apply position_at hr
    rcases hr with rfl|rfl <;> fin_cases k <;> norm_num [ShortRule.wordWidth]
  have agrees (k : Fin 3) (hk : (a:ZMod r)*(k.val:ZMod r)+(z:ZMod r)≠0) :
      (a:ZMod r)*(k.val:ZMod r)+(z:ZMod r)=B₁*(k.val:ZMod r)+(B₁*(t:ZMod r)+C₁) := by
    have hcv : (position r (c k):ℤ)=(r:ℤ)*k.val := by simp only [hc,Nat.cast_mul]
    have he : a*position r (c k)+b=(r:ℤ)*(a*k.val+z) := by rw [hcv,hz]; ring
    have hn : ¬(r:ℤ)∣a*k.val+z := by
      intro hd
      apply hk
      simpa only [Int.cast_add,Int.cast_mul,Int.cast_natCast] using
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ r).mpr hd
    have hr0 : (r:ℤ)≠0 := Int.natCast_ne_zero.mpr hp.ne_zero
    have hn2 : ¬(r:ℤ)^2∣a*position r (c k)+b := by
      intro hd
      apply hn
      apply (Int.mul_dvd_mul_iff_left hr0).mp
      simpa only [he,pow_two] using hd
    have ht' := (arithmetic_tests r _ a b hab ht (c k)).2 ⟨a*k.val+z,he⟩ hn2
    simp only [one_mul] at ht'
    rw [he,Int.mul_ediv_cancel_left _ hr0,hcv] at ht'
    simp only [Int.cast_add,Int.cast_mul,Int.cast_natCast] at ht'
    have hh := hH₁.2 (c k) (t+k.val) (by simpa [hc] using htnonzero k)
    simp only [arithmeticReparametrize,zero_mul,add_zero] at hh
    have hearg : (r:ℤ)*(t+k.val)=(r:ℤ)*k.val+(r:ℤ)*t := by ring
    rw [hearg] at hh
    have heq := ht'.symm.trans hh
    simpa [hc,mul_add,add_assoc,add_comm,add_left_comm] using heq
  have hslope : (a:ZMod r)=B₁ := by
    by_cases hz0 : (z:ZMod r)=0
    · have h1 := agrees 1 (by simpa [hz0] using ha0)
      have h2 := agrees 2 (by simpa [hz0,mul_comm] using mul_ne_zero htwo ha0)
      norm_num at h1 h2
      linear_combination h2-h1
    · have h0 := agrees 0 (by simpa using hz0)
      norm_num at h0
      by_cases hz1 : (a:ZMod r)+z=0
      · have hz2 : (a:ZMod r)*2+z≠0 := by
          intro he; apply ha0; linear_combination he-hz1
        have h2 := agrees 2 (by simpa using hz2)
        norm_num at h2
        apply mul_left_cancel₀ htwo
        linear_combination h2-h0
      · have h1 := agrees 1 (by simpa using hz1)
        norm_num at h1
        linear_combination h1-h0
  exact hslope.symm.trans ha

theorem FullAffineApproximation.straighten {r : ℕ} (hp : r.Prime)
    {V : (Column r) → ℤ → (ZMod r)ˣ} {A B C : ZMod r}
    (hH : FullAffineApproximation V A B C) (hB : B ≠ 0) (u v : ℤ)
    (hu : (u : ZMod r) = -(B⁻¹ * A)) (hv : (v : ZMod r) = -(B⁻¹ * C)) :
    FullAffineApproximation (arithmeticReparametrize V 1 u v) 0 B 0 := by
  let : Fact r.Prime := ⟨hp⟩
  have hh := hH.reparametrize hp 1 u v hB (by simp)
  have hau : A + B * (u : ZMod r) = 0 := by
    rw [hu, mul_neg, ← mul_assoc, mul_inv_cancel₀ hB, one_mul, add_neg_cancel]
  have hcv : C + B * (v : ZMod r) = 0 := by
    rw [hv, mul_neg, ← mul_assoc, mul_inv_cancel₀ hB, one_mul, add_neg_cancel]
  simpa only [hau, hcv, Int.cast_one, mul_one] using hh

theorem normalized_finite_structure {r : ℕ} (hp : r.Prime) (hlarge : 4 < r)
    (hr : r=5 ∨ r=7) (k : ℕ) :
    ∀ (V : (Column r) → ℤ → (ZMod r)ˣ) (B : ZMod r), ArithmeticLineRule r V →
      B ≠ 0 → FullAffineApproximation V 0 B 0 →
      ∃ D E : ℤ, (r : ℤ) ∣ D ∧ (r : ℤ) ∣ E ∧
        ∀ (n : (Column r)) (m : ℤ), m - D * (position r n) - E ≠ 0 →
          padicValInt r (m - D * (position r n) - E) ≤ k →
          (V n m).val = B * (lastDigit r hp (m - D * (position r n) - E)).val := by
  let : Fact r.Prime := ⟨hp⟩
  have hr0 : (r : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hp.ne_zero
  induction k with
  | zero =>
    intro V B hV hB hH
    refine ⟨0, 0, dvd_zero _, dvd_zero _, ?_⟩
    intro n m hm hv
    simp only [zero_mul, sub_zero] at hm hv ⊢
    have hnd : ¬ (r : ℤ) ∣ m := by
      intro hd
      have hh := (padicValInt_dvd_iff (p := r) 1 m).mp (by simpa using hd)
      rcases hh with hh | hh <;> omega
    have hmc : (m : ZMod r) ≠ 0 := by
      simpa only [ne_eq, ZMod.intCast_zmod_eq_zero_iff_dvd] using hnd
    have hh := hH.2 n m (by simpa using mul_ne_zero hB hmc)
    simpa only [zero_mul, zero_add, add_zero, lastDigit_eq_of_not_dvd r hp hnd] using hh
  | succ k ih =>
    intro V B hV hB hH
    let S := arithmeticReparametrize V r 0 0
    have hS : ArithmeticLineRule r S := arithmeticReparametrize_lineRule hV r 0 0
    obtain ⟨A₁, B₁, C₁, hH₁⟩ := arithmetic_initial_affine r hr hp hlarge S hS
    have hB₁ := rescale_vertical_coefficient hp hlarge hr hV hB hH hH₁
    subst B₁
    obtain ⟨u, hu⟩ := ZMod.intCast_surjective (-(B⁻¹ * A₁))
    obtain ⟨v, hv⟩ := ZMod.intCast_surjective (-(B⁻¹ * C₁))
    let S₀ := arithmeticReparametrize S 1 u v
    have hS₀ : ArithmeticLineRule r S₀ := arithmeticReparametrize_lineRule hS 1 u v
    have hN : FullAffineApproximation S₀ 0 B 0 := hH₁.straighten hp hB u v hu hv
    obtain ⟨D, E, _, _, hdepth⟩ := ih S₀ B hS₀ hB hN
    let D' := (r : ℤ) * (u + D)
    let E' := (r : ℤ) * (v + E)
    refine ⟨D', E', ⟨u + D, rfl⟩, ⟨v + E, rfl⟩, ?_⟩
    intro n m hm hval
    by_cases hmd : (r : ℤ) ∣ m
    · obtain ⟨t, rfl⟩ := hmd
      let s := t - u * ((position r n) : ℤ) - v
      have he : (r : ℤ) * t - D' * (position r n) - E' =
          (r : ℤ) * (s - D * (position r n) - E) := by dsimp [D', E', s]; ring
      have hnz : s - D * (position r n) - E ≠ 0 := by
        intro hz
        apply hm
        rw [he, hz, mul_zero]
      have hv' : padicValInt r (s - D * (position r n) - E) ≤ k := by
        rw [he, padicValInt.mul hr0 hnz, padicValInt_self] at hval
        omega
      have hh := hdepth n s hnz hv'
      have harg : (r : ℤ) * (1 * s + u * (position r n) + v) + 0 * (position r n) + 0 = r * t := by
        dsimp [s]; ring
      simp only [S₀, S, arithmeticReparametrize, harg] at hh
      rw [he, show (r : ℤ) * (s - D * (position r n) - E) =
        (r : ℤ) ^ 1 * (s - D * (position r n) - E) by rw [pow_one], lastDigit_mul_prime_pow]
      exact hh
    · have hDc : (D' : ZMod r) = 0 := by simp [D']
      have hEc : (E' : ZMod r) = 0 := by simp [E']
      have hzc : ((m - D' * (position r n) - E' : ℤ) : ZMod r) = (m : ZMod r) := by
        simp only [Int.cast_sub, Int.cast_mul, Int.cast_natCast, hDc, hEc, zero_mul, sub_zero]
      have hm0 : (m : ZMod r) ≠ 0 := by
        simpa only [ne_eq, ZMod.intCast_zmod_eq_zero_iff_dvd] using hmd
      have hznd : ¬ (r : ℤ) ∣ m - D' * (position r n) - E' := by
        intro hd
        apply hm0
        rw [← hzc]
        exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ r).mpr hd
      rw [lastDigit_eq_of_not_dvd r hp hznd, hzc]
      simpa only [zero_mul, zero_add, add_zero] using
        hH.2 n m (by simpa using mul_ne_zero hB hm0)

/-- At any finite valuation depth, a nonconstant arithmetic solution is a
constant multiple of the last nonzero digit of a sheared height. -/
theorem arithmetic_finite_structure {r : ℕ} (hp : r.Prime) (hlarge : 4 < r)
    (hr : r=5 ∨ r=7) (V : (Column r) → ℤ → (ZMod r)ˣ)
    (hV : ArithmeticLineRule r V) (hcols : ∀ n, ∃ m m', V n m ≠ V n m') (k : ℕ) :
    ∃ (D E : ℤ) (B : ZMod r), B ≠ 0 ∧
      ∀ (n : (Column r)) (m : ℤ), m - D * (position r n) - E ≠ 0 →
        padicValInt r (m - D * (position r n) - E) ≤ k →
        (V n m).val = B * (lastDigit r hp (m - D * (position r n) - E)).val := by
  let : Fact r.Prime := ⟨hp⟩
  obtain ⟨A, B, C, hB, hH⟩ := arithmetic_initial_structure r hr hp hlarge V hV hcols
  obtain ⟨u, hu⟩ := ZMod.intCast_surjective (-(B⁻¹ * A))
  obtain ⟨v, hv⟩ := ZMod.intCast_surjective (-(B⁻¹ * C))
  let V₀ := arithmeticReparametrize V 1 u v
  have hN : FullAffineApproximation V₀ 0 B 0 :=
    FullAffineApproximation.straighten hp ⟨Or.inr (Or.inl hB), hH⟩ hB u v hu hv
  obtain ⟨D, E, _, _, hdepth⟩ := normalized_finite_structure hp hlarge hr k V₀ B
    (arithmeticReparametrize_lineRule hV 1 u v) hB hN
  refine ⟨u + D, v + E, B, hB, ?_⟩
  intro n m hm hval
  let s := m - u * ((position r n) : ℤ) - v
  have he : s - D * (position r n) - E = m - (u + D) * (position r n) - (v + E) := by
    dsimp [s]; ring
  have hh := hdepth n s (by rwa [he]) (by rwa [he])
  have harg : 1 * s + u * (position r n) + v = m := by dsimp [s]; ring
  simpa only [V₀, arithmeticReparametrize, harg, he] using hh


end
end TranslationTiling.Sudoku.ShortArithmetic
