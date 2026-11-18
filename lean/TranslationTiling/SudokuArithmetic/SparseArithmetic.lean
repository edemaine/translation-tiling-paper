import TranslationTiling.SudokuArithmetic.Congruence

/-! Arithmetic classification on an independently sized board. -/
namespace TranslationTiling.Sudoku.SparseArithmetic
noncomputable section
variable {N : ℕ}
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

/-- One arithmetic component on an independently sized board. -/
def ArithmeticLineRule (r : ℕ) (V : (Fin N) → ℤ → (ZMod r)ˣ) : Prop :=
  ∀ d e : ℤ, ∃ a b : ℤ,
    (¬ (r : ℤ) ∣ a ∨ ¬ (r : ℤ) ∣ b) ∧
    ∀ n u, lowValuation r (a * n.val + b) = some u → u ≤ threshold r a →
      (V n (d * n.val + e)).val = lowDigit r (a * n.val + b)

/-- On a primitive line, valuation one can occur only when the slope is a unit. -/
theorem primitive_slope_not_dvd (r : ℕ) (a b n : ℤ)
    (hprim : ¬ (r : ℤ) ∣ a ∨ ¬ (r : ℤ) ∣ b) (ht : (r : ℤ) ∣ a * n + b) :
    ¬ (r : ℤ) ∣ a := by
  intro ha
  have hb : (r : ℤ) ∣ b := by
    have h := dvd_sub ht (dvd_mul_of_dvd_left ha n)
    simpa only [add_sub_cancel_left] using h
  exact hprim.elim (fun h => h ha) (fun h => h hb)

theorem arithmetic_tests (r : ℕ) (V : (Fin N) → (ZMod r)ˣ) (a b : ℤ)
    (hprim : ¬ (r : ℤ) ∣ a ∨ ¬ (r : ℤ) ∣ b)
    (hV : ∀ n u, lowValuation r (a * n.val + b) = some u → u ≤ threshold r a →
      (V n).val = lowDigit r (a * n.val + b)) (n : (Fin N)) :
    (¬ (r : ℤ) ∣ a * n.val + b → (V n).val = ((a * n.val + b : ℤ) : ZMod r)) ∧
    ((r : ℤ) ∣ a * n.val + b → ¬ (r : ℤ) ^ 2 ∣ a * n.val + b →
      (V n).val = (((a * n.val + b) / r : ℤ) : ZMod r)) := by
  constructor
  · intro ht
    have hv : lowValuation r (a * n.val + b) = some 0 := by simp [lowValuation, ht]
    simpa only [lowDigit, if_neg ht] using hV n 0 hv (Nat.zero_le _)
  · intro ht ht2
    have ha := primitive_slope_not_dvd r a b n.val hprim ht
    have hv : lowValuation r (a * n.val + b) = some 1 := by simp [lowValuation, ht, ht2]
    simpa only [lowDigit, if_pos ht] using hV n 1 hv (by simp [threshold, ha])

def smallColumn (r : ℕ) (hr : ArithmeticRule.wordWidth r ≤ N) (n : ArithmeticRule.Column r) : (Fin N) :=
  ⟨n.val, n.isLt.trans_le hr⟩

def arithmeticRestriction (r : ℕ) (hr : ArithmeticRule.wordWidth r ≤ N)
    (V : (Fin N) → ℤ → (ZMod r)ˣ) : ArithmeticRule.WordArray r :=
  fun n m => V (smallColumn r hr n) m

theorem arithmeticRestriction_lineRule (r : ℕ) (hr : ArithmeticRule.wordWidth r ≤ N)
    (V : (Fin N) → ℤ → (ZMod r)ˣ) (hV : ArithmeticLineRule r V) :
    ArithmeticRule.LineRule r (arithmeticRestriction r hr V) := by
  intro d e
  obtain ⟨a, b, hab, ht⟩ := hV d e
  refine ⟨a, b, hab, ?_⟩
  intro n
  exact arithmetic_tests r (fun n => V n (d * n.val + e)) a b hab ht (smallColumn r hr n)

theorem arithmeticRestriction_nonconstant (r : ℕ) (hr : ArithmeticRule.wordWidth r ≤ N)
    (V : (Fin N) → ℤ → (ZMod r)ˣ)
    (hV : ∀ n, ∃ m m', V n m ≠ V n m') :
    ArithmeticRule.NonconstantColumns (arithmeticRestriction r hr V) :=
  fun n => hV (smallColumn r hr n)

def FullAffineApproximation {r : ℕ} (V : (Fin N) → ℤ → (ZMod r)ˣ)
    (A B C : ZMod r) : Prop :=
  (A ≠ 0 ∨ B ≠ 0 ∨ C ≠ 0) ∧ ∀ (n : (Fin N)) (m : ℤ),
    A * (n.val : ZMod r) + B * (m : ZMod r) + C ≠ 0 →
    (V n m).val = A * (n.val : ZMod r) + B * (m : ZMod r) + C

theorem FullAffineApproximation.restrict {r : ℕ} {V : (Fin N) → ℤ → (ZMod r)ˣ}
    {A B C : ZMod r} (h : FullAffineApproximation V A B C) (hr : ArithmeticRule.wordWidth r ≤ N) :
    ArithmeticRule.AffineApproximation (arithmeticRestriction r hr V) A B C :=
  ⟨h.1, fun n m hn => h.2 (smallColumn r hr n) m hn⟩

open ArithmeticRule in
theorem arithmeticLineRule_affine (r : ℕ) (V : (Fin N) → ℤ → (ZMod r)ˣ)
    (hV : ArithmeticLineRule r V) (d e : ℤ) :
    ∃ a b : ZMod r, (a ≠ 0 ∨ b ≠ 0) ∧ ∀ n : (Fin N),
      a * (n.val : ZMod r) + b ≠ 0 →
        (V n (d * n.val + e)).val = a * (n.val : ZMod r) + b := by
  obtain ⟨a, b, hab, ht⟩ := hV d e
  refine ⟨(a : ZMod r), (b : ZMod r), ?_, ?_⟩
  · simpa only [ne_eq, ZMod.intCast_zmod_eq_zero_iff_dvd] using hab
  · intro n hn
    have hnd : ¬ (r : ℤ) ∣ a * n.val + b := by
      intro hd
      apply hn
      have hh := (ZMod.intCast_zmod_eq_zero_iff_dvd (a * n.val + b) r).mpr hd
      simpa only [Int.cast_add, Int.cast_mul, Int.cast_natCast] using hh
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_natCast] using
      (arithmetic_tests r (fun n => V n (d * n.val + e)) a b hab ht n).1 hnd

/-- The affine approximation obtained on the first `2r+2` columns extends along
rows to the whole board. -/
theorem arithmetic_initial_affine (r : ℕ) (hr : ArithmeticRule.wordWidth r ≤ N)
    (hp : r.Prime) (hlarge : 4 < r) (V : (Fin N) → ℤ → (ZMod r)ˣ)
    (hV : ArithmeticLineRule r V) :
    ∃ A B C : ZMod r, FullAffineApproximation V A B C := by
  let : Fact r.Prime := ⟨hp⟩
  obtain ⟨A, B, C, hH⟩ := ArithmeticRule.global_affine_approximation_improved hp hlarge
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
  let c : Fin 4 → ArithmeticRule.Column r := fun k =>
    ⟨k.val, by have := k.isLt; have := hp.one_lt; nlinarith⟩
  have agrees (k : Fin 4) (hkA : A * x k + D ≠ 0) (hka : a * x k + b ≠ 0) :
      A * x k + D = a * x k + b := by
    have hleft := hH.2 (c k) m (by simpa only [ArithmeticRule.affineValue, c, x, D,
      add_assoc] using hkA)
    have hright := hrow (smallColumn r hr (c k)) (by simpa only [smallColumn, c, x] using hka)
    simp only [arithmeticRestriction] at hleft
    simp only [zero_mul, zero_add] at hright
    have heq := hleft.symm.trans hright
    simpa only [arithmeticRestriction, smallColumn, ArithmeticRule.affineValue,
      c, x, D, zero_mul, zero_add, add_assoc] using heq
  obtain ⟨ha, hb⟩ := ArithmeticRule.affine_coefficients_eq_of_two
    (fun heq => hij (hx heq)) (agrees i hiA hia) (agrees j hjA hja)
  have hn' : a * (n.val : ZMod r) + b ≠ 0 := by
    rw [← ha, ← hb]
    simpa only [D, add_assoc] using hn
  have hh := hrow n hn'
  simpa only [zero_mul, zero_add, ← ha, ← hb, D, add_assoc] using hh

theorem arithmetic_initial_structure (r : ℕ) (hr : ArithmeticRule.wordWidth r ≤ N)
    (hp : r.Prime) (hlarge : 4 < r) (V : (Fin N) → ℤ → (ZMod r)ˣ)
    (hV : ArithmeticLineRule r V) (hcols : ∀ n, ∃ m m', V n m ≠ V n m') :
    ∃ A B C : ZMod r, B ≠ 0 ∧ ∀ (n : (Fin N)) (m : ℤ),
      A * (n.val : ZMod r) + B * (m : ZMod r) + C ≠ 0 →
      (V n m).val = A * (n.val : ZMod r) + B * (m : ZMod r) + C := by
  obtain ⟨A, B, C, hH⟩ := arithmetic_initial_affine r hr hp hlarge V hV
  have hB := (ArithmeticRule.nonconstantColumns_iff_vertical_coefficient hp hlarge
    (hH.restrict hr)).mp (arithmeticRestriction_nonconstant r hr V hcols)
  exact ⟨A, B, C, hB, hH.2⟩

def arithmeticReparametrize {r : ℕ} (V : (Fin N) → ℤ → (ZMod r)ˣ)
    (a u v : ℤ) : (Fin N) → ℤ → (ZMod r)ˣ :=
  fun n m => V n (a * m + u * n.val + v)

theorem arithmeticReparametrize_lineRule {r : ℕ} {V : (Fin N) → ℤ → (ZMod r)ˣ}
    (hV : ArithmeticLineRule r V) (a u v : ℤ) :
    ArithmeticLineRule r (arithmeticReparametrize V a u v) := by
  intro d e
  obtain ⟨b, c, hbc, ht⟩ := hV (a * d + u) (a * e + v)
  refine ⟨b, c, hbc, ?_⟩
  intro n t hn hs
  have he : a * (d * (n.val : ℤ) + e) + u * n.val + v =
      (a * d + u) * n.val + (a * e + v) := by ring
  simpa only [arithmeticReparametrize, he] using ht n t hn hs

theorem FullAffineApproximation.reparametrize {r : ℕ} {V : (Fin N) → ℤ → (ZMod r)ˣ}
    {A B C : ZMod r} (hp : r.Prime) (hH : FullAffineApproximation V A B C) (a u v : ℤ)
    (hB : B ≠ 0) (ha : (a : ZMod r) ≠ 0) :
    FullAffineApproximation (arithmeticReparametrize V a u v)
      (A + B * (u : ZMod r)) (B * (a : ZMod r)) (C + B * (v : ZMod r)) := by
  let : Fact r.Prime := ⟨hp⟩
  refine ⟨Or.inr (Or.inl (mul_ne_zero hB ha)), ?_⟩
  intro n m hm
  have he : A * (n.val : ZMod r) + B * ((a * m + u * n.val + v : ℤ) : ZMod r) + C =
      (A + B * (u : ZMod r)) * n.val + (B * (a : ZMod r)) * (m : ZMod r) +
        (C + B * (v : ZMod r)) := by
    push_cast
    ring
  exact (hH.2 n _ (by rwa [he])).trans he

theorem FullAffineApproximation.nonconstant {r : ℕ} (hp : r.Prime)
    (hlarge : 4 < r) {V : (Fin N) → ℤ → (ZMod r)ˣ} {A B C : ZMod r}
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
      ∃ m : ℤ, A * (n.val : ZMod r) + B * (m : ZMod r) + C = t := by
    obtain ⟨m, hm⟩ := ZMod.intCast_surjective (B⁻¹ * (t - A * (n.val : ZMod r) - C))
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

theorem normalized_line_coefficients {r : ℕ} (hp : r.Prime) (hlarge : 4 < r) (hN : 5 ≤ N)
    {V : (Fin N) → ℤ → (ZMod r)ˣ} {B : ZMod r}
    (hH : FullAffineApproximation V 0 B 0) (hB : B ≠ 0)
    (d e a b : ℤ) (hab : ¬ (r : ℤ) ∣ a ∨ ¬ (r : ℤ) ∣ b)
    (ht : ∀ n u, lowValuation r (a * n.val + b) = some u → u ≤ threshold r a →
      (V n (d * n.val + e)).val = lowDigit r (a * n.val + b))
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
  let c : Fin 4 → (Fin N) := fun k => ⟨k.val, by
    have := k.isLt; have := hp.one_lt; nlinarith⟩
  have agrees (k : Fin 4) (hk : (a : ZMod r) * x k + (b : ZMod r) ≠ 0)
      (hk' : (B * (d : ZMod r)) * x k + B * (e : ZMod r) ≠ 0) :
      (a : ZMod r) * x k + (b : ZMod r) =
        (B * (d : ZMod r)) * x k + B * (e : ZMod r) := by
    have hn : ¬ (r : ℤ) ∣ a * (c k).val + b := by
      intro hd
      apply hk
      simpa only [Int.cast_add, Int.cast_mul, Int.cast_natCast, c, x] using
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ r).mpr hd
    have htest := (arithmetic_tests r _ a b hab ht (c k)).1 hn
    have hform : 0 * ((c k).val : ZMod r) + B * ((d * (c k).val + e : ℤ) : ZMod r) + 0 =
        (B * (d : ZMod r)) * x k + B * (e : ZMod r) := by
      simp only [c, x, zero_mul, zero_add, add_zero, Int.cast_add, Int.cast_mul,
        Int.cast_natCast]
      ring
    have happrox := hH.2 (c k) _ (by rwa [hform])
    have hh : (a : ZMod r) * x k + (b : ZMod r) =
        (V (c k) (d * (c k).val + e)).val := by
      simpa only [Int.cast_add, Int.cast_mul, Int.cast_natCast, c, x] using htest.symm
    exact hh.trans (happrox.trans hform)
  exact ArithmeticRule.affine_coefficients_eq_of_two (fun he => hij (hx he))
    (agrees i hi hi') (agrees j hj hj')

/-- The vertical coefficient is unchanged when one prime factor is removed. -/
theorem rescale_vertical_coefficient {r : ℕ} (hp : r.Prime) (hlarge : 4 < r)
    (hr : ArithmeticRule.wordWidth r ≤ N) {V : (Fin N) → ℤ → (ZMod r)ˣ} (hV : ArithmeticLineRule r V)
    {B A₁ B₁ C₁ : ZMod r} (hB : B ≠ 0) (hH : FullAffineApproximation V 0 B 0)
    (hH₁ : FullAffineApproximation (arithmeticReparametrize V r 0 0) A₁ B₁ C₁) :
    B₁ = B := by
  let : Fact r.Prime := ⟨hp⟩
  have hB₁ : B₁ ≠ 0 := ArithmeticRule.rescale_vertical_coefficient_ne_zero hp hlarge
    (arithmeticRestriction_lineRule r hr V hV) hB (hH.restrict hr)
    (by simpa only [ArithmeticRule.AffineApproximation, arithmeticRestriction,
      arithmeticReparametrize, zero_mul,
      add_zero, ArithmeticRule.rescale] using hH₁.restrict hr)
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
  obtain ⟨ha,hb⟩ := normalized_line_coefficients hp hlarge (by dsimp [ArithmeticRule.wordWidth] at hr; omega) hH hB 1 ((r:ℤ)*t) a b hab ht (Or.inl (by simp))
  simp only [Int.cast_one,mul_one,Int.cast_mul,Int.cast_natCast,ZMod.natCast_self,zero_mul,mul_zero] at ha hb
  have hbd : (r:ℤ)∣b := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hb
  obtain ⟨z,hz⟩ := hbd
  have ha0 : (a:ZMod r)≠0 := by rwa [ha]
  let c : Fin 3 → (Fin N) := fun k => ⟨r*k.val,by
    have hk := k.isLt
    have hr' : 2*r+2≤N := hr
    nlinarith⟩
  have agrees (k : Fin 3) (hk : (a:ZMod r)*(k.val:ZMod r)+(z:ZMod r)≠0) :
      (a:ZMod r)*(k.val:ZMod r)+(z:ZMod r)=B₁*(k.val:ZMod r)+(B₁*(t:ZMod r)+C₁) := by
    have hcv : ((c k).val:ℤ)=(r:ℤ)*k.val := by simp only [c,Nat.cast_mul]
    have he : a*(c k).val+b=(r:ℤ)*(a*k.val+z) := by rw [hcv,hz]; ring
    have hn : ¬(r:ℤ)∣a*k.val+z := by
      intro hd
      apply hk
      simpa only [Int.cast_add,Int.cast_mul,Int.cast_natCast] using
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ r).mpr hd
    have hr0 : (r:ℤ)≠0 := Int.natCast_ne_zero.mpr hp.ne_zero
    have hn2 : ¬(r:ℤ)^2∣a*(c k).val+b := by
      intro hd
      apply hn
      apply (Int.mul_dvd_mul_iff_left hr0).mp
      simpa only [he,pow_two] using hd
    have ht' := (arithmetic_tests r _ a b hab ht (c k)).2 ⟨a*k.val+z,he⟩ hn2
    simp only [one_mul] at ht'
    rw [he,Int.mul_ediv_cancel_left _ hr0,hcv] at ht'
    simp only [Int.cast_add,Int.cast_mul,Int.cast_natCast] at ht'
    have hh := hH₁.2 (c k) (t+k.val) (by simpa [c] using htnonzero k)
    simp only [arithmeticReparametrize,zero_mul,add_zero] at hh
    have hearg : (r:ℤ)*(t+k.val)=(r:ℤ)*k.val+(r:ℤ)*t := by ring
    rw [hearg] at hh
    have heq := ht'.symm.trans hh
    simpa [c,mul_add,add_assoc,add_comm,add_left_comm] using heq
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
    {V : (Fin N) → ℤ → (ZMod r)ˣ} {A B C : ZMod r}
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
    (hr : ArithmeticRule.wordWidth r ≤ N) (k : ℕ) :
    ∀ (V : (Fin N) → ℤ → (ZMod r)ˣ) (B : ZMod r), ArithmeticLineRule r V →
      B ≠ 0 → FullAffineApproximation V 0 B 0 →
      ∃ D E : ℤ, (r : ℤ) ∣ D ∧ (r : ℤ) ∣ E ∧
        ∀ (n : (Fin N)) (m : ℤ), m - D * n.val - E ≠ 0 →
          padicValInt r (m - D * n.val - E) ≤ k →
          (V n m).val = B * (lastDigit r hp (m - D * n.val - E)).val := by
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
      let s := t - u * (n.val : ℤ) - v
      have he : (r : ℤ) * t - D' * n.val - E' =
          (r : ℤ) * (s - D * n.val - E) := by dsimp [D', E', s]; ring
      have hnz : s - D * n.val - E ≠ 0 := by
        intro hz
        apply hm
        rw [he, hz, mul_zero]
      have hv' : padicValInt r (s - D * n.val - E) ≤ k := by
        rw [he, padicValInt.mul hr0 hnz, padicValInt_self] at hval
        omega
      have hh := hdepth n s hnz hv'
      have harg : (r : ℤ) * (1 * s + u * n.val + v) + 0 * n.val + 0 = r * t := by
        dsimp [s]; ring
      simp only [S₀, S, arithmeticReparametrize, harg] at hh
      rw [he, show (r : ℤ) * (s - D * n.val - E) =
        (r : ℤ) ^ 1 * (s - D * n.val - E) by rw [pow_one], lastDigit_mul_prime_pow]
      exact hh
    · have hDc : (D' : ZMod r) = 0 := by simp [D']
      have hEc : (E' : ZMod r) = 0 := by simp [E']
      have hzc : ((m - D' * n.val - E' : ℤ) : ZMod r) = (m : ZMod r) := by
        simp only [Int.cast_sub, Int.cast_mul, Int.cast_natCast, hDc, hEc, zero_mul, sub_zero]
      have hm0 : (m : ZMod r) ≠ 0 := by
        simpa only [ne_eq, ZMod.intCast_zmod_eq_zero_iff_dvd] using hmd
      have hznd : ¬ (r : ℤ) ∣ m - D' * n.val - E' := by
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
    (hr : ArithmeticRule.wordWidth r ≤ N) (V : (Fin N) → ℤ → (ZMod r)ˣ)
    (hV : ArithmeticLineRule r V) (hcols : ∀ n, ∃ m m', V n m ≠ V n m') (k : ℕ) :
    ∃ (D E : ℤ) (B : ZMod r), B ≠ 0 ∧
      ∀ (n : (Fin N)) (m : ℤ), m - D * n.val - E ≠ 0 →
        padicValInt r (m - D * n.val - E) ≤ k →
        (V n m).val = B * (lastDigit r hp (m - D * n.val - E)).val := by
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
  let s := m - u * (n.val : ℤ) - v
  have he : s - D * n.val - E = m - (u + D) * n.val - (v + E) := by
    dsimp [s]; ring
  have hh := hdepth n s (by rwa [he]) (by rwa [he])
  have harg : 1 * s + u * n.val + v = m := by dsimp [s]; ring
  simpa only [V₀, arithmeticReparametrize, harg, he] using hh


end
end TranslationTiling.Sudoku.SparseArithmetic
