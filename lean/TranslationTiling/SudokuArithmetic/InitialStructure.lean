import TranslationTiling.SudokuArithmetic.Projection
import TranslationTiling.SudokuArithmetic.WordObstruction

/-! The initial affine structure on the entire decorated Sudoku board. -/

set_option maxRecDepth 2000

namespace TranslationTiling.Sudoku

def FullAffineApproximation {r : ℕ} (V : Column → ℤ → (ZMod r)ˣ)
    (A B C : ZMod r) : Prop :=
  (A ≠ 0 ∨ B ≠ 0 ∨ C ≠ 0) ∧ ∀ (n : Column) (m : ℤ),
    A * (n.val : ZMod r) + B * (m : ZMod r) + C ≠ 0 →
    (V n m).val = A * (n.val : ZMod r) + B * (m : ZMod r) + C

theorem FullAffineApproximation.restrict {r : ℕ} {V : Column → ℤ → (ZMod r)ˣ}
    {A B C : ZMod r} (h : FullAffineApproximation V A B C) (hr : r ^ 2 ≤ Width) :
    ArithmeticRule.AffineApproximation (arithmeticRestriction r hr V) A B C :=
  ⟨h.1, fun n m hn => h.2 (smallColumn r hr n) m hn⟩

open ArithmeticRule in
theorem arithmeticLineRule_affine (r : ℕ) (V : Column → ℤ → (ZMod r)ˣ)
    (hV : ArithmeticLineRule r V) (d e : ℤ) :
    ∃ a b : ZMod r, (a ≠ 0 ∨ b ≠ 0) ∧ ∀ n : Column,
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

/-- The affine approximation obtained on the first `r²` columns extends along
rows to the whole board. -/
theorem arithmetic_initial_affine (r : ℕ) (hr : r ^ 2 ≤ Width)
    (hp : r.Prime) (hlarge : 200 < r) (V : Column → ℤ → (ZMod r)ˣ)
    (hV : ArithmeticLineRule r V) :
    ∃ A B C : ZMod r, FullAffineApproximation V A B C := by
  let : Fact r.Prime := ⟨hp⟩
  obtain ⟨A, B, C, hH⟩ := ArithmeticRule.global_affine_approximation hp hlarge
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

theorem arithmetic_initial_structure (r : ℕ) (hr : r ^ 2 ≤ Width)
    (hp : r.Prime) (hlarge : 200 < r) (V : Column → ℤ → (ZMod r)ˣ)
    (hV : ArithmeticLineRule r V) (hcols : ∀ n, ∃ m m', V n m ≠ V n m') :
    ∃ A B C : ZMod r, B ≠ 0 ∧ ∀ (n : Column) (m : ℤ),
      A * (n.val : ZMod r) + B * (m : ZMod r) + C ≠ 0 →
      (V n m).val = A * (n.val : ZMod r) + B * (m : ZMod r) + C := by
  obtain ⟨A, B, C, hH⟩ := arithmetic_initial_affine r hr hp hlarge V hV
  have hB := (ArithmeticRule.nonconstantColumns_iff_vertical_coefficient hp hlarge
    (hH.restrict hr)).mp (arithmeticRestriction_nonconstant r hr V hcols)
  exact ⟨A, B, C, hB, hH.2⟩

theorem decorated_initial_structure {T : LeanWang.TileSet} (W : Array T)
    (hW : LineRule W) (hcols : NonconstantColumns W) :
    (∃ A B C : ZMod p, B ≠ 0 ∧ ∀ (n : Column) (m : ℤ),
      A * (n.val : ZMod p) + B * (m : ZMod p) + C ≠ 0 →
      (W n m).1.val = A * (n.val : ZMod p) + B * (m : ZMod p) + C) ∧
    (∃ A B C : ZMod q, B ≠ 0 ∧ ∀ (n : Column) (m : ℤ),
      A * (n.val : ZMod q) + B * (m : ZMod q) + C ≠ 0 →
      (W n m).2.1.val = A * (n.val : ZMod q) + B * (m : ZMod q) + C) :=
  ⟨arithmetic_initial_structure p (by decide) (by decide) (by decide) _
      (arithmeticLineRule_p hW) hcols.1,
    arithmetic_initial_structure q (by decide) (by decide) (by decide) _
      (arithmeticLineRule_q hW) hcols.2⟩

end TranslationTiling.Sudoku
