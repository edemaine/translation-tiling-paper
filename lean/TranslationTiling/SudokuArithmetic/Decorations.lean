import TranslationTiling.SudokuArithmetic.WordCoefficients

/-! Constant arithmetic rows have constant Wang decoration. -/

namespace TranslationTiling.Sudoku

theorem constant_word_coefficients (r : ℕ) (hp : r.Prime) (hlarge : 200 < r)
    (V : Column → (ZMod r)ˣ) (a b : ℤ)
    (hab : ¬ (r : ℤ) ∣ a ∨ ¬ (r : ℤ) ∣ b)
    (ht : ∀ n u, lowValuation r (a * n.val + b) = some u → u ≤ threshold r a →
      (V n).val = lowDigit r (a * n.val + b))
    (c : ZMod r) (hc : c ≠ 0) (hvals : ∀ n, (V n).val = c) :
    (a : ZMod r) = 0 ∧ (b : ZMod r) = c := by
  apply word_coefficients_from_four r hp hlarge V a b hab
    (fun n => (arithmetic_tests r V a b hab ht n).1) 0 c (Or.inr hc)
  intro k _
  simpa only [zero_mul, zero_add] using hvals (sample k)

theorem lowValuation_zero_of_cast_ne (r : ℕ) (z : ℤ) (hz : (z : ZMod r) ≠ 0) :
    lowValuation r z = some 0 := by
  have hn : ¬ (r : ℤ) ∣ z := by
    simpa only [ne_eq, ZMod.intCast_zmod_eq_zero_iff_dvd] using hz
  simp only [lowValuation, if_pos hn]

theorem constant_arithmetic_decoration {T : LeanWang.TileSet}
    (w : Column → Symbol T) (hw : Allowed T w) (cₚ : ZMod p) (cᵩ : ZMod q)
    (hp : cₚ ≠ 0) (hq : cᵩ ≠ 0)
    (hₚ : ∀ n, (w n).1.val = cₚ) (hᵩ : ∀ n, (w n).2.1.val = cᵩ) :
    ∀ n n', (w n).2.2 = (w n').2.2 := by
  obtain ⟨a, b, ha, hb, σ, hσ, ht⟩ := hw
  obtain ⟨hap, hbp⟩ := constant_word_coefficients p (by decide) (by decide) _ a b ha
    (fun n u hn hs => (ht n).1 u hn hs) cₚ hp hₚ
  obtain ⟨haq, hbq⟩ := constant_word_coefficients q (by decide) (by decide) _ a b hb
    (fun n u hn hs => (ht n).2.1 u hn hs) cᵩ hq hᵩ
  have hzero (r : ℕ) (c : ZMod r) (hc : c ≠ 0)
      (hA : (a : ZMod r) = 0) (hB : (b : ZMod r) = c) (n : Column) :
      lowValuation r (a * n.val + b) = some 0 := by
    apply lowValuation_zero_of_cast_ne
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_natCast, hA, hB,
      zero_mul, zero_add] using hc
  have hdecor (n : Column) := (ht n).2.2 0 0
    (hzero p cₚ hp hap hbp n) (hzero q cᵩ hq haq hbq n) (Nat.zero_le _) (Nat.zero_le _)
  intro n n'
  exact (hdecor n).trans (hdecor n').symm

def CanonicalArithmetic (r : ℕ) (hp : r.Prime)
    (V : Column → ℤ → (ZMod r)ˣ) (B : ZMod r) (k : ℕ) : Prop :=
  B ≠ 0 ∧ ∀ (n : Column) (m : ℤ), m ≠ 0 → padicValInt r m ≤ k →
    (V n m).val = B * (lastDigit r hp m).val

theorem canonical_row_decoration {T : LeanWang.TileSet} {W : Array T}
    (hW : LineRule W) {Bₚ : ZMod p} {Bᵩ : ZMod q} {k l : ℕ}
    (hₚ : CanonicalArithmetic p (by decide) (fun n m => (W n m).1) Bₚ k)
    (hᵩ : CanonicalArithmetic q (by decide) (fun n m => (W n m).2.1) Bᵩ l)
    (m : ℤ) (hm : m ≠ 0) (hp : padicValInt p m ≤ k) (hq : padicValInt q m ≤ l) :
    ∀ n n', (W n m).2.2 = (W n' m).2.2 := by
  apply constant_arithmetic_decoration (fun n => W n m)
    (by simpa only [zero_mul, zero_add] using hW 0 m)
    (Bₚ * (lastDigit p (by decide) m).val) (Bᵩ * (lastDigit q (by decide) m).val)
  · let : Fact p.Prime := ⟨by decide⟩
    exact mul_ne_zero hₚ.1 (Units.ne_zero _)
  · let : Fact q.Prime := ⟨by decide⟩
    exact mul_ne_zero hᵩ.1 (Units.ne_zero _)
  · exact fun n => hₚ.2 n m hm hp
  · exact fun n => hᵩ.2 n m hm hq

end TranslationTiling.Sudoku
