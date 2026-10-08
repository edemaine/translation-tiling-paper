import TranslationTiling.External.Sudoku
import TranslationTiling.SudokuArithmetic.WordRule

/-! Arithmetic projections of the decorated Sudoku rule. -/

namespace TranslationTiling.Sudoku

/-- One arithmetic component on the full decorated board. -/
def ArithmeticLineRule (r : ℕ) (V : Column → ℤ → (ZMod r)ˣ) : Prop :=
  ∀ d e : ℤ, ∃ a b : ℤ,
    (¬ (r : ℤ) ∣ a ∨ ¬ (r : ℤ) ∣ b) ∧
    ∀ n u, lowValuation r (a * n.val + b) = some u → u ≤ threshold r a →
      (V n (d * n.val + e)).val = lowDigit r (a * n.val + b)

theorem arithmeticLineRule_p {T : LeanWang.TileSet} {W : Array T} (hW : LineRule W) :
    ArithmeticLineRule p (fun n m => (W n m).1) := by
  intro d e
  obtain ⟨a, b, hp, _, σ, _, hw⟩ := hW d e
  exact ⟨a, b, hp, fun n u hu hs => (hw n).1 u hu hs⟩

theorem arithmeticLineRule_q {T : LeanWang.TileSet} {W : Array T} (hW : LineRule W) :
    ArithmeticLineRule q (fun n m => (W n m).2.1) := by
  intro d e
  obtain ⟨a, b, _, hq, σ, _, hw⟩ := hW d e
  exact ⟨a, b, hq, fun n u hu hs => (hw n).2.1 u hu hs⟩

/-- On a primitive line, valuation one can occur only when the slope is a unit. -/
theorem primitive_slope_not_dvd (r : ℕ) (a b n : ℤ)
    (hprim : ¬ (r : ℤ) ∣ a ∨ ¬ (r : ℤ) ∣ b) (ht : (r : ℤ) ∣ a * n + b) :
    ¬ (r : ℤ) ∣ a := by
  intro ha
  have hb : (r : ℤ) ∣ b := by
    have h := dvd_sub ht (dvd_mul_of_dvd_left ha n)
    simpa only [add_sub_cancel_left] using h
  exact hprim.elim (fun h => h ha) (fun h => h hb)

theorem arithmetic_tests (r : ℕ) (V : Column → (ZMod r)ˣ) (a b : ℤ)
    (hprim : ¬ (r : ℤ) ∣ a ∨ ¬ (r : ℤ) ∣ b)
    (hV : ∀ n u, lowValuation r (a * n.val + b) = some u → u ≤ threshold r a →
      (V n).val = lowDigit r (a * n.val + b)) (n : Column) :
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

def smallColumn (r : ℕ) (hr : r ^ 2 ≤ Width) (n : ArithmeticRule.Column r) : Column :=
  ⟨n.val, n.isLt.trans_le hr⟩

def arithmeticRestriction (r : ℕ) (hr : r ^ 2 ≤ Width)
    (V : Column → ℤ → (ZMod r)ˣ) : ArithmeticRule.WordArray r :=
  fun n m => V (smallColumn r hr n) m

theorem arithmeticRestriction_lineRule (r : ℕ) (hr : r ^ 2 ≤ Width)
    (V : Column → ℤ → (ZMod r)ˣ) (hV : ArithmeticLineRule r V) :
    ArithmeticRule.LineRule r (arithmeticRestriction r hr V) := by
  intro d e
  obtain ⟨a, b, hab, ht⟩ := hV d e
  refine ⟨a, b, hab, ?_⟩
  intro n
  exact arithmetic_tests r (fun n => V n (d * n.val + e)) a b hab ht (smallColumn r hr n)

theorem arithmeticRestriction_nonconstant (r : ℕ) (hr : r ^ 2 ≤ Width)
    (V : Column → ℤ → (ZMod r)ˣ)
    (hV : ∀ n, ∃ m m', V n m ≠ V n m') :
    ArithmeticRule.NonconstantColumns (arithmeticRestriction r hr V) :=
  fun n => hV (smallColumn r hr n)

end TranslationTiling.Sudoku
