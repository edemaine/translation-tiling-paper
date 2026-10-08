import TranslationTiling.Definitions
import Mathlib.Algebra.Field.ZMod

/-! Greenfeld–Tao, arXiv:2309.09504v2, Definition 5.1 and Proposition 5.2.
The finite low-valuation tests below give the paper's word rule without an
unbounded integer valuation. Soundness is proved in `SudokuArithmetic/Soundness`. -/

namespace TranslationTiling.Sudoku

abbrev p : ℕ := 211
abbrev q : ℕ := 223
abbrev Width : ℕ := p ^ 2 * q ^ 2
abbrev Column := Fin Width
abbrev Symbol (T : LeanWang.TileSet) := (ZMod p)ˣ × (ZMod q)ˣ × LeanWang.TileIn T
abbrev Array (T : LeanWang.TileSet) := Column → ℤ → Symbol T

def threshold (r : ℕ) (a : ℤ) : ℕ := if (r : ℤ) ∣ a then 0 else 1

/-- `some 0` and `some 1` are the two tested valuations; `none` means at least two. -/
def lowValuation (r : ℕ) (z : ℤ) : Option ℕ :=
  if ¬ (r : ℤ) ∣ z then some 0 else if ¬ (r : ℤ) ^ 2 ∣ z then some 1 else none

def lowDigit (r : ℕ) (z : ℤ) : ZMod r :=
  if (r : ℤ) ∣ z then ((z / r : ℤ) : ZMod r) else (z : ZMod r)

def ValidRectangle (T : LeanWang.TileSet) (w h : ℕ)
    (σ : Fin w → Fin h → LeanWang.TileIn T) : Prop :=
  (∀ u v (hu : u.val + 1 < w),
    LeanWang.WangTile.HMatches (σ u v).val (σ ⟨u.val + 1, hu⟩ v).val) ∧
  (∀ u v (hv : v.val + 1 < h),
    LeanWang.WangTile.VMatches (σ u v).val (σ u ⟨v.val + 1, hv⟩).val)

/-- A finite decorated rectangle witnesses the tested positions of a word. -/
def WordRectangle (T : LeanWang.TileSet) (w : Column → Symbol T) (a b : ℤ) (s t : ℕ)
    (σ : Fin (s + 1) → Fin (t + 1) → LeanWang.TileIn T) : Prop :=
      ValidRectangle T _ _ σ ∧ ∀ n,
        (∀ u, lowValuation p (a * n.val + b) = some u → u ≤ s →
          (w n).1.val = lowDigit p (a * n.val + b)) ∧
        (∀ v, lowValuation q (a * n.val + b) = some v → v ≤ t →
          (w n).2.1.val = lowDigit q (a * n.val + b)) ∧
        (∀ u v, lowValuation p (a * n.val + b) = some u →
          lowValuation q (a * n.val + b) = some v →
          ∀ (hu : u ≤ s) (hv : v ≤ t),
          (w n).2.2 = σ ⟨u, Nat.lt_succ_iff.mpr hu⟩ ⟨v, Nat.lt_succ_iff.mpr hv⟩)

/-- The word tests for one coefficient pair. -/
def AllowedCoefficients (T : LeanWang.TileSet) (w : Column → Symbol T) (a b : ℤ) : Prop :=
  (¬ (p : ℤ) ∣ a ∨ ¬ (p : ℤ) ∣ b) ∧
  (¬ (q : ℤ) ∣ a ∨ ¬ (q : ℤ) ∣ b) ∧
  ∃ σ, WordRectangle T w a b (threshold p a) (threshold q a) σ

/-- The decorated two-prime finite word rule, including the unrestricted high valuations. -/
def Allowed (T : LeanWang.TileSet) (w : Column → Symbol T) : Prop :=
  ∃ a b : ℤ, AllowedCoefficients T w a b

def LineRule {T : LeanWang.TileSet} (W : Array T) : Prop :=
  ∀ d e : ℤ, Allowed T (fun n => W n (d * n.val + e))

def NonconstantColumns {T : LeanWang.TileSet} (W : Array T) : Prop :=
  (∀ n, ∃ m m', (W n m).1 ≠ (W n m').1) ∧
  (∀ n, ∃ m m', (W n m).2.1 ≠ (W n m').2.1)

/-- The Sudoku soundness implication proved in `SudokuArithmetic/Soundness`. -/
def Soundness : Prop :=
  ∀ T (W : Array T), LineRule W → NonconstantColumns W →
    ∃ τ : ℕ × ℕ → LeanWang.TileIn T, LeanWang.ValidQuarterTiling T τ

end TranslationTiling.Sudoku
