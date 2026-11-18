import TranslationTiling.SudokuArithmetic.ShortWordRule

namespace TranslationTiling.Sudoku.ShortRule
open ArithmeticRule
open scoped Classical
noncomputable section
theorem allowed_affine {p : ℕ} {w : Word p} (hw : Allowed p w) :
    ∃ a b : ZMod p, (a ≠ 0 ∨ b ≠ 0) ∧
      ∀ n : Column p, a * (n.val : ZMod p) + b ≠ 0 →
        (w n : ZMod p) = a * (n.val : ZMod p) + b := by
  obtain ⟨a, b, hab, hw⟩ := hw
  refine ⟨(a : ZMod p), (b : ZMod p), ?_, ?_⟩
  · simpa only [ne_eq, ZMod.intCast_zmod_eq_zero_iff_dvd] using hab
  · intro n hn
    have hnd : ¬ (p : ℤ) ∣ a * (n.val : ℤ) + b := by
      intro hd
      apply hn
      have h := (ZMod.intCast_zmod_eq_zero_iff_dvd
        (a * (n.val : ℤ) + b) p).mpr hd
      simpa only [Int.cast_add, Int.cast_mul, Int.cast_natCast] using h
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_natCast] using (hw n).1 hnd

private def intColumn {p : ℕ} (n : ℤ) (hn : 0 ≤ n ∧ n < (wordWidth p : ℕ)) :
    Column p := ⟨n.toNat, by omega⟩

private theorem intColumn_val {p : ℕ} (n : ℤ)
    (hn : 0 ≤ n ∧ n < (wordWidth p : ℕ)) :
    ((intColumn n hn).val : ℤ) = n := Int.toNat_of_nonneg hn.1

private theorem intColumn_cast {p : ℕ} (n : ℤ)
    (hn : 0 ≤ n ∧ n < (wordWidth p : ℕ)) :
    ((intColumn n hn).val : ZMod p) = (n : ZMod p) := by
  simpa only [Int.cast_natCast] using
    congrArg (fun x : ℤ => (x : ZMod p)) (intColumn_val n hn)

def rawArray {p : ℕ} (W : WordArray p) (n m : ℤ) : ZMod p :=
  if hn : 0 ≤ n ∧ n < (wordWidth p : ℕ) then (W (intColumn n hn) m : ZMod p) else 1

theorem rawArray_column {p : ℕ} (W : WordArray p) (n : Column p) (m : ℤ) :
    rawArray W n.val m = (W n m : ZMod p) := by
  have hn : (0 : ℤ) ≤ n.val ∧ (n.val : ℤ) < (wordWidth p : ℕ) := by
    exact ⟨Int.natCast_nonneg _, by exact_mod_cast n.isLt⟩
  have hc : intColumn (n.val : ℤ) hn = n := by
    apply Fin.ext
    simp [intColumn]
  rw [rawArray, dif_pos hn, hc]

theorem rawArray_ne_zero {p : ℕ} [Fact p.Prime] (W : WordArray p)
    (n m : ℤ) (hn : 0 ≤ n ∧ n < (wordWidth p : ℕ)) : rawArray W n m ≠ 0 := by
  rw [rawArray, dif_pos hn]
  exact Units.ne_zero _

structure LineAffine {p : ℕ} (W : WordArray p) (d e : ℤ) where
  a : ZMod p
  b : ZMod p
  nonzero : a ≠ 0 ∨ b ≠ 0
  agrees : ∀ n : Column p, a * (n.val : ZMod p) + b ≠ 0 →
    (W n (d * (n.val : ℤ) + e) : ZMod p) = a * (n.val : ZMod p) + b

def chooseLine {p : ℕ} {W : WordArray p} (hW : LineRule p W)
    (d e : ℤ) : LineAffine W d e := by
  let h := allowed_affine (hW d e)
  exact ⟨h.choose, h.choose_spec.choose, h.choose_spec.choose_spec.1,
    h.choose_spec.choose_spec.2⟩

theorem LineAffine.raw_agrees {p : ℕ} {W : WordArray p} {d e : ℤ}
    (L : LineAffine W d e) (n : ℤ) (hn : 0 ≤ n ∧ n < (wordWidth p : ℕ))
    (hz : L.a * (n : ZMod p) + L.b ≠ 0) :
    rawArray W n (d * n + e) = L.a * (n : ZMod p) + L.b := by
  have h := L.agrees (intColumn n hn) (by simpa only [intColumn_cast] using hz)
  rw [intColumn_val, intColumn_cast] at h
  simpa only [rawArray, dif_pos hn] using h


end
end TranslationTiling.Sudoku.ShortRule
