import TranslationTiling.Compiler.SizeBound
import Mathlib.NumberTheory.Bertrand
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.SetTheory.Cardinal.Finite

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace TranslationTiling.Compiler.Size

open scoped Classical
open Effective
noncomputable section

theorem primeAbove_succ_le (b : ℕ) : primeAbove (b + 1) ≤ 2 * (b + 1) := by
  obtain ⟨q, hq, hlarge, hsmall⟩ := Nat.bertrand (b + 1) (by omega)
  have hmin : primeAbove (b + 1) ≤ q := by
    unfold primeAbove
    rw [leastWitness_eq_find]
    exact Nat.find_min' _ ⟨hq, by omega⟩
  exact hmin.trans hsmall

theorem primeSequence_le (b k : ℕ) :
    EncodingPrimeSelection.primeSequence b k ≤ 4 ^ (k + 1) * (b + 1) := by
  induction k with
  | zero =>
    change primeAbove (b + 1) ≤ _
    have h := primeAbove_succ_le b
    simp only [Nat.zero_add, pow_one]
    omega
  | succ k ih =>
    change primeAbove (EncodingPrimeSelection.primeSequence b k + 1) ≤ _
    have h := primeAbove_succ_le (EncodingPrimeSelection.primeSequence b k)
    have hp := (EncodingPrimeSelection.primeSequence_prime b k).two_le
    rw [show k + 1 + 1 = (k + 1) + 1 from rfl, pow_succ]
    nlinarith

def channelCount : ℕ := Fintype.card FixedChannel

theorem channelCount_eq : channelCount = residueModulus + 2 := by
  rw [residueModulus_eq]
  change Fintype.card (Fin Sudoku.Width ⊕ Fin 2) = Sudoku.Width + 2
  simp only [Fintype.card_eq_nat_card, Nat.card_sum, Nat.card_fin]

def usefulStart : ℕ := residueModulus ^ 2 + Sudoku.p + Sudoku.q + 3
def usefulCap : ℕ := 4 ^ (2 * channelCount + 1) * (usefulStart + 1)
def digitStart : ℕ := usefulCap ^ 2 + 2 * usefulCap + Sudoku.p + Sudoku.q + 3

/-- An explicitly bounded fixed useful-prime table, including the two seed
primes 2 and 3. All constants here are literal arithmetic expressions. -/
theorem exists_bounded_useful : ∃ u : UsefulTag → ℕ,
    Function.Injective u ∧
    (∀ i, (u i).Prime ∧ u i ≤ usefulCap ∧ u i ≠ Sudoku.p ∧ u i ≠ Sudoku.q) ∧
    (∀ t : Fin 2, u (.inl (.inr t)) = t.val + 2) ∧
    ∀ t : Fin 2, residueModulus ^ 2 < u (.inr (.inr t)) := by
  let Fresh := Sudoku.Column ⊕ FixedChannel
  let ix : Fresh ≃ Fin (Fintype.card Fresh) := Fintype.equivFin Fresh
  let f (i : Fresh) := EncodingPrimeSelection.primeSequence usefulStart (ix i).val
  have hfprime (i : Fresh) : (f i).Prime := EncodingPrimeSelection.primeSequence_prime _ _
  have hfgt (i : Fresh) : usefulStart < f i := EncodingPrimeSelection.primeSequence_gt _ _
  have hfinj : Function.Injective f := by
    intro i j h
    exact ix.injective (Fin.ext ((EncodingPrimeSelection.primeSequence_strictMono _).injective h))
  let e : UsefulTag ≃ Fin 2 ⊕ Fresh :=
    (Equiv.sumCongr (Equiv.sumComm Sudoku.Column (Fin 2))
      (Equiv.refl FixedChannel)).trans (Equiv.sumAssoc (Fin 2) Sudoku.Column FixedChannel)
  let u : UsefulTag → ℕ := Sum.elim (fun t : Fin 2 => t.val + 2) f ∘ e
  have hseedinj : Function.Injective (fun t : Fin 2 => t.val + 2) := by
    intro t s h
    change t.val + 2 = s.val + 2 at h
    exact Fin.ext (by omega)
  have hsep (t : Fin 2) (i : Fresh) : t.val + 2 ≠ f i := by
    have ht := t.isLt
    have hf := hfgt i
    unfold usefulStart at hf
    omega
  have hU : 4 ≤ usefulCap := by
    have hpow : 4 ≤ 4 ^ (2 * channelCount + 1) := by
      simpa only [pow_one] using Nat.pow_le_pow_right (by decide : 1 ≤ 4)
        (by omega : 1 ≤ 2 * channelCount + 1)
    apply hpow.trans
    change 4 ^ (2 * channelCount + 1) ≤
      4 ^ (2 * channelCount + 1) * (usefulStart + 1)
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left (4 ^ (2 * channelCount + 1))
      (Nat.succ_pos usefulStart)
  have hfbound (i : Fresh) : f i ≤ usefulCap := by
    have hcard : Fintype.card Fresh ≤ 2 * channelCount := by
      change Fintype.card (Sudoku.Column ⊕ FixedChannel) ≤ _
      rw [Fintype.card_sum]
      change Fintype.card Sudoku.Column + channelCount ≤ _
      have hc : channelCount = Fintype.card Sudoku.Column + 2 := by
        change Fintype.card (Sudoku.Column ⊕ Fin 2) = _
        simp only [Fintype.card_eq_nat_card, Nat.card_sum, Nat.card_fin]
      omega
    have hrank : (ix i).val + 1 ≤ 2 * channelCount + 1 := by
      have := (ix i).isLt
      omega
    exact (primeSequence_le usefulStart _).trans
      (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) hrank))
  refine ⟨u, (hseedinj.sumElim hfinj hsep).comp e.injective, ?_, fun _ => rfl, ?_⟩
  · intro i
    dsimp only [u, Function.comp_apply]
    cases h : e i with
    | inl t =>
      have ht := t.isLt
      simp only [Sum.elim_inl]
      refine ⟨?_, by omega, ?_, ?_⟩
      · fin_cases t <;> norm_num
      · have hp : 200 < Sudoku.p := by decide
        omega
      · have hq : 200 < Sudoku.q := by decide
        omega
    | inr j =>
      have hj := hfgt j
      simp only [Sum.elim_inr]
      refine ⟨hfprime j, hfbound j, ?_, ?_⟩ <;> unfold usefulStart at hj <;> omega
  · intro t
    exact (by have h := hfgt (.inr (.inr t)); unfold usefulStart at h; exact lt_of_le_of_lt (by omega) h)

end
end TranslationTiling.Compiler.Size
