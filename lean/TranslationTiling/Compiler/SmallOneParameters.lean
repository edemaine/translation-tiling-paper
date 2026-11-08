import TranslationTiling.Compiler.PolynomialPrimes

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace TranslationTiling.Compiler.Size

open scoped Classical BigOperators
open Effective
noncomputable section

/-- Quadratically bounded ranks also keep the fixed useful-prime table small. -/
theorem exists_small_useful : ∃ u : UsefulTag → ℕ,
    Function.Injective u ∧
    (∀ i, (u i).Prime ∧ u i ≤ 10 ^ 40 ∧ u i ≠ Sudoku.p ∧ u i ≠ Sudoku.q) ∧
    (∀ t : Fin 2, u (.inl (.inr t)) = t.val + 2) ∧
    ∀ t : Fin 2, residueModulus ^ 2 < u (.inr (.inr t)) := by
  let Fresh := Sudoku.Column ⊕ FixedChannel
  let ix : Fresh ≃ Fin (Fintype.card Fresh) := Fintype.equivFin Fresh
  let f (i : Fresh) := Nat.nth Nat.Prime (usefulStart + (ix i).val)
  have hfprime (i : Fresh) : (f i).Prime := Nat.prime_nth_prime _
  have hfgt (i : Fresh) : usefulStart < f i := by
    have := Nat.add_two_le_nth_prime (usefulStart + (ix i).val)
    dsimp [f]
    omega
  have hfinj : Function.Injective f := by
    intro i j hij
    apply ix.injective
    apply Fin.ext
    have h := (Nat.nth_strictMono Nat.infinite_setOfPred_prime).injective hij
    change usefulStart + (ix i).val = usefulStart + (ix j).val at h
    omega
  have hfbound (i : Fresh) : f i ≤ 10 ^ 40 := by
    have hc : Fintype.card Fresh ≤ 2 * channelCount := by
      change Fintype.card (Sudoku.Column ⊕ FixedChannel) ≤ _
      rw [Fintype.card_sum]
      change Fintype.card Sudoku.Column + channelCount ≤ _
      rw [channelCount_eq, residueModulus_eq]
      simp only [Fintype.card_eq_nat_card, Nat.card_fin]
      omega
    have hrank := (ix i).isLt
    have h : usefulStart + (ix i).val + 1 ≤ usefulStart + 2 * channelCount + 1 := by omega
    apply (nth_prime_le_square _).trans
    apply (Nat.pow_le_pow_left (Nat.mul_le_mul_left 8 h) 2).trans
    norm_num [usefulStart, channelCount_eq, residueModulus_eq, Sudoku.Width, Sudoku.p, Sudoku.q]
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
  refine ⟨u, (hseedinj.sumElim hfinj hsep).comp e.injective, ?_, fun _ => rfl, ?_⟩
  · intro i
    dsimp only [u, Function.comp_apply]
    cases h : e i with
    | inl t =>
      have ht := t.isLt
      simp only [Sum.elim_inl]
      refine ⟨?_, by norm_num; omega, ?_, ?_⟩
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
    change residueModulus ^ 2 < f (.inr (.inr t))
    have h := hfgt (.inr (.inr t))
    unfold usefulStart at h
    omega

/-- Explicit prime budgets for one distinct tile, still using the full reduction. -/
theorem exists_small_one_parameters (T : LeanWang.TileSet) (hT : T.length = 1) :
    ∃ E : EncodingParameters T,
      (∀ i, E.a i ≤ 10 ^ 40 ∧ E.b i ≤ 10 ^ 40) ∧
      ∀ i j, E.digitPrime i j ≤ 10 ^ 164 := by
  obtain ⟨u, huinj, hu, hseed, hseedlarge⟩ := exists_small_useful
  let Tags := Σ i : Channel T, Label T i
  let ix : Tags ≃ Fin (Fintype.card Tags) := Fintype.equivFin Tags
  let g (j : Tags) := Nat.nth Nat.Prime (primeThreshold (10 ^ 40) + (ix j).val)
  apply exists_parameters_of_bounded_families T (10 ^ 40) (10 ^ 164)
    u huinj hu hseed hseedlarge g (fun _ => Nat.prime_nth_prime _)
  · intro j
    have := Nat.add_two_le_nth_prime (primeThreshold (10 ^ 40) + (ix j).val)
    change primeThreshold (10 ^ 40) <
      Nat.nth Nat.Prime (primeThreshold (10 ^ 40) + (ix j).val)
    omega
  · intro i j hij
    apply ix.injective
    apply Fin.ext
    have h := (Nat.nth_strictMono Nat.infinite_setOfPred_prime).injective hij
    change primeThreshold (10 ^ 40) + (ix i).val =
      primeThreshold (10 ^ 40) + (ix j).val at h
    omega
  · intro j
    have hcard : Fintype.card Tags ≤ channelCount * labelsBound T.length := by
      rw [Fintype.card_sigma]
      calc
        _ ≤ ∑ i : Channel T, labelsBound T.length :=
          Finset.sum_le_sum (fun i _ => label_card_le T i)
        _ = _ := by simp [channelCount]
    rw [hT] at hcard
    have hrank := (ix j).isLt
    have h : primeThreshold (10 ^ 40) + (ix j).val + 1 ≤
        primeThreshold (10 ^ 40) + channelCount * labelsBound 1 + 1 := by omega
    apply (nth_prime_le_square _).trans
    apply (Nat.pow_le_pow_left (Nat.mul_le_mul_left 8 h) 2).trans
    norm_num [primeThreshold, channelCount_eq, residueModulus_eq, Sudoku.Width,
      Sudoku.p, Sudoku.q, labelsBound, arithmeticAlphabet]

end
end TranslationTiling.Compiler.Size
