import TranslationTiling.FiniteCompiler.EncodingParameters
import TranslationTiling.Compiler.PolynomialPrimes

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace TranslationTiling.FiniteCompiler

open scoped Classical BigOperators
noncomputable section

abbrev UsefulTag (T : System) := Channel T ⊕ Channel T
def channelCount (T : System) := T.width + 2
def usefulStart : ℕ := residueModulus ^ 2 + Sudoku.p + Sudoku.q + 3
def usefulPrimeCap (C : ℕ) := (8 * (usefulStart + 2 * C + 1)) ^ 2
def primeThreshold (U : ℕ) := U ^ 2 + 2 * U + Sudoku.p + Sudoku.q + 3
def digitPrimeCap (B C : ℕ) :=
  (8 * (primeThreshold (usefulPrimeCap C) + C * (B + 1) + 1)) ^ 2

theorem channel_card (T : System) : Fintype.card (Channel T) = channelCount T := by
  simp [Channel, Column, channelCount]

theorem label_card_le (T : System) (i : Channel T) :
    Fintype.card (Label T i) ≤ T.alphabet + 1 := by
  cases i <;> simp [Label, Symbol]

theorem exists_useful_parameters (T : System) : ∃ u : UsefulTag T → ℕ,
    Function.Injective u ∧
    (∀ i, (u i).Prime ∧ u i ≤ usefulPrimeCap (channelCount T) ∧
      u i ≠ Sudoku.p ∧ u i ≠ Sudoku.q) ∧
    (∀ t : Fin 2, u (.inl (.inr t)) = t.val + 2) ∧
    ∀ t : Fin 2, residueModulus ^ 2 < u (.inr (.inr t)) := by
  let Fresh := Column T ⊕ Channel T
  let ix : Fresh ≃ Fin (Fintype.card Fresh) := Fintype.equivFin Fresh
  let f (i : Fresh) := Nat.nth Nat.Prime (usefulStart + (ix i).val)
  have hfprime (i : Fresh) : (f i).Prime := Nat.prime_nth_prime _
  have hfgt (i : Fresh) : usefulStart < f i := by
    have := Nat.add_two_le_nth_prime (usefulStart + (ix i).val)
    dsimp [f]; omega
  have hfinj : Function.Injective f := by
    intro i j hij
    apply ix.injective
    apply Fin.ext
    have h := (Nat.nth_strictMono Nat.infinite_setOfPred_prime).injective hij
    change usefulStart + (ix i).val = usefulStart + (ix j).val at h
    omega
  have hfbound (i : Fresh) : f i ≤ usefulPrimeCap (channelCount T) := by
    have hc : Fintype.card Fresh ≤ 2 * channelCount T := by
      simp [Fresh, Column, Channel, channelCount]; omega
    have hrank := (ix i).isLt
    apply (Compiler.Size.nth_prime_le_square _).trans
    apply Nat.pow_le_pow_left _ 2
    apply Nat.mul_le_mul_left
    omega
  let e : UsefulTag T ≃ Fin 2 ⊕ Fresh :=
    (Equiv.sumCongr (Equiv.sumComm (Column T) (Fin 2))
      (Equiv.refl (Channel T))).trans (Equiv.sumAssoc (Fin 2) (Column T) (Channel T))
  let u : UsefulTag T → ℕ := Sum.elim (fun t : Fin 2 => t.val + 2) f ∘ e
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
      refine ⟨?_, ?_, ?_, ?_⟩
      · fin_cases t <;> norm_num
      · have hcap : 4 ≤ usefulPrimeCap (channelCount T) := by
          unfold usefulPrimeCap
          have : 1 ≤ usefulStart + 2 * channelCount T + 1 := by omega
          nlinarith [Nat.mul_le_mul_left 8 this]
        omega
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

theorem exists_parameters_of_bounded_families (T : System) (U Q : ℕ)
    (u : UsefulTag T → ℕ) (huinj : Function.Injective u)
    (hu : ∀ i, (u i).Prime ∧ u i ≤ U ∧ u i ≠ Sudoku.p ∧ u i ≠ Sudoku.q)
    (hseed : ∀ t : Fin 2, u (.inl (.inr t)) = t.val + 2)
    (hseedlarge : ∀ t : Fin 2, residueModulus ^ 2 < u (.inr (.inr t)))
    (g : (Σ i : Channel T, Label T i) → ℕ)
    (hgprime : ∀ j, (g j).Prime) (hggt : ∀ j, primeThreshold U < g j)
    (hginj : Function.Injective g) (hbound : ∀ j, g j ≤ Q) :
    ∃ E : EncodingParameters T,
      (∀ i, E.a i ≤ U ∧ E.b i ≤ U) ∧ ∀ i j, E.digitPrime i j ≤ Q := by
  let Tags := Σ i : Channel T, Label T i
  have hsep (t : UsefulTag T) (j : Tags) : u t ≠ g j := by
    have ht := (hu t).2.1
    have hj := hggt j
    unfold primeThreshold at hj
    omega
  let primes : PrimeTag T → ℕ := Sum.elim u g ∘
    (Equiv.sumAssoc (Channel T) (Channel T) Tags).symm
  have hpinj : Function.Injective primes :=
    (huinj.sumElim hginj hsep).comp
      (Equiv.sumAssoc (Channel T) (Channel T) Tags).symm.injective
  have hpprime (j : PrimeTag T) : (primes j).Prime := by
    rcases j with i | (i | j)
    · exact (hu _).1
    · exact (hu _).1
    · exact hgprime _
  have hpne (v : ℕ) (hv : v = Sudoku.p ∨ v = Sudoku.q) (j : PrimeTag T) :
      primes j ≠ v := by
    rcases j with i | (i | j)
    · rcases hv with rfl | rfl
      · exact (hu (.inl i)).2.2.1
      · exact (hu (.inl i)).2.2.2
    · rcases hv with rfl | rfl
      · exact (hu (.inr i)).2.2.1
      · exact (hu (.inr i)).2.2.2
    · change g j ≠ v
      have h := hggt j
      unfold primeThreshold at h
      rcases hv with rfl | rfl <;> omega
  have hrepr (i : Channel T) (j : Label T i) : ∃ A B : ℕ,
      0 < A ∧ 0 < B ∧ g ⟨i, j⟩ = A * u (.inl i) + B * u (.inr i) := by
    have ha := (hu (.inl i)).1
    have hb := (hu (.inr i)).1
    have hcop : Nat.Coprime (u (.inl i)) (u (.inr i)) :=
      (Nat.coprime_primes ha hb).mpr (fun h => by have := huinj h; cases this)
    have haB := (hu (.inl i)).2.1
    have hbB := (hu (.inr i)).2.1
    have hm := Nat.mul_le_mul haB hbB
    have h := hggt ⟨i, j⟩
    unfold primeThreshold at h
    simp only [pow_two] at h
    exact Compiler.EncodingPrimeSelection.exists_positive_combination hcop
      ha.one_lt hb.one_lt (by omega)
  choose A B hA hB hrepr using hrepr
  let E : EncodingParameters T := {
    primeAt := primes
    prime_isPrime := hpprime
    prime_injective := hpinj
    prime_ne_p := hpne Sudoku.p (Or.inl rfl)
    prime_ne_q := hpne Sudoku.q (Or.inr rfl)
    seed_a_eq := hseed
    seed_b_large := fun t => by
      change Sudoku.Width ^ 2 < u (.inr (.inr t))
      simpa only [residueModulus_eq] using hseedlarge t
    blockA := A
    blockB := B
    blockA_pos := hA
    blockB_pos := hB
    digit_representation := hrepr
    digitProduct := fun i => ∏ j : Label T i, g ⟨i, j⟩
    digitProduct_eq := fun _ => rfl }
  exact ⟨E, fun i => ⟨(hu (.inl i)).2.1, (hu (.inr i)).2.1⟩,
    fun i j => hbound ⟨i, j⟩⟩

theorem exists_bounded_parameters (T : System) :
    ∃ E : EncodingParameters T,
      (∀ i, E.a i ≤ usefulPrimeCap (channelCount T) ∧
        E.b i ≤ usefulPrimeCap (channelCount T)) ∧
      ∀ i j, E.digitPrime i j ≤ digitPrimeCap T.alphabet (channelCount T) := by
  obtain ⟨u, huinj, hu, hseed, hseedlarge⟩ := exists_useful_parameters T
  let U := usefulPrimeCap (channelCount T)
  let Tags := Σ i : Channel T, Label T i
  let ix : Tags ≃ Fin (Fintype.card Tags) := Fintype.equivFin Tags
  let g (j : Tags) := Nat.nth Nat.Prime (primeThreshold U + (ix j).val)
  apply exists_parameters_of_bounded_families T U _ u huinj hu hseed hseedlarge
    g (fun _ => Nat.prime_nth_prime _)
  · intro j
    have := Nat.add_two_le_nth_prime (primeThreshold U + (ix j).val)
    change primeThreshold U < Nat.nth Nat.Prime (primeThreshold U + (ix j).val)
    omega
  · intro i j hij
    apply ix.injective
    apply Fin.ext
    have h := (Nat.nth_strictMono Nat.infinite_setOfPred_prime).injective hij
    change primeThreshold U + (ix i).val = primeThreshold U + (ix j).val at h
    omega
  · intro j
    have hcard : Fintype.card Tags ≤ channelCount T * (T.alphabet + 1) := by
      rw [Fintype.card_sigma]
      calc
        _ ≤ ∑ _i : Channel T, (T.alphabet + 1) :=
          Finset.sum_le_sum (fun i _ => label_card_le T i)
        _ = _ := by simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, channel_card]
    have hrank := (ix j).isLt
    apply (Compiler.Size.nth_prime_le_square _).trans
    apply Nat.pow_le_pow_left _ 2
    apply Nat.mul_le_mul_left
    change primeThreshold U + (ix j).val + 1 ≤
      primeThreshold U + channelCount T * (T.alphabet + 1) + 1
    omega

end
end TranslationTiling.FiniteCompiler
