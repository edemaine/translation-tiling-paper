import TranslationTiling.Compiler.ClosedUsefulPrimes

set_option maxRecDepth 10000

/-! Bounded admissible choices of the encoding primes. Unlike numeric color
codes, the ranks of the finite label sets depend only on their cardinality. -/

namespace TranslationTiling.Compiler.Size

open scoped Classical BigOperators
open Effective

noncomputable section

/-- Uniform label-count and channel-count constants. -/
def arithmeticAlphabet : ℕ := (Sudoku.p - 1) * (Sudoku.q - 1)
def labelsBound (n : ℕ) : ℕ := arithmeticAlphabet * n + 1

/-- Upper bound for every digit prime, with no prime-search operation remaining. -/
def digitPrimeBound (n : ℕ) : ℕ :=
  4 ^ (channelCount * labelsBound n + 1) * (digitStart + 1)

theorem symbols_length (T : LeanWang.TileSet) :
    (symbols T).length = arithmeticAlphabet * T.length := by
  simp only [symbols, List.length_flatMap, List.length_map, List.map_const',
    List.length_range, List.sum_replicate, smul_eq_mul]
  unfold arithmeticAlphabet
  ring

theorem label_card_le (T : LeanWang.TileSet) (i : Channel T) :
    Fintype.card (Label T i) ≤ labelsBound T.length := by
  cases i with
  | inl n =>
    have hsub : Finset.univ.image (rawSymbol (T := T)) ⊆ (symbols T).toFinset := by
      intro s hs
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hs
      exact List.mem_toFinset.mpr ((mem_symbols T _).mpr ⟨j, rfl⟩)
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ (rawSymbol_injective T), Finset.card_univ] at hcard
    have h := hcard.trans (List.toFinset_card_le (symbols T))
    rw [symbols_length] at h
    exact h.trans (Nat.le_succ _)
  | inr t => simp [Label, labelsBound]

/-- Digit-prime threshold for any useful-coordinate bound. -/
def primeThreshold (U : ℕ) : ℕ := U ^ 2 + 2 * U + Sudoku.p + Sudoku.q + 3

/-- Build parameters with independent bounds on the useful and digit primes. -/
theorem exists_parameters_of_bounded_families (T : LeanWang.TileSet) (U Q : ℕ)
    (u : UsefulTag → ℕ) (huinj : Function.Injective u)
    (hu : ∀ i, (u i).Prime ∧ u i ≤ U ∧ u i ≠ Sudoku.p ∧ u i ≠ Sudoku.q)
    (hseed : ∀ t : Fin 2, u (.inl (.inr t)) = t.val + 2)
    (hseedlarge : ∀ t : Fin 2, residueModulus ^ 2 < u (.inr (.inr t)))
    (g : (Σ i : Channel T, Label T i) → ℕ)
    (hgprime : ∀ j, (g j).Prime) (hggt : ∀ j, primeThreshold U < g j)
    (hginj : Function.Injective g) (hbound : ∀ j, g j ≤ Q) :
    ∃ E : EncodingParameters T,
      (∀ i, E.a i ≤ U ∧ E.b i ≤ U) ∧
      ∀ i j, E.digitPrime i j ≤ Q := by
  let Tags := Σ i : Channel T, Label T i
  have hsep (t : UsefulTag) (j : Tags) : u t ≠ g j := by
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
      0 < A ∧ 0 < B ∧ g ⟨i, j⟩ =
        A * u (.inl i) + B * u (.inr i) := by
    have ha := (hu (.inl i)).1
    have hb := (hu (.inr i)).1
    have hcop : Nat.Coprime (u (.inl i)) (u (.inr i)) :=
      (Nat.coprime_primes ha hb).mpr (fun h => by
        have := huinj h
        cases this)
    have haB := (hu (.inl i)).2.1
    have hbB := (hu (.inr i)).2.1
    have hm := Nat.mul_le_mul haB hbB
    have h := hggt ⟨i, j⟩
    unfold primeThreshold at h
    simp only [pow_two] at h
    exact EncodingPrimeSelection.exists_positive_combination hcop ha.one_lt hb.one_lt (by omega)
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
  refine ⟨E, fun i => ⟨(hu (.inl i)).2.1, (hu (.inr i)).2.1⟩, ?_⟩
  exact fun i j => hbound ⟨i, j⟩

/-- Build bounded parameters from any sufficiently large injective prime family. -/
theorem exists_parameters_of_prime_family (T : LeanWang.TileSet) (Q : ℕ)
    (g : (Σ i : Channel T, Label T i) → ℕ)
    (hgprime : ∀ j, (g j).Prime) (hggt : ∀ j, digitStart < g j)
    (hginj : Function.Injective g) (hbound : ∀ j, g j ≤ Q) :
    ∃ E : EncodingParameters T,
      (∀ i, E.a i ≤ usefulCap ∧ E.b i ≤ usefulCap) ∧
      ∀ i j, E.digitPrime i j ≤ Q := by
  obtain ⟨u, huinj, hu, hseed, hseedlarge⟩ := exists_bounded_useful
  exact exists_parameters_of_bounded_families T usefulCap Q u huinj hu hseed hseedlarge
    g hgprime hggt hginj hbound

/-- There are admissible encoding parameters whose digit primes satisfy the
explicit bound, including a numerical bound on the useful-coordinate primes. -/
theorem exists_bounded_parameters (T : LeanWang.TileSet) :
    ∃ E : EncodingParameters T,
      (∀ i, E.a i ≤ usefulCap ∧ E.b i ≤ usefulCap) ∧
      ∀ i j, E.digitPrime i j ≤ digitPrimeBound T.length := by
  let Tags := Σ i : Channel T, Label T i
  let ix : Tags ≃ Fin (Fintype.card Tags) := Fintype.equivFin Tags
  let g (j : Tags) := EncodingPrimeSelection.primeSequence digitStart (ix j).val
  apply exists_parameters_of_prime_family T (digitPrimeBound T.length) g
    (fun _ => EncodingPrimeSelection.primeSequence_prime _ _)
    (fun _ => EncodingPrimeSelection.primeSequence_gt _ _)
  · intro i j hij
    exact ix.injective (Fin.ext ((EncodingPrimeSelection.primeSequence_strictMono _).injective hij))
  · rintro ⟨i, j⟩
    have hcard : Fintype.card Tags ≤ channelCount * labelsBound T.length := by
      rw [Fintype.card_sigma]
      calc
        _ ≤ ∑ _i : Channel T, labelsBound T.length :=
          Finset.sum_le_sum (fun i _ => label_card_le T i)
        _ = channelCount * labelsBound T.length := by simp [channelCount]
    have hrank : (ix ⟨i, j⟩).val + 1 ≤ channelCount * labelsBound T.length + 1 := by
      have := (ix ⟨i, j⟩).isLt
      omega
    change g ⟨i, j⟩ ≤ _
    exact (primeSequence_le digitStart _).trans
      (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) hrank))

end
end TranslationTiling.Compiler.Size
