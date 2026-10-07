import TranslationTiling.Compiler.EffectiveChoices

namespace TranslationTiling.Compiler.Effective

noncomputable section
open scoped Classical BigOperators

abbrev FixedChannel := Sudoku.Column ⊕ Fin 2
abbrev UsefulTag := FixedChannel ⊕ FixedChannel

-- Only this fixed finite table is chosen. It is independent of the input T.
def baseParameters : EncodingParameters [] := encodingParameters []

def usefulTag : UsefulTag → PrimeTag []
  | .inl i => .inl i
  | .inr i => .inr (.inl i)

def usefulPrime (u : UsefulTag) : ℕ := baseParameters.primeAt (usefulTag u)

theorem usefulTag_injective : Function.Injective usefulTag := by
  intro u v h
  cases u <;> cases v <;> simp only [usefulTag, Sum.inl.injEq, Sum.inr.injEq] at h ⊢
  all_goals first | exact h | contradiction

theorem usefulPrime_injective : Function.Injective usefulPrime :=
  baseParameters.prime_injective.comp usefulTag_injective

theorem usefulPrime_prime (u : UsefulTag) : (usefulPrime u).Prime :=
  baseParameters.prime_isPrime _

theorem usefulPrime_primrec : Primrec usefulPrime := finiteFunction_primrec usefulPrime

def usefulBound : ℕ := Finset.univ.sup usefulPrime
def digitBound : ℕ := usefulBound * usefulBound + usefulBound + usefulBound +
  Sudoku.p + Sudoku.q + 3

theorem usefulPrime_le_bound (u : UsefulTag) : usefulPrime u ≤ usefulBound :=
  Finset.le_sup (f := usefulPrime) (Finset.mem_univ u)

def channelCode (i : FixedChannel) : ℕ :=
  @Encodable.encode FixedChannel (inferInstance : Primcodable FixedChannel).toEncodable i

theorem channelCode_primrec : Primrec channelCode := Primrec.encode
theorem channelCode_injective : Function.Injective channelCode := Encodable.encode_injective

def labelCode {T : LeanWang.TileSet} (i : Channel T) : Label T i → ℕ := by
  cases i with
  | inl n => exact fun j =>
      @Encodable.encode RawSymbol (inferInstance : Primcodable RawSymbol).toEncodable (rawSymbol j)
  | inr t => exact fun _ => 0

theorem labelCode_injective {T : LeanWang.TileSet} (i : Channel T) :
    Function.Injective (labelCode i) := by
  cases i with
  | inl n => exact Encodable.encode_injective.comp (rawSymbol_injective T)
  | inr t => change Function.Injective (fun _ : Unit => (0 : ℕ)); intro a b _; exact Subsingleton.elim _ _

def digitCode {T : LeanWang.TileSet} (j : Σ i : Channel T, Label T i) : ℕ :=
  Nat.pair (channelCode j.1) (labelCode j.1 j.2)

theorem digitCode_injective (T : LeanWang.TileSet) :
    Function.Injective (digitCode (T := T)) := by
  rintro ⟨i, a⟩ ⟨j, b⟩ h
  obtain ⟨hi, hab⟩ := Nat.pair_eq_pair.mp h
  have hij : i = j := channelCode_injective hi
  subst j
  exact Sigma.ext rfl (heq_of_eq (labelCode_injective i hab))

def digitLookup (i : FixedChannel) (code : ℕ) : ℕ :=
  EncodingPrimeSelection.primeSequence digitBound (Nat.pair (channelCode i) code)

theorem digitLookup_computable : Computable (fun z : FixedChannel × ℕ => digitLookup z.1 z.2) := by
  have hcode : Primrec (fun z : FixedChannel × ℕ => Nat.pair (channelCode z.1) z.2) :=
    (Primrec.encode.comp ((channelCode_primrec.comp Primrec.fst).pair Primrec.snd)).of_eq (fun _ => rfl)
  exact EncodingPrimeSelection.primeSequence_computable.comp
    ((Primrec.const digitBound).pair hcode).to_comp

theorem digitLookup_prime (i : FixedChannel) (code : ℕ) : (digitLookup i code).Prime :=
  EncodingPrimeSelection.primeSequence_prime _ _

theorem digitLookup_gt (i : FixedChannel) (code : ℕ) : digitBound < digitLookup i code :=
  EncodingPrimeSelection.primeSequence_gt _ _

def digitPrime {T : LeanWang.TileSet} (j : Σ i : Channel T, Label T i) : ℕ :=
  digitLookup j.1 (labelCode j.1 j.2)

theorem digitPrime_injective (T : LeanWang.TileSet) :
    Function.Injective (digitPrime (T := T)) :=
  (EncodingPrimeSelection.primeSequence_strictMono digitBound).injective.comp (digitCode_injective T)

def combinedPrime {T : LeanWang.TileSet} : PrimeTag T → ℕ :=
  Sum.elim usefulPrime digitPrime ∘
    (Equiv.sumAssoc (Channel T) (Channel T) (Σ i : Channel T, Label T i)).symm

theorem combinedPrime_injective (T : LeanWang.TileSet) :
    Function.Injective (combinedPrime (T := T)) := by
  apply (usefulPrime_injective.sumElim (digitPrime_injective T) _).comp
    (Equiv.sumAssoc (Channel T) (Channel T) (Σ i : Channel T, Label T i)).symm.injective
  intro u j he
  have hu := usefulPrime_le_bound u
  have hj := digitLookup_gt j.1 (labelCode j.1 j.2)
  unfold digitBound at hj
  change usefulPrime u = digitLookup j.1 (labelCode j.1 j.2) at he
  omega

def blockInput {T : LeanWang.TileSet} (i : Channel T) (j : Label T i) : CombinationInput :=
  (usefulPrime (.inl i), usefulPrime (.inr i), digitLookup i (labelCode i j))

theorem blockInput_required {T : LeanWang.TileSet} (i : Channel T) (j : Label T i) :
    CombinationRequired (blockInput i j) := by
  have ha := usefulPrime_prime (.inl i)
  have hb := usefulPrime_prime (.inr i)
  have hab : usefulPrime (.inl i) ≠ usefulPrime (.inr i) := by
    intro he
    have := usefulPrime_injective he
    contradiction
  have hA := usefulPrime_le_bound (.inl i)
  have hB := usefulPrime_le_bound (.inr i)
  have hmul := Nat.mul_le_mul hA hB
  have hd := digitLookup_gt i (labelCode i j)
  unfold digitBound at hd
  exact ⟨ha, hb, hab, by dsimp only [blockInput]; omega⟩

/-- A parameter family whose input-dependent numerical fields use the uniform
prime sequence and the total coefficient search. -/
def parameters (T : LeanWang.TileSet) : EncodingParameters T where
  primeAt := combinedPrime
  prime_isPrime := by
    intro x
    rcases x with i | (i | j)
    · exact usefulPrime_prime (.inl i)
    · exact usefulPrime_prime (.inr i)
    · exact digitLookup_prime _ _
  prime_injective := combinedPrime_injective T
  prime_ne_p := by
    intro x
    rcases x with i | (i | j)
    · exact baseParameters.prime_ne_p (.inl i)
    · exact baseParameters.prime_ne_p (.inr (.inl i))
    · have h := digitLookup_gt j.1 (labelCode j.1 j.2)
      unfold digitBound at h
      change digitLookup j.1 (labelCode j.1 j.2) ≠ Sudoku.p
      omega
  prime_ne_q := by
    intro x
    rcases x with i | (i | j)
    · exact baseParameters.prime_ne_q (.inl i)
    · exact baseParameters.prime_ne_q (.inr (.inl i))
    · have h := digitLookup_gt j.1 (labelCode j.1 j.2)
      unfold digitBound at h
      change digitLookup j.1 (labelCode j.1 j.2) ≠ Sudoku.q
      omega
  seed_a_eq := fun t => baseParameters.seed_a_eq t
  seed_b_large := fun t => baseParameters.seed_b_large t
  blockA := fun i j => (positiveCombination (blockInput i j)).1
  blockB := fun i j => (positiveCombination (blockInput i j)).2
  blockA_pos := fun i j => (positiveCombination_spec _ (blockInput_required i j)).1
  blockB_pos := fun i j => (positiveCombination_spec _ (blockInput_required i j)).2.1
  digit_representation := fun i j => (positiveCombination_spec _ (blockInput_required i j)).2.2
  digitProduct := fun i => ∏ j : Label T i, digitLookup i (labelCode i j)
  digitProduct_eq := fun _ => rfl

theorem parameters_a (T : LeanWang.TileSet) (i : FixedChannel) :
    (parameters T).a i = usefulPrime (.inl i) := rfl

theorem parameters_b (T : LeanWang.TileSet) (i : FixedChannel) :
    (parameters T).b i = usefulPrime (.inr i) := rfl

end
end TranslationTiling.Compiler.Effective
