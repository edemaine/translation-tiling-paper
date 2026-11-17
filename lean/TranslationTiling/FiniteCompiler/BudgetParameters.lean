import TranslationTiling.FiniteCompiler.SmallBudgetParameters

namespace TranslationTiling.FiniteCompiler
open scoped Classical BigOperators
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def primeBudget (T : System) : ℕ := max (channelCount T) 256

/-- Prime caps can use a budget larger than the number of actual channels. -/
def BudgetPrimes {T : System} (E : EncodingParameters T) (C : ℕ) : Prop :=
  (∀ i, E.a i≤C^4 ∧ E.b i≤C^4) ∧
  (∀ i j, E.digitPrime i j≤C^4) ∧
  (∀ i, E.a i*E.b i≤C^4) ∧
  (∀ n : Column T, E.a (.inl n)*E.b (.inl n)≤C^3) ∧
  ∀ n j, E.digitPrime (.inl n) j≤C^3

theorem EconomicalPrimes.budget {T : System} {E : EncodingParameters T}
    (h : EconomicalPrimes E) : BudgetPrimes E (channelCount T) :=
  ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2.2⟩

private def paddedSystem (T : System) : System :=
  ⟨254,by decide,T.alphabet,fun _ => 0,∅,fun _ _ => False⟩

private def paddedChannel {T : System} (h : T.width≤254) : Channel T→Channel (paddedSystem T)
  | .inl n => .inl ⟨n.val,n.isLt.trans_le h⟩
  | .inr t => .inr t

private theorem paddedChannel_injective {T : System} (h : T.width≤254) :
    Function.Injective (paddedChannel h) := by
  intro i j he
  cases i <;> cases j <;> simp only [paddedChannel,Sum.inl.injEq,Sum.inr.injEq,reduceCtorEq] at he
  · apply congrArg Sum.inl
    apply Fin.ext
    exact congrArg (fun z : Fin 254 => z.val) he
  · exact congrArg Sum.inr he

private def paddedLabel {T : System} (h : T.width≤254) (i : Channel T) :
    Label T i→Label (paddedSystem T) (paddedChannel h i) := by
  cases i <;> exact id

private theorem paddedLabel_injective {T : System} (h : T.width≤254) (i : Channel T) :
    Function.Injective (paddedLabel h i) := by
  cases i <;> exact Function.injective_id

private def paddedPrime {T : System} (h : T.width≤254) : PrimeTag T→PrimeTag (paddedSystem T)
  | .inl i => .inl (paddedChannel h i)
  | .inr (.inl i) => .inr (.inl (paddedChannel h i))
  | .inr (.inr ⟨i,j⟩) => .inr (.inr ⟨paddedChannel h i,paddedLabel h i j⟩)

private theorem paddedPrime_injective {T : System} (h : T.width≤254) :
    Function.Injective (paddedPrime h) := by
  intro i j he
  rcases i with i | (i | ⟨i,k⟩) <;> rcases j with j | (j | ⟨j,l⟩) <;>
    simp only [paddedPrime,Sum.inl.injEq,Sum.inr.injEq,reduceCtorEq] at he
  · exact congrArg Sum.inl (paddedChannel_injective h he)
  · exact congrArg (Sum.inr ∘ Sum.inl) (paddedChannel_injective h he)
  · have hij := paddedChannel_injective h (congrArg Sigma.fst he)
    subst j
    have hkl : k=l := by
      have hh := (Sigma.mk.inj_iff.mp he).2
      exact paddedLabel_injective h i (eq_of_heq hh)
    subst l
    rfl

private def restrictParameters {T : System} (h : T.width≤254)
    (E : EncodingParameters (paddedSystem T)) : EncodingParameters T where
  primeAt := E.primeAt ∘ paddedPrime h
  prime_isPrime := fun i => E.prime_isPrime _
  prime_injective := E.prime_injective.comp (paddedPrime_injective h)
  prime_ne_p := fun i => E.prime_ne_p _
  prime_ne_q := fun i => E.prime_ne_q _
  prime_ne_five := fun i => E.prime_ne_five _
  seed_a_eq := E.seed_a_eq
  seed_b_large := E.seed_b_large
  blockA := fun i j => E.blockA (paddedChannel h i) (paddedLabel h i j)
  blockB := fun i j => E.blockB (paddedChannel h i) (paddedLabel h i j)
  blockA_pos := fun i j => E.blockA_pos _ _
  blockB_pos := fun i j => E.blockB_pos _ _
  digit_representation := fun i j => E.digit_representation _ _
  digitProduct := fun i => ∏ j : Label T i, E.digitPrime (paddedChannel h i) (paddedLabel h i j)
  digitProduct_eq := fun _ => rfl

private theorem restrict_budget {T : System} (h : T.width≤254)
    (E : EncodingParameters (paddedSystem T)) (hp : EconomicalPrimes E) :
    BudgetPrimes (restrictParameters h E) 256 := by
  have hh := hp.budget
  change BudgetPrimes E 256 at hh
  exact ⟨fun i => hh.1 _,fun i j => hh.2.1 _ _,fun i => hh.2.2.1 _,
    fun n => hh.2.2.2.1 _,fun n j => hh.2.2.2.2 _ _⟩

theorem exists_bounded_parameters_budget (T : System) :
    ∃ E : EncodingParameters T,
      (∀ i, E.a i≤usefulPrimeCap (channelCount T) ∧ E.b i≤usefulPrimeCap (channelCount T)) ∧
      (∀ i j, E.digitPrime i j≤digitPrimeCap T.alphabet (channelCount T)) ∧
      (596750≤channelCount T ∧ T.alphabet=3 →
        (∀ i, E.a i≤channelCount T^2 ∧ E.b i≤channelCount T^2) ∧
        (∀ i j, E.digitPrime i j≤channelCount T^3) ∧
        ∀ i, (E.a i*E.b i)^3≤channelCount T^8) ∧
      (1202≤channelCount T ∧ T.alphabet=3 → CompactPrimes E) ∧
      (962≤channelCount T ∧ T.alphabet=3 → EconomicalPrimes E) ∧
      (T.alphabet=3 → BudgetPrimes E (primeBudget T)) := by
  by_cases hsmall : channelCount T<256 ∧ T.alphabet=3
  · have hw : T.width≤254 := by unfold channelCount at hsmall; omega
    obtain ⟨E,hu,hd,hp⟩ := exists_small_budget_parameters (paddedSystem T) (by change 256≤254+2; decide) hsmall.2
    let R := restrictParameters hw E
    have hb : BudgetPrimes R 256 := restrict_budget hw E hp
    have huCap : 256^4≤usefulPrimeCap (channelCount T) := by
      unfold usefulPrimeCap usefulStart
      have hc : 0≤channelCount T := Nat.zero_le _
      norm_num [residueModulus_eq,Sudoku.SeedModulus,Sudoku.p,Sudoku.q] at *
      nlinarith
    have hdCap : 256^4≤digitPrimeCap T.alphabet (channelCount T) := by
      apply huCap.trans
      unfold digitPrimeCap
      have h : usefulPrimeCap (channelCount T)≤
          8*(primeThreshold (usefulPrimeCap (channelCount T))+channelCount T*(T.alphabet+1)+1) := by
        unfold primeThreshold
        omega
      exact h.trans (Nat.le_self_pow (by decide) _)
    refine ⟨R,fun i => ⟨(hb.1 i).1.trans huCap,(hb.1 i).2.trans huCap⟩,
      fun i j => (hb.2.1 i j).trans hdCap,?_,?_,?_,?_⟩
    · intro hh; omega
    · intro hh; omega
    · intro hh; omega
    · intro _
      simpa only [primeBudget,max_eq_right hsmall.1.le] using hb
  · by_cases hmid : channelCount T<962 ∧ T.alphabet=3
    · have hC : 256≤channelCount T := by omega
      obtain ⟨E,hu,hd,he⟩ := exists_small_budget_parameters T hC hmid.2
      refine ⟨E,hu,hd,?_,?_,?_,?_⟩
      · intro hh; omega
      · intro hh; omega
      · intro hh; omega
      · intro _
        simpa only [primeBudget,max_eq_left hC] using he.budget
    obtain ⟨E,hu,hd,hs,hc,he⟩ := exists_bounded_parameters_economical T
    refine ⟨E,hu,hd,hs,hc,he,?_⟩
    intro hB
    have hC : 962≤channelCount T := by omega
    simpa only [primeBudget,max_eq_left (show 256≤channelCount T by omega)] using (he ⟨hC,hB⟩).budget

end
end TranslationTiling.FiniteCompiler
