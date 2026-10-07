import TranslationTiling.Compiler.EffectiveAlphabet
import TranslationTiling.Compiler.EncodingPrimeSelection

namespace TranslationTiling.Compiler.Effective

theorem finFunction_primrec {β : Type*} [Primcodable β] {n : ℕ} (f : Fin n → β) :
    Primrec f := by
  have h : Primrec₂ (fun i : Fin n => fun _ : Unit => f i) :=
    Primrec.fin_curry₁.mpr (fun i => Primrec.const (f i))
  exact h.comp Primrec.id (Primrec.const ())

/-- Any fixed table on a finite encoded domain is primitive recursive. This
does not assert uniform computability when the domain or table varies. -/
theorem finiteFunction_primrec {α β : Type*} [Primcodable α] [Primcodable β]
    [Fintype α] [Inhabited β] (f : α → β) : Primrec f := by
  classical
  let encode : α → ℕ := @Encodable.encode α (inferInstance : Primcodable α).toEncodable
  let decode : ℕ → Option α := @Encodable.decode α (inferInstance : Primcodable α).toEncodable
  let bound := (Finset.univ.sup encode) + 1
  have hbound (a : α) : encode a < bound :=
    Nat.lt_succ_of_le (Finset.le_sup (f := encode) (Finset.mem_univ a))
  let ix : α → Fin bound := fun a => ⟨encode a, hbound a⟩
  have hix : Primrec ix := Primrec.fin_val_iff.mp Primrec.encode
  let g : Fin bound → β := fun i => ((decode i.val).map f).getD default
  apply ((finFunction_primrec g).comp hix).of_eq
  intro a
  change ((decode (encode a)).map f).getD default = f a
  rw [show decode (encode a) = some a from
    @Encodable.encodek α (inferInstance : Primcodable α).toEncodable a]
  rfl

@[fun_prop] theorem primeRule {α : Type*} [Primcodable α] {f : α → ℕ}
    (hf : Primrec f) : PrimrecPred (fun a => (f a).Prime) := nat_prime_primrec.comp hf

abbrev CombinationInput := ℕ × ℕ × ℕ

def CombinationRequired (z : CombinationInput) : Prop :=
  z.1.Prime ∧ z.2.1.Prime ∧ z.1 ≠ z.2.1 ∧ z.1 * z.2.1 + z.1 + z.2.1 < z.2.2

instance (z : CombinationInput) : Decidable (CombinationRequired z) := by
  unfold CombinationRequired
  infer_instance

@[fun_prop] theorem combinationRequired_primrec : PrimrecPred CombinationRequired := by
  unfold CombinationRequired
  fun_prop

def CombinationValid (z : CombinationInput) (code : ℕ) : Prop :=
  if CombinationRequired z then
    0 < code.unpair.1 ∧ 0 < code.unpair.2 ∧
      z.2.2 = code.unpair.1 * z.1 + code.unpair.2 * z.2.1
  else code = 0

instance (z : CombinationInput) (code : ℕ) : Decidable (CombinationValid z code) := by
  unfold CombinationValid
  infer_instance

theorem combinationValid_primrec :
    PrimrecPred (fun z : CombinationInput × ℕ => CombinationValid z.1 z.2) := by
  unfold CombinationValid
  have hr : PrimrecPred (fun z : CombinationInput × ℕ => CombinationRequired z.1) :=
    combinationRequired_primrec.comp Primrec.fst
  have hyes : PrimrecPred (fun z : CombinationInput × ℕ =>
    0 < z.2.unpair.1 ∧ 0 < z.2.unpair.2 ∧
      z.1.2.2 = z.2.unpair.1 * z.1.1 + z.2.unpair.2 * z.1.2.1) := by fun_prop
  have hno : PrimrecPred (fun z : CombinationInput × ℕ => z.2 = 0) := by fun_prop
  apply ((hr.and hyes).or (hr.not.and hno)).of_eq
  intro z
  by_cases hc : CombinationRequired z.1 <;> simp [hc]

private theorem exists_combinationCode (z : CombinationInput) : ∃ n, CombinationValid z n := by
  by_cases h : CombinationRequired z
  · have hparams := h
    obtain ⟨ha, hb, hab, hr⟩ := hparams
    have hcop := (Nat.coprime_primes ha hb).mpr hab
    obtain ⟨A, B, hA, hB, he⟩ :=
      EncodingPrimeSelection.exists_positive_combination hcop ha.one_lt hb.one_lt hr
    exact ⟨Nat.pair A B, by simpa only [CombinationValid, if_pos h, Nat.unpair_pair] using ⟨hA, hB, he⟩⟩
  · exact ⟨0, by simp only [CombinationValid, if_neg h]⟩

noncomputable def combinationCode (z : CombinationInput) : ℕ :=
  leastWitness CombinationValid exists_combinationCode z

theorem combinationCode_computable : Computable combinationCode :=
  leastWitness_computable _ combinationValid_primrec.computablePred _

noncomputable def positiveCombination (z : CombinationInput) : ℕ × ℕ :=
  (combinationCode z).unpair

theorem positiveCombination_computable : Computable positiveCombination :=
  Primrec.unpair.to_comp.comp combinationCode_computable

theorem positiveCombination_spec (z : CombinationInput) (hz : CombinationRequired z) :
    0 < (positiveCombination z).1 ∧ 0 < (positiveCombination z).2 ∧
      z.2.2 = (positiveCombination z).1 * z.1 + (positiveCombination z).2 * z.2.1 := by
  have h : CombinationValid z (combinationCode z) := by
    unfold combinationCode leastWitness
    exact @Nat.find_spec (CombinationValid z) (Classical.decPred _) (exists_combinationCode z)
  simpa only [CombinationValid, if_pos hz, positiveCombination] using h

end TranslationTiling.Compiler.Effective
