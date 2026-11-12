import TranslationTiling.FiniteCompiler.Effective.Parameters
import TranslationTiling.FiniteCompiler.Effective.Tables

namespace TranslationTiling.FiniteCompiler.Effective

open Compiler.Effective

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
noncomputable section

private theorem exists_parameterCertificate (d : ℕ × ℕ) :
    ∃ c : ParameterCertificate, ParameterValid d c := by
  classical
  by_cases hw : d.1 = 0
  · exact ⟨([],[],[]), Or.inl hw⟩
  let T : System := ⟨d.1, Nat.pos_of_ne_zero hw, d.2, fun _ => 0, ∅, fun _ _ => False⟩
  obtain ⟨E, hu, hd⟩ := exists_bounded_parameters T
  obtain ⟨ps, hp⟩ := exists_finite_table (primeKey (T := T)) (primeKey_injective T) E.primeAt 0
  let key (j : Σ i : Channel T, Label T i) := primeKey (.inr (.inr j))
  have hkey : Function.Injective key := by
    intro i j h
    exact Sum.inr.inj (Sum.inr.inj (primeKey_injective T h))
  obtain ⟨as, ha⟩ := exists_finite_table key hkey (fun j => E.blockA j.1 j.2) 0
  obtain ⟨bs, hb⟩ := exists_finite_table key hkey (fun j => E.blockB j.1 j.2) 0
  refine ⟨(ps,as,bs), Or.inr ⟨?_,?_,?_,?_,?_⟩⟩
  · intro k hk
    obtain ⟨i,rfl⟩ := (mem_primeKeys T k).mp hk
    dsimp only [Prod.fst]
    rw [hp]
    exact ⟨E.prime_isPrime i, E.prime_ne_p i, E.prime_ne_q i⟩
  · intro k hk l hl
    obtain ⟨i,rfl⟩ := (mem_primeKeys T k).mp hk
    obtain ⟨j,rfl⟩ := (mem_primeKeys T l).mp hl
    dsimp only [Prod.fst]
    rw [hp, hp]
    by_cases hij : E.primeAt i = E.primeAt j
    · exact Or.inl (congrArg primeKey (E.prime_injective hij))
    · exact Or.inr hij
  · intro k hk
    obtain ⟨i,rfl⟩ := (mem_channelKeys T k).mp hk
    change ps.getD (primeKey (.inl i)) 0 ≤ _ ∧ ps.getD (primeKey (.inr (.inl i))) 0 ≤ _
    rw [hp, hp]
    exact hu i
  · intro t ht
    have ht' : t < 2 := List.mem_range.mp ht
    let t' : Fin 2 := ⟨t,ht'⟩
    change ps.getD (primeKey (T := T) (.inl (.inr t'))) 0 = _ ∧
      _ < ps.getD (primeKey (T := T) (.inr (.inl (.inr t')))) 0
    rw [hp, hp]
    exact ⟨E.seed_a_eq t', E.seed_b_large t'⟩
  · intro k hk
    obtain ⟨⟨i,j⟩,rfl⟩ := (mem_digitKeys T k).mp hk
    change 0 < as.getD (key ⟨i,j⟩) 0 ∧ 0 < bs.getD (key ⟨i,j⟩) 0 ∧
      ps.getD (primeKey (.inr (.inr ⟨i,j⟩))) 0 =
        as.getD (key ⟨i,j⟩) 0 * ps.getD (primeKey (.inl i)) 0 +
        bs.getD (key ⟨i,j⟩) 0 * ps.getD (primeKey (.inr (.inl i))) 0 ∧ _
    change _ ∧ _ ∧ _ ∧ ps.getD (primeKey (.inr (.inr ⟨i,j⟩))) 0 ≤ _
    rw [ha, hb, hp, hp, hp]
    exact ⟨E.blockA_pos i j, E.blockB_pos i j, E.digit_representation i j, hd i j⟩

def decodeParameterCertificate (n : ℕ) : ParameterCertificate :=
  (Encodable.decode n).getD ([],[],[])

theorem decodeParameterCertificate_primrec : Primrec decodeParameterCertificate :=
  Primrec.option_getD.comp Primrec.decode (Primrec.const ([],[],[]))

private theorem exists_parameterCode (d : ℕ × ℕ) :
    ∃ n, ParameterValid d (decodeParameterCertificate n) := by
  obtain ⟨c,hc⟩ := exists_parameterCertificate d
  refine ⟨Encodable.encode c, ?_⟩
  simpa only [decodeParameterCertificate, Encodable.encodek, Option.getD_some] using hc

def parameterCode (d : ℕ × ℕ) : ℕ :=
  leastWitness (fun d n => ParameterValid d (decodeParameterCertificate n)) exists_parameterCode d

theorem parameterCode_computable : Computable parameterCode :=
  leastWitness_computable _
    ((parameterValid_primrec.comp
      (Primrec.fst.pair (decodeParameterCertificate_primrec.comp Primrec.snd))).computablePred) _

def parameterCertificate (d : ℕ × ℕ) : ParameterCertificate :=
  decodeParameterCertificate (parameterCode d)

theorem parameterCertificate_computable : Computable parameterCertificate :=
  decodeParameterCertificate_primrec.to_comp.comp parameterCode_computable

theorem parameterCertificate_valid (d : ℕ × ℕ) : ParameterValid d (parameterCertificate d) := by
  unfold parameterCertificate parameterCode leastWitness
  exact @Nat.find_spec (fun n => ParameterValid d (decodeParameterCertificate n))
    (Classical.decPred _) (exists_parameterCode d)

/-- Reconstruct the typed encoding parameters from a checked numerical table. -/
def parametersOfCertificate (T : System) (c : ParameterCertificate)
    (hc : ParameterValid (T.width,T.alphabet) c) : EncodingParameters T := by
  obtain ⟨hp,hinj,_,hs,hd⟩ := hc.resolve_left (Nat.ne_of_gt T.width_pos)
  exact {
    primeAt := fun i => c.1.getD (primeKey i) 0
    prime_isPrime := fun i => (hp _ ((mem_primeKeys T _).mpr ⟨i,rfl⟩)).1
    prime_ne_p := fun i => (hp _ ((mem_primeKeys T _).mpr ⟨i,rfl⟩)).2.1
    prime_ne_q := fun i => (hp _ ((mem_primeKeys T _).mpr ⟨i,rfl⟩)).2.2
    prime_injective := fun i j h => primeKey_injective T
      ((hinj _ ((mem_primeKeys T _).mpr ⟨i,rfl⟩) _
        ((mem_primeKeys T _).mpr ⟨j,rfl⟩)).resolve_right (not_not.mpr h))
    seed_a_eq := fun t => (hs t.val (List.mem_range.mpr t.isLt)).1
    seed_b_large := fun t => (hs t.val (List.mem_range.mpr t.isLt)).2
    blockA := fun i j => c.2.1.getD (primeKey (.inr (.inr ⟨i,j⟩))) 0
    blockB := fun i j => c.2.2.getD (primeKey (.inr (.inr ⟨i,j⟩))) 0
    blockA_pos := fun i j => (hd _ ((mem_digitKeys T _).mpr ⟨⟨i,j⟩,rfl⟩)).1
    blockB_pos := fun i j => (hd _ ((mem_digitKeys T _).mpr ⟨⟨i,j⟩,rfl⟩)).2.1
    digit_representation := fun i j => (hd _ ((mem_digitKeys T _).mpr ⟨⟨i,j⟩,rfl⟩)).2.2.1
    digitProduct := fun i => ∏ j : Label T i, c.1.getD (primeKey (.inr (.inr ⟨i,j⟩))) 0
    digitProduct_eq := fun _ => rfl }

def parameters (T : System) : EncodingParameters T :=
  parametersOfCertificate T (parameterCertificate (T.width,T.alphabet)) (parameterCertificate_valid _)

theorem parameters_bounded (T : System) :
    (∀ i, (parameters T).a i ≤ usefulPrimeCap (channelCount T) ∧
      (parameters T).b i ≤ usefulPrimeCap (channelCount T)) ∧
    ∀ i j, (parameters T).digitPrime i j ≤ digitPrimeCap T.alphabet (channelCount T) := by
  have h := (parameterCertificate_valid (T.width,T.alphabet)).resolve_left (Nat.ne_of_gt T.width_pos)
  constructor
  · intro i
    exact h.2.2.1 _ ((mem_channelKeys T _).mpr ⟨i,rfl⟩)
  · intro i j
    exact (h.2.2.2.2 _ ((mem_digitKeys T _).mpr ⟨⟨i,j⟩,rfl⟩)).2.2.2

end
end TranslationTiling.FiniteCompiler.Effective
