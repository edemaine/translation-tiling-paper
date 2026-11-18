import TranslationTiling.FiniteCompiler.BudgetParameters
import TranslationTiling.FiniteCompiler.Effective.Parameters
import TranslationTiling.FiniteCompiler.Effective.CertificateConstruction
import TranslationTiling.FiniteCompiler.Effective.SmallCertificates

namespace TranslationTiling.FiniteCompiler.Effective

open Compiler.Effective

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
noncomputable section

private theorem exists_parameterCertificate (d : ℕ × ℕ) :
    ∃ c : ParameterCertificate, ParameterValid d c := by
  by_cases hw : d.1=0
  · exact ⟨([],[],[]),Or.inl hw⟩
  let T : System := ⟨d.1,Nat.pos_of_ne_zero hw,d.2,fun _ => 0,∅,fun _ _ => False⟩
  obtain ⟨E,hu,hd,hs,hc,he,hb⟩ := exists_bounded_parameters_budget T
  obtain ⟨c,hc,_,_,_⟩ := certificate_of_parameters T E hu hd hs hc he hb
  exact ⟨c,hc⟩

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

def searchedParameterCertificate (d : ℕ × ℕ) : ParameterCertificate :=
  decodeParameterCertificate (parameterCode d)

theorem searchedParameterCertificate_computable : Computable searchedParameterCertificate :=
  decodeParameterCertificate_primrec.to_comp.comp parameterCode_computable

theorem searchedParameterCertificate_valid (d : ℕ × ℕ) : ParameterValid d (searchedParameterCertificate d) := by
  unfold searchedParameterCertificate parameterCode leastWitness
  exact @Nat.find_spec (fun n => ParameterValid d (decodeParameterCertificate n))
    (Classical.decPred _) (exists_parameterCode d)

def parameterCertificate (d : ℕ×ℕ) : ParameterCertificate :=
  if d.1=48 ∧ d.2=3 then SmallProfiles.certificate 0 else
  if d.1=64 ∧ d.2=3 then SmallProfiles.certificate 1 else
  if d.1=80 ∧ d.2=3 then SmallProfiles.certificate 2 else
  if d.1=96 ∧ d.2=3 then SmallProfiles.certificate 3 else
  if d.1=112 ∧ d.2=3 then SmallProfiles.certificate 4 else
  searchedParameterCertificate d

theorem parameterCertificate_computable : Computable parameterCertificate := by
  have h0 : Primrec (fun d : ℕ×ℕ => decide (d.1=48 ∧ d.2=3)) := by fun_prop
  have h1 : Primrec (fun d : ℕ×ℕ => decide (d.1=64 ∧ d.2=3)) := by fun_prop
  have h2 : Primrec (fun d : ℕ×ℕ => decide (d.1=80 ∧ d.2=3)) := by fun_prop
  have h3 : Primrec (fun d : ℕ×ℕ => decide (d.1=96 ∧ d.2=3)) := by fun_prop
  have h4 : Primrec (fun d : ℕ×ℕ => decide (d.1=112 ∧ d.2=3)) := by fun_prop
  exact (h0.to_comp.cond (Computable.const (SmallProfiles.certificate 0)) (h1.to_comp.cond (Computable.const (SmallProfiles.certificate 1)) (h2.to_comp.cond (Computable.const (SmallProfiles.certificate 2)) (h3.to_comp.cond (Computable.const (SmallProfiles.certificate 3)) (h4.to_comp.cond (Computable.const (SmallProfiles.certificate 4)) searchedParameterCertificate_computable))))).of_eq (fun d => by simp only [parameterCertificate,Bool.cond_decide])

theorem parameterCertificate_valid (d : ℕ×ℕ) : ParameterValid d (parameterCertificate d) := by
  rcases d with ⟨w,B⟩
  unfold parameterCertificate
  split_ifs with h0 h1 h2 h3 h4
  · obtain ⟨rfl,rfl⟩ := h0; exact SmallProfiles.certificate_valid 0
  · obtain ⟨rfl,rfl⟩ := h1; exact SmallProfiles.certificate_valid 1
  · obtain ⟨rfl,rfl⟩ := h2; exact SmallProfiles.certificate_valid 2
  · obtain ⟨rfl,rfl⟩ := h3; exact SmallProfiles.certificate_valid 3
  · obtain ⟨rfl,rfl⟩ := h4; exact SmallProfiles.certificate_valid 4
  · exact searchedParameterCertificate_valid (w,B)

theorem parameterCertificate_small (i : Fin 5) :
    parameterCertificate (SmallProfiles.width i,3)=SmallProfiles.certificate i := by
  fin_cases i <;> simp [parameterCertificate,SmallProfiles.width]

/-- Reconstruct the typed encoding parameters from a checked numerical table. -/
def parametersOfCertificate (T : System) (c : ParameterCertificate)
    (hc : ParameterValid (T.width,T.alphabet) c) : EncodingParameters T := by
  obtain ⟨hp,hinj,_,hs,hd,_⟩ := hc.resolve_left (Nat.ne_of_gt T.width_pos)
  exact {
    primeAt := fun i => c.1.getD (primeKey i) 0
    prime_isPrime := fun i => (hp _ ((mem_primeKeys T _).mpr ⟨i,rfl⟩)).1
    prime_ne_p := fun i => (hp _ ((mem_primeKeys T _).mpr ⟨i,rfl⟩)).2.1
    prime_ne_q := fun i => (hp _ ((mem_primeKeys T _).mpr ⟨i,rfl⟩)).2.2.1
    prime_ne_five := fun i => (hp _ ((mem_primeKeys T _).mpr ⟨i,rfl⟩)).2.2.2
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
    exact (h.2.2.2.2.1 _ ((mem_digitKeys T _).mpr ⟨⟨i,j⟩,rfl⟩)).2.2.2


theorem parameters_bounded_sharp (T : System) (hC : 596750 ≤ channelCount T) (hB : T.alphabet=3) :
    (∀ i, (parameters T).a i ≤ channelCount T^2 ∧ (parameters T).b i ≤ channelCount T^2) ∧
    ∀ i j, (parameters T).digitPrime i j ≤ channelCount T^5 := by
  have h := (parameterCertificate_valid (T.width,T.alphabet)).resolve_left (Nat.ne_of_gt T.width_pos)
  have hs := h.2.2.2.2.2.1.resolve_left (not_not.mpr ⟨hC,hB⟩)
  exact ⟨fun i => hs.1 _ ((mem_channelKeys T _).mpr ⟨i,rfl⟩),
    fun i j => (hs.2.1 _ ((mem_digitKeys T _).mpr ⟨⟨i,j⟩,rfl⟩)).trans
      (Nat.pow_le_pow_right (by omega) (by decide))⟩

theorem parameters_bounded_tight (T : System) (hC : 596750≤channelCount T) (hB : T.alphabet=3) :
    (∀ i, (parameters T).a i≤channelCount T^2 ∧ (parameters T).b i≤channelCount T^2) ∧
    (∀ i j, (parameters T).digitPrime i j≤channelCount T^3) ∧
    ∀ i, ((parameters T).a i*(parameters T).b i)^3≤channelCount T^8 := by
  have h := (parameterCertificate_valid (T.width,T.alphabet)).resolve_left (Nat.ne_of_gt T.width_pos)
  have hs := h.2.2.2.2.2.1.resolve_left (not_not.mpr ⟨hC,hB⟩)
  exact ⟨fun i => hs.1 _ ((mem_channelKeys T _).mpr ⟨i,rfl⟩),
    fun i j => hs.2.1 _ ((mem_digitKeys T _).mpr ⟨⟨i,j⟩,rfl⟩),
    fun i => hs.2.2 _ ((mem_channelKeys T _).mpr ⟨i,rfl⟩)⟩

theorem parameters_bounded_compact (T : System) (hC : 1202≤channelCount T) (hB : T.alphabet=3) :
    CompactPrimes (parameters T) := by
  have h := (parameterCertificate_valid (T.width,T.alphabet)).resolve_left (Nat.ne_of_gt T.width_pos)
  have hs := h.2.2.2.2.2.2.1.resolve_left (not_not.mpr ⟨hC,hB⟩)
  exact ⟨fun i => hs.1 _ ((mem_channelKeys T _).mpr ⟨i,rfl⟩),
    fun i j => hs.2.1 _ ((mem_digitKeys T _).mpr ⟨⟨i,j⟩,rfl⟩),
    fun i => hs.2.2 _ ((mem_channelKeys T _).mpr ⟨i,rfl⟩)⟩

theorem parameters_digitPrime_eq (T : System) (i : Channel T) (j : Label T i) :
    (parameters T).digitPrime i j =
      (parameterCertificate (T.width,T.alphabet)).1.getD (primeKey (.inr (.inr ⟨i,j⟩))) 0 := rfl

theorem parameters_bounded_economical (T : System) (hC : 962≤channelCount T) (hB : T.alphabet=3) :
    EconomicalPrimes (parameters T) := by
  have h := (parameterCertificate_valid (T.width,T.alphabet)).resolve_left (Nat.ne_of_gt T.width_pos)
  have hs := h.2.2.2.2.2.2.2.1.resolve_left (not_not.mpr ⟨hC,hB⟩)
  refine ⟨fun i => hs.1 _ ((mem_channelKeys T _).mpr ⟨i,rfl⟩),
    fun i j => hs.2.1 _ ((mem_digitKeys T _).mpr ⟨⟨i,j⟩,rfl⟩),
    fun i => hs.2.2.1 _ ((mem_channelKeys T _).mpr ⟨i,rfl⟩),
    fun n => hs.2.2.2.1 n.val (List.mem_range.mpr n.isLt),?_,?_⟩
  · intro i j
    rw [parameters_digitPrime_eq]
    dsimp only [channelCount,primeKey]
    exact hs.2.2.2.2.1 (channelKey i,labelKey i j) ((mem_digitKeys T _).mpr ⟨⟨i,j⟩,rfl⟩)
  · intro n j
    rw [parameters_digitPrime_eq]
    exact hs.2.2.2.2.2 n.val (List.mem_range.mpr n.isLt) j.val (List.mem_range.mpr j.isLt)

theorem parameters_bounded_budget (T : System) (hB : T.alphabet=3) :
    BudgetPrimes (parameters T) (primeBudget T) := by
  have h := (parameterCertificate_valid (T.width,T.alphabet)).resolve_left (Nat.ne_of_gt T.width_pos)
  have hs := h.2.2.2.2.2.2.2.2.resolve_left (not_not.mpr hB)
  refine ⟨fun i => hs.1 _ ((mem_channelKeys T _).mpr ⟨i,rfl⟩),
    fun i j => hs.2.1 _ ((mem_digitKeys T _).mpr ⟨⟨i,j⟩,rfl⟩),
    fun i => hs.2.2.1 _ ((mem_channelKeys T _).mpr ⟨i,rfl⟩),
    fun n => hs.2.2.2.1 n.val (List.mem_range.mpr n.isLt),?_⟩
  intro n j
  rw [parameters_digitPrime_eq]
  exact hs.2.2.2.2 n.val (List.mem_range.mpr n.isLt) j.val (List.mem_range.mpr j.isLt)

end
end TranslationTiling.FiniteCompiler.Effective

namespace TranslationTiling.FiniteCompiler.Effective
open scoped Classical BigOperators
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem parameters_small_prime (T : System) (i : Fin 5)
    (hw : T.width=SmallProfiles.width i) (hB : T.alphabet=3) (j : PrimeTag T) :
    (parameters T).primeAt j=(SmallProfiles.profile i).entry (SmallProfiles.tagIndex j) := by
  rcases T with ⟨w,hpos,B,s,a,se⟩
  dsimp only at hw hB
  subst w B
  change (parameterCertificate (SmallProfiles.width i,3)).1.getD (primeKey j) 0 = _
  rw [parameterCertificate_small]
  rcases j with c | (c | ⟨c,l⟩)
  · cases c with
    | inl n => exact SmallProfiles.certificate_lookup i (.inl (.inl n))
    | inr t => exact SmallProfiles.certificate_lookup i (.inl (.inr t))
  · cases c with
    | inl n => exact SmallProfiles.certificate_lookup i (.inr (.inl (.inl n)))
    | inr t => exact SmallProfiles.certificate_lookup i (.inr (.inl (.inr t)))
  · cases c with
    | inl n => exact SmallProfiles.certificate_lookup i (.inr (.inr ⟨.inl n,l⟩))
    | inr t => exact SmallProfiles.certificate_lookup i (.inr (.inr ⟨.inr t,l⟩))

theorem parameters_small_r (T : System) (i : Fin 5)
    (hw : T.width=SmallProfiles.width i) (hB : T.alphabet=3) (c : Channel T) :
    (parameters T).r c=(SmallProfiles.profile i).rAt T.width (SmallProfiles.channelIndex c) := by
  rcases T with ⟨w,hpos,B,s,a,se⟩
  dsimp only at hw hB
  subst B
  have hprime := parameters_small_prime (System.mk w hpos 3 s a se) i hw rfl
  rw [(parameters _).r_eq_prod]
  cases c with
  | inl n =>
    change (∏ j : Fin 3, (parameters (System.mk w hpos 3 s a se)).primeAt
      (.inr (.inr ⟨.inl n,j⟩))) = _
    simp only [Fin.prod_univ_succ,Fin.prod_univ_zero,mul_one]
    rw [hprime _,hprime _,hprime _]
    change _ = (SmallProfiles.profile i).rAt w n.val
    rw [SmallProfiles.Profile.rAt,if_pos (show n.val<w from n.isLt)]
    simp only [SmallProfiles.tagIndex,SmallProfiles.digitIndex,Fin.val_zero,Fin.val_succ,
      Nat.add_zero,Nat.add_assoc,Nat.mul_assoc]
  | inr t =>
    haveI : Unique (Label (System.mk w hpos 3 s a se) (.inr t)) := by change Unique Unit; infer_instance
    rw [Fintype.prod_unique]
    change (parameters (System.mk w hpos 3 s a se)).primeAt (.inr (.inr ⟨.inr t,default⟩)) = _
    rw [hprime _]
    simp only [SmallProfiles.tagIndex,SmallProfiles.digitIndex,SmallProfiles.channelIndex,
      SmallProfiles.Profile.rAt,if_neg (by omega : ¬ w+t.val<w),Nat.add_sub_cancel_left,Nat.add_assoc]

end
end TranslationTiling.FiniteCompiler.Effective
