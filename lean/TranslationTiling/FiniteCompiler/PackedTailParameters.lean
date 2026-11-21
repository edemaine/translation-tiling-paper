import TranslationTiling.FiniteCompiler.PackedPrimeSupply
import TranslationTiling.FiniteCompiler.CoreMassBounds
import TranslationTiling.Compiler.EncodingPrimeSelection

namespace TranslationTiling.FiniteCompiler.Packed

open Compiler.Size TranslationTiling.FiniteCompiler.Effective
open scoped BigOperators Classical

noncomputable section

local instance packedTailParametersFrame : SeedFrame := compactSeedFrame

/-- The unused prime tags are omitted from both pools. -/
def tailPair (k i : ℕ) : ℕ := (pairPool k).getD i 0

def tailDigit (k i j : ℕ) : ℕ := (digitPool k).getD (digitRank i j) 0

def tailSeedA (t : Fin 2) : ℕ := t.val+2
def tailSeedB (t : Fin 2) : ℕ := ![1229,773] t
def tailSeedDigit (t : Fin 2) : ℕ := ![1231,797] t

variable {T : System} [AlphabetFamily T] {k : ℕ}

/-- Primes for a refined system, with separate ranks for pairs and digits. -/
def tailPrime (k : ℕ) : PrimeTag T → ℕ
  | .inl (.inl i) => tailPair k (2*i.val)
  | .inl (.inr t) => tailSeedA t
  | .inr (.inl (.inl i)) => tailPair k (2*i.val+1)
  | .inr (.inl (.inr t)) => tailSeedB t
  | .inr (.inr ⟨.inl i, j⟩) => tailDigit k i.val j.val
  | .inr (.inr ⟨.inr t, _⟩) => tailSeedDigit t

variable (hk : 20 ≤ k) (hw : T.width = (ternaryLayoutProfile k).width)
  (ha : ∀ n : Column T, AlphabetFamily.size (T:=T) n = (ternaryLayoutProfile k).arity n.val)

private theorem tailPair_in {i : ℕ} (hi : i < 36+4*k) : tailPair k i ∈ pairPool k := by
  exact getD_mem_of_lt _ _ _ (hi.trans_le (pairPool_length k))

include hw in
private theorem ordinaryIndex (i : Column T) : i.val < (ternaryLayoutProfile k).width := by
  exact (show i.val < T.width from i.isLt).trans_le hw.le

include ha in
private theorem ordinaryLabel (i : Column T) (j : Label T (.inl i)) :
    j.val < (ternaryLayoutProfile k).arity i.val :=
  (show j.val < AlphabetFamily.size (T:=T) i from j.isLt).trans_le (ha i).le

include hk hw ha in
private theorem tailDigit_in (i : Column T) (j : Label T (.inl i)) :
    tailDigit k i.val j.val ∈ digitPool k := by
  have h := digitRank_lt (by omega : 0 < k) (ordinaryIndex hw i) (ordinaryLabel ha i j)
  exact getD_mem_of_lt _ _ _ (h.trans_le (digitPool_length k))

include hw in
private theorem tailPair_lt (i : Column T) : 2*i.val+1 < 36+4*k := by
  have h := ordinaryIndex hw i
  rw [ternaryLayout_width] at h
  omega

private theorem tailSeed_info (t : Fin 2) :
    (tailSeedA t).Prime ∧ (tailSeedB t).Prime ∧ (tailSeedDigit t).Prime ∧
    tailSeedA t ∈ reservedPrimes ∧ tailSeedB t ∈ reservedPrimes ∧
    tailSeedDigit t ∈ reservedPrimes := by
  fin_cases t <;> norm_num [tailSeedA,tailSeedB,tailSeedDigit,reservedPrimes]

include hk in
private theorem start_large : 1231 ≤ guardedDigitStart k := by
  have hx := (guardedPairCaps_ge hk).2
  unfold guardedPairRanks at hx
  have h : 124 ≤ guardedPairCap k := by omega
  have hp := Nat.pow_le_pow_left h 2
  unfold guardedDigitStart
  omega

private theorem reserved_le (q : ℕ) (hq : q ∈ reservedPrimes) : q ≤ 1231 := by
  simp only [reservedPrimes, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide

include hk hw ha in
theorem tailPrime_isPrime (i : PrimeTag T) : (tailPrime k i).Prime := by
  rcases i with (i|t) | ((i|t) | ⟨i,j⟩)
  · exact (pairPool_facts (tailPair_in (Nat.lt_of_succ_lt (tailPair_lt hw i)))).1
  · exact (tailSeed_info t).1
  · exact (pairPool_facts (tailPair_in (tailPair_lt hw i))).1
  · exact (tailSeed_info t).2.1
  · cases i with
    | inl i => exact (digitPool_facts (tailDigit_in hk hw ha i j)).1
    | inr t => exact (tailSeed_info t).2.2.1

include hk hw ha in
theorem tailPrime_bound (i : PrimeTag T) : tailPrime k i ≤ guardedDigitCap k := by
  have hs := start_large hk
  have hy := guardedDigitCap_gt hk
  have hx : guardedPairCap k ≤ guardedDigitStart k := by unfold guardedDigitStart; omega
  rcases i with (i|t) | ((i|t) | ⟨i,j⟩)
  · exact (pairPool_facts (tailPair_in (Nat.lt_of_succ_lt (tailPair_lt hw i)))).2.2.trans
      (hx.trans hy.le)
  · exact (reserved_le _ (tailSeed_info t).2.2.2.1).trans (hs.trans hy.le)
  · exact (pairPool_facts (tailPair_in (tailPair_lt hw i))).2.2.trans (hx.trans hy.le)
  · exact (reserved_le _ (tailSeed_info t).2.2.2.2.1).trans (hs.trans hy.le)
  · cases i with
    | inl i => exact (digitPool_facts (tailDigit_in hk hw ha i j)).2.2
    | inr t => exact (reserved_le _ (tailSeed_info t).2.2.2.2.2).trans (hs.trans hy.le)

private def seedPrimes : Fin 6 → ℕ := ![2,3,1229,773,1231,797]

private abbrev Source := ℕ ⊕ ℕ ⊕ Fin 6

private def tailSource : PrimeTag T → Source
  | .inl (.inl i) => .inl (2*i.val)
  | .inl (.inr t) => .inr (.inr ⟨t.val, t.isLt.trans (by decide)⟩)
  | .inr (.inl (.inl i)) => .inl (2*i.val+1)
  | .inr (.inl (.inr t)) => .inr (.inr ⟨2+t.val, (Nat.add_lt_add_left t.isLt 2).trans (by decide)⟩)
  | .inr (.inr ⟨.inl i, j⟩) => .inr (.inl (digitRank i.val j.val))
  | .inr (.inr ⟨.inr t, _⟩) => .inr (.inr ⟨4+t.val, Nat.add_lt_add_left t.isLt 4⟩)

private def sourcePrime (k : ℕ) : Source → ℕ
  | .inl j => tailPair k j
  | .inr (.inl j) => (digitPool k).getD j 0
  | .inr (.inr t) => seedPrimes t

private def sourceValid (k : ℕ) : Source → Prop
  | .inl j => j < 36+4*k
  | .inr (.inl j) => j < 90+6*k
  | .inr (.inr _) => True

include hk hw ha in
private theorem tailSource_valid (i : PrimeTag T) : sourceValid k (tailSource i) := by
  rcases i with (i|t) | ((i|t) | ⟨i,j⟩)
  · exact Nat.lt_of_succ_lt (tailPair_lt hw i)
  · trivial
  · exact tailPair_lt hw i
  · trivial
  · rcases i with i | t
    · exact digitRank_lt (by omega : 0 < k) (ordinaryIndex hw i) (ordinaryLabel ha i j)
    · trivial

private theorem tailSource_prime (i : PrimeTag T) :
    sourcePrime k (tailSource i) = tailPrime k i := by
  rcases i with (i|t) | ((i|t) | ⟨i,j⟩)
  · rfl
  · fin_cases t <;> rfl
  · rfl
  · fin_cases t <;> rfl
  · rcases i with i | t
    · rfl
    · fin_cases t <;> rfl

include hk hw ha in
private theorem tailSource_injective : Function.Injective (tailSource (T:=T)) := by
  rintro ((i|t)|((i|t)|⟨(i|t),j⟩)) ((i'|t')|((i'|t')|⟨(i'|t'),j'⟩)) h
  all_goals simp only [tailSource, Sum.inl.injEq, Sum.inr.injEq, Sum.inl_ne_inr,
    Sum.inr_ne_inl, Fin.mk.injEq] at h
  all_goals try (exfalso; have ht := t.isLt; have ht' := t'.isLt; omega)
  all_goals try (exfalso; omega)
  all_goals try (have he : i=i' := Fin.ext (by omega); subst i'; rfl)
  all_goals try (have he : t=t' := Fin.ext (by omega); subst t'; congr)
  obtain ⟨he,he'⟩ := digitRank_inj (by omega : 0 < k) (ordinaryIndex hw i) (ordinaryIndex hw i')
    (ordinaryLabel ha i j) (ordinaryLabel ha i' j') h
  have hii : i=i' := Fin.ext he
  subst i'
  have hjj : j=j' := Fin.ext he'
  subst j'
  rfl

private theorem poolIndex_inj {l : List ℕ} (hl : l.Nodup) {i j : ℕ}
    (hi : i < l.length) (hj : j < l.length) (h : l.getD i 0 = l.getD j 0) : i = j := by
  rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj] at h
  exact hl.getElem_inj_iff.mp h

private theorem seedPrimes_mem (t : Fin 6) : seedPrimes t ∈ reservedPrimes := by
  fin_cases t <;> decide

include hk in
private theorem sourcePrime_injective {a b : Source}
    (ha : sourceValid k a) (hb : sourceValid k b) (h : sourcePrime k a = sourcePrime k b) : a = b := by
  have hs := start_large hk
  have hx : guardedPairCap k ≤ guardedDigitStart k := by unfold guardedDigitStart; omega
  have pair (j : ℕ) (hj : j < 36+4*k) := pairPool_facts (tailPair_in hj)
  have digit (j : ℕ) (hj : j < 90+6*k) :=
    digitPool_facts (getD_mem_of_lt _ _ _ (hj.trans_le (digitPool_length k)) :
      (digitPool k).getD j 0 ∈ digitPool k)
  rcases a with i | (i|t) <;> rcases b with j | (j|u)
  all_goals simp only [sourceValid] at ha hb
  all_goals simp only [sourcePrime] at h
  · exact congrArg Sum.inl (poolIndex_inj (pairPool_nodup k)
      (ha.trans_le (pairPool_length k)) (hb.trans_le (pairPool_length k)) h)
  · have h₁ := (pair i ha).2.2
    have h₂ := (digit j hb).2.1
    omega
  · exact ((pair i ha).2.1 (h ▸ seedPrimes_mem u)).elim
  · have h₁ := (digit i ha).2.1
    have h₂ := (pair j hb).2.2
    omega
  · exact congrArg (Sum.inr ∘ Sum.inl) (poolIndex_inj (digitPool_nodup k)
      (ha.trans_le (digitPool_length k)) (hb.trans_le (digitPool_length k)) h)
  · have h₁ := (digit i ha).2.1
    have h₂ := reserved_le _ (seedPrimes_mem u)
    omega
  · exact ((pair j hb).2.1 (h ▸ seedPrimes_mem t)).elim
  · have h₁ := reserved_le _ (seedPrimes_mem t)
    have h₂ := (digit j hb).2.1
    omega
  · exact congrArg (Sum.inr ∘ Sum.inr) ((by decide : Function.Injective seedPrimes) h)

include hk hw ha in
theorem tailPrime_injective : Function.Injective (tailPrime (T:=T) k) := by
  intro a b h
  apply tailSource_injective hk hw ha
  apply sourcePrime_injective hk (tailSource_valid hk hw ha a) (tailSource_valid hk hw ha b)
  simpa only [tailSource_prime] using h

include hk hw ha in
private theorem tailPrime_ne {q : ℕ} (hq : q = 5 ∨ q = 7) (i : PrimeTag T) :
    tailPrime k i ≠ q := by
  have hrs : q ∈ reservedPrimes := by rcases hq with rfl|rfl <;> decide
  have hq' := reserved_le _ hrs
  have hs := start_large hk
  rcases i with (i|t) | ((i|t) | ⟨i,j⟩)
  · exact fun he => (pairPool_facts (tailPair_in (Nat.lt_of_succ_lt (tailPair_lt hw i)))).2.1
      (by rw [show tailPair k (2*i.val) = q from he]; exact hrs)
  · rcases hq with rfl|rfl <;> fin_cases t <;> norm_num [tailPrime,tailSeedA,tailSeedB,tailSeedDigit]
  · exact fun he => (pairPool_facts (tailPair_in (tailPair_lt hw i))).2.1
      (by rw [show tailPair k (2*i.val+1) = q from he]; exact hrs)
  · rcases hq with rfl|rfl <;> fin_cases t <;> norm_num [tailPrime,tailSeedA,tailSeedB,tailSeedDigit]
  · cases i with
    | inl i =>
      have hh := (digitPool_facts (tailDigit_in hk hw ha i j)).2.1
      change tailDigit k i.val j.val ≠ q
      omega
    | inr t => rcases hq with rfl|rfl <;> fin_cases t <;> norm_num [tailPrime,tailSeedA,tailSeedB,tailSeedDigit]

include hk hw ha in
private theorem tail_representation (i : Channel T) (j : Label T i) :
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ tailPrime k (.inr (.inr ⟨i,j⟩)) =
      a * tailPrime k (.inl i) + b * tailPrime k (.inr (.inl i)) := by
  cases i with
  | inr t =>
    change ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ tailSeedDigit t = a*tailSeedA t+b*tailSeedB t
    fin_cases t
    · exact ⟨1,1,by decide,by decide,by decide⟩
    · exact ⟨8,1,by decide,by decide,by decide⟩
  | inl i =>
    have hA := pairPool_facts (tailPair_in (Nat.lt_of_succ_lt (tailPair_lt hw i)))
    have hB := pairPool_facts (tailPair_in (tailPair_lt hw i))
    have hD := digitPool_facts (tailDigit_in hk hw ha i j)
    have he : tailPair k (2*i.val) ≠ tailPair k (2*i.val+1) :=
      fun h => (by simp : ¬ 2*i.val = 2*i.val+1)
        (poolIndex_inj (pairPool_nodup k)
          ((Nat.lt_of_succ_lt (tailPair_lt hw i)).trans_le (pairPool_length k))
          ((tailPair_lt hw i).trans_le (pairPool_length k)) h)
    have hmul := Nat.mul_le_mul hA.2.2 hB.2.2
    apply TranslationTiling.Compiler.EncodingPrimeSelection.exists_positive_combination
      ((Nat.coprime_primes hA.1 hB.1).mpr he) (hA.1.one_lt) (hB.1.one_lt)
    change tailPair k (2*i.val) * tailPair k (2*i.val+1) +
      tailPair k (2*i.val) + tailPair k (2*i.val+1) < tailDigit k i.val j.val
    have hd := hD.2.1
    unfold guardedDigitStart at hd
    nlinarith only [hd, hmul, hA.2.2, hB.2.2]

include hk hw ha in
def tailEncoding : EncodingParameters T := by
  classical
  choose a b ha₁ hb₁ hab using tail_representation hk hw ha
  refine {
    primeAt := tailPrime k
    prime_isPrime := tailPrime_isPrime hk hw ha
    prime_injective := tailPrime_injective hk hw ha
    prime_ne_p := tailPrime_ne hk hw ha (q := 5) (Or.inl rfl)
    prime_ne_q := tailPrime_ne hk hw ha (q := 7) (Or.inr rfl)
    prime_ne_five := tailPrime_ne hk hw ha (q := 5) (Or.inl rfl)
    seed_a_eq := fun _ => rfl
    seed_b_large := ?_
    blockA := a
    blockB := b
    blockA_pos := ha₁
    blockB_pos := hb₁
    digit_representation := hab
    digitProduct := fun i => ∏ j : Label T i, tailPrime k (.inr (.inr ⟨i,j⟩))
    digitProduct_eq := fun _ => rfl }
  intro t
  fin_cases t <;> norm_num [tailPrime,tailSeedB,show SeedFrame.compact = true from rfl]

theorem tailEncoding_pair (i : Column T) :
    (tailEncoding hk hw ha).a (.inl i) ≤ guardedPairCap k ∧
      (tailEncoding hk hw ha).b (.inl i) ≤ guardedPairCap k :=
  ⟨(pairPool_facts (tailPair_in (Nat.lt_of_succ_lt (tailPair_lt hw i)))).2.2,
    (pairPool_facts (tailPair_in (tailPair_lt hw i))).2.2⟩

theorem tailEncoding_seed_r (t : Fin 2) :
    (tailEncoding hk hw ha).r (.inr t) = tailSeedDigit t := by
  rw [EncodingParameters.r_eq_prod]
  haveI : Unique (Label T (.inr t)) := by change Unique Unit; infer_instance
  rw [Fintype.prod_unique]
  rfl

theorem tailEncoding_r (i : Column T) :
    (tailEncoding hk hw ha).r (.inl i) ≤ (guardedDigitCap k)^6 := by
  let E := tailEncoding hk hw ha
  have hs : (Fintype.card (Label T (.inl i))) ≤ 6 := by
    change Fintype.card (Fin (AlphabetFamily.size i)) ≤ 6
    rw [Fintype.card_fin,ha i,ternaryLayout_arity (by omega) (ordinaryIndex hw i)]
    split_ifs <;> decide
  rw [E.r_eq_prod]
  calc
    _ ≤ ∏ _ : Label T (.inl i), guardedDigitCap k :=
      Finset.prod_le_prod (fun j _ => (digitPool_facts (tailDigit_in hk hw ha i j)).2.2)
    _ ≤ _ := by
      simp only [Finset.prod_const, Finset.card_univ]
      exact Nat.pow_le_pow_right (Nat.zero_le _ |>.trans_lt (guardedDigitCap_gt hk)) hs

theorem tailEncoding_prime_bound (i : PrimeTag T) :
    (tailEncoding hk hw ha).primeAt i ≤ guardedDigitCap k :=
  tailPrime_bound hk hw ha i

theorem tailEncoding_pair_prod :
    (∏ i : Channel T, (tailEncoding hk hw ha).a i * (tailEncoding hk hw ha).b i) ≤
      2^23 * (guardedPairCap k)^(36+4*k) := by
  let E := tailEncoding hk hw ha
  have ho : (∏ i : Column T, E.a (.inl i)*E.b (.inl i)) ≤
      (guardedPairCap k)^(36+4*k) := by
    calc
      _ ≤ ∏ _ : Column T, (guardedPairCap k)^2 := by
        apply Finset.prod_le_prod
        intro i _
        rw [pow_two]
        exact Nat.mul_le_mul (tailEncoding_pair hk hw ha i).1 (tailEncoding_pair hk hw ha i).2
      _ = _ := by
        simp only [Finset.prod_const, Finset.card_univ, Column, Fintype.card_fin, ← pow_mul,
          hw, ternaryLayout_width]
        congr 1
        omega
  have hs : (∏ t : Fin 2, E.a (.inr t)*E.b (.inr t)) ≤ 2^23 := by
    rw [Fin.prod_univ_two]
    change (2*1229)*(3*773) ≤ 2^23
    decide
  rw [Fintype.prod_sum_type]
  exact (Nat.mul_le_mul ho hs).trans_eq (Nat.mul_comm _ _)

theorem tailEncoding_order :
    inputOrder (tailEncoding hk hw ha) ≤ 2^21 * (guardedDigitCap k)^(90+6*k) := by
  let E := tailEncoding hk hw ha
  have hf : Nonempty (Column T) := ⟨⟨0,T.width_pos⟩⟩
  let f : (Σ i : Column T, Label T (.inl i)) → Fin (90+6*k) :=
    fun z => ⟨digitRank z.1.val z.2.val,
      digitRank_lt (by omega) (ordinaryIndex hw z.1) (ordinaryLabel ha z.1 z.2)⟩
  have hi : Function.Injective f := by
    rintro ⟨i,j⟩ ⟨i',j'⟩ h
    have h' := congrArg Fin.val h
    obtain ⟨he,he'⟩ := digitRank_inj (by omega : 0<k) (ordinaryIndex hw i) (ordinaryIndex hw i')
      (ordinaryLabel ha i j) (ordinaryLabel ha i' j') h'
    have he'' : i=i' := Fin.ext he
    subst i'
    have hh : j=j' := Fin.ext he'
    subst j'
    rfl
  have hc : Fintype.card (Σ i : Column T, Label T (.inl i)) ≤ 90+6*k := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective f hi
  have hw' : (∏ i : Column T, E.r (.inl i)) ≤ (guardedDigitCap k)^(90+6*k) := by
    simp_rw [E.r_eq_prod]
    rw [← Fintype.prod_sigma (fun z : Σ i : Column T, Label T (.inl i) => E.digitPrime (.inl z.1) z.2)]
    calc
      _ ≤ ∏ _ : (Σ i : Column T, Label T (.inl i)), guardedDigitCap k :=
        Finset.prod_le_prod (fun z _ => (digitPool_facts (tailDigit_in hk hw ha z.1 z.2)).2.2)
      _ ≤ _ := by
        simp only [Finset.prod_const, Finset.card_univ]
        exact Nat.pow_le_pow_right (Nat.zero_le _ |>.trans_lt (guardedDigitCap_gt hk)) hc
  have hs : (∏ t : Fin 2, E.r (.inr t)) ≤ 2^21 := by
    change (∏ t : Fin 2, (tailEncoding hk hw ha).r (.inr t)) ≤ 2^21
    simp_rw [tailEncoding_seed_r hk hw ha]
    rw [Fin.prod_univ_two]
    decide
  unfold inputOrder
  rw [Fintype.prod_sum_type]
  exact (Nat.mul_le_mul hw' hs).trans_eq (Nat.mul_comm _ _)

theorem tailEncoding_order_mass :
    inputOrder (tailEncoding hk hw ha) * MassSize.mass (tailEncoding hk hw ha) ≤
      2^76 * (guardedDigitCap k)^(180+12*k) * (guardedPairCap k)^(36+4*k) := by
  let E := tailEncoding hk hw ha
  have he : MassSize.mass E = 1225 * inputOrder E * (∏ i : Channel T, E.a i * E.b i) := by
    unfold MassSize.mass inputOrder
    rw [Finset.prod_mul_distrib, mul_assoc]
    have hde : D T = 1225 := by norm_num [D, residueModulus_value, compactSeedFrame]
    rw [hde]
  change inputOrder E * MassSize.mass E ≤ _
  rw [he]
  calc
    _ = 1225 * (inputOrder E)^2 * (∏ i : Channel T, E.a i * E.b i) := by ring
    _ ≤ 2^11 * (2^21*(guardedDigitCap k)^(90+6*k))^2 *
        (2^23*(guardedPairCap k)^(36+4*k)) :=
      Nat.mul_le_mul (Nat.mul_le_mul (by decide)
        (Nat.pow_le_pow_left (tailEncoding_order hk hw ha) 2)) (tailEncoding_pair_prod hk hw ha)
    _ = _ := by
      rw [mul_pow, ← pow_mul, ← pow_mul, show (90+6*k)*2 = 180+12*k by omega]
      rw [show (21 : ℕ)*2 = 42 by decide]
      have htwo : (2 : ℕ)^11 * 2^42 * 2^23 = 2^76 := by
        rw [← pow_add, ← pow_add]
      rw [← htwo]
      ac_rfl

end
end TranslationTiling.FiniteCompiler.Packed
