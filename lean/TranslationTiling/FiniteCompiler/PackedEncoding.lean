import TranslationTiling.FiniteCompiler.PackedProfiles
import TranslationTiling.FiniteCompiler.CyclicFactorCRT
import TranslationTiling.FiniteCompiler.CoreMassBounds

namespace TranslationTiling.FiniteCompiler.Packed

open TranslationTiling.FiniteCompiler.Effective
open scoped BigOperators
noncomputable section

local instance : SeedFrame := compactSeedFrame

abbrev Profile.I (p : Profile) := Fin (p.width+2)
abbrev Profile.Tag (p : Profile) := p.I ⊕ p.I ⊕ ((i : p.I) × Fin (p.arity i.val))

def Profile.atPrime (p : Profile) : p.Tag → ℕ
  | .inl i => p.a i.val
  | .inr (.inl i) => p.b i.val
  | .inr (.inr ⟨i,j⟩) => (p.digit i.val j.val).1

def Profile.injectivityCheck (p : Profile) : Prop :=
  (Finset.univ.image p.atPrime).card = Fintype.card p.Tag

instance (p : Profile) : Decidable p.injectivityCheck := by unfold Profile.injectivityCheck; infer_instance

theorem profile1_injective : profile1.injectivityCheck := by decide +kernel
theorem profile12_injective : profile12.injectivityCheck := by decide +kernel
theorem profile36_injective : profile36.injectivityCheck := by decide +kernel
theorem profile243_injective : profile243.injectivityCheck := by decide +kernel

variable (p : Profile) (hv : Valid p)

include hv in
private theorem atPrime_mem (i : p.Tag) : p.atPrime i ∈ p.primes := by
  have hp (i : p.I) : i.val < p.pairs.length := by rw [hv.1]; exact i.isLt
  have hr (i : p.I) : i.val < p.digits.length := by rw [hv.2.1]; exact i.isLt
  have hm (i : p.I) : p.pairs.getD i.val (0,0) ∈ p.pairs := by
    rw [List.getD_eq_getElem _ _ (hp i)]
    exact List.getElem_mem _
  change p.atPrime i ∈ _ ++ _
  rcases i with i | (i | ⟨i,j⟩)
  · exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨_,hm i,by simp [Profile.atPrime,Profile.a]⟩)
  · exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨_,hm i,by simp [Profile.atPrime,Profile.b]⟩)
  · apply List.mem_append_right
    apply List.mem_flatMap.mpr
    refine ⟨p.row i.val, ?_, List.mem_map.mpr ⟨p.digit i.val j.val, ?_, rfl⟩⟩
    · unfold Profile.row
      rw [List.getD_eq_getElem _ _ (hr i)]
      exact List.getElem_mem _
    · have hj : j.val < (p.row i.val).length := by
        rw [(hv.2.2.2.2.1 i.val (List.mem_range.mpr i.isLt)).1]
        exact j.isLt
      unfold Profile.digit
      rw [List.getD_eq_getElem _ _ hj]
      exact List.getElem_mem _

variable {T : System} [AlphabetFamily T]
  (hw : T.width = p.width) (ha : ∀ n : Column T, AlphabetFamily.size (T:=T) n = p.arity n.val)

def channelEquiv : Channel T ≃ p.I :=
  ((finCongr hw).sumCongr (Equiv.refl _)).trans finSumFinEquiv

@[simp] theorem channel_inl (n : Column T) :
    (channelEquiv p hw (.inl n)).val = n.val := rfl

@[simp] theorem channel_inr (t : Fin 2) :
    (channelEquiv p hw (.inr t)).val = p.width+t.val := rfl

private theorem arity_seed (t : Fin 2) : p.arity (p.width+t.val) = 1 := by
  unfold Profile.arity
  have he : 18 ≤ p.width := by unfold Profile.width; omega
  split_ifs <;> omega

private def labelEquiv (i : Channel T) : Label T i ≃ Fin (p.arity (channelEquiv p hw i).val) := by
  cases i with
  | inl n => exact finCongr (ha n)
  | inr t =>
    rw [channel_inr, arity_seed]
    change Unit ≃ Fin 1
    exact Equiv.ofUnique ..

private def tagEquiv : PrimeTag T ≃ p.Tag :=
  (channelEquiv p hw).sumCongr ((channelEquiv p hw).sumCongr
    (Equiv.sigmaCongr (channelEquiv p hw) (labelEquiv p hw ha)))

include hv in
private theorem representation (i : p.I) (j : Fin (p.arity i.val)) :
    let d := p.digit i.val j.val
    0 < d.2.1 ∧ 0 < d.2.2 ∧ d.1 = d.2.1*p.a i.val + d.2.2*p.b i.val := by
  obtain ⟨hlen, h⟩ := hv.2.2.2.2.1 i.val (List.mem_range.mpr i.isLt)
  apply h
  unfold Profile.digit
  have hj : j.val < (p.row i.val).length := by rw [hlen]; exact j.isLt
  rw [List.getD_eq_getElem _ _ hj]
  exact List.getElem_mem _

def encoding (hinj : p.injectivityCheck) : EncodingParameters T where
  primeAt := p.atPrime ∘ tagEquiv p hw ha
  prime_isPrime i := (hv.2.2.2.1 _ (atPrime_mem p hv _)).1
  prime_ne_p i := (hv.2.2.2.1 _ (atPrime_mem p hv _)).2.1
  prime_ne_q i := (hv.2.2.2.1 _ (atPrime_mem p hv _)).2.2.1
  prime_ne_five i := (hv.2.2.2.1 _ (atPrime_mem p hv _)).2.1
  prime_injective := by
    apply Function.Injective.comp _ (tagEquiv p hw ha).injective
    have hi := Finset.card_image_iff.mp hinj
    exact fun _ _ he => hi (Finset.mem_univ _) (Finset.mem_univ _) he
  seed_a_eq t := (hv.2.2.2.2.2 t.val (List.mem_range.mpr t.isLt)).1
  seed_b_large t := by
    change 1225 < p.b (p.width+t.val) ∨ t=1 ∧
      p.b (p.width+t.val)%3=2 ∧ 1225 < 2*p.b (p.width+t.val)
    have h : t.val = 1 ↔ t = 1 := ⟨fun e => Fin.ext e, fun e => congrArg Fin.val e⟩
    simpa only [h] using (hv.2.2.2.2.2 t.val (List.mem_range.mpr t.isLt)).2
  blockA i j := (p.digit (channelEquiv p hw i).val (labelEquiv p hw ha i j).val).2.1
  blockB i j := (p.digit (channelEquiv p hw i).val (labelEquiv p hw ha i j).val).2.2
  blockA_pos i j := (representation p hv _ (labelEquiv p hw ha i j)).1
  blockB_pos i j := (representation p hv _ (labelEquiv p hw ha i j)).2.1
  digit_representation i j := (representation p hv _ (labelEquiv p hw ha i j)).2.2
  digitProduct i := ∏ j : Label T i, p.atPrime (tagEquiv p hw ha (.inr (.inr ⟨i,j⟩)))
  digitProduct_eq _ := rfl

variable (hinj : p.injectivityCheck)

theorem encoding_prime (i : PrimeTag T) :
    (encoding p hv hw ha hinj).primeAt i ≤ 65536 :=
  (hv.2.2.2.1 _ (atPrime_mem p hv _)).2.2.2

theorem encoding_r (i : Channel T) :
    (encoding p hv hw ha hinj).r i = p.r (channelEquiv p hw i).val := by
  let c := channelEquiv p hw i
  have hlen := (hv.2.2.2.2.1 c.val (List.mem_range.mpr c.isLt)).1
  rw [(encoding p hv hw ha hinj).r_eq_prod]
  calc
    _ = ∏ j : Fin (p.arity c.val), (p.digit c.val j.val).1 :=
      Fintype.prod_equiv (labelEquiv p hw ha i) _ _ (fun _ => rfl)
    _ = p.r c.val := by
      unfold Profile.r
      rw [← Fin.prod_ofFn]
      congr 1
      apply List.ext_getElem
      · simp [hlen]
      · intro n h1 h2
        simp only [List.getElem_ofFn, List.getElem_map]
        unfold Profile.digit
        rw [List.getD_eq_getElem _ _ (by simpa using h2)]

private theorem prod_channels (f : ℕ → ℕ) :
    (∏ i : Channel T, f (channelEquiv p hw i).val) = ((List.range (p.width+2)).map f).prod := by
  calc
    _ = ∏ i : p.I, f i.val :=
      Fintype.prod_equiv (channelEquiv p hw) _ _ (fun _ => rfl)
    _ = _ := ?_
  rw [← Fin.prod_ofFn]
  congr 1
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.getElem_ofFn,List.getElem_map,List.getElem_range]

theorem encoding_inputOrder :
    inputOrder (encoding p hv hw ha hinj) = p.inputOrder := by
  unfold inputOrder Profile.inputOrder
  simp_rw [encoding_r]
  exact prod_channels p hw p.r

theorem encoding_mass :
    MassSize.mass (encoding p hv hw ha hinj) = p.mass := by
  unfold MassSize.mass Profile.mass
  have hd : D T = 1225 := by
    change residueModulus^2 = 1225
    norm_num [residueModulus_value,compactSeedFrame]
  rw [hd]
  simp_rw [encoding_r]
  exact congrArg (1225*·) (prod_channels p hw (fun i => p.r i*(p.a i*p.b i)))

end
end TranslationTiling.FiniteCompiler.Packed
