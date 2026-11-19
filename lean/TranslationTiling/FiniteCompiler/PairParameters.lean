import TranslationTiling.FiniteCompiler.CyclicFactorCRT
import TranslationTiling.FiniteCompiler.CoreSupport
import TranslationTiling.FiniteCompiler.CoreMassBounds
import Mathlib.Data.List.Nodup

/-! Finite prime certificates for alphabets with at most thirty letters per channel. -/
namespace TranslationTiling.FiniteCompiler.PairParameters
open scoped Classical BigOperators
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

structure Profile where
  alphabet : ℕ
  primes : List ℕ
  coeffA : List ℕ
  coeffB : List ℕ

def Profile.entry (p : Profile) (i : ℕ) : ℕ := p.primes.getD i 0
def Profile.arity (p : Profile) (c : ℕ) : ℕ :=
  if c<9 then 4 else if c<18 then 6 else if c<20 then p.alphabet else 1

@[simp] theorem Profile.arity_seed (p : Profile) (t : Fin 2) : p.arity (20+t.val)=1 := by
  unfold Profile.arity
  split_ifs <;> omega

def Representation (p : Profile) (c j : ℕ) : Prop :=
  0<p.coeffA.getD (30*c+j) 0 ∧ 0<p.coeffB.getD (30*c+j) 0 ∧
  p.entry (44+30*c+j)=p.coeffA.getD (30*c+j) 0*p.entry c+
    p.coeffB.getD (30*c+j) 0*p.entry (22+c)
instance (p : Profile) (c j : ℕ) : Decidable (Representation p c j) := by unfold Representation; infer_instance

def Valid (p : Profile) : Prop :=
  p.primes.length=704 ∧ p.primes.Nodup ∧
  (∀ v∈p.primes, v.Prime ∧ v≠5 ∧ v≠7 ∧ v≤65536) ∧
  (0<p.alphabet ∧ p.alphabet≤30) ∧
  (∀ t∈List.range 2, p.entry (20+t)=t+2 ∧ 30625<p.entry (42+t)) ∧
  ∀ c∈List.range 22, ∀ j∈List.range (p.arity c), Representation p c j
instance (p : Profile) : Decidable (Valid p) := by unfold Valid; infer_instance

variable {T : System} [AlphabetFamily T]

def channelIndex : Channel T → ℕ
  | .inl n => n.val
  | .inr t => 20+t.val

def labelIndex (i : Channel T) : Label T i → ℕ := by
  cases i with
  | inl _ => exact fun j => j.val
  | inr _ => exact fun _ => 0

def tagIndex : PrimeTag T → ℕ
  | .inl i => channelIndex i
  | .inr (.inl i) => 22+channelIndex i
  | .inr (.inr j) => 44+30*channelIndex j.1+labelIndex j.1 j.2

variable (p : Profile) (hv : Valid p) (hw : T.width=20)
    (hs : ∀ n : Column T, AlphabetFamily.size (T:=T) n=p.arity n.val)

include hv hw hs

theorem channelIndex_lt (i : Channel T) : channelIndex i<22 := by
  cases i with
  | inl n => have := n.isLt; simp only [channelIndex]; omega
  | inr t => have := t.isLt; simp only [channelIndex]; omega

theorem channelIndex_injective : Function.Injective (channelIndex (T:=T)) := by
  intro i j h
  cases i <;> cases j <;> simp only [channelIndex] at h
  · exact congrArg Sum.inl (Fin.ext h)
  · have := ‹Column T›.isLt; omega
  · have := ‹Column T›.isLt; omega
  · exact congrArg Sum.inr (Fin.ext (by omega))

theorem labelIndex_lt (i : Channel T) (j : Label T i) : labelIndex i j<p.arity (channelIndex i) := by
  cases i with
  | inl n => simpa only [labelIndex,channelIndex,←hs n] using j.isLt
  | inr t => simp [labelIndex,channelIndex]

theorem labelIndex_thirty (i : Channel T) (j : Label T i) : labelIndex i j<30 := by
  have hh := labelIndex_lt p hv hw hs i j
  cases i with
  | inl n =>
    have hn : n.val<20 := by rw [←hw]; exact n.isLt
    change labelIndex (.inl n) j<p.arity n.val at hh
    have ha := hv.2.2.2.1
    unfold Profile.arity at hh
    split_ifs at hh <;> omega
  | inr t => simp [labelIndex]

theorem digitIndex_injective : Function.Injective
    (fun j : Σ i : Channel T, Label T i => 30*channelIndex j.1+labelIndex j.1 j.2) := by
  rintro ⟨i,j⟩ ⟨k,l⟩ h
  change 30*channelIndex i+labelIndex i j=30*channelIndex k+labelIndex k l at h
  have hj := labelIndex_thirty p hv hw hs i j
  have hl := labelIndex_thirty p hv hw hs k l
  have hc : channelIndex i=channelIndex k := by omega
  have he := channelIndex_injective p hv hw hs hc
  subst k
  have he' : labelIndex i j=labelIndex i l := by omega
  have he'' : j=l := by
    cases i with
    | inl n => exact Fin.ext he'
    | inr t => exact Subsingleton.elim (α:=Unit) j l
  subst l
  rfl

theorem tagIndex_lt (i : PrimeTag T) : tagIndex i<704 := by
  rcases i with i | (i | ⟨i,j⟩)
  · exact (channelIndex_lt p hv hw hs i).trans (by decide)
  · have := channelIndex_lt p hv hw hs i; simp only [tagIndex]; omega
  · have := channelIndex_lt p hv hw hs i; have := labelIndex_thirty p hv hw hs i j
    simp only [tagIndex]; omega

theorem tagIndex_injective : Function.Injective (tagIndex (T:=T)) := by
  intro i j h
  rcases i with i | (i | i) <;> rcases j with j | (j | j) <;> simp only [tagIndex] at h
  · exact congrArg Sum.inl (channelIndex_injective p hv hw hs h)
  · have := channelIndex_lt p hv hw hs i; omega
  · have := channelIndex_lt p hv hw hs i; omega
  · have := channelIndex_lt p hv hw hs j; omega
  · exact congrArg (Sum.inr ∘ Sum.inl) (channelIndex_injective p hv hw hs (by omega))
  · have := channelIndex_lt p hv hw hs i; omega
  · have := channelIndex_lt p hv hw hs j; omega
  · have := channelIndex_lt p hv hw hs j; omega
  · exact congrArg (Sum.inr ∘ Sum.inr) (digitIndex_injective p hv hw hs (by dsimp; omega))

theorem at_mem {i : ℕ} (hi : i<704) : p.entry i∈p.primes := by
  unfold Profile.entry
  have hi' : i<p.primes.length := by rw [hv.1]; exact hi
  rw [List.getD_eq_getElem _ _ hi']
  exact List.getElem_mem hi'

def encoding : EncodingParameters T where
  primeAt i := p.entry (tagIndex i)
  prime_isPrime i := (hv.2.2.1 _ (at_mem p hv hw hs (tagIndex_lt p hv hw hs i))).1
  prime_injective := by
    intro i j h
    apply tagIndex_injective p hv hw hs
    have hi : tagIndex i<p.primes.length := by rw [hv.1]; exact tagIndex_lt p hv hw hs i
    have hj : tagIndex j<p.primes.length := by rw [hv.1]; exact tagIndex_lt p hv hw hs j
    have hh : p.primes[tagIndex i]=p.primes[tagIndex j] := by
      simpa only [Profile.entry,List.getD_eq_getElem _ _ hi,List.getD_eq_getElem _ _ hj] using h
    exact (hv.2.1.getElem_inj_iff (hi:=hi) (hj:=hj)).mp hh
  prime_ne_p i := (hv.2.2.1 _ (at_mem p hv hw hs (tagIndex_lt p hv hw hs i))).2.1
  prime_ne_q i := (hv.2.2.1 _ (at_mem p hv hw hs (tagIndex_lt p hv hw hs i))).2.2.1
  prime_ne_five i := (hv.2.2.1 _ (at_mem p hv hw hs (tagIndex_lt p hv hw hs i))).2.1
  seed_a_eq t := (hv.2.2.2.2.1 t.val (List.mem_range.mpr t.isLt)).1
  seed_b_large t := by
    have h := (hv.2.2.2.2.1 t.val (List.mem_range.mpr t.isLt)).2
    convert h using 1 <;> norm_num [tagIndex,channelIndex,Sudoku.SeedModulus,Sudoku.p,Sudoku.q,Nat.add_assoc]
    exact congrArg p.entry (by omega)
  blockA i j := p.coeffA.getD (30*channelIndex i+labelIndex i j) 0
  blockB i j := p.coeffB.getD (30*channelIndex i+labelIndex i j) 0
  blockA_pos i j := (hv.2.2.2.2.2 _ (List.mem_range.mpr (channelIndex_lt p hv hw hs i)) _
    (List.mem_range.mpr (labelIndex_lt p hv hw hs i j))).1
  blockB_pos i j := (hv.2.2.2.2.2 _ (List.mem_range.mpr (channelIndex_lt p hv hw hs i)) _
    (List.mem_range.mpr (labelIndex_lt p hv hw hs i j))).2.1
  digit_representation i j := (hv.2.2.2.2.2 _ (List.mem_range.mpr (channelIndex_lt p hv hw hs i)) _
    (List.mem_range.mpr (labelIndex_lt p hv hw hs i j))).2.2
  digitProduct i := ∏ j : Label T i, p.entry (tagIndex (.inr (.inr ⟨i,j⟩)))
  digitProduct_eq _ := rfl

def Profile.rAt (p : Profile) (c : ℕ) : ℕ :=
  ((List.range (p.arity c)).map fun j => p.entry (44+30*c+j)).prod

def Profile.wordCount (p : Profile) : ℕ := ((List.range 20).map p.arity).prod

def Profile.order (p : Profile) : ℕ :=
  30625*((List.range 22).map fun c => (p.rAt c)^2*p.entry c*p.entry (22+c)).prod

def Profile.mass (p : Profile) : ℕ :=
  30625*((List.range 22).map fun c => p.rAt c*p.entry c*p.entry (22+c)).prod

def SupportValid (p : Profile) (H : ℕ) : Prop :=
  175≤H ∧ (∀ c∈List.range 20, 32*p.rAt c*(p.entry c*p.entry (22+c))^2≤H) ∧
  ∀ t∈List.range 2, 2*(3-t)*p.rAt (20+t)*(p.entry (20+t)*p.entry (42+t))^2*175^3≤H
instance (p : Profile) (H : ℕ) : Decidable (SupportValid p H) := by unfold SupportValid; infer_instance

def labelEquiv (i : Channel T) : Label T i ≃ Fin (p.arity (channelIndex i)) where
  toFun j := ⟨labelIndex i j,labelIndex_lt p hv hw hs i j⟩
  invFun j := by
    cases i with
    | inl n => exact ⟨j.val,by simpa only [channelIndex,←hs n] using j.isLt⟩
    | inr _ => exact ()
  left_inv j := by cases i <;> rfl
  right_inv j := by
    cases i with
    | inl n => rfl
    | inr t =>
      apply Fin.ext
      have hh : j.val<1 := by simpa [channelIndex] using j.isLt
      change 0=j.val
      omega

omit hv hw hs in
private theorem prod_range (w : ℕ) (f : ℕ→ℕ) :
    ((List.range w).map f).prod=∏ i : Fin w, f i.val := by
  have he : (List.range w).map f=List.ofFn (fun i : Fin w => f i.val) := by
    apply List.ext_getElem
    · simp
    · intro i hi hi'; simp
  rw [he,Fin.prod_ofFn]

theorem encoding_r (i : Channel T) : (encoding p hv hw hs).r i=p.rAt (channelIndex i) := by
  rw [(encoding p hv hw hs).r_eq_prod]
  unfold Profile.rAt
  rw [prod_range]
  exact Fintype.prod_equiv (labelEquiv p hv hw hs i) _ _ (fun _ => rfl)

private theorem prod_channels (f : ℕ→ℕ) :
    (∏ c : Channel T, f (channelIndex c))=((List.range 22).map f).prod := by
  rw [prod_range,Fintype.prod_sum_type]
  change (∏ n : Fin T.width, f n.val)*(∏ t : Fin 2, f (20+t.val))=_
  have he := congrArg (fun w : ℕ => ∏ n : Fin w, f n.val) hw
  rw [he]
  exact (Fin.prod_univ_add (a:=20) (b:=2) (fun i => f i.val)).symm

theorem encoding_order : (encoding p hv hw hs).cyclicOrder=p.order := by
  unfold EncodingParameters.cyclicOrder EncodingParameters.blockModulus
  simp_rw [encoding_r p hv hw hs,EncodingParameters.a,EncodingParameters.b,encoding,tagIndex]
  rw [prod_channels p hv hw hs (fun c => (p.rAt c)^2*p.entry c*p.entry (22+c))]
  unfold Profile.order
  have hd : residueModulus^2=30625 := by norm_num [residueModulus_eq,Sudoku.SeedModulus,Sudoku.p,Sudoku.q]
  change residueModulus^2*_=30625*_
  rw [hd]

theorem encoding_mass : MassSize.mass (encoding p hv hw hs)=p.mass := by
  unfold MassSize.mass
  simp_rw [encoding_r p hv hw hs,EncodingParameters.a,EncodingParameters.b,encoding,tagIndex]
  simp_rw [←Nat.mul_assoc]
  rw [prod_channels p hv hw hs (fun c => p.rAt c*p.entry c*p.entry (22+c))]
  unfold Profile.mass
  have hd : residueModulus^2=30625 := by norm_num [residueModulus_eq,Sudoku.SeedModulus,Sudoku.p,Sudoku.q]
  change residueModulus^2*_=30625*_
  rw [hd]

theorem encoding_support {H : ℕ} (hH : SupportValid p H)
    (hS : ∀ n, (T.slope n).natAbs≤16) : CompactSupport.Bound (encoding p hv hw hs) H := by
  have hm : residueModulus≤H := by
    have he : residueModulus=175 := by norm_num [residueModulus_eq,Sudoku.SeedModulus,Sudoku.p,Sudoku.q]
    rw [he]; exact hH.1
  refine ⟨hm,fun n => (hS n).trans ((by norm_num [residueModulus_eq,Sudoku.SeedModulus,Sudoku.p,Sudoku.q] : 16≤residueModulus).trans hm),?_,?_⟩
  · intro n
    unfold CompactSupport.B
    rw [encoding_r p hv hw hs]
    have hh := hH.2.1 n.val (List.mem_range.mpr (by rw [←hw]; exact n.isLt))
    simpa only [EncodingParameters.a,EncodingParameters.b,encoding,tagIndex,channelIndex,Nat.mul_assoc] using hh
  · intro t
    unfold CompactSupport.B
    rw [(encoding p hv hw hs).seed_a,encoding_r p hv hw hs]
    have ho : (otherSeed t).val+2=3-t.val := by dsimp [otherSeed]; have := t.isLt; omega
    rw [ho]
    change 2*(3-t.val)*(p.rAt (20+t.val)*(p.entry (20+t.val)*p.entry (22+(20+t.val)))^2)*residueModulus^3≤H
    have he : residueModulus=175 := by norm_num [residueModulus_eq,Sudoku.SeedModulus,Sudoku.p,Sudoku.q]
    rw [he,show 22+(20+t.val)=42+t.val by omega]
    simpa only [Nat.mul_assoc] using hH.2.2 t.val (List.mem_range.mpr t.isLt)



theorem word_card : Fintype.card (Word T)=p.wordCount := by
  simp only [Word,Letter,Fintype.card_pi,Fintype.card_fin]
  simp_rw [hs]
  unfold Profile.wordCount
  rw [prod_range]
  exact congrArg (fun w : ℕ => ∏ n : Fin w, p.arity n.val) hw

end
end TranslationTiling.FiniteCompiler.PairParameters
