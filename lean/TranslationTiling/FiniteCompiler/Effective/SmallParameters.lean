import TranslationTiling.FiniteCompiler.Effective.SmallProfiles

namespace TranslationTiling.FiniteCompiler.Effective.SmallProfiles
open scoped Classical BigOperators
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

variable {T : System}

def channelIndex : Channel T → ℕ
  | .inl n => n.val
  | .inr t => T.width+t.val

theorem channelIndex_lt (i : Channel T) : channelIndex i<T.width+2 := by
  cases i <;> simp only [channelIndex] <;> omega

theorem channelIndex_injective : Function.Injective (channelIndex (T:=T)) := by
  intro i j h
  cases i <;> cases j <;> simp only [channelIndex] at h
  · exact congrArg Sum.inl (Fin.ext h)
  · omega
  · omega
  · exact congrArg Sum.inr (Fin.ext (by omega))

def digitIndex (i : Channel T) : Label T i → ℕ := by
  cases i with
  | inl n => exact fun j => 3*n.val+j.val
  | inr t => exact fun _ => 3*T.width+t.val

theorem digitIndex_lt (hB : T.alphabet=3) (i : Channel T) (j : Label T i) :
    digitIndex i j<3*T.width+2 := by
  cases i with
  | inl n => have hj : j.val<3 := hB ▸ j.isLt; simp only [digitIndex]; omega
  | inr t => simp only [digitIndex]; omega

theorem digitIndex_injective (hB : T.alphabet=3) : Function.Injective
    (fun j : Σ i : Channel T, Label T i => digitIndex j.1 j.2) := by
  rintro ⟨i,j⟩ ⟨i',j'⟩ h
  cases i with
  | inl n =>
    have hj : j.val<3 := hB ▸ j.isLt
    cases i' with
    | inl n' =>
      have hj' : j'.val<3 := hB ▸ j'.isLt
      simp only [digitIndex] at h
      have hn : n=n' := Fin.ext (by omega)
      subst n'
      have he : j=j' := Fin.ext (by omega)
      subst j'; rfl
    | inr t => simp only [digitIndex] at h; omega
  | inr t =>
    cases i' with
    | inl n' =>
      have hj' : j'.val<3 := hB ▸ j'.isLt
      simp only [digitIndex] at h; omega
    | inr t' =>
      simp only [digitIndex] at h
      have ht : t=t' := Fin.ext (by omega)
      subst t'
      cases j
      cases j'
      rfl

def tagIndex : PrimeTag T → ℕ
  | .inl i => channelIndex i
  | .inr (.inl i) => T.width+2+channelIndex i
  | .inr (.inr j) => 2*T.width+4+digitIndex j.1 j.2

theorem tagIndex_lt (hB : T.alphabet=3) (i : PrimeTag T) : tagIndex i<5*T.width+6 := by
  rcases i with i | (i | ⟨i,j⟩)
  · exact (channelIndex_lt i).trans_le (by omega)
  · have := channelIndex_lt i; simp only [tagIndex]; omega
  · have := digitIndex_lt hB i j; simp only [tagIndex]; omega

theorem tagIndex_injective (hB : T.alphabet=3) : Function.Injective (tagIndex (T:=T)) := by
  intro i j h
  rcases i with i | (i | i) <;> rcases j with j | (j | j) <;>
    simp only [tagIndex] at h
  · exact congrArg Sum.inl (channelIndex_injective h)
  · have := channelIndex_lt i; omega
  · have := channelIndex_lt i; omega
  · have := channelIndex_lt j; omega
  · exact congrArg (Sum.inr ∘ Sum.inl) (channelIndex_injective (by omega))
  · have := channelIndex_lt i; omega
  · have := channelIndex_lt j; omega
  · have := channelIndex_lt j; omega
  · exact congrArg (Sum.inr ∘ Sum.inr) (digitIndex_injective hB (Nat.add_left_cancel h))

theorem at_mem {w : ℕ} {p : Profile} (hv : Valid w p) {i : ℕ} (hi : i<5*w+6) :
    p.entry i∈p.primes := by
  unfold Profile.entry
  have hi' : i<p.primes.length := by rw [hv.1]; exact hi
  rw [List.getD_eq_getElem _ _ hi']
  exact List.getElem_mem hi'

def encoding (p : Profile) (hv : Valid T.width p) (hB : T.alphabet=3) : EncodingParameters T where
  primeAt := fun i => p.entry (tagIndex i)
  prime_isPrime := fun i => (hv.2.2.1 _ (at_mem hv (tagIndex_lt hB i))).1
  prime_injective := by
    intro i j h
    apply tagIndex_injective hB
    have hi : tagIndex i<p.primes.length := by rw [hv.1]; exact tagIndex_lt hB i
    have hj : tagIndex j<p.primes.length := by rw [hv.1]; exact tagIndex_lt hB j
    have hh : p.primes[tagIndex i]=p.primes[tagIndex j] := by
      simpa only [Profile.entry,List.getD_eq_getElem _ _ hi,List.getD_eq_getElem _ _ hj] using h
    exact (hv.2.1.getElem_inj_iff (hi:=hi) (hj:=hj)).mp hh
  prime_ne_p := fun i => (hv.2.2.1 _ (at_mem hv (tagIndex_lt hB i))).2.1
  prime_ne_q := fun i => (hv.2.2.1 _ (at_mem hv (tagIndex_lt hB i))).2.2.1
  prime_ne_five := fun i => (hv.2.2.1 _ (at_mem hv (tagIndex_lt hB i))).2.1
  seed_a_eq := fun t => (hv.2.2.2.1 t.val (List.mem_range.mpr t.isLt)).1
  seed_b_large := fun t => by
    have h := (hv.2.2.2.1 t.val (List.mem_range.mpr t.isLt)).2
    convert h using 1 <;> simp [tagIndex,channelIndex,Sudoku.SeedModulus,Sudoku.p,Sudoku.q] <;> congr 1 <;> omega
  blockA := fun i j => p.coeffA.getD (digitIndex i j) 0
  blockB := fun i j => p.coeffB.getD (digitIndex i j) 0
  blockA_pos := by
    intro i j
    cases i with
    | inl n => exact (hv.2.2.2.2.2.1 n.val (List.mem_range.mpr n.isLt) j.val (List.mem_range.mpr (hB ▸ j.isLt))).1
    | inr t => exact (hv.2.2.2.2.2.2 t.val (List.mem_range.mpr t.isLt)).1
  blockB_pos := by
    intro i j
    cases i with
    | inl n => exact (hv.2.2.2.2.2.1 n.val (List.mem_range.mpr n.isLt) j.val (List.mem_range.mpr (hB ▸ j.isLt))).2.1
    | inr t => exact (hv.2.2.2.2.2.2 t.val (List.mem_range.mpr t.isLt)).2.1
  digit_representation := by
    intro i j
    cases i with
    | inl n => exact (hv.2.2.2.2.2.1 n.val (List.mem_range.mpr n.isLt) j.val (List.mem_range.mpr (hB ▸ j.isLt))).2.2
    | inr t =>
      have h := (hv.2.2.2.2.2.2 t.val (List.mem_range.mpr t.isLt)).2.2
      simpa only [tagIndex,channelIndex,digitIndex,show T.width+2+(T.width+t.val)=2*T.width+2+t.val by omega] using h
  digitProduct := fun i => ∏ j : Label T i, p.entry (tagIndex (.inr (.inr ⟨i,j⟩)))
  digitProduct_eq := fun _ => rfl

end
end TranslationTiling.FiniteCompiler.Effective.SmallProfiles

namespace TranslationTiling.FiniteCompiler.Effective.SmallProfiles
open scoped Classical
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def width (i : Fin 5) : ℕ := 48+16*i.val

def profile (i : Fin 5) : Profile :=
  if i=0 then profile48 else if i=1 then profile64 else if i=2 then profile80
  else if i=3 then profile96 else profile112

theorem profile_valid (i : Fin 5) : Valid (width i) (profile i) := by
  fin_cases i
  · exact profile48_valid
  · exact profile64_valid
  · exact profile80_valid
  · exact profile96_valid
  · exact profile112_valid

def shape (i : Fin 5) : System := ⟨width i,by unfold width; omega,3,fun _ => 0,∅,fun _ _ => False⟩

theorem encoding_prime_bound {T : System} (p : Profile) (hv : Valid T.width p)
    (hB : T.alphabet=3) (i : PrimeTag T) : (encoding p hv hB).primeAt i≤65536 :=
  (hv.2.2.1 _ (at_mem hv (tagIndex_lt hB i))).2.2.2

theorem encoding_pair_bound {T : System} (p : Profile) (hv : Valid T.width p)
    (hB : T.alphabet=3) (i : Channel T) :
    (encoding p hv hB).a i*(encoding p hv hB).b i≤256^3 :=
  hv.2.2.2.2.1 (channelIndex i) (List.mem_range.mpr (channelIndex_lt i))

end
end TranslationTiling.FiniteCompiler.Effective.SmallProfiles

namespace TranslationTiling.FiniteCompiler.Effective.SmallProfiles
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def horizontal (i : Fin 5) : ℕ :=
  if i=0 then horizontal48 else if i=1 then horizontal64 else if i=2 then horizontal80
  else if i=3 then horizontal96 else horizontal112

def exponent (i : Fin 5) : ℕ :=
  if i=0 then 6629 else if i=1 then 9124 else if i=2 then 11678
  else if i=3 then 14302 else 17001

theorem support (i : Fin 5) : SupportValid (profile i) (width i) (horizontal i) := by
  fin_cases i
  · exact support48
  · exact support64
  · exact support80
  · exact support96
  · exact support112

theorem volume (i : Fin 5) :
    (horizontal i)^2≤(2^15*3^(2*width i+2))*(profile i).order (width i) ∧
    (2^24*549072*8003^4)*(horizontal i)^2*(profile i).order (width i)*
      (profile i).mass (width i)*(2^15*3^(2*width i+2))^2≤2^exponent i := by
  fin_cases i
  · exact volume48
  · exact volume64
  · exact volume80
  · exact volume96
  · exact volume112

end TranslationTiling.FiniteCompiler.Effective.SmallProfiles
