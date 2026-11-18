import TranslationTiling.FiniteCompiler.CompactParameters
import TranslationTiling.Compiler.IntervalPrimeCounting

namespace TranslationTiling.FiniteCompiler
open scoped Classical BigOperators
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

/-- Only the two seed b-primes need the large seed threshold. -/
theorem exists_economical_useful (T : System) (hC : 962 ≤ channelCount T) :
    ∃ u : UsefulTag T → ℕ, Function.Injective u ∧
      (∀ i, (u i).Prime ∧ u i ≤ channelCount T ^ 4 ∧ u i ≠ Sudoku.p ∧ u i ≠ Sudoku.q) ∧
      (∀ i, u i ≠ 5) ∧
      (∀ t : Fin 2, u (.inl (.inr t)) = t.val+2) ∧
      (∀ t : Fin 2, residueModulus^2 < u (.inr (.inr t))) ∧
      (∀ i, u i≤usefulPrimeCap (channelCount T)) ∧
      (∀ n : Column T, u (.inl (.inl n))*u (.inr (.inl n))≤channelCount T^3 ∧
        u (.inl (.inl n))*u (.inr (.inl n))+u (.inl (.inl n))+u (.inr (.inl n))≤
          15*channelCount T^3/32+2*Compiler.Size.economicalUsefulCap (channelCount T)) ∧
      (∀ i, u (.inl i)*u (.inr i)≤channelCount T^4 ∧
        u (.inl i)*u (.inr i)+u (.inl i)+u (.inr i)≤
          max (channelCount T^3+2*Compiler.Size.economicalUsefulCap (channelCount T))
            (4*Compiler.Size.seedPrime1+3)) ∧
      ∀ i, u i≤max (Compiler.Size.economicalUsefulCap (channelCount T)) Compiler.Size.seedPrime1 := by
  let C := channelCount T
  let D : ℕ := 244453225
  have hD : 2 ≤ D := by norm_num [D,residueModulus_eq,Sudoku.SeedModulus,Sudoku.p,Sudoku.q]
  let b0 := Compiler.Size.seedPrime0
  let b1 := Compiler.Size.seedPrime1
  have hb0 := Compiler.Size.seedPrime0_prime
  have hb1 := Compiler.Size.seedPrime1_prime
  have hb0l : D<b0 := by norm_num [b0,D,Compiler.Size.seedPrime0,residueModulus_eq,Sudoku.SeedModulus,Sudoku.p,Sudoku.q]
  have hb1l : D<b1 := by norm_num [b1,D,Compiler.Size.seedPrime1,residueModulus_eq,Sudoku.SeedModulus,Sudoku.p,Sudoku.q]
  have hb0u : b0≤2*D := by norm_num [b0,D,Compiler.Size.seedPrime0,residueModulus_eq,Sudoku.SeedModulus,Sudoku.p,Sudoku.q]
  have hb1u : b1≤4*D := by norm_num [b1,D,Compiler.Size.seedPrime1,residueModulus_eq,Sudoku.SeedModulus,Sudoku.p,Sudoku.q]
  have hb01 : b0<b1 := by norm_num [b0,b1,Compiler.Size.seedPrime0,Compiler.Size.seedPrime1]
  have hbig : 4*D ≤ C^4 := by
    apply (show 4*D≤962^4 by
      norm_num [D,residueModulus_eq,Sudoku.SeedModulus,Sudoku.p,Sudoku.q]).trans
    exact Nat.pow_le_pow_left hC 4
  let U := Compiler.Size.economicalUsefulCap C
  obtain ⟨hU2,hUC,hpi,hDigit⟩ := Compiler.Size.economical_caps hC
  let banned : Finset ℕ := {2,3,5,Sudoku.p,Sudoku.q,b0,b1}
  let pool := Nat.primesLE U \ banned
  have hban : banned.card ≤ 7 := by
    have he : banned = [2,3,5,Sudoku.p,Sudoku.q,b0,b1].toFinset := by ext x; simp [banned]
    rw [he]
    exact List.toFinset_card_le _
  have hpool : 2*T.width ≤ pool.card := by
    have hp := hpi
    have hs := Finset.card_le_card_sdiff_add_card (s:=Nat.primesLE U) (t:=banned)
    rw [Nat.primesLE_card_eq_primeCounting] at hs
    dsimp [pool,C,U] at *
    unfold channelCount at *
    omega
  let small := Nat.primesLE (Compiler.Size.asymmetricUsefulCap C) \ banned
  have hsmall : T.width≤small.card := by
    have hp := Compiler.Size.asymmetric_useful_count hC
    have hs := Finset.card_le_card_sdiff_add_card (s:=Nat.primesLE (Compiler.Size.asymmetricUsefulCap C)) (t:=banned)
    rw [Nat.primesLE_card_eq_primeCounting] at hs
    dsimp [small,C] at *
    unfold channelCount at *
    omega
  obtain ⟨fa⟩ := Function.Embedding.nonempty_of_card_le
    (show Fintype.card (Column T)≤Fintype.card ↥small by simpa [Column] using hsmall)
  let a (n : Column T) : ℕ := (fa n).val
  have ha (n) : (a n).Prime ∧ a n≤Compiler.Size.asymmetricUsefulCap C ∧ a n∉banned := by
    obtain ⟨hp,hn⟩ := Finset.mem_sdiff.mp (fa n).property
    exact ⟨(Nat.mem_primesLE.mp hp).2,(Nat.mem_primesLE.mp hp).1,hn⟩
  have hcap : Compiler.Size.asymmetricUsefulCap C≤U := by
    have hd := Nat.mul_div_le (15*U) 32
    change 32*(15*U/32)≤15*U at hd
    change 15*U/32≤U
    omega
  let rest := pool \ Finset.univ.image a
  have hrest : T.width≤rest.card := by
    have hs := Finset.card_le_card_sdiff_add_card (s:=pool) (t:=Finset.univ.image a)
    have hi : (Finset.univ.image a).card≤T.width := by simpa [Column] using Finset.card_image_le (s:=Finset.univ) (f:=a)
    dsimp [rest] at *
    omega
  obtain ⟨fb⟩ := Function.Embedding.nonempty_of_card_le
    (show Fintype.card (Column T)≤Fintype.card ↥rest by simpa [Column] using hrest)
  let b (n : Column T) : ℕ := (fb n).val
  have hb (n) : (b n).Prime ∧ b n≤U ∧ b n∉banned := by
    obtain ⟨hp,hn⟩ := Finset.mem_sdiff.mp (Finset.mem_sdiff.mp (fb n).property).1
    exact ⟨(Nat.mem_primesLE.mp hp).2,(Nat.mem_primesLE.mp hp).1,hn⟩
  let g : Column T ⊕ Column T → ℕ := Sum.elim a b
  have hg (i) : (g i).Prime ∧ g i≤U ∧ g i∉banned := by
    cases i with
    | inl n => exact ⟨(ha n).1,(ha n).2.1.trans hcap,(ha n).2.2⟩
    | inr n => exact hb n
  have hginj : Function.Injective g := by
    apply Function.Injective.sumElim
    · exact fun i j he => fa.injective (Subtype.ext he)
    · exact fun i j he => fb.injective (Subtype.ext he)
    · intro i j he
      have hn := (Finset.mem_sdiff.mp (fb j).property).2
      exact hn (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,he⟩)
  let e : UsefulTag T ≃ (Column T ⊕ Column T) ⊕ (Fin 2 ⊕ Fin 2) :=
    Equiv.sumSumSumComm (Column T) (Fin 2) (Column T) (Fin 2)
  let seed : Fin 2 ⊕ Fin 2 → ℕ := Sum.elim (fun t => t.val+2) (fun t => if t=0 then b0 else b1)
  have hseedinj : Function.Injective seed := by
    intro i j h
    have hd : 1000 < D := by norm_num [D,residueModulus_eq,Sudoku.SeedModulus,Sudoku.p,Sudoku.q]
    rcases i with i | i <;> rcases j with j | j
    · exact congrArg Sum.inl (Fin.ext (by simpa [seed] using h))
    · fin_cases i <;> fin_cases j <;> simp [seed] at h <;> omega
    · fin_cases i <;> fin_cases j <;> simp [seed] at h <;> omega
    · fin_cases i <;> fin_cases j <;> simp_all [seed] <;> omega
  have hsep (i) (j) : g i ≠ seed j := by
    have h := (hg i).2.2
    rcases j with j | j <;> fin_cases j <;> simp [seed] <;> intro he <;> simp [banned,he] at h
  let u : UsefulTag T → ℕ := Sum.elim g seed ∘ e
  refine ⟨u,(hginj.sumElim hseedinj hsep).comp e.injective,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro i
    change (u i).Prime ∧ u i ≤ C^4 ∧ u i ≠ Sudoku.p ∧ u i ≠ Sudoku.q
    dsimp only [u,Function.comp_apply]
    cases he : e i with
    | inl j =>
      have hn := (hg j).2.2
      exact ⟨(hg j).1,(((hg j).2.1.trans hUC).trans (Nat.pow_le_pow_right (by omega : 1≤C) (by decide))),by intro he; change g j = _ at he; exact hn (by simp [banned,he]),by intro he; change g j = _ at he; exact hn (by simp [banned,he])⟩
    | inr j =>
      have hd : 1000 < D := by norm_num [D,residueModulus_eq,Sudoku.SeedModulus,Sudoku.p,Sudoku.q]
      rcases j with j | j <;> fin_cases j <;> simp [seed,Sudoku.p,Sudoku.q]
      all_goals norm_num [Sudoku.p,Sudoku.q] at *
      all_goals first | exact ⟨hb0,by omega,by omega,by omega⟩ | exact ⟨hb1,by omega,by omega,by omega⟩ | omega
  · intro i
    change Sum.elim g seed (e i) ≠ 5
    cases he : e i with
    | inl j =>
      have h := (hg j).2.2
      intro he
      change g j = 5 at he
      exact h (by simp [banned,he])
    | inr j =>
      have hd : 1000 < D := by norm_num [D,residueModulus_eq,Sudoku.SeedModulus,Sudoku.p,Sudoku.q]
      rcases j with j | j <;> fin_cases j <;> simp [seed] <;> omega
  · intro t
    rfl
  · intro t
    change residueModulus^2 < if t=0 then b0 else b1
    have hd : residueModulus^2≤D := by norm_num [D,residueModulus_eq,Sudoku.SeedModulus,Sudoku.p,Sudoku.q]
    split_ifs <;> omega

  · intro i
    change Sum.elim g seed (e i)≤usefulPrimeCap C
    cases he : e i with
    | inl j => exact ((hg j).2.1.trans hUC).trans (square_le_usefulPrimeCap C)
    | inr j =>
      have hb : seed j≤4*D := by
        rcases j with j | j <;> fin_cases j <;> simp [seed] <;> omega
      apply hb.trans
      unfold usefulPrimeCap usefulStart
      norm_num [D,residueModulus_eq,Sudoku.SeedModulus,Sudoku.p,Sudoku.q]
      nlinarith
  · intro n
    have hd := Nat.mul_div_le (15*U) 32
    have has : 32*a n≤15*U := by
      apply (Nat.mul_le_mul_left 32 (ha n).2.1).trans
      exact hd
    have hm := Nat.mul_le_mul_right (b n) has
    have hu := Nat.mul_le_mul_left (15*U) (hb n).2.1
    have hU := Nat.mul_le_mul_left 15 hU2
    have hp : a n*b n≤15*C^3/32 := (Nat.le_div_iff_mul_le (by decide : 0<32)).mpr (by nlinarith only [hm,hu,hU])
    have hdiv := Nat.mul_div_le (15*C^3) 32
    have hap : a n≤U := (ha n).2.1.trans hcap
    have hbp := (hb n).2.1
    change a n*b n≤C^3 ∧ a n*b n+a n+b n≤15*C^3/32+2*U
    constructor
    · omega
    · omega

  · intro i
    cases i with
    | inl n =>
      change g (.inl n)*g (.inr n)≤C^4 ∧
        g (.inl n)*g (.inr n)+g (.inl n)+g (.inr n)≤max (C^3+2*U) (4*b1+3)
      have ha := (hg (.inl n)).2.1
      have hb := (hg (.inr n)).2.1
      have hm : g (.inl n)*g (.inr n)≤C^3 :=
        (Nat.mul_le_mul ha hb).trans (by simpa [pow_two] using hU2)
      exact ⟨hm.trans (Nat.pow_le_pow_right (by omega) (by decide)),
        (by nlinarith : g (.inl n)*g (.inr n)+g (.inl n)+g (.inr n)≤C^3+2*U).trans (le_max_left _ _)⟩
    | inr t =>
      change (t.val+2)*(if t=0 then b0 else b1)≤C^4 ∧
        (t.val+2)*(if t=0 then b0 else b1)+(t.val+2)+(if t=0 then b0 else b1)≤max (C^3+2*U) (4*b1+3)
      have ht := t.isLt
      have hb : (if t=0 then b0 else b1)≤4*D := by split_ifs <;> omega
      have hm : (t.val+2)*(if t=0 then b0 else b1)≤12*D := by nlinarith
      have hfixed : 16*D+3≤C^4 := by
        apply (show 16*D+3≤962^4 by norm_num [D,residueModulus_eq,Sudoku.SeedModulus,Sudoku.p,Sudoku.q]).trans
        exact Nat.pow_le_pow_left hC 4
      have hth : (t.val+2)*(if t=0 then b0 else b1)+(t.val+2)+(if t=0 then b0 else b1)≤4*b1+3 := by
        fin_cases t <;> simp <;> omega
      exact ⟨by omega,hth.trans (le_max_right _ _)⟩

  · intro i
    change Sum.elim g seed (e i)≤max U b1
    cases he : e i with
    | inl j => exact (hg j).2.1.trans (le_max_left _ _)
    | inr j =>
      apply (show seed j≤b1 from ?_).trans (le_max_right _ _)
      rcases j with j | j <;> fin_cases j <;> simp [seed] <;> omega

/-- Separate caps for ordinary channels and the two exceptional seed channels. -/
def EconomicalPrimes {T : System} (E : EncodingParameters T) : Prop :=
  (∀ i, E.a i≤channelCount T^4 ∧ E.b i≤channelCount T^4) ∧
  (∀ i j, E.digitPrime i j≤channelCount T^4) ∧
  (∀ i, E.a i*E.b i≤channelCount T^4) ∧
  (∀ n : Column T, E.a (.inl n)*E.b (.inl n)≤channelCount T^3) ∧
  (∀ i j, E.digitPrime i j^20≤channelCount T^71) ∧
  ∀ n j, E.digitPrime (.inl n) j≤channelCount T^3

theorem exists_economical_parameters (T : System) (hC : 962≤channelCount T) (hB : T.alphabet=3) :
    ∃ E : EncodingParameters T,
      (∀ i, E.a i≤usefulPrimeCap (channelCount T) ∧ E.b i≤usefulPrimeCap (channelCount T)) ∧
      (∀ i j, E.digitPrime i j≤digitPrimeCap T.alphabet (channelCount T)) ∧ EconomicalPrimes E := by
  obtain ⟨u,huinj,hu,hfive,hseed,hlarge,hOld,hOrd,hpair,huseful⟩ := exists_economical_useful T hC
  let C := channelCount T
  change 962≤C at hC
  simp only [← show C=channelCount T from rfl] at hu hOld hOrd hpair huseful
  let F := 15*C^3/32+2*Compiler.Size.economicalUsefulCap C
  let L := Compiler.Size.ordinaryDigitThreshold C
  let Q := C^3
  have hL : L=F+117 := by norm_num [L,F,Compiler.Size.ordinaryDigitThreshold,Sudoku.p,Sudoku.q]
  have hseedF : Compiler.Size.seedPrime1≤F := by
    have hc : 962^3≤C^3 := Nat.pow_le_pow_left hC 3
    have hd := Nat.mod_add_div (15*C^3) 32
    have hm := Nat.mod_lt (15*C^3) (by decide : 0<32)
    dsimp [F]
    norm_num [Compiler.Size.seedPrime1] at *
    omega
  have hu' (i : UsefulTag T) : (u i).Prime ∧ u i≤F ∧ u i≠Sudoku.p ∧ u i≠Sudoku.q := by
    refine ⟨(hu i).1,?_,(hu i).2.2⟩
    have huse := huseful i
    change u i≤max (Compiler.Size.economicalUsefulCap C) Compiler.Size.seedPrime1 at huse
    apply huse.trans
    exact max_le (by dsimp [F]; omega) hseedF
  let pool := Nat.primesLE Q \ Nat.primesLE L
  have hLQ : L≤Q := by
    have hh : 40*L≤19*Q := Compiler.Size.ordinary_threshold_bound hC
    dsimp only [Q] at hh ⊢
    omega
  have hsub : Nat.primesLE L⊆Nat.primesLE Q := by
    intro z hz
    exact Nat.mem_primesLE.mpr ⟨(Nat.mem_primesLE.mp hz).1.trans hLQ,(Nat.mem_primesLE.mp hz).2⟩
  have hpool : 3*C+1≤pool.card := by
    have hh : Nat.primeCounting L+3*C+1≤Nat.primeCounting Q := Compiler.Size.ordinary_interval_count hC
    simp only [pool,Finset.card_sdiff_of_subset hsub,Nat.primesLE_card_eq_primeCounting]
    omega
  let Ordinary := Σ n : Column T, Label T (.inl n)
  have hcard : Fintype.card Ordinary≤Fintype.card ↥pool := by
    have hh : Fintype.card Ordinary=3*T.width := by simp [Ordinary,Label,Letter,uniform_size,Symbol,hB,Column,Nat.mul_comm]
    simp only [Fintype.card_coe,hh]
    unfold C channelCount at hpool
    omega
  obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le hcard
  let go (j : Ordinary) : ℕ := (f j).val
  have hgo (j) : (go j).Prime ∧ L<go j ∧ go j≤Q := by
    obtain ⟨hp,hn⟩ := Finset.mem_sdiff.mp (f j).property
    obtain ⟨hb,hpr⟩ := Nat.mem_primesLE.mp hp
    change go j≤Q at hb
    change (go j).Prime at hpr
    change go j∉Nat.primesLE L at hn
    have hl : L<go j := by
      by_contra hh
      exact hn (Nat.mem_primesLE.mpr ⟨by omega,hpr⟩)
    exact ⟨hpr,hl,hb⟩
  let B := max Q (max (C^3+2*Compiler.Size.economicalUsefulCap C) (4*Compiler.Size.seedPrime1+3)+117)
  have hBpos : 0<B := by dsimp [B]; positivity
  obtain ⟨z0,hz0,hz0lo,hz0hi⟩ := Nat.bertrand B (Nat.ne_of_gt hBpos)
  obtain ⟨z1,hz1,hz1lo,hz1hi⟩ := Nat.bertrand z0 hz0.ne_zero
  have hBcap : B≤2*C^3 := by
    have hu : Compiler.Size.economicalUsefulCap C≤C^2 := (Compiler.Size.economical_caps hC).2.1
    have hc : 962^3≤C^3 := Nat.pow_le_pow_left hC 3
    have hh : 962*C^2≤C^3 := by
      calc
        _ ≤ C*C^2 := Nat.mul_le_mul_right (C^2) hC
        _ = _ := by ring
    dsimp [B,Q]
    norm_num [Compiler.Size.seedPrime1] at *
    omega
  have hz0cap : z0≤C^4 := by
    have hh := Nat.mul_le_mul_right (C^3) hC
    nlinarith only [hz0hi,hBcap,hh]
  have hz1cap : z1≤C^4 := by
    have hh := Nat.mul_le_mul_right (C^3) hC
    nlinarith only [hz1hi,hz0hi,hBcap,hh]
  let g : (Σ i : Channel T, Label T i) → ℕ := fun j => match j with
    | ⟨.inl n,l⟩ => go ⟨n,l⟩
    | ⟨.inr t,_⟩ => if t=0 then z0 else z1
  have hgp (j) : (g j).Prime := by
    rcases j with ⟨n,j⟩
    cases n with
    | inl n => exact (hgo ⟨n,j⟩).1
    | inr t => change (if t=0 then z0 else z1).Prime; split_ifs <;> assumption
  have hggt (j) : F+117<g j := by
    rw [← hL]
    rcases j with ⟨n,j⟩
    cases n with
    | inl n => exact (hgo ⟨n,j⟩).2.1
    | inr t =>
      have hb : L≤B := hLQ.trans (le_max_left _ _)
      change L<(if t=0 then z0 else z1)
      split_ifs <;> omega
  have hthreshold (i) (j) : u (.inl i)*u (.inr i)+u (.inl i)+u (.inr i)<g ⟨i,j⟩ := by
    cases i with
    | inl n =>
      have hh : u (.inl (.inl n))*u (.inr (.inl n))+u (.inl (.inl n))+u (.inr (.inl n))≤F := (hOrd n).2
      change _<go ⟨n,j⟩
      apply hh.trans_lt
      have hg := (hgo ⟨n,j⟩).2.1
      rw [hL] at hg
      omega
    | inr t =>
      have hh := (hpair (.inr t)).2
      have hb : max (C^3+2*Compiler.Size.economicalUsefulCap C) (4*Compiler.Size.seedPrime1+3)≤B := by dsimp [B]; omega
      change _<(if t=0 then z0 else z1)
      split_ifs <;> omega
  have hginj : Function.Injective g := by
    rintro ⟨i,j⟩ ⟨i',j'⟩ he
    cases i with
    | inl n =>
      cases i' with
      | inl n' =>
        have hh : (⟨n,j⟩:Ordinary)=⟨n',j'⟩ := f.injective (Subtype.ext he)
        cases hh
        rfl
      | inr t =>
        have hl := (hgo ⟨n,j⟩).2.2
        have hb : Q≤B := le_max_left _ _
        change go ⟨n,j⟩=(if t=0 then z0 else z1) at he
        split_ifs at he <;> omega
    | inr t =>
      cases i' with
      | inl n =>
        have hl := (hgo ⟨n,j'⟩).2.2
        have hb : Q≤B := le_max_left _ _
        change (if t=0 then z0 else z1)=go ⟨n,j'⟩ at he
        split_ifs at he <;> omega
      | inr t' =>
        have ht : t=t' := by
          change (if t=0 then z0 else z1)=(if t'=0 then z0 else z1) at he
          fin_cases t <;> fin_cases t' <;> simp_all
        subst t'
        congr 1
  have hgb (j) : g j≤C^4 := by
    rcases j with ⟨n,j⟩
    cases n with
    | inl n => exact (hgo ⟨n,j⟩).2.2.trans (Nat.pow_le_pow_right (by omega : 1≤C) (by decide))
    | inr t => change (if t=0 then z0 else z1)≤C^4; split_ifs <;> assumption
  obtain ⟨E,he,hd⟩ := exists_parameters_of_pair_bounded_families_exact T F (C^4) u huinj hu' hfive hseed hlarge
    g hgp (fun j => by have hh := hggt j; norm_num [Sudoku.p,Sudoku.q] at *; omega) hthreshold hginj hgb
  refine ⟨E,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro i; rw [(he i).1,(he i).2]; exact ⟨hOld _,hOld _⟩
  · intro i j
    rw [hB,hd]
    exact (hgb ⟨i,j⟩).trans ((Nat.pow_le_pow_right (by omega : 1≤C) (by decide : 4≤5)).trans (fifth_le_digitPrimeCap (by omega)))
  · intro i; rw [(he i).1,(he i).2]; exact ⟨(hu _).2.1,(hu _).2.1⟩
  · intro i j; rw [hd]; exact hgb ⟨i,j⟩
  · intro i; rw [(he i).1,(he i).2]; exact (hpair i).1
  · intro n; rw [(he (.inl n)).1,(he (.inl n)).2]; exact (hOrd n).1
  · intro i j
    rw [hd]
    have hbound : g ⟨i,j⟩≤8*C^3 := by
      cases i with
      | inl n => exact (hgo ⟨n,j⟩).2.2.trans (by dsimp [Q]; omega)
      | inr t => change (if t=0 then z0 else z1)≤8*C^3; split_ifs <;> omega
    have hh : 8^20≤C^11 := (by norm_num : 8^20≤962^11).trans (Nat.pow_le_pow_left hC _)
    calc
      _ ≤ (8*C^3)^20 := Nat.pow_le_pow_left hbound _
      _ = 8^20*C^60 := by ring
      _ ≤ C^11*C^60 := Nat.mul_le_mul_right _ hh
      _ = _ := by ring
  · intro n j; rw [hd]; exact (hgo ⟨n,j⟩).2.2

theorem EconomicalPrimes.compact {T : System} {E : EncodingParameters T} (h : EconomicalPrimes E) :
    CompactPrimes E :=
  ⟨h.1,fun i j => (h.2.1 i j).trans (Nat.pow_le_pow_right (by unfold channelCount; omega) (by decide)),h.2.2.1⟩

theorem exists_bounded_parameters_economical (T : System) :
    ∃ E : EncodingParameters T,
      (∀ i, E.a i≤usefulPrimeCap (channelCount T) ∧ E.b i≤usefulPrimeCap (channelCount T)) ∧
      (∀ i j, E.digitPrime i j≤digitPrimeCap T.alphabet (channelCount T)) ∧
      (596750≤channelCount T ∧ T.alphabet=3 →
        (∀ i, E.a i≤channelCount T^2 ∧ E.b i≤channelCount T^2) ∧
        (∀ i j, E.digitPrime i j≤channelCount T^3) ∧
        ∀ i, (E.a i*E.b i)^3≤channelCount T^8) ∧
      (1202≤channelCount T ∧ T.alphabet=3 → CompactPrimes E) ∧
      (962≤channelCount T ∧ T.alphabet=3 → EconomicalPrimes E) := by
  by_cases hbig : 596750≤channelCount T ∧ T.alphabet=3
  · obtain ⟨E,hu,hd,ht,hc⟩ := exists_bounded_parameters_compact T
    refine ⟨E,hu,hd,ht,hc,fun _ => ?_⟩
    have hs := ht hbig
    have h1 : 1≤channelCount T := by omega
    have he : EconomicalPrimes E := by
      refine ⟨fun i => ⟨(hs.1 i).1.trans (Nat.pow_le_pow_right h1 (by decide)),
        (hs.1 i).2.trans (Nat.pow_le_pow_right h1 (by decide))⟩,
        fun i j => (hs.2.1 i j).trans (Nat.pow_le_pow_right h1 (by decide)),
        (hc ⟨by omega,hbig.2⟩).2.2,(fun n => ?_),(fun i j => ?_),fun n j => hs.2.1 (.inl n) j⟩
      · apply (Nat.pow_le_pow_iff_left (by decide : 3≠0)).mp
        apply (hs.2.2 (.inl n)).trans
        rw [← pow_mul]
        exact Nat.pow_le_pow_right h1 (by decide)
      · apply (Nat.pow_le_pow_left (hs.2.1 i j) 20).trans
        rw [← pow_mul]
        exact Nat.pow_le_pow_right h1 (by decide)
    exact he
  · by_cases hshort : 962≤channelCount T ∧ T.alphabet=3
    · obtain ⟨E,hu,hd,hc⟩ := exists_economical_parameters T hshort.1 hshort.2
      exact ⟨E,hu,hd,fun h => (hbig h).elim,fun _ => hc.compact,fun _ => hc⟩
    · obtain ⟨E,hu,hd,ht,hc⟩ := exists_bounded_parameters_compact T
      exact ⟨E,hu,hd,ht,hc,fun h => (hshort h).elim⟩

theorem economical_r_le {T : System} (E : EncodingParameters T) (hB : T.alphabet=3)
    (hp : EconomicalPrimes E) (i : Channel T) : E.r i≤channelCount T^12 := by
  rw [E.r_eq_prod]
  calc
    _ ≤ ∏ _j : Label T i, channelCount T^4 := Finset.prod_le_prod (fun j _ => hp.2.1 i j)
    _ = channelCount T^(4*Fintype.card (Label T i)) := by simp [← pow_mul]
    _ ≤ _ := Nat.pow_le_pow_right (by unfold channelCount; omega)
      (by cases i <;> simp [Label,Letter,uniformAlphabetFamily,Symbol,hB])

theorem economical_seed_r_le {T : System} (E : EncodingParameters T)
    (hp : EconomicalPrimes E) (t : Fin 2) : E.r (.inr t)≤channelCount T^4 := by
  rw [E.r_eq_prod]
  calc
    _ ≤ ∏ _j : Label T (.inr t), channelCount T^4 := Finset.prod_le_prod (fun j _ => hp.2.1 (.inr t) j)
    _ = channelCount T^(4*Fintype.card (Label T (.inr t))) := by simp [← pow_mul]
    _ = _ := by simp [Label]

theorem economical_parameterBudget {T : System} (E : EncodingParameters T) (hC : 962≤channelCount T)
    (hB : T.alphabet=3) (hp : EconomicalPrimes E) (hS : ∀ n, (T.slope n).natAbs≤Sudoku.Width) :
    Size.ParameterBudget E (channelCount T^12) ∧ channelCount T≤channelCount T^12 ∧
      T.alphabet+1≤channelCount T^12 := by
  have h1 : 1≤channelCount T := by omega
  have hc : channelCount T≤channelCount T^12 := Nat.le_self_pow (by decide) _
  have hseed : residueModulus≤channelCount T^2 := by
    apply (show residueModulus≤962^2 by norm_num [residueModulus_eq,Sudoku.SeedModulus,Sudoku.p,Sudoku.q]).trans
    exact Nat.pow_le_pow_left hC 2
  have hwidth : Sudoku.Width≤channelCount T^2 := by
    apply (show Sudoku.Width≤962^2 by norm_num [Sudoku.Width,Sudoku.q]).trans
    exact Nat.pow_le_pow_left hC 2
  refine ⟨⟨(by omega : 2≤channelCount T).trans hc,
    hseed.trans (Nat.pow_le_pow_right h1 (by decide)),economical_r_le E hB hp,
    fun i => (hp.1 i).1.trans (Nat.pow_le_pow_right h1 (by decide)),
    fun i => (hp.1 i).2.trans (Nat.pow_le_pow_right h1 (by decide)),
    fun n => (hS n).trans (hwidth.trans (Nat.pow_le_pow_right h1 (by decide)))⟩,hc,?_⟩
  rw [hB]
  exact (by omega : 4≤channelCount T).trans hc

theorem economical_r_le_nine {T : System} (E : EncodingParameters T) (hB : T.alphabet=3)
    (hp : EconomicalPrimes E) (i : Channel T) : E.r i≤channelCount T^9 := by
  cases i with
  | inl n =>
    rw [E.r_eq_prod]
    calc
      _ ≤ ∏ _j : Label T (.inl n), channelCount T^3 := Finset.prod_le_prod (fun j _ => hp.2.2.2.2.2 n j)
      _ = _ := by simp [Label,Letter,uniformAlphabetFamily,Symbol,hB,← pow_mul]
  | inr t => exact (economical_seed_r_le E hp t).trans (Nat.pow_le_pow_right (by unfold channelCount; omega) (by decide))

theorem economical_parameterBudget_nine {T : System} (E : EncodingParameters T) (hC : 962≤channelCount T)
    (hB : T.alphabet=3) (hp : EconomicalPrimes E) (hS : ∀ n, (T.slope n).natAbs≤Sudoku.Width) :
    Size.ParameterBudget E (channelCount T^9) ∧ channelCount T≤channelCount T^9 ∧
      T.alphabet+1≤channelCount T^9 := by
  have h1 : 1≤channelCount T := by omega
  have hc : channelCount T≤channelCount T^9 := Nat.le_self_pow (by decide) _
  have hseed : residueModulus≤channelCount T^2 := by
    apply (show residueModulus≤962^2 by norm_num [residueModulus_eq,Sudoku.SeedModulus,Sudoku.p,Sudoku.q]).trans
    exact Nat.pow_le_pow_left hC 2
  have hwidth : Sudoku.Width≤channelCount T^2 := by
    apply (show Sudoku.Width≤962^2 by norm_num [Sudoku.Width,Sudoku.q]).trans
    exact Nat.pow_le_pow_left hC 2
  refine ⟨⟨(by omega : 2≤channelCount T).trans hc,
    hseed.trans (Nat.pow_le_pow_right h1 (by decide)),economical_r_le_nine E hB hp,
    fun i => (hp.1 i).1.trans (Nat.pow_le_pow_right h1 (by decide)),
    fun i => (hp.1 i).2.trans (Nat.pow_le_pow_right h1 (by decide)),
    fun n => (hS n).trans (hwidth.trans (Nat.pow_le_pow_right h1 (by decide)))⟩,hc,?_⟩
  rw [hB]
  exact (by omega : 4≤channelCount T).trans hc

end
end TranslationTiling.FiniteCompiler
