import TranslationTiling.FiniteCompiler.CompactParameters
import TranslationTiling.Compiler.EconomicalPrimeCounting

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
      (∀ n : Column T, u (.inl (.inl n))*u (.inr (.inl n))≤channelCount T^3) ∧
      ∀ i, u (.inl i)*u (.inr i)≤channelCount T^4 ∧
        u (.inl i)*u (.inr i)+u (.inl i)+u (.inr i)≤
          max (channelCount T^3+2*Compiler.Size.economicalUsefulCap (channelCount T))
            (16*residueModulus^2+3) := by
  let C := channelCount T
  let D := residueModulus^2
  have hD : 2 ≤ D := by norm_num [D,residueModulus_eq,Sudoku.SeedModulus,Sudoku.p,Sudoku.q]
  obtain ⟨b0,hb0,hb0l,hb0u⟩ := Nat.bertrand D (by omega)
  obtain ⟨b1,hb1,hb1l,hb1u⟩ := Nat.bertrand (2*D) (by omega)
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
  have hcard : Fintype.card (Column T ⊕ Column T) ≤ Fintype.card ↥pool := by
    simpa [Column,Fintype.card_sum,Fintype.card_coe,two_mul] using hpool
  obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le hcard
  let g (i : Column T ⊕ Column T) : ℕ := (f i).val
  have hg (i) : (g i).Prime ∧ g i ≤ U ∧ g i ∉ banned := by
    have hp := (f i).property
    obtain ⟨hp,hn⟩ := Finset.mem_sdiff.mp hp
    exact ⟨(Nat.mem_primesLE.mp hp).2,(Nat.mem_primesLE.mp hp).1,hn⟩
  have hginj : Function.Injective g := fun _ _ h => f.injective (Subtype.ext h)
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
  refine ⟨u,(hginj.sumElim hseedinj hsep).comp e.injective,?_,?_,?_,?_,?_,?_,?_⟩
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
    change D < if t=0 then b0 else b1
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
      change 4*D≤(8*(D+Sudoku.p+Sudoku.q+3+2*C+1))^2
      nlinarith
  · intro n
    change g (.inl n)*g (.inr n)≤C^3
    exact (Nat.mul_le_mul (hg (.inl n)).2.1 (hg (.inr n)).2.1).trans
      (by simpa [pow_two] using hU2)
  · intro i
    cases i with
    | inl n =>
      change g (.inl n)*g (.inr n)≤C^4 ∧
        g (.inl n)*g (.inr n)+g (.inl n)+g (.inr n)≤max (C^3+2*U) (16*D+3)
      have ha := (hg (.inl n)).2.1
      have hb := (hg (.inr n)).2.1
      have hm : g (.inl n)*g (.inr n)≤C^3 :=
        (Nat.mul_le_mul ha hb).trans (by simpa [pow_two] using hU2)
      exact ⟨hm.trans (Nat.pow_le_pow_right (by omega) (by decide)),
        (by nlinarith : g (.inl n)*g (.inr n)+g (.inl n)+g (.inr n)≤C^3+2*U).trans (le_max_left _ _)⟩
    | inr t =>
      change (t.val+2)*(if t=0 then b0 else b1)≤C^4 ∧
        (t.val+2)*(if t=0 then b0 else b1)+(t.val+2)+(if t=0 then b0 else b1)≤max (C^3+2*U) (16*D+3)
      have ht := t.isLt
      have hb : (if t=0 then b0 else b1)≤4*D := by split_ifs <;> omega
      have hm : (t.val+2)*(if t=0 then b0 else b1)≤12*D := by nlinarith
      have hfixed : 16*D+3≤C^4 := by
        apply (show 16*D+3≤962^4 by norm_num [D,residueModulus_eq,Sudoku.SeedModulus,Sudoku.p,Sudoku.q]).trans
        exact Nat.pow_le_pow_left hC 4
      exact ⟨by omega,(by nlinarith : _≤16*D+3).trans (le_max_right _ _)⟩

/-- Separate caps for ordinary channels and the two exceptional seed channels. -/
def EconomicalPrimes {T : System} (E : EncodingParameters T) : Prop :=
  (∀ i, E.a i≤channelCount T^4 ∧ E.b i≤channelCount T^4) ∧
  (∀ i j, E.digitPrime i j≤channelCount T^4) ∧
  (∀ i, E.a i*E.b i≤channelCount T^4) ∧
  ∀ n : Column T, E.a (.inl n)*E.b (.inl n)≤channelCount T^3

theorem exists_economical_parameters (T : System) (hC : 962≤channelCount T) (hB : T.alphabet=3) :
    ∃ E : EncodingParameters T,
      (∀ i, E.a i≤usefulPrimeCap (channelCount T) ∧ E.b i≤usefulPrimeCap (channelCount T)) ∧
      (∀ i j, E.digitPrime i j≤digitPrimeCap T.alphabet (channelCount T)) ∧ EconomicalPrimes E := by
  obtain ⟨u,huinj,hu,hfive,hseed,hlarge,hOld,hOrd,hpair⟩ := exists_economical_useful T hC
  let C := channelCount T
  let F := max (C^3+2*Compiler.Size.economicalUsefulCap C) (16*residueModulus^2+3)
  let L := F+Sudoku.p+Sudoku.q+5
  have hu' (i : UsefulTag T) : (u i).Prime ∧ u i≤F ∧ u i≠Sudoku.p ∧ u i≠Sudoku.q := by
    refine ⟨(hu i).1,?_,(hu i).2.2⟩
    cases i with
    | inl i => have hh := (hpair i).2; change _≤F at hh; omega
    | inr i => have hh := (hpair i).2; change _≤F at hh; omega
  let Tags := Σ i : Channel T, Label T i
  let ix : Tags ≃ Fin (Fintype.card Tags) := Fintype.equivFin _
  let g (j : Tags) := Nat.nth Nat.Prime (L+(ix j).val)
  have hg (j : Tags) : L<g j := by
    have h := Nat.add_two_le_nth_prime (L+(ix j).val)
    dsimp [g]; omega
  obtain ⟨E,he,hp⟩ := exists_parameters_of_pair_bounded_families T F (C^4) u huinj hu' hfive hseed hlarge
    g (fun _ => Nat.prime_nth_prime _) (by
      intro j; have h := hg j; dsimp [L] at h; omega) (by
      intro i j
      have h := hg ⟨i,j⟩
      have hh := (hpair i).2
      change u (.inl i)*u (.inr i)+u (.inl i)+u (.inr i)≤max (C^3+2*Compiler.Size.economicalUsefulCap C) (16*residueModulus^2+3) at hh
      change _≤F at hh
      dsimp [L] at h
      omega) (by
      intro i j h
      apply ix.injective
      apply Fin.ext
      have hh := (Nat.nth_strictMono Nat.infinite_setOfPred_prime).injective h
      change L+(ix i).val=L+(ix j).val at hh
      omega) (by
      intro j
      have hcard : Fintype.card Tags≤3*C := by
        rw [Fintype.card_sigma]
        calc
          _ ≤ ∑ _i : Channel T, 3 := Finset.sum_le_sum (fun i _ => by cases i <;> simp [Label,Symbol,hB])
          _ = _ := by simp [C,channelCount,Nat.mul_comm]
      have hpi : L+3*C+1≤Nat.primeCounting (C^4) := by
        simpa [L,F,Compiler.Size.economicalDigitThreshold,residueModulus_eq] using (Compiler.Size.economical_caps hC).2.2.2
      have hk := (ix j).isLt
      have hh : L+(ix j).val<Nat.count Nat.Prime (C^4+1) := by
        change _<Nat.primeCounting (C^4)
        omega
      exact Nat.le_of_lt_succ (Nat.nth_lt_of_lt_count hh))
  refine ⟨E,?_,?_,?_,hp,?_,?_⟩
  · intro i; rw [(he i).1,(he i).2]; exact ⟨hOld _,hOld _⟩
  · intro i j
    rw [hB]
    exact (hp i j).trans ((Nat.pow_le_pow_right (by omega : 1≤C) (by decide : 4≤5)).trans (fifth_le_digitPrimeCap (by omega)))
  · intro i; rw [(he i).1,(he i).2]; exact ⟨(hu _).2.1,(hu _).2.1⟩
  · intro i; rw [(he i).1,(he i).2]; exact (hpair i).1

  · intro n; rw [(he (.inl n)).1,(he (.inl n)).2]; exact hOrd n

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
        (hc ⟨by omega,hbig.2⟩).2.2,fun n => ?_⟩
      apply (Nat.pow_le_pow_iff_left (by decide : 3≠0)).mp
      apply (hs.2.2 (.inl n)).trans
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
      (by cases i <;> simp [Label,Symbol,hB])

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

end
end TranslationTiling.FiniteCompiler
