import TranslationTiling.FiniteCompiler.SharpParameters
import TranslationTiling.Compiler.TightPrimeCounting

namespace TranslationTiling.FiniteCompiler
open scoped Classical BigOperators
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

/-- Only the two seed b-primes need the large seed threshold. -/
theorem exists_tight_useful (T : System) (hC : 596750 ≤ channelCount T) :
    ∃ u : UsefulTag T → ℕ, Function.Injective u ∧
      (∀ i, (u i).Prime ∧ u i ≤ channelCount T ^ 2 ∧ u i ≠ Sudoku.p ∧ u i ≠ Sudoku.q) ∧
      (∀ i, u i ≠ 5) ∧
      (∀ t : Fin 2, u (.inl (.inr t)) = t.val+2) ∧
      (∀ t : Fin 2, residueModulus^2 < u (.inr (.inr t))) ∧
      ∀ i, (u (.inl i)*u (.inr i))^3 ≤ channelCount T^8 ∧
        u (.inl i)*u (.inr i)+u (.inl i)+u (.inr i) ≤
          Compiler.Size.tightUsefulCap (channelCount T)^2+2*Compiler.Size.tightUsefulCap (channelCount T) := by
  let C := channelCount T
  let D := residueModulus^2
  let U := Compiler.Size.tightUsefulCap C
  obtain ⟨hU3,hUlo,hUsq,hpi,_⟩ := Compiler.Size.tight_caps C hC
  have hD : 2 ≤ D := by norm_num [D,residueModulus_eq,Sudoku.SeedModulus,Sudoku.p,Sudoku.q]
  obtain ⟨b0,hb0,hb0l,hb0u⟩ := Nat.bertrand D (by omega)
  obtain ⟨b1,hb1,hb1l,hb1u⟩ := Nat.bertrand (2*D) (by omega)
  have hbig : 4*D ≤ C^2 := by
    dsimp [D]
    rw [residueModulus_eq]
    norm_num [Sudoku.SeedModulus,Sudoku.p,Sudoku.q]
    have h := Nat.pow_le_pow_left hC 2
    norm_num at h
    exact (by norm_num : 221398480900 ≤ 596750^2).trans h
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
  refine ⟨u,(hginj.sumElim hseedinj hsep).comp e.injective,?_,?_,?_,?_,?_⟩
  · intro i
    change (u i).Prime ∧ u i ≤ C^2 ∧ u i ≠ Sudoku.p ∧ u i ≠ Sudoku.q
    dsimp only [u,Function.comp_apply]
    cases he : e i with
    | inl j =>
      have hn := (hg j).2.2
      exact ⟨(hg j).1,(hg j).2.1.trans hUsq,by intro he; change g j = _ at he; exact hn (by simp [banned,he]),by intro he; change g j = _ at he; exact hn (by simp [banned,he])⟩
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
    cases i with
    | inl n =>
      change (g (.inl n)*g (.inr n))^3 ≤ C^8 ∧ _
      have ha := (hg (.inl n)).2.1
      have hb := (hg (.inr n)).2.1
      have hm := Nat.mul_le_mul ha hb
      constructor
      · calc
          _ ≤ (U*U)^3 := Nat.pow_le_pow_left hm 3
          _ = (U^3)^2 := by ring
          _ ≤ (C^4)^2 := Nat.pow_le_pow_left hU3 2
          _ = _ := by ring
      · change g (.inl n)*g (.inr n)+g (.inl n)+g (.inr n) ≤ U^2+2*U
        nlinarith
    | inr t =>
      change ((t.val+2)*(if t=0 then b0 else b1))^3 ≤ C^8 ∧ _
      have ht := t.isLt
      have hb : (if t=0 then b0 else b1)≤4*D := by split_ifs <;> omega
      have hm : (t.val+2)*(if t=0 then b0 else b1)≤12*D := by nlinarith
      constructor
      · apply (Nat.pow_le_pow_left hm 3).trans
        apply (show (12*D)^3≤596750^8 by norm_num [D,residueModulus_eq,Sudoku.SeedModulus,Sudoku.p,Sudoku.q]).trans
        exact Nat.pow_le_pow_left hC 8
      · change (t.val+2)*(if t=0 then b0 else b1)+(t.val+2)+(if t=0 then b0 else b1)≤U^2+2*U
        have hmin : 16*D+3≤(84*596750)^2 := by norm_num [D,residueModulus_eq,Sudoku.SeedModulus,Sudoku.p,Sudoku.q]
        have hu := Nat.pow_le_pow_left ((Nat.mul_le_mul_left 84 hC).trans hUlo) 2
        nlinarith

/-- Pairwise Frobenius thresholds need only cubically bounded digit primes. -/
theorem exists_tight_parameters (T : System) (hC : 596750≤channelCount T) (hB : T.alphabet=3) :
    ∃ E : EncodingParameters T,
      (∀ i, E.a i≤channelCount T^2 ∧ E.b i≤channelCount T^2) ∧
      (∀ i j, E.digitPrime i j≤channelCount T^3) ∧
      ∀ i, (E.a i*E.b i)^3≤channelCount T^8 := by
  obtain ⟨u,huinj,hu,hfive,hseed,hlarge,hpair⟩ := exists_tight_useful T hC
  let C := channelCount T
  let Tags := Σ i : Channel T, Label T i
  let ix : Tags ≃ Fin (Fintype.card Tags) := Fintype.equivFin _
  let g (j : Tags) := Nat.nth Nat.Prime (Compiler.Size.tightDigitThreshold C+(ix j).val)
  have hg (j : Tags) : Compiler.Size.tightDigitThreshold C<g j := by
    have h := Nat.add_two_le_nth_prime (Compiler.Size.tightDigitThreshold C+(ix j).val)
    dsimp [g]; omega
  obtain ⟨E,he,hp⟩ := exists_parameters_of_pair_bounded_families T (C^2) (C^3) u huinj hu hfive hseed hlarge
    g (fun _ => Nat.prime_nth_prime _) (by
      intro j
      have h := hg j
      obtain ⟨_,hlo,_,_,_⟩ := Compiler.Size.tight_caps C hC
      unfold Compiler.Size.tightDigitThreshold at h
      have hh := Nat.pow_le_pow_left hlo 2
      nlinarith) (by
      intro i j
      have h := hg ⟨i,j⟩
      have hpair := (hpair i).2
      change u (.inl i)*u (.inr i)+u (.inl i)+u (.inr i)≤Compiler.Size.tightUsefulCap C^2+2*Compiler.Size.tightUsefulCap C at hpair
      unfold Compiler.Size.tightDigitThreshold at h
      omega) (by
      intro i j h
      apply ix.injective
      apply Fin.ext
      have hh := (Nat.nth_strictMono Nat.infinite_setOfPred_prime).injective h
      change Compiler.Size.tightDigitThreshold C+(ix i).val=Compiler.Size.tightDigitThreshold C+(ix j).val at hh
      omega) (by
      intro j
      have hcard : Fintype.card Tags≤3*C := by
        rw [Fintype.card_sigma]
        calc
          _ ≤ ∑ _i : Channel T, 3 := Finset.sum_le_sum (fun i _ => by cases i <;> simp [Label,Symbol,hB])
          _ = _ := by simp [C,channelCount,Nat.mul_comm]
      have hp := (Compiler.Size.tight_caps C hC).2.2.2.2
      have hk := (ix j).isLt
      have hh : Compiler.Size.tightDigitThreshold C+(ix j).val<Nat.count Nat.Prime (C^3+1) := by
        change _<Nat.primeCounting (C^3)
        omega
      exact Nat.le_of_lt_succ (Nat.nth_lt_of_lt_count hh))
  refine ⟨E,?_,hp,?_⟩
  · intro i
    rw [(he i).1,(he i).2]
    exact ⟨(hu (.inl i)).2.1,(hu (.inr i)).2.1⟩
  · intro i
    rw [(he i).1,(he i).2]
    exact (hpair i).1

theorem exists_bounded_parameters_tight (T : System) :
    ∃ E : EncodingParameters T,
      (∀ i, E.a i≤usefulPrimeCap (channelCount T) ∧ E.b i≤usefulPrimeCap (channelCount T)) ∧
      (∀ i j, E.digitPrime i j≤digitPrimeCap T.alphabet (channelCount T)) ∧
      (596750≤channelCount T ∧ T.alphabet=3 →
        (∀ i, E.a i≤channelCount T^2 ∧ E.b i≤channelCount T^2) ∧
        (∀ i j, E.digitPrime i j≤channelCount T^3) ∧
        ∀ i, (E.a i*E.b i)^3≤channelCount T^8) := by
  by_cases h : 596750≤channelCount T ∧ T.alphabet=3
  · obtain ⟨E,hu,hp,hpair⟩ := exists_tight_parameters T h.1 h.2
    refine ⟨E,fun i => ⟨(hu i).1.trans (square_le_usefulPrimeCap _),
      (hu i).2.trans (square_le_usefulPrimeCap _)⟩,?_,fun _ => ⟨hu,hp,hpair⟩⟩
    intro i j
    apply (hp i j).trans
    rw [h.2]
    exact (Nat.pow_le_pow_right (by unfold channelCount; omega) (by decide : 3≤5)).trans
      (fifth_le_digitPrimeCap (by unfold channelCount; omega))
  · obtain ⟨E,hu,hp⟩ := exists_bounded_parameters T
    exact ⟨E,hu,hp,fun hh => (h hh).elim⟩

end
end TranslationTiling.FiniteCompiler
