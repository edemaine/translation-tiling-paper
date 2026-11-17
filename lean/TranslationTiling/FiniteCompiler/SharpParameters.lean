import TranslationTiling.FiniteCompiler.Parameters
import TranslationTiling.Compiler.SharpPrimeCounting

namespace TranslationTiling.FiniteCompiler
open scoped Classical BigOperators
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

/-- Only the two seed b-primes need the large seed threshold. -/
theorem exists_sharp_useful (T : System) (hC : 596750 ≤ channelCount T) :
    ∃ u : UsefulTag T → ℕ, Function.Injective u ∧
      (∀ i, (u i).Prime ∧ u i ≤ channelCount T ^ 2 ∧ u i ≠ Sudoku.p ∧ u i ≠ Sudoku.q) ∧
      (∀ i, u i ≠ 5) ∧
      (∀ t : Fin 2, u (.inl (.inr t)) = t.val+2) ∧
      (∀ t : Fin 2, residueModulus^2 < u (.inr (.inr t))) := by
  let C := channelCount T
  let D := residueModulus^2
  have hD : 2 ≤ D := by norm_num [D,residueModulus_eq,Sudoku.SeedModulus,Sudoku.p,Sudoku.q]
  obtain ⟨b0,hb0,hb0l,hb0u⟩ := Nat.bertrand D (by omega)
  obtain ⟨b1,hb1,hb1l,hb1u⟩ := Nat.bertrand (2*D) (by omega)
  have hbig : 4*D ≤ C^2 := by
    dsimp [D]
    rw [residueModulus_eq]
    norm_num [Sudoku.SeedModulus,Sudoku.p,Sudoku.q]
    have h := Nat.pow_le_pow_left hC 2
    norm_num at h
    exact (by norm_num : 2044900 ≤ 596750^2).trans h
  let banned : Finset ℕ := {2,3,5,Sudoku.p,Sudoku.q,b0,b1}
  let pool := Nat.primesLE (C^2) \ banned
  have hban : banned.card ≤ 7 := by
    have he : banned = [2,3,5,Sudoku.p,Sudoku.q,b0,b1].toFinset := by ext x; simp [banned]
    rw [he]
    exact List.toFinset_card_le _
  have hpool : 2*T.width ≤ pool.card := by
    have hp := Compiler.Size.primeCounting_square_large hC
    have hs := Finset.card_le_card_sdiff_add_card (s:=Nat.primesLE (C^2)) (t:=banned)
    rw [Nat.primesLE_card_eq_primeCounting] at hs
    dsimp [pool,C] at *
    unfold channelCount at *
    omega
  have hcard : Fintype.card (Column T ⊕ Column T) ≤ Fintype.card ↥pool := by
    simpa [Column,Fintype.card_sum,Fintype.card_coe,two_mul] using hpool
  obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le hcard
  let g (i : Column T ⊕ Column T) : ℕ := (f i).val
  have hg (i) : (g i).Prime ∧ g i ≤ C^2 ∧ g i ∉ banned := by
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
  refine ⟨u,(hginj.sumElim hseedinj hsep).comp e.injective,?_,?_,?_,?_⟩
  · intro i
    change (u i).Prime ∧ u i ≤ C^2 ∧ u i ≠ Sudoku.p ∧ u i ≠ Sudoku.q
    dsimp only [u,Function.comp_apply]
    cases he : e i with
    | inl j =>
      have hn := (hg j).2.2
      exact ⟨(hg j).1,(hg j).2.1,by intro he; change g j = _ at he; exact hn (by simp [banned,he]),by intro he; change g j = _ at he; exact hn (by simp [banned,he])⟩
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

theorem exists_sharp_parameters (T : System) (hC : 596750 ≤ channelCount T) (hB : T.alphabet = 3) :
    ∃ E : EncodingParameters T,
      (∀ i, E.a i ≤ channelCount T^2 ∧ E.b i ≤ channelCount T^2) ∧
      ∀ i j, E.digitPrime i j ≤ channelCount T^5 := by
  obtain ⟨u,huinj,hu,hfive,hseed,hlarge⟩ := exists_sharp_useful T hC
  let C := channelCount T
  let Tags := Σ i : Channel T, Label T i
  let ix : Tags ≃ Fin (Fintype.card Tags) := Fintype.equivFin _
  let g (j : Tags) := Nat.nth Nat.Prime (primeThreshold (C^2)+(ix j).val)
  apply exists_parameters_of_bounded_families T (C^2) (C^5) u huinj hu hfive hseed hlarge
    g (fun _ => Nat.prime_nth_prime _)
  · intro j
    have h := Nat.add_two_le_nth_prime (primeThreshold (C^2)+(ix j).val)
    dsimp [g]; omega
  · intro i j h
    apply ix.injective
    apply Fin.ext
    have hh := (Nat.nth_strictMono Nat.infinite_setOfPred_prime).injective h
    change primeThreshold (C^2)+(ix i).val = primeThreshold (C^2)+(ix j).val at hh
    omega
  · intro j
    have hcard : Fintype.card Tags ≤ 3*C := by
      rw [Fintype.card_sigma]
      calc
        _ ≤ ∑ _i : Channel T, 3 := Finset.sum_le_sum (fun i _ => by cases i <;> simp [Label,Symbol,hB])
        _ = _ := by simp [C,channelCount,Nat.mul_comm]
    have hp := Compiler.Size.primeCounting_fifth_large hC
    have hc : primeThreshold (C^2)+3*C+1 ≤ 3*C^4 := by
      have hh : 596750 ≤ C := hC
      unfold primeThreshold
      norm_num [Sudoku.p,Sudoku.q]
      nlinarith [sq_nonneg (C^2-1:ℤ),show (C^2)^2=C^4 by ring]
    change 3*C^4 ≤ Nat.primeCounting (C^5) at hp
    have hk := (ix j).isLt
    have h' : primeThreshold (C^2)+(ix j).val < Nat.count Nat.Prime (C^5+1) := by
      change _ < Nat.primeCounting (C^5)
      omega
    exact Nat.le_of_lt_succ (Nat.nth_lt_of_lt_count h')


theorem square_le_usefulPrimeCap (C : ℕ) : C^2 ≤ usefulPrimeCap C := by
  unfold usefulPrimeCap
  exact Nat.pow_le_pow_left (by omega : C ≤ 8*(usefulStart+2*C+1)) 2

theorem fifth_le_digitPrimeCap {C : ℕ} (hC : 1 ≤ C) : C^5 ≤ digitPrimeCap 3 C := by
  have hu := square_le_usefulPrimeCap C
  have hu2 := Nat.pow_le_pow_left hu 2
  have hbase : C^4 ≤ 8*(primeThreshold (usefulPrimeCap C)+C*(3+1)+1) := by
    unfold primeThreshold
    nlinarith [show (C^2)^2=C^4 by ring]
  calc
    _ ≤ C^8 := Nat.pow_le_pow_right hC (by decide)
    _ = (C^4)^2 := by ring
    _ ≤ _ := Nat.pow_le_pow_left hbase 2

theorem exists_bounded_parameters_sharp (T : System) :
    ∃ E : EncodingParameters T,
      (∀ i, E.a i ≤ usefulPrimeCap (channelCount T) ∧ E.b i ≤ usefulPrimeCap (channelCount T)) ∧
      (∀ i j, E.digitPrime i j ≤ digitPrimeCap T.alphabet (channelCount T)) ∧
      (596750 ≤ channelCount T ∧ T.alphabet=3 →
        (∀ i, E.a i ≤ channelCount T^2 ∧ E.b i ≤ channelCount T^2) ∧
        ∀ i j, E.digitPrime i j ≤ channelCount T^5) := by
  by_cases h : 596750 ≤ channelCount T ∧ T.alphabet=3
  · obtain ⟨E,hu,hp⟩ := exists_sharp_parameters T h.1 h.2
    refine ⟨E,fun i => ⟨(hu i).1.trans (square_le_usefulPrimeCap _),
      (hu i).2.trans (square_le_usefulPrimeCap _)⟩,?_,fun _ => ⟨hu,hp⟩⟩
    intro i j
    exact (hp i j).trans (by rw [h.2]; exact fifth_le_digitPrimeCap (by have := T.width_pos; unfold channelCount; omega))
  · obtain ⟨E,hu,hp⟩ := exists_bounded_parameters T
    exact ⟨E,hu,hp,fun hh => (h hh).elim⟩

end
end TranslationTiling.FiniteCompiler
