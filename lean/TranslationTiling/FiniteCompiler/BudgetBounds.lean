import TranslationTiling.FiniteCompiler.BudgetParameters
import TranslationTiling.FiniteCompiler.RefinedBounds

namespace TranslationTiling.FiniteCompiler.BudgetSize
open Compiler.Size Size
open scoped Classical BigOperators
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
variable {T : System} {C : ℕ} (E : EncodingParameters T)

theorem seed_r_le (hp : BudgetPrimes E C) (t : Fin 2) : E.r (.inr t)≤C^4 := by
  rw [E.r_eq_prod]
  calc
    _ ≤ ∏ _j : Label T (.inr t), C^4 := Finset.prod_le_prod (fun j _ => hp.2.1 (.inr t) j)
    _ = _ := by simp [Label]

theorem r_le_nine (hC : 256≤C) (hB : T.alphabet=3) (hp : BudgetPrimes E C) (i : Channel T) : E.r i≤C^9 := by
  cases i with
  | inl n =>
    rw [E.r_eq_prod]
    calc
      _ ≤ ∏ _j : Label T (.inl n), C^3 := Finset.prod_le_prod (fun j _ => hp.2.2.2.2 n j)
      _ = _ := by simp [Label,Symbol,hB,← pow_mul]
  | inr t => exact (seed_r_le E hp t).trans (Nat.pow_le_pow_right (by omega) (by decide))

theorem parameterBudget_nine (hC : 256≤C) (hc : channelCount T≤C)
    (hB : T.alphabet=3) (hp : BudgetPrimes E C) (hS : ∀ n, (T.slope n).natAbs≤Sudoku.Width) :
    Size.ParameterBudget E (C^9) ∧ channelCount T≤C^9 ∧ T.alphabet+1≤C^9 := by
  have h1 : 1≤C := by omega
  have hh : C≤C^9 := Nat.le_self_pow (by decide) _
  have hseed := EconomicalSize.seedModulus_le_square hC
  have hwidth : Sudoku.Width≤C^2 := by
    apply (show Sudoku.Width≤256^2 by norm_num [Sudoku.Width,Sudoku.q]).trans
    exact Nat.pow_le_pow_left hC 2
  refine ⟨⟨(by omega : 2≤C).trans hh,
    hseed.trans (Nat.pow_le_pow_right h1 (by decide)),r_le_nine E hC hB hp,
    fun i => (hp.1 i).1.trans (Nat.pow_le_pow_right h1 (by decide)),
    fun i => (hp.1 i).2.trans (Nat.pow_le_pow_right h1 (by decide)),
    fun n => (hS n).trans (hwidth.trans (Nat.pow_le_pow_right h1 (by decide)))⟩,hc.trans hh,?_⟩
  rw [hB]
  exact (by omega : 4≤C).trans hh

theorem seed_cycle_card_le (hp : BudgetPrimes E C) (t : Fin 2) (n : Column T) (j : Symbol T) :
    (fixedCycleTiles E (seedCycle t n) (seedCycleLabels t n j)).card≤C^15 := by
  have hP (i : Channel T) : Fintype.card (P E i) = E.a i*E.b i := by simp [P]
  have hprod : (∏ z : ZMod 2, Fintype.card (P E (seedCycle t n (z-1)))*
      Fintype.card (digitSubgroup E (seedCycle t n z) (seedCycleLabels t n j z)))≤C^15 := by
    rw [show (Finset.univ : Finset (ZMod 2))={0,1} by decide]
    simp only [Finset.prod_insert,Finset.mem_singleton,zero_ne_one,not_false_eq_true,
      Finset.prod_singleton,show (0:ZMod 2)-1=1 by decide,sub_self,seedCycle_zero,seedCycle_one,
      seedCycleLabels_zero,seedCycleLabels_one,hP]
    calc
      _ ≤ (C^3*C^4)*(C^4*C^4) := Nat.mul_le_mul
        (Nat.mul_le_mul (hp.2.2.2.1 n) ((digitSubgroup_card_le_prime E _ _).trans (hp.2.1 _ _)))
        (Nat.mul_le_mul (hp.2.2.1 _) ((digitSubgroup_card_le_prime E _ _).trans (hp.2.1 _ _)))
      _ = _ := by ring
  exact (fixedCycleTiles_card_le E _ _).trans hprod

theorem seed_card_le (hB : T.alphabet=3) (hp : BudgetPrimes E C) (hC : 962≤C) (hc : channelCount T≤C) :
    (seedConstraintTiles E).card≤C^17 := by
  have hi : Fintype.card (Fin 2×Column T×Symbol T)≤C^2 := by
    simp only [Fintype.card_prod,Fintype.card_fin,Column,Symbol,hB]
    unfold channelCount at hc
    nlinarith
  unfold seedConstraintTiles
  calc
    _ ≤ ∑ _q ∈ Finset.univ.filter (fun q : Fin 2×Column T×Symbol T => ¬ SeedSet T q.1 q.2.2), C^15 :=
      Finset.card_biUnion_le.trans (Finset.sum_le_sum (fun q _ => seed_cycle_card_le E hp q.1 q.2.1 q.2.2))
    _ ≤ Fintype.card (Fin 2×Column T×Symbol T)*C^15 := by
      simp only [Finset.sum_const,smul_eq_mul]
      exact Nat.mul_le_mul_right _ (Finset.card_filter_le _ _)
    _ ≤ C^2*C^15 := Nat.mul_le_mul_right _ hi
    _ = _ := by ring

theorem ordinary_r_pow (hB : T.alphabet=3) (hp : BudgetPrimes E C) (hC : 256≤C) (n : Column T) :
    E.r (.inl n)^20≤C^180 := by
  have hr := r_le_nine E hC hB hp (.inl n)
  simpa only [← pow_mul] using Nat.pow_le_pow_left hr 20

theorem cyclicOrder_pow (hB : T.alphabet=3) (hp : BudgetPrimes E C) (hC : 256≤C) :
    E.cyclicOrder^10≤C^(210*T.width+280) := by
  have ho (n : Column T) : E.blockModulus (.inl n)^10≤C^210 := by
    calc
      _ = E.r (.inl n)^20*(E.a (.inl n)*E.b (.inl n))^10 := by unfold EncodingParameters.blockModulus; ring
      _ ≤ C^180*(C^3)^10 := Nat.mul_le_mul (ordinary_r_pow E hB hp hC n) (Nat.pow_le_pow_left (hp.2.2.2.1 n) 10)
      _ = _ := by ring
  have hs (t : Fin 2) : E.blockModulus (.inr t)^10≤C^120 := by
    have hh : E.blockModulus (.inr t)≤C^12 := by
      calc
        _ = E.r (.inr t)^2*(E.a (.inr t)*E.b (.inr t)) := by unfold EncodingParameters.blockModulus; ring
        _ ≤ (C^4)^2*C^4 := Nat.mul_le_mul (Nat.pow_le_pow_left (seed_r_le E hp t) 2) (hp.2.2.1 _)
        _ = _ := by ring
    simpa only [← pow_mul] using Nat.pow_le_pow_left hh 10
  calc
    _ = (residueModulus^2)^10*((∏ n : Column T, E.blockModulus (.inl n)^10)*
        (∏ t : Fin 2, E.blockModulus (.inr t)^10)) := by
      simp only [EncodingParameters.cyclicOrder,Fintype.prod_sum_type,mul_pow,Finset.prod_pow]
    _ ≤ ((C^2)^2)^10*((∏ _n : Column T, C^210)*(∏ _t : Fin 2, C^120)) :=
      Nat.mul_le_mul (Nat.pow_le_pow_left (Nat.pow_le_pow_left (EconomicalSize.seedModulus_le_square hC) 2) 10)
        (Nat.mul_le_mul (Finset.prod_le_prod (fun n _ => ho n)) (Finset.prod_le_prod (fun t _ => hs t)))
    _ = _ := by simp [Column,← pow_mul,← pow_add]; congr 1; ring

theorem ordinary_cycle_card (hp : BudgetPrimes E C) (Q : ℕ)
    (hq : ∀ n j, E.digitPrime (.inl n) j≤Q) (w : Word T) :
    (fixedCycleTiles E (ordinaryCycle T) (ordinaryCycleLabels w)).card≤(C^3*Q)^T.width := by
  have hP (n : Column T) : Fintype.card (P E (.inl n))≤C^3 := by
    simpa only [P,Fintype.card_prod,ZMod.card] using hp.2.2.2.1 n
  calc
    _ ≤ ∏ j : ZMod T.width, Fintype.card (P E (ordinaryCycle T (j-1)))*
        Fintype.card (digitSubgroup E (ordinaryCycle T j) (ordinaryCycleLabels w j)) := fixedCycleTiles_card_le E _ _
    _ ≤ ∏ _j : ZMod T.width, C^3*Q := Finset.prod_le_prod (fun j _ =>
      Nat.mul_le_mul (hP _) ((digitSubgroup_card_le_prime E _ _).trans (hq _ _)))
    _ = _ := by simp

theorem word_card (hB : T.alphabet=3) (hp : BudgetPrimes E C) (Q : ℕ)
    (hq : ∀ n j, E.digitPrime (.inl n) j≤Q) :
    (wordConstraintTiles E).card≤(3*C^3*Q)^T.width := by
  have hw : Fintype.card (Word T)=3^T.width := by simp [Word,Symbol,hB]
  unfold wordConstraintTiles
  calc
    _ ≤ ∑ _w ∈ Finset.univ.filter (fun w : Word T => w∉allowedWords T), (C^3*Q)^T.width :=
      Finset.card_biUnion_le.trans (Finset.sum_le_sum (fun w _ => ordinary_cycle_card E hp Q hq w))
    _ ≤ Fintype.card (Word T)*(C^3*Q)^T.width := by
      simp only [Finset.sum_const,smul_eq_mul]
      exact Nat.mul_le_mul_right _ (Finset.card_filter_le _ _)
    _ = _ := by rw [hw,← mul_pow]; congr 1; ring

theorem testTiles_card (hB : T.alphabet=3) (hp : BudgetPrimes E C)
    (hC : 962≤C) (hc : channelCount T≤C) (hw : 16≤T.width) (hS : ∀ n, (T.slope n).natAbs≤Sudoku.Width)
    (Q : ℕ) (hQ : 1≤Q) (hq : ∀ n j, E.digitPrime (.inl n) j≤Q) :
    (testTiles E).card≤6*(3*C^3*Q)^T.width := by
  let A := (3*C^3*Q)^T.width
  have h1 : 1≤C := by omega
  have hw3 : 48≤3*T.width := by omega
  have hself : C≤C^12 := Nat.le_self_pow (by decide) _
  have hb9 := (parameterBudget_nine E (by omega) hc hB hp hS).1
  have hb : Size.ParameterBudget E (C^12) := by
    rcases hb9 with ⟨h1',h2',h3',h4',h5',h6'⟩
    have hh : C^9≤C^12 := Nat.pow_le_pow_right h1 (by decide)
    exact ⟨h1'.trans hh,h2'.trans hh,fun i => (h3' i).trans hh,
      fun i => (h4' i).trans hh,fun i => (h5' i).trans hh,fun i => (h6' i).trans hh⟩
  have hsmall : C^48≤A := by
    calc
      _ ≤ C^(3*T.width) := Nat.pow_le_pow_right h1 hw3
      _ = (C^3)^T.width := by rw [← pow_mul]
      _ ≤ _ := Nat.pow_le_pow_left ((by omega : C^3≤3*C^3).trans (Nat.le_mul_of_pos_right _ (by omega))) _
  have hdep : (dependenceTiles E).card≤A := by
    have hd := dependenceTiles_card_le hb (hc.trans hself)
    apply hd.trans
    rw [← pow_mul]
    exact hsmall
  have hword : (wordConstraintTiles E).card≤A := word_card E hB hp Q hq
  have hseed : (seedConstraintTiles E).card≤A := (seed_card_le E hB hp hC hc).trans
    ((Nat.pow_le_pow_right h1 (by decide : 17≤48)).trans hsmall)
  have hsingle : 1≤A := (Nat.one_le_pow _ _ h1).trans hsmall
  have hchannel : C≤A := (Nat.le_self_pow (by decide : 48≠0) _).trans hsmall
  have hact : (Finset.univ.image (ordinaryActivationTile E)).card≤A := by
    apply Finset.card_image_le.trans
    rw [Finset.card_univ]
    have hh : Fintype.card (Column T)≤C := by simp only [Column,Fintype.card_fin]; unfold channelCount at hc; omega
    exact hh.trans hchannel
  have hseeds : (Finset.univ.image (seedActivationTile E)).card≤A := by
    apply Finset.card_image_le.trans
    rw [Finset.card_univ,Fintype.card_fin]
    exact (by omega : 2≤C).trans hchannel
  unfold testTiles
  have h := Finset.card_union_le
    ({kernelTile E} ∪ dependenceTiles E ∪ wordConstraintTiles E ∪ seedConstraintTiles E ∪
      Finset.univ.image (ordinaryActivationTile E)) (Finset.univ.image (seedActivationTile E))
  have h' := Finset.card_union_le
    ({kernelTile E} ∪ dependenceTiles E ∪ wordConstraintTiles E ∪ seedConstraintTiles E)
      (Finset.univ.image (ordinaryActivationTile E))
  have h'' := Finset.card_union_le
    ({kernelTile E} ∪ dependenceTiles E ∪ wordConstraintTiles E) (seedConstraintTiles E)
  have h''' := Finset.card_union_le ({kernelTile E} ∪ dependenceTiles E) (wordConstraintTiles E)
  have h'''' := Finset.card_union_le {kernelTile E} (dependenceTiles E)
  simp only [Finset.card_singleton] at h''''
  change _≤6*A
  omega

theorem testBudget_pow (hB : T.alphabet=3) (hp : BudgetPrimes E C)
    (hC : 962≤C) (hc : channelCount T≤C) (hw : 16≤T.width) (hS : ∀ n, (T.slope n).natAbs≤Sudoku.Width) :
    (max (testTiles E).card (C^2))^60≤C^(370*T.width+30) := by
  let Q := C^3
  have hQ : 1≤Q := Nat.one_le_pow _ _ (by omega)
  have hq (n j) : E.digitPrime (.inl n) j≤Q := hp.2.2.2.2 n j
  have hqpow : Q^20≤C^60 := by dsimp [Q]; rw [← pow_mul]
  apply RefinedSize.count_pow hC hqpow
  apply max_le (testTiles_card E hB hp hC hc hw hS Q hQ hq)
  have hw3 : 2≤3*T.width := by omega
  calc
    _ ≤ C^(3*T.width) := Nat.pow_le_pow_right (by omega) hw3
    _ = (C^3)^T.width := by rw [← pow_mul]
    _ ≤ (3*C^3*Q)^T.width := Nat.pow_le_pow_left ((by omega : C^3≤3*C^3).trans (Nat.le_mul_of_pos_right _ (by omega))) _
    _ ≤ _ := Nat.le_mul_of_pos_left _ (by decide : 0<6)

theorem cyclicOrder_primeBound (hB : T.alphabet=3) (hp : BudgetPrimes E C)
    (hC : 256≤C) :
    Effective.PrimeBound E.cyclicOrder (C^4) := by
  intro q hq
  by_cases hprime : q.Prime
  · right
    by_cases hd : q ∣ E.cyclicOrder
    · right
      by_contra hl
      have hlarge : C^4 < q := by omega
      have h1 : 1 ≤ C := by omega
      have hcop (a : ℕ) (ha : 0<a) (hb : a≤C^4) : Nat.Coprime q a := by
        apply hprime.coprime_iff_not_dvd.mpr
        intro hh
        have := Nat.le_of_dvd ha hh
        omega
      have hR : Nat.Coprime q residueModulus := hcop _ (by rw [residueModulus_eq]; decide)
        ((EconomicalSize.seedModulus_le_square hC).trans (Nat.pow_le_pow_right (by omega) (by decide : 2≤4)))
      have hi (i : Channel T) : Nat.Coprime q (E.blockModulus i) := by
        have hr : Nat.Coprime q (E.r i) := by
          rw [E.r_eq_prod]
          apply Nat.coprime_fintype_prod_right_iff.mpr
          intro j
          exact hcop _ (E.prime_isPrime (.inr (.inr ⟨i,j⟩))).pos (hp.2.1 i j)
        exact ((hr.pow_right 2).mul_right (hcop _ (E.prime_isPrime (.inl i)).pos
          ((hp.1 i).1.trans (Nat.pow_le_pow_right h1 (by decide))))).mul_right
          (hcop _ (E.prime_isPrime (.inr (.inl i))).pos ((hp.1 i).2.trans (Nat.pow_le_pow_right h1 (by decide))))
      have ht : Nat.Coprime q E.cyclicOrder :=
        (hR.pow_right 2).mul_right (Nat.coprime_fintype_prod_right_iff.mpr hi)
      exact (hprime.coprime_iff_not_dvd.mp ht) hd
    · exact Or.inl hd
  · exact Or.inl hprime

theorem geometry_pow {C w H M : ℕ} (hC : 962≤C)
    (hH : H≤C^199) (hM : M^30≤C^(1000*w+960)) :
    ((9*2^24*972*36*8003^4)*H^4*M^3)^10≤C^(1000*w+9030) := by
  let K := 9*2^24*972*36*8003^4
  have hk : K≤C^11 := by
    apply (by norm_num [K] : K≤(2^9)^11).trans
    exact Nat.pow_le_pow_left (by norm_num; omega) _
  change (K*H^4*M^3)^10≤_
  calc
    _ = K^10*H^40*M^30 := by simp only [mul_pow,← pow_mul]
    _ ≤ (C^11)^10*(C^199)^40*C^(1000*w+960) := Nat.mul_le_mul
      (Nat.mul_le_mul (Nat.pow_le_pow_left hk _) (Nat.pow_le_pow_left hH _)) hM
    _ = C^(1000*w+9030) := by simp only [← pow_mul,← pow_add]; congr 1; omega

theorem primeBudget_pow {k : ℕ} (hc : 256≤2*channelCount T) (hk : 2^k≤channelCount T) :
    primeBudget T^k≤channelCount T^(k+1) := by
  have hh : primeBudget T≤2*channelCount T := max_le (by omega) (by omega)
  calc
    _ ≤ (2*channelCount T)^k := Nat.pow_le_pow_left hh _
    _ = 2^k*channelCount T^k := mul_pow _ _ _
    _ ≤ channelCount T*channelCount T^k := Nat.mul_le_mul_right _ hk
    _ = _ := (pow_succ' _ _).symm

theorem smallPrimes_of_budget (hp : BudgetPrimes E (primeBudget T)) (hc : 256≤channelCount T) :
    Size.SmallPrimes E := by
  have hh : primeBudget T^4≤channelCount T^5 := primeBudget_pow (by omega) (by norm_num; omega)
  exact ⟨fun i => ⟨(hp.1 i).1.trans hh,(hp.1 i).2.trans hh⟩,
    fun i j => ((hp.2.1 i j).trans hh).trans (Nat.pow_le_pow_right (by omega) (by decide))⟩

end
end TranslationTiling.FiniteCompiler.BudgetSize
