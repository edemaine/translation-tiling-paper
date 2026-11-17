import TranslationTiling.FiniteCompiler.SmallBudgetParameters
import TranslationTiling.FiniteCompiler.TernaryBounds
import TranslationTiling.FiniteCompiler.SupportBounds
import TranslationTiling.FiniteCompiler.Effective.FreshStack
import Mathlib.Analysis.SpecialFunctions.Log.Base

namespace TranslationTiling.FiniteCompiler.EconomicalSize
open Compiler.Size Size
open scoped Classical BigOperators
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
variable {T : System} (E : EncodingParameters T)

theorem seedModulus_le_square {C : ℕ} (hC : 256≤C) : residueModulus≤C^2 := by
  apply (show residueModulus≤256^2 by norm_num [residueModulus_eq,Sudoku.SeedModulus,Sudoku.p,Sudoku.q]).trans
  exact Nat.pow_le_pow_left hC 2

theorem cyclicOrder_le (hB : T.alphabet=3) (hp : EconomicalPrimes E) (hC : 962≤channelCount T) :
    E.cyclicOrder≤channelCount T^(27*channelCount T) := by
  let C := channelCount T
  have h1 : 1≤C := by omega
  have ho (n : Column T) : E.blockModulus (.inl n)≤C^27 := by
    calc
      _ = E.r (.inl n)^2*(E.a (.inl n)*E.b (.inl n)) := by unfold EncodingParameters.blockModulus; ring
      _ ≤ (C^12)^2*C^3 := Nat.mul_le_mul (Nat.pow_le_pow_left (economical_r_le E hB hp _) 2) (hp.2.2.2.1 n)
      _ = _ := by ring
  have hs (t : Fin 2) : E.blockModulus (.inr t)≤C^12 := by
    calc
      _ = E.r (.inr t)^2*(E.a (.inr t)*E.b (.inr t)) := by unfold EncodingParameters.blockModulus; ring
      _ ≤ (C^4)^2*C^4 := Nat.mul_le_mul (Nat.pow_le_pow_left (economical_seed_r_le E hp t) 2) (hp.2.2.1 _)
      _ = _ := by ring
  change residueModulus^2*(∏ i : Channel T, E.blockModulus i)≤_
  rw [Fintype.prod_sum_type]
  calc
    _ ≤ (C^2)^2*((∏ _n : Column T, C^27)*(∏ _t : Fin 2, C^12)) :=
      Nat.mul_le_mul (Nat.pow_le_pow_left (seedModulus_le_square (by omega)) 2)
        (Nat.mul_le_mul (Finset.prod_le_prod (fun n _ => ho n)) (Finset.prod_le_prod (fun t _ => hs t)))
    _ = C^(27*T.width+28) := by simp [Column,← pow_mul,← pow_add]; congr 1; ring
    _ ≤ _ := Nat.pow_le_pow_right h1 (by unfold channelCount; omega)

theorem ordinary_cycle_card_le (hp : EconomicalPrimes E) (w : Word T) :
    (fixedCycleTiles E (ordinaryCycle T) (ordinaryCycleLabels w)).card≤channelCount T^(7*T.width) := by
  let C := channelCount T
  have hP (n : Column T) : Fintype.card (P E (.inl n))≤C^3 := by
    simpa only [P,Fintype.card_prod,ZMod.card] using hp.2.2.2.1 n
  calc
    _ ≤ ∏ j : ZMod T.width, Fintype.card (P E (ordinaryCycle T (j-1)))*
        Fintype.card (digitSubgroup E (ordinaryCycle T j) (ordinaryCycleLabels w j)) := fixedCycleTiles_card_le E _ _
    _ ≤ ∏ _j : ZMod T.width, C^3*C^4 := Finset.prod_le_prod (fun j _ =>
      Nat.mul_le_mul (hP _) ((digitSubgroup_card_le_prime E _ _).trans (hp.2.1 _ _)))
    _ = _ := by simp [C,← pow_add,← pow_mul]

theorem seed_cycle_card_le (hp : EconomicalPrimes E) (t : Fin 2) (n : Column T) (j : Symbol T) :
    (fixedCycleTiles E (seedCycle t n) (seedCycleLabels t n j)).card≤channelCount T^15 := by
  let C := channelCount T
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

theorem word_card_le (hB : T.alphabet=3) (hp : EconomicalPrimes E) :
    (wordConstraintTiles E).card≤(3*channelCount T^7)^(channelCount T) := by
  let C := channelCount T
  have hc : 0<C := by unfold C channelCount; omega
  have hw : Fintype.card (Word T)=3^T.width := by simp [Word,Symbol,hB]
  unfold wordConstraintTiles
  calc
    _ ≤ ∑ _w ∈ Finset.univ.filter (fun w : Word T => w∉allowedWords T), C^(7*T.width) :=
      Finset.card_biUnion_le.trans (Finset.sum_le_sum (fun w _ => ordinary_cycle_card_le E hp w))
    _ ≤ Fintype.card (Word T)*C^(7*T.width) := by
      simp only [Finset.sum_const,smul_eq_mul]
      exact Nat.mul_le_mul_right _ (Finset.card_filter_le _ _)
    _ = (3*C^7)^T.width := by rw [hw,mul_pow,← pow_mul]
    _ ≤ _ := Nat.pow_le_pow_right (by positivity) (by unfold channelCount; omega)

theorem seed_card_le (hB : T.alphabet=3) (hp : EconomicalPrimes E) (hC : 962≤channelCount T) :
    (seedConstraintTiles E).card≤channelCount T^17 := by
  let C := channelCount T
  have hi : Fintype.card (Fin 2×Column T×Symbol T)≤C^2 := by
    simp only [Fintype.card_prod,Fintype.card_fin,Column,Symbol,hB]
    dsimp [C] at *
    unfold channelCount at *
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

theorem testTiles_card_le (hB : T.alphabet=3) (hp : EconomicalPrimes E)
    (hC : 962≤channelCount T) (hS : ∀ n, (T.slope n).natAbs≤Sudoku.Width) :
    (testTiles E).card≤channelCount T^(8*channelCount T) := by
  let C := channelCount T
  let A := (3*C^7)^C
  have h1 : 1≤C := by omega
  have hself : C≤C^12 := Nat.le_self_pow (by decide) _
  have hb := (economical_parameterBudget E hC hB hp hS).1
  have hsmall : C^48≤A := by
    calc
      _ ≤ C^(7*C) := Nat.pow_le_pow_right h1 (by omega)
      _ = (C^7)^C := by rw [← pow_mul]
      _ ≤ _ := Nat.pow_le_pow_left (by omega : C^7≤3*C^7) C
  have hdep : (dependenceTiles E).card≤A := by
    have hd := dependenceTiles_card_le hb hself
    apply hd.trans
    rw [← pow_mul]
    exact hsmall
  have hword : (wordConstraintTiles E).card≤A := word_card_le E hB hp
  have hseed : (seedConstraintTiles E).card≤A := (seed_card_le E hB hp hC).trans
    ((Nat.pow_le_pow_right h1 (by decide : 17≤48)).trans hsmall)
  have hsingle : 1≤A := (Nat.one_le_pow _ _ h1).trans hsmall
  have hchannel : C≤A := (Nat.le_self_pow (by decide : 48≠0) _).trans hsmall
  have hact : (Finset.univ.image (ordinaryActivationTile E)).card≤A := by
    apply Finset.card_image_le.trans
    rw [Finset.card_univ]
    have hw : Fintype.card (Column T)≤C := by simp [Column,C,channelCount]
    exact hw.trans hchannel
  have hseeds : (Finset.univ.image (seedActivationTile E)).card≤A := by
    apply Finset.card_image_le.trans
    rw [Finset.card_univ,Fintype.card_fin]
    exact (by omega : 2≤C).trans hchannel
  have hsum : (testTiles E).card≤6*A := by
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
    omega
  calc
    _ ≤ 6*A := hsum
    _ ≤ 6^C*A := Nat.mul_le_mul_right _ (Nat.le_self_pow (by omega : C≠0) _)
    _ = (18*C^7)^C := by dsimp [A]; rw [← mul_pow]; congr 1; ring
    _ ≤ (C*C^7)^C := Nat.pow_le_pow_left (Nat.mul_le_mul_right _ (by omega : 18≤C)) C
    _ = C^(8*C) := by rw [← pow_succ',← pow_mul]


theorem cyclicOrder_primeBound (hB : T.alphabet=3) (hp : EconomicalPrimes E)
    (hC : 962≤channelCount T) :
    Effective.PrimeBound E.cyclicOrder (channelCount T^4) := by
  intro q hq
  by_cases hprime : q.Prime
  · right
    by_cases hd : q ∣ E.cyclicOrder
    · right
      by_contra hl
      have hlarge : channelCount T^4 < q := by omega
      have h1 : 1 ≤ channelCount T := by unfold channelCount; omega
      have hcop (a : ℕ) (ha : 0<a) (hb : a≤channelCount T^4) : Nat.Coprime q a := by
        apply hprime.coprime_iff_not_dvd.mpr
        intro hh
        have := Nat.le_of_dvd ha hh
        omega
      have hR : Nat.Coprime q residueModulus := hcop _ (by rw [residueModulus_eq]; decide)
        ((seedModulus_le_square (by omega)).trans (Nat.pow_le_pow_right (by omega) (by decide : 2≤4)))
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

theorem differenceLog_channel_le {C : ℕ} (hC : 256 ≤ C) :
    Stacking.differenceLog (C^(8*C)) ≤ C^2 := by
  have hcr : (256:ℝ) ≤ C := by exact_mod_cast (by omega : 256 ≤ C)
  have hl := Compiler.Size.small_budget_log_bound (by omega : 256 ≤ C)
  have htwo : (1/2:ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at h ⊢
    exact h
  have hlg : Real.logb 2 (C:ℝ) ≤ C/20 := by
    rw [Real.logb]
    apply (div_le_iff₀ (Real.log_pos (by norm_num : (1:ℝ)<2))).mpr
    nlinarith [mul_le_mul_of_nonneg_left htwo (show (0:ℝ)≤C by positivity)]
  have hlog := Real.natLog_le_logb (2*C^(8*C)) 2
  push_cast at hlog
  rw [Real.logb_mul (by norm_num) (by positivity),Real.logb_pow,
    Real.logb_self_eq_one (by norm_num : (1:ℝ)<2)] at hlog
  push_cast at hlog
  have hL : (Stacking.differenceLog (C^(8*C)):ℝ) ≤ (C:ℝ)^2 := by
    unfold Stacking.differenceLog
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left hlg (show (0:ℝ)≤C by positivity)]
  exact_mod_cast hL

theorem freshCap_channel_le {C : ℕ} (hC : 962 ≤ C) :
    Effective.freshCap (C^(8*C)) (C^4) ≤ C^(17*C) := by
  have hc : 962 ≤ C := by simpa [Sudoku.Width,Sudoku.q] using hC
  have h1 : 1 ≤ C := by omega
  have hL := differenceLog_channel_le (C:=C) (by omega)
  have hLp : 1 ≤ Stacking.differenceLog (C^(8*C)) := by unfold Stacking.differenceLog; omega
  have hP : C^4 ≤ (C^(8*C))^2 := by
    rw [← pow_mul]
    exact Nat.pow_le_pow_right h1 (by omega)
  have hX : 3 ≤ (C^(8*C))^2 := by
    apply (show 3 ≤ C by omega).trans
    rw [← pow_mul]
    exact Nat.le_self_pow (by omega) _
  have hXL : (C^(8*C))^2 ≤ (C^(8*C))^2*Stacking.differenceLog (C^(8*C)) :=
    Nat.le_mul_of_pos_right _ (by omega)
  calc
    _ ≤ 132*(C^(8*C))^2*Stacking.differenceLog (C^(8*C)) := by
      unfold Effective.freshCap Stacking.logPartitionThreshold
      nlinarith
    _ ≤ 132*(C^(8*C))^2*C^2 := Nat.mul_le_mul_left _ hL
    _ = 132*C^(16*C+2) := by rw [← pow_mul,mul_assoc,← pow_add]; congr 2; ring
    _ ≤ C*C^(16*C+2) := Nat.mul_le_mul_right _ (by omega)
    _ = C^(16*C+3) := by simpa only [Nat.add_assoc] using (pow_succ' C (16*C+2)).symm
    _ ≤ _ := Nat.pow_le_pow_right h1 (by omega)


theorem compact_geometry_bound {C H : ℕ} (hC : 962≤C) (hH : H≤C^2532) :
    (9*2^24*972*36*8003^4)*H^4*(C^(44*C))^3≤C^(143*C) := by
  have h1 : 1≤C := by omega
  have hk : 9*2^24*972*36*8003^4≤C^11 := by
    apply (by norm_num : 9*2^24*972*36*8003^4≤(2^9)^11).trans
    exact Nat.pow_le_pow_left (by norm_num; omega) _
  calc
    _ ≤ C^11*(C^2532)^4*(C^(44*C))^3 := Nat.mul_le_mul
      (Nat.mul_le_mul hk (Nat.pow_le_pow_left hH 4)) le_rfl
    _ = C^(132*C+10139) := by simp only [← pow_mul,← pow_add]; congr 1; ring
    _ ≤ _ := Nat.pow_le_pow_right h1 (by omega)

end
end TranslationTiling.FiniteCompiler.EconomicalSize
