import TranslationTiling.FiniteCompiler.CompactParameters
import TranslationTiling.FiniteCompiler.TernaryBounds
import TranslationTiling.FiniteCompiler.SupportBounds
import TranslationTiling.FiniteCompiler.Effective.FreshStack
import TranslationTiling.Compiler.SharpPrimeCounting
import Mathlib.Analysis.SpecialFunctions.Log.Base

namespace TranslationTiling.FiniteCompiler.CompactSize
open Compiler.Size Size
open scoped Classical BigOperators
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

variable {T : System} (E : EncodingParameters T)

theorem seedModulus_le_square {C : ℕ} (hC : 1202≤C) : residueModulus≤C^2 := by
  apply (show residueModulus≤1202^2 by norm_num [residueModulus_eq,Sudoku.SeedModulus,Sudoku.p,Sudoku.q]).trans
  exact Nat.pow_le_pow_left hC 2

theorem sharp_label_card (hB : T.alphabet = 3) (i : Channel T) :
    Fintype.card (Label T i) ≤ 3 := by cases i <;> simp [Label, Symbol, hB]

theorem sharp_r_le (hB : T.alphabet = 3) (hp : CompactPrimes E) (i : Channel T) :
    E.r i ≤ channelCount T ^ 15 := by
  have hC : 1 ≤ channelCount T := by unfold channelCount; omega
  rw [E.r_eq_prod]
  calc
    _ ≤ ∏ _j : Label T i, channelCount T ^ 5 := Finset.prod_le_prod (fun j _ => hp.2.1 i j)
    _ = channelCount T ^ (5 * Fintype.card (Label T i)) := by simp [← pow_mul]
    _ ≤ _ := Nat.pow_le_pow_right hC (by have := sharp_label_card hB i; omega)

theorem sharp_cyclicOrder_le (hB : T.alphabet = 3) (hp : CompactPrimes E)
    (hC : 1202≤channelCount T) :
    E.cyclicOrder ≤ channelCount T ^ (35 * channelCount T) := by
  let C := channelCount T
  have h1 : 1 ≤ C := by unfold C channelCount; omega
  have hblock (i : Channel T) : E.blockModulus i≤C^34 := by
    calc
      _ = E.r i^2*(E.a i*E.b i) := by unfold EncodingParameters.blockModulus; ring
      _ ≤ (C^15)^2*C^4 := Nat.mul_le_mul (Nat.pow_le_pow_left (sharp_r_le E hB hp i) 2) (hp.2.2 i)
      _ = _ := by ring
  have hN : residueModulus≤C^2 := seedModulus_le_square hC
  calc
    _ ≤ (C^2)^2*∏ _i : Channel T, C^34 := Nat.mul_le_mul (Nat.pow_le_pow_left hN 2)
      (Finset.prod_le_prod (fun i _ => hblock i))
    _ = C^(34*C+4) := by simp only [Finset.prod_const,Finset.card_univ,channel_card,← pow_mul,← pow_add]; congr 1; ring
    _ ≤ _ := Nat.pow_le_pow_right h1 (by omega)

set_option maxHeartbeats 200000 in
theorem sharp_cycleTiles_card_le (hp : CompactPrimes E) (hC : 1202≤channelCount T)
    {t : ℕ} [NeZero t] (cycle : ZMod t ↪ Channel T) (labels : ∀ j, Label T (cycle j)) :
    (sparseCycleTiles E cycle labels).card ≤ channelCount T ^ (9 * channelCount T) := by
  have ht : t ≤ channelCount T := by
    simpa only [ZMod.card, channel_card] using Fintype.card_le_of_injective cycle cycle.injective
  have hP (i : Channel T) : Fintype.card (P E i)≤channelCount T^4 := by
    simpa only [P,Fintype.card_prod,ZMod.card] using hp.2.2 i
  calc
    _ ≤ ∏ j : ZMod t, Fintype.card (P E (cycle (j-1))) *
        Fintype.card (digitSubgroup E (cycle j) (labels j)) := sparseCycleTiles_card_le E cycle labels
    _ ≤ ∏ _j : ZMod t, (channelCount T ^ 4 * channelCount T ^ 5) :=
      Finset.prod_le_prod (fun j _ => Nat.mul_le_mul (hP _)
        ((digitSubgroup_card_le_prime E _ _).trans (hp.2.1 _ _)))
    _ = channelCount T ^ (9 * t) := by
      simp only [← pow_add, Finset.prod_const, Finset.card_univ, ZMod.card, ← pow_mul]
    _ ≤ _ := Nat.pow_le_pow_right (by unfold channelCount; omega) (by omega)

theorem smallPrimes_budget (hB : T.alphabet = 3) (hp : CompactPrimes E)
    (hC : 1202≤channelCount T) (hS : ∀ n, (T.slope n).natAbs ≤ Sudoku.Width) :
    ParameterBudget E (channelCount T ^ 15) := by
  have h1 : 1 ≤ channelCount T := by unfold channelCount; omega
  have hself : channelCount T ≤ channelCount T ^ 15 := Nat.le_self_pow (by decide) _
  have hN := (seedModulus_le_square hC).trans (Nat.pow_le_pow_right h1 (by decide : 2≤15))
  have hW : Sudoku.Width≤channelCount T^2 := by
    apply (show Sudoku.Width≤1202^2 by norm_num [Sudoku.Width,Sudoku.q]).trans
    exact Nat.pow_le_pow_left hC 2
  exact ⟨(by omega : 2≤channelCount T).trans hself,hN,
    sharp_r_le E hB hp,fun i => (hp.1 i).1.trans (Nat.pow_le_pow_right h1 (by decide)),
    fun i => (hp.1 i).2.trans (Nat.pow_le_pow_right h1 (by decide)),
    fun n => (hS n).trans (hW.trans (Nat.pow_le_pow_right h1 (by decide)))⟩

theorem sharp_wordConstraintTiles_card_le (hB : T.alphabet = 3) (hp : CompactPrimes E)
    (hC : 1202≤channelCount T) :
    (wordConstraintTiles E).card ≤ channelCount T ^ (10 * channelCount T) := by
  let C := channelCount T
  have hwords : Fintype.card (Word T) ≤ C ^ C := by
    simp only [Word, Symbol, Fintype.card_fun, Fintype.card_fin, hB]
    exact (Nat.pow_le_pow_left (by unfold C channelCount; have := T.width_pos; omega) _).trans
      (Nat.pow_le_pow_right (by unfold C channelCount; omega) (by unfold C channelCount; omega))
  unfold wordConstraintTiles
  apply Finset.card_biUnion_le.trans
  calc
    _ ≤ ∑ _w ∈ (Finset.univ.filter (fun w : Word T => w ∉ allowedWords T)), C ^ (9 * C) :=
      Finset.sum_le_sum (fun _ _ => sharp_cycleTiles_card_le E hp hC _ _)
    _ ≤ Fintype.card (Word T) * C ^ (9 * C) := by
      simp only [Finset.sum_const, smul_eq_mul]
      exact Nat.mul_le_mul_right _ (Finset.card_filter_le _ _)
    _ ≤ C ^ C * C ^ (9 * C) := Nat.mul_le_mul_right _ hwords
    _ = _ := by rw [← pow_add]; congr 1; omega

theorem sharp_seedConstraintTiles_card_le (hB : T.alphabet = 3) (hp : CompactPrimes E)
    (hbig : 6 ≤ channelCount T) (hC : 1202≤channelCount T) :
    (seedConstraintTiles E).card ≤ channelCount T ^ (10 * channelCount T) := by
  let C := channelCount T
  have hindex : Fintype.card (Fin 2 × Column T × Symbol T) ≤ C ^ 2 := by
    simp only [Fintype.card_prod, Fintype.card_fin, Column, Symbol, hB]
    unfold C channelCount at *
    nlinarith [T.width_pos]
  unfold seedConstraintTiles
  apply Finset.card_biUnion_le.trans
  calc
    _ ≤ ∑ _q ∈ (Finset.univ.filter (fun q : Fin 2 × Column T × Symbol T =>
        ¬ SeedSet T q.1 q.2.2)), C ^ (9 * C) :=
      Finset.sum_le_sum (fun _ _ => sharp_cycleTiles_card_le E hp hC _ _)
    _ ≤ Fintype.card (Fin 2 × Column T × Symbol T) * C ^ (9 * C) := by
      simp only [Finset.sum_const, smul_eq_mul]
      exact Nat.mul_le_mul_right _ (Finset.card_filter_le _ _)
    _ ≤ C ^ 2 * C ^ (9 * C) := Nat.mul_le_mul_right _ hindex
    _ = C ^ (9 * C + 2) := by rw [← pow_add]; congr 1; omega
    _ ≤ _ := Nat.pow_le_pow_right (by unfold C channelCount; omega) (by dsimp [C]; omega)

theorem sharp_testTiles_card_le (hB : T.alphabet = 3) (hp : CompactPrimes E)
    (hC : 1202≤channelCount T) (hS : ∀ n, (T.slope n).natAbs ≤ Sudoku.Width) :
    (testTiles E).card ≤ channelCount T ^ (11 * channelCount T) := by
  let C := channelCount T
  have hbig : 300 ≤ C := by
    have : 15 ≤ Sudoku.Width := by norm_num [Sudoku.Width, Sudoku.p, Sudoku.q]
    omega
  have h1 : 1 ≤ C := by omega
  have hself : C ≤ C ^ 15 := Nat.le_self_pow (by decide) _
  have hb := smallPrimes_budget E hB hp hC hS
  have hdep : (dependenceTiles E).card ≤ C ^ (10 * C) := by
    have hd := dependenceTiles_card_le hb hself
    apply hd.trans
    rw [← pow_mul]
    exact Nat.pow_le_pow_right h1 (by omega)
  have hword := sharp_wordConstraintTiles_card_le E hB hp hC
  have hseed := sharp_seedConstraintTiles_card_le E hB hp (by omega) hC
  change (wordConstraintTiles E).card ≤ C ^ (10 * C) at hword
  change (seedConstraintTiles E).card ≤ C ^ (10 * C) at hseed
  have hsingle : 1 ≤ C ^ (10 * C) := Nat.one_le_pow _ _ h1
  have hsmall : C ≤ C ^ (10 * C) := Nat.le_self_pow (by omega) _
  have hact : (Finset.univ.image (ordinaryActivationTile E)).card ≤ C ^ (10 * C) := by
    apply Finset.card_image_le.trans
    rw [Finset.card_univ]
    have hw : Fintype.card (Column T) ≤ C := by
      simp only [Column, Fintype.card_fin]; unfold C channelCount; omega
    exact hw.trans hsmall
  have hseeds : (Finset.univ.image (seedActivationTile E)).card ≤ C ^ (10 * C) := by
    apply Finset.card_image_le.trans
    rw [Finset.card_univ, Fintype.card_fin]
    exact (by omega : 2 ≤ C).trans hsmall
  have hsum : (testTiles E).card ≤ 6 * C ^ (10 * C) := by
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
    _ ≤ 6 * C ^ (10 * C) := hsum
    _ ≤ C * C ^ (10 * C) := Nat.mul_le_mul_right _ (by omega)
    _ = C ^ (10 * C + 1) := by rw [pow_succ']
    _ ≤ _ := Nat.pow_le_pow_right h1 (by omega)



theorem cyclicOrder_primeBound (hB : T.alphabet=3) (hp : CompactPrimes E)
    (hC : 1202≤channelCount T) :
    Effective.PrimeBound E.cyclicOrder (channelCount T^5) := by
  intro q hq
  by_cases hprime : q.Prime
  · right
    by_cases hd : q ∣ E.cyclicOrder
    · right
      by_contra hl
      have hlarge : channelCount T^5 < q := by omega
      have h1 : 1 ≤ channelCount T := by unfold channelCount; omega
      have hcop (a : ℕ) (ha : 0<a) (hb : a≤channelCount T^5) : Nat.Coprime q a := by
        apply hprime.coprime_iff_not_dvd.mpr
        intro hh
        have := Nat.le_of_dvd ha hh
        omega
      have hR : Nat.Coprime q residueModulus := hcop _ (by rw [residueModulus_eq]; decide)
        ((seedModulus_le_square hC).trans (Nat.pow_le_pow_right (by omega) (by decide : 2≤5)))
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

theorem differenceLog_channel_le {C : ℕ} (hC : 1202 ≤ C) :
    Stacking.differenceLog (C^(11*C)) ≤ C^2 := by
  have hcr : (1024:ℝ) ≤ C := by exact_mod_cast (by omega : 1024 ≤ C)
  have hl := Compiler.Size.log_le_div_sixtyfour (by omega : 768 ≤ C)
  have htwo : (1/2:ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at h ⊢
    exact h
  have hlg : Real.logb 2 (C:ℝ) ≤ C/32 := by
    rw [Real.logb]
    apply (div_le_iff₀ (Real.log_pos (by norm_num : (1:ℝ)<2))).mpr
    nlinarith [mul_le_mul_of_nonneg_left htwo (show (0:ℝ)≤C by positivity)]
  have hlog := Real.natLog_le_logb (2*C^(11*C)) 2
  push_cast at hlog
  rw [Real.logb_mul (by norm_num) (by positivity),Real.logb_pow,
    Real.logb_self_eq_one (by norm_num : (1:ℝ)<2)] at hlog
  push_cast at hlog
  have hL : (Stacking.differenceLog (C^(11*C)):ℝ) ≤ (C:ℝ)^2 := by
    unfold Stacking.differenceLog
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left hlg (show (0:ℝ)≤C by positivity)]
  exact_mod_cast hL

theorem freshCap_channel_le {C : ℕ} (hC : 1202 ≤ C) :
    Effective.freshCap (C^(11*C)) (C^5) ≤ C^(23*C) := by
  have hc : 1202 ≤ C := by simpa [Sudoku.Width,Sudoku.q] using hC
  have h1 : 1 ≤ C := by omega
  have hL := differenceLog_channel_le hc
  have hLp : 1 ≤ Stacking.differenceLog (C^(11*C)) := by unfold Stacking.differenceLog; omega
  have hP : C^5 ≤ (C^(11*C))^2 := by
    rw [← pow_mul]
    exact Nat.pow_le_pow_right h1 (by omega)
  have hX : 3 ≤ (C^(11*C))^2 := by
    apply (show 3 ≤ C by omega).trans
    rw [← pow_mul]
    exact Nat.le_self_pow (by omega) _
  have hXL : (C^(11*C))^2 ≤ (C^(11*C))^2*Stacking.differenceLog (C^(11*C)) :=
    Nat.le_mul_of_pos_right _ (by omega)
  calc
    _ ≤ 132*(C^(11*C))^2*Stacking.differenceLog (C^(11*C)) := by
      unfold Effective.freshCap Stacking.logPartitionThreshold
      nlinarith
    _ ≤ 132*(C^(11*C))^2*C^2 := Nat.mul_le_mul_left _ hL
    _ = 132*C^(22*C+2) := by rw [← pow_mul,mul_assoc,← pow_add]; congr 2; ring
    _ ≤ C*C^(22*C+2) := Nat.mul_le_mul_right _ (by omega)
    _ = C^(22*C+3) := by simpa only [Nat.add_assoc] using (pow_succ' C (22*C+2)).symm
    _ ≤ _ := Nat.pow_le_pow_right h1 (by omega)


theorem compact_geometry_bound {C H : ℕ} (hC : 1202≤C) (hH : H≤C^3165) :
    (9*2^24*972*36*8003^4)*H^4*(C^(58*C))^3≤C^(185*C) := by
  have h1 : 1≤C := by omega
  have hk : 9*2^24*972*36*8003^4≤C^10 := by
    apply (by norm_num : 9*2^24*972*36*8003^4≤(2^10)^10).trans
    exact Nat.pow_le_pow_left (by norm_num; omega) _
  calc
    _ ≤ C^10*(C^3165)^4*(C^(58*C))^3 := Nat.mul_le_mul
      (Nat.mul_le_mul hk (Nat.pow_le_pow_left hH 4)) le_rfl
    _ = C^(174*C+12670) := by simp only [← pow_mul,← pow_add]; congr 1; ring
    _ ≤ _ := Nat.pow_le_pow_right h1 (by omega)

end
end TranslationTiling.FiniteCompiler.CompactSize
