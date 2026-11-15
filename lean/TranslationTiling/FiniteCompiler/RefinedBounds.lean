import TranslationTiling.FiniteCompiler.EconomicalBounds

namespace TranslationTiling.FiniteCompiler.RefinedSize
open Compiler.Size Size
open scoped Classical BigOperators
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
variable {T : System} (E : EncodingParameters T)

theorem ordinary_r_pow (hB : T.alphabet=3) (hp : EconomicalPrimes E) (n : Column T) :
    E.r (.inl n)^20≤channelCount T^213 := by
  rw [E.r_eq_prod,← Finset.prod_pow]
  calc
    _ ≤ ∏ _j : Label T (.inl n), channelCount T^71 := Finset.prod_le_prod (fun j _ => hp.2.2.2.2 _ j)
    _ = _ := by simp [Label,Symbol,hB,← pow_mul]

theorem cyclicOrder_pow (hB : T.alphabet=3) (hp : EconomicalPrimes E) (hC : 962≤channelCount T) :
    E.cyclicOrder^10≤channelCount T^(243*T.width+280) := by
  let C := channelCount T
  have ho (n : Column T) : E.blockModulus (.inl n)^10≤C^243 := by
    calc
      _ = E.r (.inl n)^20*(E.a (.inl n)*E.b (.inl n))^10 := by unfold EncodingParameters.blockModulus; ring
      _ ≤ C^213*(C^3)^10 := Nat.mul_le_mul (ordinary_r_pow E hB hp n) (Nat.pow_le_pow_left (hp.2.2.2.1 n) 10)
      _ = _ := by ring
  have hs (t : Fin 2) : E.blockModulus (.inr t)^10≤C^120 := by
    have hh : E.blockModulus (.inr t)≤C^12 := by
      calc
        _ = E.r (.inr t)^2*(E.a (.inr t)*E.b (.inr t)) := by unfold EncodingParameters.blockModulus; ring
        _ ≤ (C^4)^2*C^4 := Nat.mul_le_mul (Nat.pow_le_pow_left (economical_seed_r_le E hp t) 2) (hp.2.2.1 _)
        _ = _ := by ring
    simpa only [← pow_mul] using Nat.pow_le_pow_left hh 10
  calc
    _ = (residueModulus^2)^10*((∏ n : Column T, E.blockModulus (.inl n)^10)*
        (∏ t : Fin 2, E.blockModulus (.inr t)^10)) := by
      simp only [EncodingParameters.cyclicOrder,Fintype.prod_sum_type,mul_pow,Finset.prod_pow]
    _ ≤ ((C^2)^2)^10*((∏ _n : Column T, C^243)*(∏ _t : Fin 2, C^120)) :=
      Nat.mul_le_mul (Nat.pow_le_pow_left (Nat.pow_le_pow_left (EconomicalSize.seedModulus_le_square hC) 2) 10)
        (Nat.mul_le_mul (Finset.prod_le_prod (fun n _ => ho n)) (Finset.prod_le_prod (fun t _ => hs t)))
    _ = _ := by simp [C,Column,← pow_mul,← pow_add]; congr 1; ring

theorem ordinary_cycle_card (hp : EconomicalPrimes E) (Q : ℕ)
    (hq : ∀ i j, E.digitPrime i j≤Q) (w : Word T) :
    (sparseCycleTiles E (ordinaryCycle T) (ordinaryCycleLabels w)).card≤(channelCount T^3*Q)^T.width := by
  have hP (n : Column T) : Fintype.card (P E (.inl n))≤channelCount T^3 := by
    simpa only [P,Fintype.card_prod,ZMod.card] using hp.2.2.2.1 n
  calc
    _ ≤ ∏ j : ZMod T.width, Fintype.card (P E (ordinaryCycle T (j-1)))*
        Fintype.card (digitSubgroup E (ordinaryCycle T j) (ordinaryCycleLabels w j)) := sparseCycleTiles_card_le E _ _
    _ ≤ ∏ _j : ZMod T.width, channelCount T^3*Q := Finset.prod_le_prod (fun j _ =>
      Nat.mul_le_mul (hP _) ((digitSubgroup_card_le_prime E _ _).trans (hq _ _)))
    _ = _ := by simp

theorem word_card (hB : T.alphabet=3) (hp : EconomicalPrimes E) (Q : ℕ)
    (hq : ∀ i j, E.digitPrime i j≤Q) :
    (wordConstraintTiles E).card≤(3*channelCount T^3*Q)^T.width := by
  let C := channelCount T
  have hw : Fintype.card (Word T)=3^T.width := by simp [Word,Symbol,hB]
  unfold wordConstraintTiles
  calc
    _ ≤ ∑ _w ∈ Finset.univ.filter (fun w : Word T => w∉allowedWords T), (C^3*Q)^T.width :=
      Finset.card_biUnion_le.trans (Finset.sum_le_sum (fun w _ => ordinary_cycle_card E hp Q hq w))
    _ ≤ Fintype.card (Word T)*(C^3*Q)^T.width := by
      simp only [Finset.sum_const,smul_eq_mul]
      exact Nat.mul_le_mul_right _ (Finset.card_filter_le _ _)
    _ = _ := by rw [hw,← mul_pow]; congr 1; ring

theorem testTiles_card (hB : T.alphabet=3) (hp : EconomicalPrimes E)
    (hC : 962≤channelCount T) (hS : ∀ n, (T.slope n).natAbs≤Sudoku.Width)
    (Q : ℕ) (hQ : 1≤Q) (hq : ∀ i j, E.digitPrime i j≤Q) :
    (testTiles E).card≤6*(3*channelCount T^3*Q)^T.width := by
  let C := channelCount T
  let A := (3*C^3*Q)^T.width
  have h1 : 1≤C := by omega
  have hw : 48≤3*T.width := by unfold channelCount at hC; omega
  have hself : C≤C^12 := Nat.le_self_pow (by decide) _
  have hb := (economical_parameterBudget E hC hB hp hS).1
  have hsmall : C^48≤A := by
    calc
      _ ≤ C^(3*T.width) := Nat.pow_le_pow_right h1 hw
      _ = (C^3)^T.width := by rw [← pow_mul]
      _ ≤ _ := Nat.pow_le_pow_left ((by omega : C^3≤3*C^3).trans (Nat.le_mul_of_pos_right _ (by omega))) _
  have hdep : (dependenceTiles E).card≤A := by
    have hd := dependenceTiles_card_le hb hself
    apply hd.trans
    rw [← pow_mul]
    exact hsmall
  have hword : (wordConstraintTiles E).card≤A := word_card E hB hp Q hq
  have hseed : (seedConstraintTiles E).card≤A := (EconomicalSize.seed_card_le E hB hp hC).trans
    ((Nat.pow_le_pow_right h1 (by decide : 17≤48)).trans hsmall)
  have hsingle : 1≤A := (Nat.one_le_pow _ _ h1).trans hsmall
  have hchannel : C≤A := (Nat.le_self_pow (by decide : 48≠0) _).trans hsmall
  have hact : (Finset.univ.image (ordinaryActivationTile E)).card≤A := by
    apply Finset.card_image_le.trans
    rw [Finset.card_univ]
    have hh : Fintype.card (Column T)≤C := by simp [Column,C,channelCount]
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

/-- Keep the small factors until after taking powers. -/
theorem count_pow {C w Q X : ℕ} (hC : 962≤C) (hq : Q^20≤C^71)
    (hX : X≤6*(3*C^3*Q)^w) : X^60≤C^(403*w+30) := by
  have h36 : 6^60≤C^30 := by
    calc
      _ = (6^2)^30 := by ring
      _ ≤ C^30 := Nat.pow_le_pow_left (by norm_num; omega) _
  have hq60 : Q^60≤C^213 := by
    simpa only [← pow_mul] using Nat.pow_le_pow_left hq 3
  have h3 : 3^60≤C^10 := by
    calc
      _ = (3^6)^10 := by ring
      _ ≤ C^10 := Nat.pow_le_pow_left (by norm_num; omega) _
  have hcore : (3*C^3*Q)^60≤C^403 := by
    calc
      _ = 3^60*C^180*Q^60 := by ring
      _ ≤ C^10*C^180*C^213 := Nat.mul_le_mul (Nat.mul_le_mul_right _ h3) hq60
      _ = _ := by ring
  calc
    _ ≤ (6*(3*C^3*Q)^w)^60 := Nat.pow_le_pow_left hX _
    _ = 6^60*((3*C^3*Q)^60)^w := by rw [mul_pow]; congr 1; rw [← pow_mul,← pow_mul,Nat.mul_comm w 60]
    _ ≤ C^30*(C^403)^w := Nat.mul_le_mul h36 (Nat.pow_le_pow_left hcore _)
    _ = _ := by rw [← pow_mul,← pow_add]; congr 1; omega

theorem testBudget_pow (hB : T.alphabet=3) (hp : EconomicalPrimes E)
    (hC : 962≤channelCount T) (hS : ∀ n, (T.slope n).natAbs≤Sudoku.Width) :
    (max (testTiles E).card (channelCount T^2))^60≤channelCount T^(403*T.width+30) := by
  let C := channelCount T
  let Q := Nat.nthRoot 20 (C^71)
  have hQ : 1≤Q := (Nat.le_nthRoot_iff (by decide : 20≠0)).mpr (by simpa only [one_pow] using Nat.one_le_pow 71 C (by omega : 1≤C))
  have hq (i j) : E.digitPrime i j≤Q := (Nat.le_nthRoot_iff (by decide : 20≠0)).mpr (hp.2.2.2.2 i j)
  have hqpow : Q^20≤C^71 := Nat.pow_nthRoot_le (Or.inl (by decide))
  apply count_pow hC hqpow
  apply max_le (testTiles_card E hB hp hC hS Q hQ hq)
  have hw : 2≤3*T.width := by unfold channelCount at hC; omega
  calc
    _ ≤ C^(3*T.width) := Nat.pow_le_pow_right (by omega) hw
    _ = (C^3)^T.width := by rw [← pow_mul]
    _ ≤ (3*C^3*Q)^T.width := Nat.pow_le_pow_left ((by omega : C^3≤3*C^3).trans (Nat.le_mul_of_pos_right _ (by omega))) _
    _ ≤ _ := Nat.le_mul_of_pos_left _ (by decide : 0<6)

theorem freshCap_pow {C w X : ℕ} (hC : 962≤C) (hXlo : C^2≤X) (hXhi : X≤C^(8*C))
    (hX : X^60≤C^(403*w+30)) : Effective.freshCap X (C^4)^30≤C^(403*w+120) := by
  have h1 : 1≤C := by omega
  have hL : Stacking.differenceLog X≤C^2 := by
    apply (show Stacking.differenceLog X≤Stacking.differenceLog (C^(8*C)) from by
      unfold Stacking.differenceLog
      exact Nat.add_le_add_right (Nat.log_mono_right (Nat.mul_le_mul_left 2 hXhi)) 1).trans
    exact EconomicalSize.differenceLog_channel_le hC
  have hLp : 1≤Stacking.differenceLog X := by unfold Stacking.differenceLog; omega
  have hP : C^4≤X^2 := by
    calc
      _ = (C^2)^2 := by ring
      _ ≤ _ := Nat.pow_le_pow_left hXlo _
  have hX3 : 3≤X^2 := (by nlinarith : 3≤C^4).trans hP
  have hXL : X^2≤X^2*Stacking.differenceLog X := Nat.le_mul_of_pos_right _ (by omega)
  have hf : Effective.freshCap X (C^4)≤C^3*X^2 := by
    calc
      _ ≤ 132*X^2*Stacking.differenceLog X := by
        unfold Effective.freshCap Stacking.logPartitionThreshold
        nlinarith
      _ ≤ 132*X^2*C^2 := Nat.mul_le_mul_left _ hL
      _ ≤ C*X^2*C^2 := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega))
      _ = _ := by ring
  calc
    _ ≤ (C^3*X^2)^30 := Nat.pow_le_pow_left hf _
    _ = C^90*X^60 := by ring
    _ ≤ C^90*C^(403*w+30) := Nat.mul_le_mul_left _ hX
    _ = _ := by rw [← pow_add]; congr 1; omega

theorem geometry_pow {C w H M : ℕ} (hC : 962≤C) (hw : w+2=C)
    (hH : H≤C^265) (hM : M^30≤C^(1132*w+960)) :
    ((9*2^24*972*36*8003^4)*H^4*M^3)^5≤C^(571*C) := by
  let K := 9*2^24*972*36*8003^4
  have hk : K≤C^11 := by
    apply (by norm_num [K] : K≤(2^9)^11).trans
    exact Nat.pow_le_pow_left (by norm_num; omega) _
  apply (Nat.pow_le_pow_iff_left (by decide : 2≠0)).mp
  change ((K*H^4*M^3)^5)^2≤_
  calc
    _ = K^10*H^40*M^30 := by simp only [mul_pow,← pow_mul]
    _ ≤ (C^11)^10*(C^265)^40*C^(1132*w+960) := Nat.mul_le_mul
      (Nat.mul_le_mul (Nat.pow_le_pow_left hk _) (Nat.pow_le_pow_left hH _)) hM
    _ = C^(1132*w+11670) := by simp only [← pow_mul,← pow_add]; congr 1; omega
    _ ≤ C^(1142*C) := Nat.pow_le_pow_right (by omega) (by omega)
    _ = _ := by rw [← pow_mul]; congr 1; omega

end
end TranslationTiling.FiniteCompiler.RefinedSize
