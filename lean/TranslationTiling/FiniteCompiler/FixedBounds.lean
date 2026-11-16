import TranslationTiling.FiniteCompiler.BudgetBounds

namespace TranslationTiling.FiniteCompiler.FixedSize
open Compiler.Size Size
open scoped Classical BigOperators
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem successor_pow {P : ℕ} (hP : 962≤P) : (P+1)^36≤3*P^36 := by
  have hh : 962*(P+1)≤963*P := by omega
  have hpow := Nat.pow_le_pow_left hh 36
  rw [mul_pow,mul_pow] at hpow
  apply (Nat.mul_le_mul_left_iff (by norm_num : 0<962^36)).mp
  calc
    _ ≤ 963^36*P^36 := hpow
    _ ≤ (962^36*3)*P^36 := Nat.mul_le_mul_right _ (by norm_num)
    _ = _ := by ring

theorem budget_pow_le_three (w : ℕ) (hw : 240≤w) :
    (max (w+2) 962)^36≤3^w := by
  induction w,hw using Nat.le_induction with
  | base => norm_num
  | succ w hw ih =>
    have hh : max (w+1+2) 962≤max (w+2) 962+1 := by omega
    calc
      _ ≤ (max (w+2) 962+1)^36 := Nat.pow_le_pow_left hh _
      _ ≤ 3*(max (w+2) 962)^36 := successor_pow (le_max_right _ _)
      _ ≤ 3*3^w := Nat.mul_le_mul_left _ ih
      _ = _ := (pow_succ' _ _).symm

variable {T : System} (E : EncodingParameters T)

theorem testTiles_card (hB : T.alphabet=3) (hp : BudgetPrimes E (primeBudget T))
    (hw : 240≤T.width) (hS : ∀ n, (T.slope n).natAbs≤Sudoku.Width) :
    (testTiles E).card≤3^(T.width+1) := by
  let P := primeBudget T
  have hP : 962≤P := le_max_right _ _
  have hCP : channelCount T≤P := le_max_left _ _
  have hb := BudgetSize.parameterBudget_nine E hP hCP hB hp hS
  have hdep : (dependenceTiles E).card≤P^36 := by
    simpa only [←pow_mul] using dependenceTiles_card_le hb.1 hb.2.1
  have hword : (wordConstraintTiles E).card≤3^T.width := by
    unfold wordConstraintTiles
    apply Finset.card_biUnion_le.trans
    simp only [fixedCycleTiles,Finset.card_singleton,Finset.sum_const,smul_eq_mul,mul_one]
    apply (Finset.card_filter_le _ _).trans
    simp [Word,Symbol,hB]
  have hseed : (seedConstraintTiles E).card≤6*T.width := by
    unfold seedConstraintTiles
    apply Finset.card_biUnion_le.trans
    simp only [fixedCycleTiles,Finset.card_singleton,Finset.sum_const,smul_eq_mul,mul_one]
    apply (Finset.card_filter_le _ _).trans
    simp [Column,Symbol,hB,Fintype.card_prod]
    omega
  have hact : (Finset.univ.image (ordinaryActivationTile E)).card≤T.width := by
    calc
      _ ≤ (Finset.univ : Finset (Column T)).card := Finset.card_image_le
      _ = _ := by simp [Column]
  have hsact : (Finset.univ.image (seedActivationTile E)).card≤2 := by
    calc
      _ ≤ (Finset.univ : Finset (Fin 2)).card := Finset.card_image_le
      _ = _ := by simp
  have hp36 : P^36≤3^T.width := budget_pow_le_three T.width hw
  have hlin : 7*T.width+3≤3^T.width := by
    apply le_trans (b:=P^2) _ ((Nat.pow_le_pow_right (by omega) (by decide : 2≤36)).trans hp36)
    unfold channelCount at hCP
    nlinarith
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
  rw [pow_succ']
  omega

theorem freshCap_le {P X : ℕ} (hP : 962≤P) (hXlo : P^2≤X) (hXhi : X≤P^(8*P)) :
    Effective.freshCap X (P^4)≤P^3*X^2 := by
  have hL : Stacking.differenceLog X≤P^2 := by
    apply (show Stacking.differenceLog X≤Stacking.differenceLog (P^(8*P)) from by
      unfold Stacking.differenceLog
      exact Nat.add_le_add_right (Nat.log_mono_right (Nat.mul_le_mul_left 2 hXhi)) 1).trans
    exact EconomicalSize.differenceLog_channel_le hP
  have hLp : 1≤Stacking.differenceLog X := by unfold Stacking.differenceLog; omega
  have hcap : P^4≤X^2 := by simpa only [←pow_mul] using Nat.pow_le_pow_left hXlo 2
  have hX3 : 3≤X^2 := (by nlinarith : 3≤P^4).trans hcap
  have hXL : X^2≤X^2*Stacking.differenceLog X := Nat.le_mul_of_pos_right _ (by omega)
  calc
    _ ≤ 132*X^2*Stacking.differenceLog X := by
      unfold Effective.freshCap Stacking.logPartitionThreshold
      nlinarith
    _ ≤ 132*X^2*P^2 := Nat.mul_le_mul_left _ hL
    _ ≤ P*X^2*P^2 := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega))
    _ = _ := by ring

theorem geometry_bound {P w H M : ℕ} (hP : 962≤P)
    (hH : H≤P^199) (hM : M^30≤P^(630*w+930)*3^(60*w+60)) :
    ((9*2^24*972*36*8003^4)*H^4*M^3)^10≤P^(640*w+9010) := by
  have hk : 9*2^24*972*36*8003^4≤P^11 := by
    apply (by norm_num : 9*2^24*972*36*8003^4≤(2^9)^11).trans
    exact Nat.pow_le_pow_left (by norm_num; omega) _
  have hthree : 3^(60*w+60)≤P^(10*w+10) := by
    calc
      _ = (3^6)^(10*w+10) := by rw [←pow_mul]; congr 1; omega
      _ ≤ _ := Nat.pow_le_pow_left (by norm_num; omega) _
  let K := 9*2^24*972*36*8003^4
  change (K*H^4*M^3)^10≤_
  calc
    _ = K^10*H^40*M^30 := by simp only [mul_pow,←pow_mul]
    _ ≤ (P^11)^10*(P^199)^40*(P^(630*w+930)*3^(60*w+60)) :=
      Nat.mul_le_mul (Nat.mul_le_mul (Nat.pow_le_pow_left hk 10)
        (Nat.pow_le_pow_left hH 40)) hM
    _ ≤ (P^11)^10*(P^199)^40*(P^(630*w+930)*P^(10*w+10)) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hthree)
    _ = _ := by simp only [←pow_mul,←pow_add]; congr 1; ring

end
end TranslationTiling.FiniteCompiler.FixedSize
