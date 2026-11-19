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

/-- Only a quadratic budget needs to be dominated by the word count. -/
theorem budget_square_le_three (w : ℕ) (hw : 64≤w) :
    (max (w+2) 256)^2≤3^(w+1) := by
  induction w,hw using Nat.le_induction with
  | base => norm_num
  | succ w hw ih =>
    have hh : max (w+1+2) 256≤max (w+2) 256+1 := by omega
    have hp : 2≤max (w+2) 256 := by omega
    calc
      _ ≤ (max (w+2) 256+1)^2 := Nat.pow_le_pow_left hh _
      _ ≤ 3*(max (w+2) 256)^2 := by nlinarith
      _ ≤ 3*3^(w+1) := Nat.mul_le_mul_left _ ih
      _ = _ := (pow_succ' _ _).symm

theorem quadratic_le_three (w : ℕ) (hw : 4≤w) : w^2+12*w+11≤3^w := by
  induction w,hw using Nat.le_induction with
  | base => norm_num
  | succ w hw ih =>
    rw [show 3^(w+1)=3^w*3 by exact pow_succ 3 w]
    nlinarith

variable {T : System} (E : EncodingParameters T)

/-- Count the dependence indices directly, independently of prime sizes. -/
theorem dependence_card [SeedFrame] {T : System} [AlphabetFamily T] (E : EncodingParameters T) : (dependenceTiles E).card≤(T.width+2)^2+T.width+4 := by
  have hsub (i : Channel T) : Fintype.card {j : Channel T // j≠i}≤T.width+2 := by
    simpa only [channel_card,channelCount] using
      Fintype.card_le_of_injective Subtype.val (Subtype.val_injective (p:=fun j : Channel T => j≠i))
  have hpair : Fintype.card (Σ i : Channel T, {j : Channel T // j≠i})≤(T.width+2)^2 := by
    rw [Fintype.card_sigma]
    calc
      _ ≤ ∑ _i : Channel T, (T.width+2) := Finset.sum_le_sum (fun i _ => hsub i)
      _ = _ := by simp [channel_card,channelCount,pow_two]
  unfold dependenceTiles
  apply (Finset.card_image_le.trans (le_of_eq Finset.card_univ)).trans
  simp only [DependenceIndex,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin,Fintype.card_bool]
  simpa [Column,Nat.add_assoc] using Nat.add_le_add_right hpair (T.width+2*2)

theorem testTiles_card (hB : T.alphabet=3) (hp : BudgetPrimes E (primeBudget T))
    (hw : 4≤T.width) (hS : ∀ n, (T.slope n).natAbs≤Sudoku.Width) :
    (testTiles E).card≤3^(T.width+1) := by
  have hdep := dependence_card E
  have hword : (wordConstraintTiles E).card≤3^T.width := by
    unfold wordConstraintTiles
    apply Finset.card_biUnion_le.trans
    simp only [fixedCycleTiles,Finset.card_singleton,Finset.sum_const,smul_eq_mul,mul_one]
    apply (Finset.card_filter_le _ _).trans
    simp [Word,Letter,uniformAlphabetFamily,Symbol,hB]
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
  have hlin : (T.width+2)^2+8*T.width+7≤3^T.width := by
    have hh := quadratic_le_three T.width hw
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

theorem freshCap_le {P X : ℕ} (hP : 256≤P) (hXlo : P^2≤X) (hXhi : X≤P^(8*P)) :
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
