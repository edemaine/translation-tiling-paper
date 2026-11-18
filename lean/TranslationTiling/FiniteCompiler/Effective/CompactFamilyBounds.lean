import TranslationTiling.FiniteCompiler.Effective.CompactFamilyCompiler
import TranslationTiling.FiniteCompiler.Effective.CompactHorizontal

namespace TranslationTiling.FiniteCompiler.Effective
open Compiler Compiler.Effective
open scoped Classical
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem family_freshCap_bound (T : System) (G : List CyclicTile) (hf : FamilyBudget T G)
    (hw : 48≤T.width) : freshCap (max G.length (primeBudget T^2)) (primeBudget T^4)≤
      primeBudget T^3*3^(2*T.width+2) := by
  let C := primeBudget T
  let X := max G.length (C^2)
  have hC : 256≤C := le_max_right _ _
  have hX : X≤3^(T.width+1) := max_le hf.count (budget_square_le_three_48 _ hw)
  have hXhi : X≤C^(8*C) := by
    apply hX.trans
    apply (Nat.pow_le_pow_left (by omega : 3≤C) _).trans
    apply Nat.pow_le_pow_right (by omega)
    have hh : T.width+2≤C := le_max_left _ _
    omega
  apply (FixedSize.freshCap_le hC (le_max_right _ _) hXhi).trans
  apply Nat.mul_le_mul_left
  convert Nat.pow_le_pow_left hX 2 using 1 <;> rw [←pow_mul] <;> congr 1 <;> ring

theorem family_compact_bound (T : System) (G : List CyclicTile) (hf : FamilyBudget T G)
    (hS : ∀ n, (T.slope n).natAbs≤Sudoku.Width) (hB : T.alphabet=3) (hw : 48≤T.width)
    (H : ℕ) (hH : 1≤H) (hHcap : H≤primeBudget T^16)
    (hxy : ∀ F∈G, ∀ f∈F, f.1.1.natAbs≤H ∧ f.1.2.natAbs≤H) :
    (familyTileAt ((parameterData T,G),H)).length≤primeBudget T^(33*T.width+98)*3^(4*T.width+4) := by
  have hlen := (familyTileAt_facts T G hf hS hB hw H hH hxy).2.2.2
  let C := primeBudget T
  let L := freshCap (max G.length (C^2)) (C^4)
  have hC : 256≤C := le_max_right _ _
  have hpr := parameters_bounded_budget T hB
  have hv : (parameters T).cyclicOrder≤C^(21*T.width+28) := by
    apply (Nat.pow_le_pow_iff_left (by decide : 10≠0)).mp
    simpa only [←pow_mul,show (21*T.width+28)*10=210*T.width+280 by ring] using
      BudgetSize.cyclicOrder_pow (parameters T) hB hpr hC
  have hell : L≤C^3*3^(2*T.width+2) := family_freshCap_bound T G hf hw
  have hM : max (H^2) ((parameters T).cyclicOrder*L)≤C^(21*T.width+31)*3^(2*T.width+2) := by
    apply max_le
    · apply (Nat.pow_le_pow_left hHcap 2).trans
      rw [←pow_mul]
      apply (Nat.pow_le_pow_right (by omega : 1≤C) (by omega : 16*2≤21*T.width+31)).trans
      exact Nat.le_mul_of_pos_right _ (by positivity)
    · calc
        _ ≤ C^(21*T.width+28)*(C^3*3^(2*T.width+2)) := Nat.mul_le_mul hv hell
        _ = _ := by rw [←mul_assoc,←pow_add]
  have hJ : MassSize.mass (parameters T)*L≤C^(12*T.width+23)*3^(2*T.width+2) := by
    calc
      _ ≤ C^(12*T.width+20)*(C^3*3^(2*T.width+2)) :=
        Nat.mul_le_mul (MassSize.mass_bound (parameters T) hB hpr) hell
      _ = _ := by rw [←mul_assoc,←pow_add]
  exact hlen.trans (Rails.compact_geometry_bound hC hHcap hM hJ)

theorem family_small_freshCap_bound (T : System) (G : List CyclicTile) (hf : FamilyBudget T G)
    (hw : 48≤T.width) (hw' : T.width≤112) :
    freshCap (max G.length (primeBudget T^2)) (primeBudget T^4)≤2^15*3^(2*T.width+2) := by
  have hC : primeBudget T=256 := by unfold primeBudget channelCount; omega
  rw [hC]
  let X := max G.length (256^2)
  have hsmall : max (T.width+2) 256=256 := by omega
  have hbudget := budget_square_le_three_48 T.width hw
  rw [hsmall] at hbudget
  have hX : X≤3^(T.width+1) := max_le hf.count hbudget
  have hX113 : X≤3^113 := hX.trans (Nat.pow_le_pow_right (by decide) (by omega))
  have hL : Stacking.differenceLog X≤192 := by
    have hh := Nat.add_le_add_right (Nat.log_mono_right (b:=2) (Nat.mul_le_mul_left 2 hX113)) 1
    exact hh.trans (by decide : Nat.log 2 (2*3^113)+1≤192)
  have hLo : 1≤Stacking.differenceLog X := by unfold Stacking.differenceLog; omega
  have hP : 256^4≤X^2 := by
    calc
      256^4 = (256^2)^2 := by norm_num
      _ ≤ X^2 := Nat.pow_le_pow_left (le_max_right G.length (256^2)) 2
  have hcap : freshCap X (256^4)≤132*X^2*Stacking.differenceLog X := by
    unfold freshCap Stacking.logPartitionThreshold
    have hh : X^2≤X^2*Stacking.differenceLog X := Nat.le_mul_of_pos_right _ hLo
    nlinarith
  calc
    _ ≤ 132*X^2*192 := hcap.trans (Nat.mul_le_mul_left _ hL)
    _ ≤ 2^15*X^2 := by omega
    _ ≤ 2^15*(3^(T.width+1))^2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hX 2)
    _ = _ := by rw [←pow_mul]; congr 2; ring

theorem family_small_bound (T : System) (G : List CyclicTile) (hf : FamilyBudget T G)
    (hS : ∀ n, (T.slope n).natAbs≤Sudoku.Width) (hB : T.alphabet=3)
    (i : Fin 5) (hw : T.width=SmallProfiles.width i)
    (hxy : ∀ F∈G, ∀ f∈F, f.1.1.natAbs≤SmallProfiles.horizontal i ∧
      f.1.2.natAbs≤SmallProfiles.horizontal i) :
    (familyTileAt ((parameterData T,G),SmallProfiles.horizontal i)).length≤2^SmallProfiles.exponent i := by
  have hwlo : 48≤T.width := by rw [hw]; unfold SmallProfiles.width; omega
  have hwhi : T.width≤112 := by rw [hw]; unfold SmallProfiles.width; omega
  have hH : 1≤SmallProfiles.horizontal i := (by decide : 1≤175).trans (SmallProfiles.support i).1
  have hlen := (familyTileAt_facts T G hf hS hB hwlo _ hH hxy).2.2.2
  have hell := family_small_freshCap_bound T G hf hwlo hwhi
  have hv := SmallProfiles.volume i
  rw [parameters_small_order T i hw hB,parameters_small_mass T i hw hB,hw] at hlen
  rw [hw] at hell
  apply hlen.trans
  apply le_trans _ hv.2
  have hM : max ((SmallProfiles.horizontal i)^2)
      ((SmallProfiles.profile i).order (SmallProfiles.width i)*
        freshCap (max G.length (primeBudget T^2)) (primeBudget T^4))≤
      (SmallProfiles.profile i).order (SmallProfiles.width i)*(2^15*3^(2*SmallProfiles.width i+2)) := by
    apply max_le
    · simpa only [Nat.mul_comm] using hv.1
    · exact Nat.mul_le_mul_left _ hell
  calc
    _ ≤ (2^24*((SmallProfiles.profile i).mass (SmallProfiles.width i)*(2^15*3^(2*SmallProfiles.width i+2))))*
        (549072*8003^4)*(SmallProfiles.horizontal i)^2*
        ((SmallProfiles.profile i).order (SmallProfiles.width i)*(2^15*3^(2*SmallProfiles.width i+2))) :=
      Nat.mul_le_mul (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hell)))) hM
    _ = _ := by ring

end
end TranslationTiling.FiniteCompiler.Effective
