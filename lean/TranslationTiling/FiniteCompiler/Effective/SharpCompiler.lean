import TranslationTiling.FiniteCompiler.Effective.Correctness
import TranslationTiling.FiniteCompiler.Effective.SparseGeometry
import TranslationTiling.FiniteCompiler.TightBounds
import TranslationTiling.FiniteCompiler.FixedBounds
import TranslationTiling.FiniteCompiler.Effective.MassGeometry
import TranslationTiling.Rails.SizeBound
import TranslationTiling.FourLayer.MSSBound
import TranslationTiling.FourLayer.SizeBound

namespace TranslationTiling.FiniteCompiler.Effective
open Compiler Compiler.Effective
open scoped Classical
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def sharpCyclic (d : InputData) : CyclicTileData :=
  let C := max (d.1.1+2) 256
  let Fs := canonicalInputFamily d
  freshStack (max Fs.length (C^2),rawOrder d.1,C^4,Fs)

theorem sharpCyclic_computable : Computable sharpCyclic := by
  have hlen := Primrec.list_length.to_comp.comp canonicalInputFamily_computable
  have hC2 : Primrec (fun d : InputData => (max (d.1.1+2) 256)^2) := by fun_prop
  have hmax : Primrec (fun z : ℕ×ℕ => max z.1 z.2) := by fun_prop
  have hX := hmax.to_comp.comp (hlen.pair hC2.to_comp)
  have hP : Primrec (fun d : InputData => (max (d.1.1+2) 256)^4) := by fun_prop
  exact freshStack_computable.comp (hX.pair
    ((rawOrder_primrec.to_comp.comp Computable.fst).pair (hP.to_comp.pair canonicalInputFamily_computable)))

def sharpTile (d : InputData) : Tile 3 :=
  let c := sharpCyclic d
  let H := rawHorizontal d.1
  Rails.connectedTile (Compiler.integerTile c) H (max (H^2) c.1)

theorem sharpTile_computable : Computable sharpTile := by
  have hE := Compiler.integerTile_computable.comp sharpCyclic_computable
  have hH : Primrec (fun d : InputData => rawHorizontal d.1) := by fun_prop
  have hmax : Primrec (fun z : ℕ×ℕ => max z.1 z.2) := by fun_prop
  have hM := hmax.to_comp.comp (((show Primrec (fun d : InputData => (rawHorizontal d.1)^2) by fun_prop).to_comp).pair (Computable.fst.comp sharpCyclic_computable))
  have h := Rails.connectedTile_computable.comp (hE.pair (hH.to_comp.pair hM))
  dsimp only at h
  unfold sharpTile
  exact h

theorem sharpCyclic_facts (T : System) (p : Payload) (hp : PayloadCorrect T p)
    (hpos : ∀ n, 0≤T.slope n) (hS : ∀ n, (T.slope n).natAbs≤Sudoku.Width)
    (hB : T.alphabet=3) (hC : 6*Sudoku.Width+2 ≤ channelCount T) :
    0<(sharpCyclic (parameterData T,p)).1 ∧ (sharpCyclic (parameterData T,p)).2≠[] ∧
    (sharpCyclic (parameterData T,p)).1^30≤primeBudget T^(630*T.width+930)*3^(60*T.width+60) ∧
    (∀ f ∈ (sharpCyclic (parameterData T,p)).2,
      f.1.1.natAbs≤rawHorizontal (parameterData T) ∧ f.1.2.natAbs≤rawHorizontal (parameterData T)) ∧
    ((∃ A : Set (Ambient (parameters T)), Solves (parameters T) A) ↔
      ∃ B : Set (Plane × ZMod (sharpCyclic (parameterData T,p)).1),
        Tiles (cyclicTileSet (sharpCyclic (parameterData T,p)).1 (sharpCyclic (parameterData T,p)).2) B) := by
  let C := primeBudget T
  let Fs := canonicalInputFamily (parameterData T,p)
  let X := max Fs.length (C^2)
  have hbig : 256≤C := le_max_right _ _
  have hcp : channelCount T≤C := le_max_left _ _
  have hw : 16≤T.width := by norm_num [channelCount,Sudoku.Width,Sudoku.q] at hC; omega
  have hsmall : BudgetPrimes (parameters T) C := parameters_bounded_budget T hB
  have hcount : Fs.length≤3^(T.width+1) := by
    rw [canonicalInputFamily_length T p hp hpos hS]
    exact FixedSize.testTiles_card (parameters T) hB hsmall (by
      norm_num [channelCount,Sudoku.Width,Sudoku.q] at hC; omega) hS
  have hX3 : X≤3^(T.width+1) := max_le hcount
    (FixedSize.budget_square_le_three T.width (by
      norm_num [channelCount,Sudoku.Width,Sudoku.q] at hC; omega))
  have hXhi : X≤C^(8*C) := by
    apply hX3.trans
    apply (Nat.pow_le_pow_left (by omega : 3≤C) _).trans
    exact Nat.pow_le_pow_right (by omega) (by unfold channelCount at hcp; omega)
  have hXlo : C^2≤X := le_max_right _ _
  have hlen : 0<Fs.length := by
    rw [canonicalInputFamily_length T p hp hpos hS]
    exact Finset.card_pos.mpr (testTiles_nonempty (parameters T))
  have hP : C^4≤X^2 := by simpa only [← pow_mul] using Nat.pow_le_pow_left hXlo 2
  have hpr := BudgetSize.cyclicOrder_primeBound (parameters T) hB hsmall hbig
  have hraw : sharpCyclic (parameterData T,p) = freshStack (X,(parameters T).cyclicOrder,C^4,Fs) := by
    unfold sharpCyclic
    rw [rawOrder_eq]
    rfl
  rw [hraw]
  obtain ⟨hm,hne,hcap,hiff⟩ := freshStack_facts _ _ _ Fs (parameters T).cyclicOrder_pos hlen
    (le_max_left _ _) hP hpr (canonicalInputFamily_nonempty T p hp hpos hS)
  refine ⟨hm,hne,?_,?_,?_⟩
  · have hv := BudgetSize.cyclicOrder_pow (parameters T) hB hsmall hbig
    have hv30 : (parameters T).cyclicOrder^30≤C^(630*T.width+840) := by
      convert Nat.pow_le_pow_left hv 3 using 1 <;> simp only [← pow_mul] <;> congr 1 <;> ring
    have hell : freshCap X (C^4)≤C^3*3^(2*T.width+2) := by
      apply (FixedSize.freshCap_le hbig hXlo hXhi).trans
      apply Nat.mul_le_mul_left
      convert Nat.pow_le_pow_left hX3 2 using 1 <;> rw [←pow_mul] <;> congr 1 <;> ring
    calc
      _ ≤ ((parameters T).cyclicOrder*freshCap X (C^4))^30 := Nat.pow_le_pow_left hcap _
      _ = (parameters T).cyclicOrder^30*freshCap X (C^4)^30 := by ring
      _ ≤ C^(630*T.width+840)*(C^3*3^(2*T.width+2))^30 :=
        Nat.mul_le_mul hv30 (Nat.pow_le_pow_left hell _)
      _ = C^(630*T.width+930)*3^(60*T.width+60) := by
        simp only [mul_pow,←pow_mul]
        rw [←mul_assoc,←pow_add]
        rw [show 630*T.width+840+3*30=630*T.width+930 by ring,
          show (2*T.width+2)*30=60*T.width+60 by ring]
  · exact stackCodes_horizontal _ _ Fs _ (canonicalFamily_horizontal _ _ _)
  · exact (family_solution_iff (parameters T) Fs (canonicalInputFamily_correct T p hp hpos hS)).trans hiff

theorem sharpCyclic_mass (T : System) (p : Payload) (hp : PayloadCorrect T p)
    (hpos : ∀ n, 0≤T.slope n) (hS : ∀ n, (T.slope n).natAbs≤Sudoku.Width)
    (hB : T.alphabet=3) (hC : 6*Sudoku.Width+2 ≤ channelCount T) :
    (cyclicTileSet (sharpCyclic (parameterData T,p)).1 (sharpCyclic (parameterData T,p)).2).card≤
      primeBudget T^(12*T.width+23)*3^(2*T.width+2) := by
  let C := primeBudget T
  let Fs := canonicalInputFamily (parameterData T,p)
  let X := max Fs.length (C^2)
  have hbig : 256≤C := le_max_right _ _
  have hcp : channelCount T≤C := le_max_left _ _
  have hw : 16≤T.width := by norm_num [channelCount,Sudoku.Width,Sudoku.q] at hC; omega
  have hsmall : BudgetPrimes (parameters T) C := parameters_bounded_budget T hB
  have hcount : Fs.length≤3^(T.width+1) := by
    rw [canonicalInputFamily_length T p hp hpos hS]
    exact FixedSize.testTiles_card (parameters T) hB hsmall (by
      norm_num [channelCount,Sudoku.Width,Sudoku.q] at hC; omega) hS
  have hX3 : X≤3^(T.width+1) := max_le hcount
    (FixedSize.budget_square_le_three T.width (by
      norm_num [channelCount,Sudoku.Width,Sudoku.q] at hC; omega))
  have hXhi : X≤C^(8*C) := by
    apply hX3.trans
    apply (Nat.pow_le_pow_left (by omega : 3≤C) _).trans
    exact Nat.pow_le_pow_right (by omega) (by unfold channelCount at hcp; omega)
  have hXlo : C^2≤X := le_max_right _ _
  have hlen : 0<Fs.length := by
    rw [canonicalInputFamily_length T p hp hpos hS]
    exact Finset.card_pos.mpr (testTiles_nonempty (parameters T))
  have hP : C^4≤X^2 := by simpa only [← pow_mul] using Nat.pow_le_pow_left hXlo 2
  have hpr := BudgetSize.cyclicOrder_primeBound (parameters T) hB hsmall hbig
  have hraw : sharpCyclic (parameterData T,p) = freshStack (X,(parameters T).cyclicOrder,C^4,Fs) := by
    unfold sharpCyclic
    rw [rawOrder_eq]
    rfl
  rw [hraw]
  have hj := freshStack_mass X (parameters T).cyclicOrder (C^4) Fs
    (parameters T).cyclicOrder_pos hlen (le_max_left _ _) hP hpr _
    (family_mass T p hp hpos hS)
  have hell : freshCap X (C^4)≤C^3*3^(2*T.width+2) := by
    apply (FixedSize.freshCap_le hbig hXlo hXhi).trans
    apply Nat.mul_le_mul_left
    convert Nat.pow_le_pow_left hX3 2 using 1 <;> rw [←pow_mul] <;> congr 1 <;> ring
  calc
    _ ≤ MassSize.mass (parameters T)*freshCap X (C^4) := hj
    _ ≤ C^(12*T.width+20)*(C^3*3^(2*T.width+2)) :=
      Nat.mul_le_mul (MassSize.mass_bound (parameters T) hB hsmall) hell
    _ = C^(12*T.width+23)*3^(2*T.width+2) := by
      rw [←mul_assoc,←pow_add,show 12*T.width+20+3=12*T.width+23 by ring]

theorem sharpTile_facts (T : System) (p : Payload) (hp : PayloadCorrect T p)
    (hpos : ∀ n, 0≤T.slope n) (hS : ∀ n, (T.slope n).natAbs≤Sudoku.Width)
    (hB : T.alphabet=3) (hC : 6*Sudoku.Width+2 ≤ channelCount T) :
    sharpTile (parameterData T,p)≠[] ∧ FaceConnected (sharpTile (parameterData T,p)) ∧
    ((∃ A : Set (Ambient (parameters T)), Solves (parameters T) A) ↔
      TranslationTiling.Tiles (sharpTile (parameterData T,p))) ∧
    (sharpTile (parameterData T,p)).length≤primeBudget T^(33*T.width+466)*3^(4*T.width+4) := by
  obtain ⟨hm,hne,hR30,hxy,hiff⟩ := sharpCyclic_facts T p hp hpos hS hB hC
  have hcard := sharpCyclic_mass T p hp hpos hS hB hC
  dsimp only [sharpTile]
  generalize hd : sharpCyclic (parameterData T,p)=d at hm hne hR30 hxy hiff hcard ⊢
  let H := rawHorizontal (parameterData T)
  let C := primeBudget T
  let M := max (H^2) d.1
  have hbig : 256≤C := le_max_right _ _
  have hw : 168≤T.width := by norm_num [channelCount,Sudoku.Width,Sudoku.q] at hC; omega
  have heq : rawBudget (parameterData T)=C^9 := by
    change (if T.alphabet=3 then (max (T.width+2) 256)^9 else _)=C^9
    rw [if_pos hB]
    rfl
  have hH : H≤C^200 := by
    change Size.horizontalCap (rawBudget (parameterData T))≤_
    rw [heq]
    exact Size.horizontalCap_channel_nine_le hbig
  have hH1 : 1≤H := by
    exact ((by unfold channelCount; omega : 1≤channelCount T).trans (parameters_rawBudget T hS).2.1).trans (Size.le_horizontalCap _)
  have hR : d.1≤C^(21*T.width+31)*3^(2*T.width+2) := by
    apply (Nat.pow_le_pow_iff_left (by decide : 30≠0)).mp
    simpa only [mul_pow,←pow_mul,show (21*T.width+31)*30=630*T.width+930 by ring,
      show (2*T.width+2)*30=60*T.width+60 by ring] using hR30
  have hMc : M≤C^(21*T.width+31)*3^(2*T.width+2) := by
    apply max_le _ hR
    apply (Nat.pow_le_pow_left hH 2).trans
    rw [←pow_mul]
    apply (Nat.pow_le_pow_right (by omega : 1≤C) (by omega : 200*2≤21*T.width+31)).trans
    exact Nat.le_mul_of_pos_right _ (by positivity)
  have hM : d.1≤M := le_max_right _ _
  have hHM : H^2≤M := le_max_left _ _
  have hn := Compiler.integerTile_nonempty d hne
  have hrect := Compiler.Size.integerTile_rectangle_bound d H M hm hM hne hxy
  change Rails.connectedTile (Compiler.integerTile d) H M≠[] ∧ _
  refine ⟨Rails.connectedTile_nonempty _ H M hn,
    Rails.connectedTile_connected _ H M hrect,?_,?_⟩
  · exact hiff.trans ((Compiler.integerTile_correct MSS.rigidity d hm hne).trans
      (Rails.connectedTile_correct (Compiler.integerTile d) H M).symm)
  · have hvol := Compiler.Size.integerTile_cubeCount_mass d hm
    have hlen := Rails.connectedTile_length_mass (Compiler.integerTile d) H M hH1 hHM
    exact hlen.trans ((Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _
      (Nat.mul_le_mul_right _ hvol))).trans (Rails.geometry_bound hbig hH hMc hcard))

end
end TranslationTiling.FiniteCompiler.Effective
