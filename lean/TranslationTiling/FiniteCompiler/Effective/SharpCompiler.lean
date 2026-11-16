import TranslationTiling.FiniteCompiler.Effective.Correctness
import TranslationTiling.FiniteCompiler.Effective.SparseGeometry
import TranslationTiling.FiniteCompiler.TightBounds
import TranslationTiling.FiniteCompiler.BudgetBounds
import TranslationTiling.FourLayer.MSSBound
import TranslationTiling.FourLayer.SizeBound

namespace TranslationTiling.FiniteCompiler.Effective
open Compiler Compiler.Effective
open scoped Classical
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def sharpCyclic (d : InputData) : CyclicTileData :=
  let C := max (d.1.1+2) 962
  let Fs := canonicalInputFamily d
  freshStack (max Fs.length (C^2),rawOrder d.1,C^4,Fs)

theorem sharpCyclic_computable : Computable sharpCyclic := by
  have hlen := Primrec.list_length.to_comp.comp canonicalInputFamily_computable
  have hC2 : Primrec (fun d : InputData => (max (d.1.1+2) 962)^2) := by fun_prop
  have hmax : Primrec (fun z : ℕ×ℕ => max z.1 z.2) := by fun_prop
  have hX := hmax.to_comp.comp (hlen.pair hC2.to_comp)
  have hP : Primrec (fun d : InputData => (max (d.1.1+2) 962)^4) := by fun_prop
  exact freshStack_computable.comp (hX.pair
    ((rawOrder_primrec.to_comp.comp Computable.fst).pair (hP.to_comp.pair canonicalInputFamily_computable)))

def sharpTile (d : InputData) : Tile 3 :=
  let c := sharpCyclic d
  let H := rawHorizontal d.1
  FourLayer.connectedTile (Compiler.integerTile c) H (max H c.1)

theorem sharpTile_computable : Computable sharpTile := by
  have hE := Compiler.integerTile_computable.comp sharpCyclic_computable
  have hH : Primrec (fun d : InputData => rawHorizontal d.1) := by fun_prop
  have hmax : Primrec (fun z : ℕ×ℕ => max z.1 z.2) := by fun_prop
  have hM := hmax.to_comp.comp (hH.to_comp.pair (Computable.fst.comp sharpCyclic_computable))
  have h := FourLayer.connectedTile_computable.comp (hE.pair (hH.to_comp.pair hM))
  dsimp only at h
  unfold sharpTile
  exact h

theorem sharpCyclic_facts (T : System) (p : Payload) (hp : PayloadCorrect T p)
    (hpos : ∀ n, 0≤T.slope n) (hS : ∀ n, (T.slope n).natAbs≤Sudoku.Width)
    (hB : T.alphabet=3) (hC : 6*Sudoku.Width+2 ≤ channelCount T) :
    0<(sharpCyclic (parameterData T,p)).1 ∧ (sharpCyclic (parameterData T,p)).2≠[] ∧
    (sharpCyclic (parameterData T,p)).1^30≤primeBudget T^(1000*T.width+960) ∧
    (∀ f ∈ (sharpCyclic (parameterData T,p)).2,
      f.1.1.natAbs≤rawHorizontal (parameterData T) ∧ f.1.2.natAbs≤rawHorizontal (parameterData T)) ∧
    ((∃ A : Set (Ambient (parameters T)), Solves (parameters T) A) ↔
      ∃ B : Set (Plane × ZMod (sharpCyclic (parameterData T,p)).1),
        Tiles (cyclicTileSet (sharpCyclic (parameterData T,p)).1 (sharpCyclic (parameterData T,p)).2) B) := by
  let C := primeBudget T
  let Fs := canonicalInputFamily (parameterData T,p)
  let X := max Fs.length (C^2)
  have hbig : 962≤C := le_max_right _ _
  have hcp : channelCount T≤C := le_max_left _ _
  have hw : 16≤T.width := by norm_num [channelCount,Sudoku.Width,Sudoku.q] at hC; omega
  have hsmall : BudgetPrimes (parameters T) C := parameters_bounded_budget T hB
  have hcount' := BudgetSize.testTiles_card (parameters T) hB hsmall hbig hcp hw hS
    (C^3) (Nat.one_le_pow _ _ (by omega)) (hsmall.2.2.2.2)
  have hcount : Fs.length≤C^(8*C) := by
    rw [canonicalInputFamily_length T p hp hpos hS]
    apply hcount'.trans
    calc
      _ = 6*(3*C^6)^T.width := by congr 2; ring
      _ ≤ C*(C^7)^T.width := Nat.mul_le_mul (by omega)
        (Nat.pow_le_pow_left (by calc
          3*C^6 ≤ C*C^6 := Nat.mul_le_mul_right _ (by omega : 3≤C)
          _ = C^7 := (pow_succ' _ _).symm) _)
      _ = C^(7*T.width+1) := by rw [← pow_mul,pow_succ']
      _ ≤ _ := Nat.pow_le_pow_right (by omega) (by unfold channelCount at hcp; omega)
  have hXhi : X≤C^(8*C) := max_le hcount (Nat.pow_le_pow_right (by omega) (by omega))
  have hXlo : C^2≤X := le_max_right _ _
  have hX60 : X^60≤C^(370*T.width+30) := by
    dsimp only [X,Fs]
    rw [canonicalInputFamily_length T p hp hpos hS]
    exact BudgetSize.testBudget_pow (parameters T) hB hsmall hbig hcp hw hS
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
    calc
      _ ≤ ((parameters T).cyclicOrder*freshCap X (C^4))^30 := Nat.pow_le_pow_left hcap _
      _ = (parameters T).cyclicOrder^30*freshCap X (C^4)^30 := by ring
      _ ≤ C^(630*T.width+840)*C^(370*T.width+120) := Nat.mul_le_mul hv30
        (RefinedSize.freshCap_pow hbig hXlo hXhi hX60)
      _ = _ := by rw [← pow_add]; congr 1; ring
  · exact stackCodes_horizontal _ _ Fs _ (canonicalFamily_horizontal _ _ _)
  · exact (family_solution_iff (parameters T) Fs (canonicalInputFamily_correct T p hp hpos hS)).trans hiff

theorem sharpTile_facts (T : System) (p : Payload) (hp : PayloadCorrect T p)
    (hpos : ∀ n, 0≤T.slope n) (hS : ∀ n, (T.slope n).natAbs≤Sudoku.Width)
    (hB : T.alphabet=3) (hC : 6*Sudoku.Width+2 ≤ channelCount T) :
    sharpTile (parameterData T,p)≠[] ∧ FaceConnected (sharpTile (parameterData T,p)) ∧
    ((∃ A : Set (Ambient (parameters T)), Solves (parameters T) A) ↔
      TranslationTiling.Tiles (sharpTile (parameterData T,p))) ∧
    (sharpTile (parameterData T,p)).length^10≤primeBudget T^(1000*T.width+9030) := by
  obtain ⟨hm,hne,hR30,hxy,hiff⟩ := sharpCyclic_facts T p hp hpos hS hB hC
  dsimp only [sharpTile]
  generalize hd : sharpCyclic (parameterData T,p)=d at hm hne hR30 hxy hiff ⊢
  let H := rawHorizontal (parameterData T)
  let C := primeBudget T
  let M := max H d.1
  have hbig : 962≤C := le_max_right _ _
  have hw : 16≤T.width := by norm_num [channelCount,Sudoku.Width,Sudoku.q] at hC; omega
  have heq : rawBudget (parameterData T)=C^9 := by
    change (if T.alphabet=3 then (max (T.width+2) 962)^9 else _)=C^9
    rw [if_pos hB]
    rfl
  have hH : H≤C^199 := by
    change Size.horizontalCap (rawBudget (parameterData T))≤_
    rw [heq]
    exact Size.horizontalCap_channel_nine_le hbig
  have hH1 : 1≤H := by
    exact ((by unfold channelCount; omega : 1≤channelCount T).trans (parameters_rawBudget T hS).2.1).trans (Size.le_horizontalCap _)
  have hM30 : M^30≤C^(1000*T.width+960) := by
    rcases le_total H d.1 with hh | hh
    · simpa only [M,max_eq_right hh] using hR30
    · rw [show M=H from max_eq_left hh]
      apply (Nat.pow_le_pow_left hH _).trans
      rw [← pow_mul]
      exact Nat.pow_le_pow_right (by omega) (by omega)
  have hM : d.1≤M := le_max_right _ _
  have hHM : H≤M := le_max_left _ _
  have hn := Compiler.integerTile_nonempty d hne
  have hrect := Compiler.Size.integerTile_rectangle_bound d H M hm hM hne hxy
  change FourLayer.connectedTile (Compiler.integerTile d) H M≠[] ∧ _
  refine ⟨FourLayer.connectedTile_nonempty _ H M hn,
    FourLayer.connectedTile_connected _ H M hrect,?_,?_⟩
  · exact hiff.trans ((Compiler.integerTile_correct MSS.rigidity d hm hne).trans
      (FourLayer.connectedTile_correct (Compiler.integerTile d) H M).symm)
  · have hs : (2*H+1)^2≤9*H^2 := by nlinarith
    have hvol : Compiler.Size.cubeCount (Compiler.integerTile d)≤9*2^24*H^2*M := by
      calc
        _ ≤ 2^24*((2*H+1)^2*d.1) := Compiler.Size.integerTile_cubeCount_sparse d H hm hxy
        _ ≤ 2^24*(9*H^2*M) := Nat.mul_le_mul_left _ (Nat.mul_le_mul hs hM)
        _ = _ := by ring
    exact (Nat.pow_le_pow_left (FourLayer.connectedTile_length_le _ H M hH1 hHM hvol) _).trans
      (BudgetSize.geometry_pow hbig hH hM30)

end
end TranslationTiling.FiniteCompiler.Effective
