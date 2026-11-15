import TranslationTiling.FiniteCompiler.Effective.Correctness
import TranslationTiling.FiniteCompiler.Effective.SparseGeometry
import TranslationTiling.FiniteCompiler.TightBounds
import TranslationTiling.FiniteCompiler.EconomicalBounds
import TranslationTiling.FourLayer.MSSBound
import TranslationTiling.FourLayer.SizeBound

namespace TranslationTiling.FiniteCompiler.Effective
open Compiler Compiler.Effective
open scoped Classical
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def sharpCyclic (d : InputData) : CyclicTileData :=
  let C := d.1.1+2
  freshStack (C^(8*C),rawOrder d.1,C^4,canonicalInputFamily d)

theorem sharpCyclic_computable : Computable sharpCyclic := by
  have hC : Primrec (fun d : InputData => d.1.1+2) := by fun_prop
  have hcap : Primrec (fun d : InputData => (d.1.1+2)^(8*(d.1.1+2))) := by fun_prop
  have hP : Primrec (fun d : InputData => (d.1.1+2)^4) := by fun_prop
  exact freshStack_computable.comp (hcap.to_comp.pair
    ((rawOrder_primrec.to_comp.comp Computable.fst).pair (hP.to_comp.pair canonicalInputFamily_computable)))

def sharpTile (d : InputData) : Tile 3 :=
  FourLayer.connectedTile (Compiler.integerTile (sharpCyclic d)) (rawHorizontal d.1)
    ((d.1.1+2)^(44*(d.1.1+2)))

theorem sharpTile_computable : Computable sharpTile := by
  have hE := Compiler.integerTile_computable.comp sharpCyclic_computable
  have hH : Primrec (fun d : InputData => rawHorizontal d.1) := by fun_prop
  have hM : Primrec (fun d : InputData => (d.1.1+2)^(44*(d.1.1+2))) := by fun_prop
  have h := FourLayer.connectedTile_computable.comp (hE.pair (hH.to_comp.pair hM.to_comp))
  dsimp only at h
  unfold sharpTile
  exact h

theorem sharpCyclic_facts (T : System) (p : Payload) (hp : PayloadCorrect T p)
    (hpos : ∀ n, 0≤T.slope n) (hS : ∀ n, (T.slope n).natAbs≤Sudoku.Width)
    (hB : T.alphabet=3) (hC : 8*Sudoku.Width+2 ≤ channelCount T) :
    0<(sharpCyclic (parameterData T,p)).1 ∧ (sharpCyclic (parameterData T,p)).2≠[] ∧
    (sharpCyclic (parameterData T,p)).1≤channelCount T^(44*channelCount T) ∧
    (∀ f ∈ (sharpCyclic (parameterData T,p)).2,
      f.1.1.natAbs≤rawHorizontal (parameterData T) ∧ f.1.2.natAbs≤rawHorizontal (parameterData T)) ∧
    ((∃ A : Set (Ambient (parameters T)), Solves (parameters T) A) ↔
      ∃ B : Set (Plane × ZMod (sharpCyclic (parameterData T,p)).1),
        Tiles (cyclicTileSet (sharpCyclic (parameterData T,p)).1 (sharpCyclic (parameterData T,p)).2) B) := by
  let C := channelCount T
  let Fs := canonicalInputFamily (parameterData T,p)
  have hbig : 962≤C := by simpa [Sudoku.Width,Sudoku.q] using hC
  have hsmall : EconomicalPrimes (parameters T) := parameters_bounded_economical T hbig hB
  have hcount : Fs.length≤C^(8*C) := by
    rw [canonicalInputFamily_length T p hp hpos hS]
    exact EconomicalSize.testTiles_card_le (parameters T) hB hsmall hC hS
  have hlen : 0<Fs.length := by
    rw [canonicalInputFamily_length T p hp hpos hS]
    exact Finset.card_pos.mpr (testTiles_nonempty (parameters T))
  have hP : C^4≤(C^(8*C))^2 := by
    rw [← pow_mul]
    exact Nat.pow_le_pow_right (by omega) (by omega)
  have hpr := EconomicalSize.cyclicOrder_primeBound (parameters T) hB hsmall hC
  have hraw : sharpCyclic (parameterData T,p) = freshStack (C^(8*C),(parameters T).cyclicOrder,C^4,Fs) := by
    unfold sharpCyclic
    rw [rawOrder_eq]
    rfl
  rw [hraw]
  obtain ⟨hm,hne,hcap,hiff⟩ := freshStack_facts _ _ _ Fs (parameters T).cyclicOrder_pos hlen hcount hP hpr
    (canonicalInputFamily_nonempty T p hp hpos hS)
  refine ⟨hm,hne,?_,?_,?_⟩
  · apply hcap.trans
    apply (Nat.mul_le_mul (EconomicalSize.cyclicOrder_le (parameters T) hB hsmall hC)
      (EconomicalSize.freshCap_channel_le hC)).trans
    rw [← pow_add]
    have he : 27*C+17*C=44*C := by ring
    rw [he]
  · exact stackCodes_horizontal _ _ Fs _ (canonicalFamily_horizontal _ _ _)
  · exact (family_solution_iff (parameters T) Fs (canonicalInputFamily_correct T p hp hpos hS)).trans hiff

theorem sharpTile_facts (T : System) (p : Payload) (hp : PayloadCorrect T p)
    (hpos : ∀ n, 0≤T.slope n) (hS : ∀ n, (T.slope n).natAbs≤Sudoku.Width)
    (hB : T.alphabet=3) (hC : 8*Sudoku.Width+2 ≤ channelCount T) :
    sharpTile (parameterData T,p)≠[] ∧ FaceConnected (sharpTile (parameterData T,p)) ∧
    ((∃ A : Set (Ambient (parameters T)), Solves (parameters T) A) ↔
      TranslationTiling.Tiles (sharpTile (parameterData T,p))) ∧
    (sharpTile (parameterData T,p)).length≤channelCount T^(143*channelCount T) := by
  obtain ⟨hm,hne,hM,hxy,hiff⟩ := sharpCyclic_facts T p hp hpos hS hB hC
  dsimp only [sharpTile]
  generalize hd : sharpCyclic (parameterData T,p)=d at hm hne hM hxy hiff ⊢
  let H := rawHorizontal (parameterData T)
  let C := channelCount T
  let M := C^(44*C)
  have hn := Compiler.integerTile_nonempty d hne
  have hrect := Compiler.Size.integerTile_rectangle_bound d H M hm hM hne hxy
  change FourLayer.connectedTile (Compiler.integerTile d) H M≠[] ∧ _
  refine ⟨FourLayer.connectedTile_nonempty _ H M hn,
    FourLayer.connectedTile_connected _ H M hrect,?_,?_⟩
  · exact hiff.trans ((Compiler.integerTile_correct MSS.rigidity d hm hne).trans
      (FourLayer.connectedTile_correct (Compiler.integerTile d) H M).symm)
  · have hbig : 962≤C := by simpa [C,Sudoku.Width,Sudoku.q] using hC
    have heq : rawBudget (parameterData T)=C^12 := by
      unfold rawBudget
      rw [if_pos ⟨hbig,hB⟩]
      rfl
    have hb2 := (parameters_rawBudget T hS).1.two
    have hH : H≤C^2532 := by
      change Size.horizontalCap (rawBudget (parameterData T))≤_
      apply (Size.horizontalCap_degree_211 _ hb2).trans
      rw [heq,← pow_mul]
    have hH1 : 1≤H := by
      exact ((by omega : 1≤C).trans (parameters_rawBudget T hS).2.1).trans (Size.le_horizontalCap _)
    have hHM : H≤M := hH.trans (Nat.pow_le_pow_right (by omega) (by omega))
    have hs : (2*H+1)^2≤9*H^2 := by nlinarith
    have hvol : Compiler.Size.cubeCount (Compiler.integerTile d)≤9*2^24*H^2*M := by
      calc
        _ ≤ 2^24*((2*H+1)^2*d.1) := Compiler.Size.integerTile_cubeCount_sparse d H hm hxy
        _ ≤ 2^24*(9*H^2*M) := Nat.mul_le_mul_left _ (Nat.mul_le_mul hs hM)
        _ = _ := by ring
    exact (FourLayer.connectedTile_length_le _ H M hH1 hHM hvol).trans
      (EconomicalSize.compact_geometry_bound hbig hH)

end
end TranslationTiling.FiniteCompiler.Effective
