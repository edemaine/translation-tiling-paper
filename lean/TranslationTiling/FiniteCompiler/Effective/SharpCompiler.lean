import TranslationTiling.FiniteCompiler.Effective.Correctness
import TranslationTiling.FiniteCompiler.Effective.SparseGeometry
import TranslationTiling.FiniteCompiler.TightBounds

namespace TranslationTiling.FiniteCompiler.Effective
open Compiler Compiler.Effective
open scoped Classical
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def sharpCyclic (d : InputData) : CyclicTileData :=
  let C := d.1.1+2
  freshStack (C^(6*C),rawOrder d.1,C^3,canonicalInputFamily d)

theorem sharpCyclic_computable : Computable sharpCyclic := by
  have hC : Primrec (fun d : InputData => d.1.1+2) := by fun_prop
  have hcap : Primrec (fun d : InputData => (d.1.1+2)^(6*(d.1.1+2))) := by fun_prop
  have hP : Primrec (fun d : InputData => (d.1.1+2)^3) := by fun_prop
  exact freshStack_computable.comp (hcap.to_comp.pair
    ((rawOrder_primrec.to_comp.comp Computable.fst).pair (hP.to_comp.pair canonicalInputFamily_computable)))

def sharpTile (d : InputData) : Tile 3 :=
  (Compiler.connectedTile (Compiler.integerTile (sharpCyclic d))).dedup

theorem sharpTile_computable : Computable sharpTile :=
  dedup_primrec.to_comp.comp (Compiler.connectedTile_computable.comp
    (Compiler.integerTile_computable.comp sharpCyclic_computable))

theorem sharpCyclic_facts (T : System) (p : Payload) (hp : PayloadCorrect T p)
    (hpos : ∀ n, 0≤T.slope n) (hS : ∀ n, (T.slope n).natAbs≤Sudoku.Width)
    (hB : T.alphabet=3) (hC : 12*Sudoku.Width+2 ≤ channelCount T) :
    0<(sharpCyclic (parameterData T,p)).1 ∧ (sharpCyclic (parameterData T,p)).2≠[] ∧
    (sharpCyclic (parameterData T,p)).1≤channelCount T^(34*channelCount T) ∧
    (∀ f ∈ (sharpCyclic (parameterData T,p)).2,
      f.1.1.natAbs≤rawHorizontal (parameterData T) ∧ f.1.2.natAbs≤rawHorizontal (parameterData T)) ∧
    ((∃ A : Set (Ambient (parameters T)), Solves (parameters T) A) ↔
      ∃ B : Set (Plane × ZMod (sharpCyclic (parameterData T,p)).1),
        Tiles (cyclicTileSet (sharpCyclic (parameterData T,p)).1 (sharpCyclic (parameterData T,p)).2) B) := by
  let C := channelCount T
  let Fs := canonicalInputFamily (parameterData T,p)
  have hbig : 596750≤C := by simpa [Sudoku.Width,Sudoku.q] using hC
  have hsmall : TightSize.TightPrimes (parameters T) := parameters_bounded_tight T hbig hB
  have hcount : Fs.length≤C^(6*C) := by
    rw [canonicalInputFamily_length T p hp hpos hS]
    exact TightSize.tight_testTiles_card_le (parameters T) hB hsmall hC hS
  have hlen : 0<Fs.length := by
    rw [canonicalInputFamily_length T p hp hpos hS]
    exact Finset.card_pos.mpr (testTiles_nonempty (parameters T))
  have hP : C^3≤(C^(6*C))^2 := by
    rw [← pow_mul]
    exact Nat.pow_le_pow_right (by omega) (by omega)
  have hpr := TightSize.cyclicOrder_primeBound (parameters T) hB hsmall hC
  have hraw : sharpCyclic (parameterData T,p) = freshStack (C^(6*C),(parameters T).cyclicOrder,C^3,Fs) := by
    unfold sharpCyclic
    rw [rawOrder_eq]
    rfl
  rw [hraw]
  obtain ⟨hm,hne,hcap,hiff⟩ := freshStack_facts _ _ _ Fs (parameters T).cyclicOrder_pos hlen hcount hP hpr
    (canonicalInputFamily_nonempty T p hp hpos hS)
  refine ⟨hm,hne,?_,?_,?_⟩
  · apply hcap.trans
    apply (Nat.mul_le_mul (TightSize.tight_cyclicOrder_le (parameters T) hB hsmall hC)
      (TightSize.freshCap_channel_le hC)).trans
    rw [← pow_add]
    have he : 21*C+13*C=34*C := by ring
    rw [he]
  · exact stackCodes_horizontal _ _ Fs _ (canonicalFamily_horizontal _ _ _)
  · exact (family_solution_iff (parameters T) Fs (canonicalInputFamily_correct T p hp hpos hS)).trans hiff

theorem sharpTile_facts (T : System) (p : Payload) (hp : PayloadCorrect T p)
    (hpos : ∀ n, 0≤T.slope n) (hS : ∀ n, (T.slope n).natAbs≤Sudoku.Width)
    (hB : T.alphabet=3) (hC : 12*Sudoku.Width+2 ≤ channelCount T) :
    sharpTile (parameterData T,p)≠[] ∧ FaceConnected (sharpTile (parameterData T,p)) ∧
    ((∃ A : Set (Ambient (parameters T)), Solves (parameters T) A) ↔
      TranslationTiling.Tiles (sharpTile (parameterData T,p))) ∧
    (sharpTile (parameterData T,p)).length≤channelCount T^(239*channelCount T) := by
  obtain ⟨hm,hne,hM,hxy,hiff⟩ := sharpCyclic_facts T p hp hpos hS hB hC
  dsimp only [sharpTile]
  generalize hd : sharpCyclic (parameterData T,p)=d at hm hne hM hxy hiff ⊢
  have hn := Compiler.integerTile_nonempty d hne
  have hc := Compiler.connectedTile_nonempty (Compiler.integerTile d) hn
  change (Compiler.connectedTile (Compiler.integerTile d)).dedup≠[] ∧ _
  refine ⟨(List.dedup_eq_nil _).not.mpr hc,?_,?_,?_⟩
  · simpa only [FaceConnected,List.mem_dedup] using Compiler.connectedTile_connected (Compiler.integerTile d)
  · have ht := hiff.trans ((Compiler.integerTile_correct MSS.rigidity d hm hne).trans
        (Compiler.connectedTile_correct Kim.cosetRigidity (Compiler.integerTile d)).symm)
    simpa only [TranslationTiling.Tiles,List.mem_dedup] using ht
  · have hg := Compiler.Size.integerTile_connected_sparseGeometryCap d
      (rawHorizontal (parameterData T)) (channelCount T^(34*channelCount T)) hm hM hne hxy
    have hb : Size.parameterBase T.alphabet Sudoku.Width (channelCount T) ≤ channelCount T ^ 73 := by
      rw [hB]
      exact MixedSize.mixed_parameterBase_le hC
    have hgeo := TightSize.sharp_geometry_bound hC hb (parameters_budget T Sudoku.Width hS).1.two
    have hout := hg.trans hgeo
    simpa only [Compiler.Size.cubeCount,List.card_toFinset] using hout

end
end TranslationTiling.FiniteCompiler.Effective
