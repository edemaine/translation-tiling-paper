import TranslationTiling.FiniteCompiler.Effective.CanonicalCorrect
import TranslationTiling.FiniteCompiler.Effective.StackSupport
import TranslationTiling.FiniteCompiler.Effective.BitInputCorrect
import TranslationTiling.FiniteCompiler.Effective.ConcreteGeometryBound

namespace TranslationTiling.FiniteCompiler.Effective
open Compiler Compiler.Effective
open scoped Classical
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 500000

theorem decodedTile_image {T : System} (E : EncodingParameters T) (F : CyclicTile) :
    (F.toFinset.image (decodeNumericalPoint E)).image (ambientCyclicEquiv E) =
      cyclicTileSet E.cyclicOrder F := by
  rw [decodedTile_eq_image,Finset.image_image]
  simp only [AddEquiv.apply_symm_apply,Function.comp_def,Finset.image_id']

theorem family_solution_iff {T : System} (E : EncodingParameters T) (Fs : List CyclicTile)
    (he : decodedFamily E Fs = testTiles E) :
    (∃ A : Set (Ambient E), Solves E A) ↔
      ∃ B : Set (Plane × ZMod E.cyclicOrder),
        ∀ i : Fin Fs.length, Tiles (cyclicTileSet E.cyclicOrder (Fs.getD i.val [])) B := by
  constructor
  · rintro ⟨A,hA⟩
    refine ⟨ambientCyclicEquiv E '' A,fun i => ?_⟩
    have hm : (Fs.getD i.val []).toFinset.image (decodeNumericalPoint E) ∈ testTiles E := by
      rw [← he]
      exact (mem_decodedFamily _ _ _).mpr ⟨_,getD_mem_of_lt Fs i.val [] i.isLt,rfl⟩
    have h := covers_image (ambientCyclicEquiv E) _ A (hA _ hm)
    rwa [decodedTile_image] at h
  · rintro ⟨B,hB⟩
    refine ⟨(ambientCyclicEquiv E).symm '' B,fun F hF => ?_⟩
    rw [← he,mem_decodedFamily] at hF
    obtain ⟨xs,hxs,rfl⟩ := hF
    obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp hxs
    have hi' : Fs.getD i [] = Fs[i] := by
      rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi,Option.getD_some]
    have h := covers_image (ambientCyclicEquiv E).symm _ B (hB ⟨i,hi⟩)
    rw [hi',← decodedTile_eq_image] at h
    exact h

theorem canonicalInputFamily_nonempty (T : System) (p : Payload) (hp : PayloadCorrect T p)
    (hpos : ∀ n, 0 ≤ T.slope n) (hS : ∀ n, (T.slope n).natAbs ≤ Sudoku.Width) :
    ∀ F ∈ canonicalInputFamily (parameterData T,p), F ≠ [] := by
  intro F hF he
  have hm : F.toFinset.image (decodeNumericalPoint (parameters T)) ∈ testTiles (parameters T) := by
    rw [← canonicalInputFamily_correct T p hp hpos hS]
    exact (mem_decodedFamily _ _ _).mpr ⟨F,hF,rfl⟩
  have hn := nonempty_of_mem_testTiles (parameters T) hm
  simp only [he,List.toFinset_nil,Finset.image_empty,Finset.not_nonempty_empty] at hn

/-- All hypotheses required by the bounded numerical stacking compiler. -/
theorem optimizedCyclic_facts (T : System) (p : Payload) (hp : PayloadCorrect T p)
    (hpos : ∀ n, 0 ≤ T.slope n) (hS : ∀ n, (T.slope n).natAbs ≤ Sudoku.Width) :
    0 < (optimizedCyclic (parameterData T,p)).1 ∧
    (optimizedCyclic (parameterData T,p)).2 ≠ [] ∧
    (optimizedCyclic (parameterData T,p)).1 ≤ Size.stackPolynomial (rawCountCap (parameterData T)) ∧
    (∀ f ∈ (optimizedCyclic (parameterData T,p)).2,
      f.1.1.natAbs ≤ rawHorizontal (parameterData T) ∧
      f.1.2.natAbs ≤ rawHorizontal (parameterData T)) ∧
    ((∃ A : Set (Ambient (parameters T)), Solves (parameters T) A) ↔
      ∃ B : Set (Plane × ZMod (optimizedCyclic (parameterData T,p)).1),
        Tiles (cyclicTileSet (optimizedCyclic (parameterData T,p)).1
          (optimizedCyclic (parameterData T,p)).2) B) := by
  let Fs := canonicalInputFamily (parameterData T,p)
  let X := rawCountCap (parameterData T)
  let N := (parameters T).cyclicOrder
  have hlen : 0 < Fs.length := by
    rw [canonicalInputFamily_length T p hp hpos hS]
    exact Finset.card_pos.mpr (testTiles_nonempty (parameters T))
  obtain ⟨hb,hC,hL⟩ := parameters_budget T Sudoku.Width hS
  have hcount : Fs.length ≤ X := by
    rw [canonicalInputFamily_length T p hp hpos hS]
    exact Size.testTiles_card_le_commonCap hb hC hL
  have hNX : N ≤ X := Size.cyclicOrder_le_commonCap hb
  have hN : 0 < N := (parameters T).cyclicOrder_pos
  have hraw : optimizedCyclic (parameterData T,p) = boundedStack (X,N,Fs) := by
    unfold optimizedCyclic
    rw [rawOrder_eq]
  rw [hraw]
  refine ⟨boundedStack_pos X N hN Fs hlen hcount hNX,?_,
    boundedStack_modulus_bound X N Fs hlen hcount hNX,?_,?_⟩
  · dsimp only [boundedStack]
    exact stackCodes_nonempty N (boundedPartition (Fs.length-1,N,X)) Fs hlen
      (boundedPartition_spec (Fs.length-1) N X (by omega) hNX).1
      (canonicalInputFamily_nonempty T p hp hpos hS)
  · dsimp only [boundedStack]
    exact stackCodes_horizontal N (boundedPartition (Fs.length-1,N,X)) Fs _
      (canonicalFamily_horizontal _ _ _)
  · exact (family_solution_iff (parameters T) Fs
      (canonicalInputFamily_correct T p hp hpos hS)).trans
      (boundedStack_correct X N hN Fs hlen hcount hNX)

end
end TranslationTiling.FiniteCompiler.Effective
