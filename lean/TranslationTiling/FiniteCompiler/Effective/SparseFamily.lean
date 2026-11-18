import TranslationTiling.FiniteCompiler.Effective.SparseSeedFamily
import TranslationTiling.FiniteCompiler.Effective.FamilyCompiler

namespace TranslationTiling.FiniteCompiler.Effective
open Compiler Compiler.Effective
open scoped Classical
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

theorem sparseSystem_nonnegative (T : LeanWang.TileSet) : ∀ n, 0≤(SparseTernary.system T).slope n := by
  intro n
  change 0≤SparseTernary.slope T.length n
  unfold SparseTernary.slope
  split_ifs <;> positivity

def rawSparseFamily (T : LeanWang.TileSet) : List CyclicTile :=
  rawFamily (sparseInput T) ++ sparseRawSeedFamily T

theorem rawSparseFamily_computable : Computable rawSparseFamily := by
  have hraw : Computable (fun T => rawFamily (sparseInput T)) :=
    rawFamily_primrec.to_comp.comp sparseInput_computable
  have ha : Primrec (fun z : List CyclicTile × List CyclicTile => z.1++z.2) := by fun_prop
  have h := ha.to_comp.comp (hraw.pair sparseRawSeedFamily_computable)
  exact h.of_eq (fun T => rfl)

def sparseFamily (T : LeanWang.TileSet) : List CyclicTile :=
  canonicalFamily (rawHorizontal (parameterData (SparseTernary.system T)))
    (rawOrder (parameterData (SparseTernary.system T))) (rawSparseFamily T)

theorem sparseFamily_computable : Computable sparseFamily := by
  have h := canonicalFamily_primrec.to_comp.comp
    (((rawHorizontal_primrec.to_comp.comp sparseParameterData_computable).pair
      (rawOrder_primrec.to_comp.comp sparseParameterData_computable)).pair rawSparseFamily_computable)
  exact h.of_eq (fun T => rfl)

theorem rawSparseFamily_correct (T : LeanWang.TileSet) :
    decodedFamily (parameters (SparseTernary.system T)) (rawSparseFamily T) =
      SparseTernary.testFamily (parameters (SparseTernary.system T)) := by
  rw [rawSparseFamily,decodedFamily_append,sparseRawSeedFamily_correct]
  rw [show sparseInput T=(parameterData (SparseTernary.system T),sparsePayload T) from rfl,
    rawFamily_correct _ _ (sparsePayload_correct T) (sparseSystem_nonnegative T)]
  rfl

theorem rawSparseFamily_horizontal (T : LeanWang.TileSet) :
    ∀ F∈rawSparseFamily T, ∀ f∈F,
      f.1.1.natAbs≤rawHorizontal (parameterData (SparseTernary.system T)) ∧
      f.1.2.natAbs≤rawHorizontal (parameterData (SparseTernary.system T)) := by
  intro F hF f hf
  have hm : F.toFinset.image (decodeNumericalPoint (parameters (SparseTernary.system T))) ∈
      SparseTernary.testFamily (parameters (SparseTernary.system T)) := by
    rw [←rawSparseFamily_correct]
    exact (mem_decodedFamily _ _ _).mpr ⟨F,hF,rfl⟩
  exact SparseTernary.test_horizontal_coarse _ (parameters_rawBudget _ (SparseTernary.slope_bound T)).1 hm
    (Finset.mem_image.mpr ⟨f,List.mem_toFinset.mpr hf,rfl⟩)

theorem sparseFamily_correct (T : LeanWang.TileSet) :
    decodedFamily (parameters (SparseTernary.system T)) (sparseFamily T) =
      SparseTernary.testFamily (parameters (SparseTernary.system T)) := by
  unfold sparseFamily
  rw [rawOrder_eq,canonicalDecoded_correct _ _ _ (rawSparseFamily_horizontal T),rawSparseFamily_correct]

theorem sparseFamily_length (T : LeanWang.TileSet) :
    (sparseFamily T).length = (SparseTernary.testFamily (parameters (SparseTernary.system T))).card := by
  rw [←sparseFamily_correct,decodedFamily_card]
  unfold sparseFamily
  rw [rawOrder_eq]
  exact canonicalFamily_length _ _ _

theorem sparseFamily_budget (T : LeanWang.TileSet) (hn : 0<T.length) :
    FamilyBudget (SparseTernary.system T) (sparseFamily T) := by
  have hm (F : CyclicTile) (hF : F∈sparseFamily T) :
      F.toFinset.image (decodeNumericalPoint (parameters (SparseTernary.system T))) ∈
      SparseTernary.testFamily (parameters (SparseTernary.system T)) := by
    rw [←sparseFamily_correct]
    exact (mem_decodedFamily _ _ _).mpr ⟨F,hF,rfl⟩
  refine ⟨?_,?_,?_,?_,?_⟩
  · rw [sparseFamily_length]
    apply Finset.card_pos.mpr
    exact ⟨_,Finset.mem_union_left _ (kernelTile_mem_testTiles _)⟩
  · rw [sparseFamily_length]
    exact SparseTernary.testFamily_card _
  · intro F hF he
    have hh := SparseTernary.nonempty_of_mem_testFamily _ (hm F hF)
    rw [he] at hh
    exact Finset.not_nonempty_empty (by simpa only [List.toFinset_nil,Finset.image_empty] using hh)
  · exact canonicalFamily_horizontal _ _ _
  · intro F hF
    have hh := SparseTernary.test_card _ (hm F hF)
    rw [decodedTile_eq_image,Finset.card_image_of_injective _ (ambientCyclicEquiv (parameters (SparseTernary.system T))).symm.injective] at hh
    exact hh

theorem sparse_family_solution_iff (T : LeanWang.TileSet) :
    (∃ A : Set (Ambient (parameters (SparseTernary.system T))),
      SparseTernary.Solves (parameters (SparseTernary.system T)) A) ↔
      ∃ B : Set (Plane × ZMod (parameters (SparseTernary.system T)).cyclicOrder),
        ∀ i : Fin (sparseFamily T).length,
          Tiles (cyclicTileSet (parameters (SparseTernary.system T)).cyclicOrder ((sparseFamily T).getD i.val [])) B := by
  let E := parameters (SparseTernary.system T)
  let Fs := sparseFamily T
  have he := sparseFamily_correct T
  constructor
  · rintro ⟨A,hA⟩
    refine ⟨ambientCyclicEquiv E '' A,fun i => ?_⟩
    have hm : (Fs.getD i.val []).toFinset.image (decodeNumericalPoint E) ∈
        SparseTernary.testFamily E := by
      rw [←he]
      exact (mem_decodedFamily _ _ _).mpr ⟨_,getD_mem_of_lt Fs i.val [] i.isLt,rfl⟩
    have h := covers_image (ambientCyclicEquiv E) _ A (hA _ hm)
    rwa [decodedTile_image] at h
  · rintro ⟨B,hB⟩
    refine ⟨(ambientCyclicEquiv E).symm '' B,fun F hF => ?_⟩
    rw [←he,mem_decodedFamily] at hF
    obtain ⟨xs,hxs,rfl⟩ := hF
    obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp hxs
    have hi' : Fs.getD i []=Fs[i] := by
      rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi,Option.getD_some]
    have h := covers_image (ambientCyclicEquiv E).symm _ B (hB ⟨i,hi⟩)
    rw [hi',←decodedTile_eq_image] at h
    exact h

end
end TranslationTiling.FiniteCompiler.Effective
