import TranslationTiling.Compiler.EffectiveConstraintFamilies
import TranslationTiling.Compiler.EffectiveDependence
import TranslationTiling.Compiler.EffectiveActivationFamily
import TranslationTiling.Compiler.EffectiveStacking
import TranslationTiling.Compiler.Completeness

set_option maxRecDepth 1000
set_option maxHeartbeats 100000

namespace TranslationTiling.Compiler.Effective

open scoped Classical

/-- The complete finite system, with the kernel gadget first. -/
noncomputable def family (T : LeanWang.TileSet) : List (List NumericalPoint) :=
  kernelCompiler T :: (dependenceFamily T ++ wordFamily T ++ seedConstraintFamily T ++
    ordinaryFamily T ++ seedFamily T)

theorem family_computable : Computable family := by
  exact Computable.list_cons.comp kernelCompiler_computable
    (Computable.list_append.comp
      (Computable.list_append.comp
        (Computable.list_append.comp
          (Computable.list_append.comp dependenceFamily_computable wordFamily_computable)
          seedConstraintFamily_computable) ordinaryFamily_computable) seedFamily_computable)

theorem family_length_pos (T : LeanWang.TileSet) : 0 < (family T).length := by
  unfold family
  simp only [List.length_cons]
  omega

theorem kernelCompiler_nonempty (T : LeanWang.TileSet) : kernelCompiler T ≠ [] := by
  obtain ⟨g, hg⟩ := kernelTile_nonempty (parameters T)
  rw [← kernelCompiler_correct T] at hg
  intro he
  simp only [he, List.toFinset_nil, Finset.image_empty] at hg
  exact Finset.notMem_empty g hg

theorem family_correct (T : LeanWang.TileSet) :
    ((family T).map (fun xs => xs.toFinset.image
      (decodeNumericalPoint (parameters T)))).toFinset = testTiles (parameters T) := by
  unfold family
  simp only [List.map_cons, List.map_append, List.toFinset_cons, List.toFinset_append,
    kernelCompiler_correct, dependenceFamily_correct, wordFamily_correct,
    seedConstraintFamily_correct, ordinaryFamily_correct, seedFamily_correct]
  simp only [testTiles, Finset.singleton_union, Finset.union_assoc, Finset.insert_union]

theorem solves_family_iff (T : LeanWang.TileSet) (A : Set (Ambient (parameters T))) :
    Solves (parameters T) A ↔ ∀ xs ∈ family T,
      Tiles (xs.toFinset.image (decodeNumericalPoint (parameters T))) A := by
  unfold Solves
  rw [← family_correct T]
  simp only [List.mem_toFinset, List.forall_mem_map]

theorem forall_list_getD {α : Type*} (xs : List α) (d : α) (P : α → Prop) :
    (∀ x ∈ xs, P x) ↔ ∀ i : Fin xs.length, P (xs.getD i.val d) := by
  rw [List.forall_mem_iff_get]
  apply forall_congr'
  intro i
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem i.isLt,
    Option.getD_some, List.get_eq_getElem]

noncomputable def ambientCyclicEquiv {T : LeanWang.TileSet} (E : EncodingParameters T) :
    (Plane × ZMod E.cyclicOrder) ≃+ Ambient E :=
  AddEquiv.prodCongr (AddEquiv.refl Plane) (cyclicToFiniteFactor E)

theorem decodeCyclicPoint {T : LeanWang.TileSet} (E : EncodingParameters T)
    (f : NumericalPoint) : ambientCyclicEquiv E (cyclicPoint E.cyclicOrder f) =
      decodeNumericalPoint E f := by
  exact Prod.ext (by rfl) (numericalFactor_eq E f.2).symm

theorem decodeCyclicTile {T : LeanWang.TileSet} (E : EncodingParameters T)
    (xs : List NumericalPoint) :
    (cyclicTileSet E.cyclicOrder xs).image (ambientCyclicEquiv E) =
      xs.toFinset.image (decodeNumericalPoint E) := by
  rw [cyclicTileSet, Finset.image_image]
  apply Finset.image_congr
  intro f _
  exact decodeCyclicPoint E f

theorem family_tiling_iff (sound : Sudoku.Soundness) (T : LeanWang.TileSet) :
    LeanWang.TilesPlane T ↔ ∃ A : Set (Plane × ZMod (numericalOrder T)),
      ∀ i : Fin (family T).length, Tiles (cyclicTileSet (numericalOrder T)
        ((family T).getD i.val [])) A := by
  rw [finite_system_iff_wang sound (parameters T), numericalOrder_eq T]
  let E := parameters T
  let e := ambientCyclicEquiv E
  constructor
  · rintro ⟨A, hA⟩
    refine ⟨e.symm '' A, ?_⟩
    apply (forall_list_getD (family T) [] (fun xs =>
      Tiles (cyclicTileSet E.cyclicOrder xs) (e.symm '' A))).mp
    intro xs hxs
    have hs := (solves_family_iff T A).mp hA xs hxs
    have h := covers_image e.symm _ A hs
    rw [← decodeCyclicTile E xs, Finset.image_image] at h
    simpa only [e, Function.comp_def, AddEquiv.symm_apply_apply, Finset.image_id'] using h
  · rintro ⟨A, hA⟩
    refine ⟨e '' A, (solves_family_iff T _).mpr ?_⟩
    have hall := (forall_list_getD (family T) [] (fun xs =>
      Tiles (cyclicTileSet E.cyclicOrder xs) A)).mpr hA
    intro xs hxs
    have h := covers_image e _ A (hall xs hxs)
    rwa [decodeCyclicTile E xs] at h

end TranslationTiling.Compiler.Effective
