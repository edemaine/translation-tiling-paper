import TranslationTiling.FiniteCompiler.Effective.SharedBatchDeck
import TranslationTiling.FiniteCompiler.Effective.SharedDeckDependence

namespace TranslationTiling.FiniteCompiler.Packed

open Compiler Compiler.Effective Effective SharedCoordinates
open scoped Classical BigOperators

noncomputable section

/-- A finite complement of a graph has exactly the mass of a base fibre.
The graph can be different for each individual test. -/
theorem sharedGraph_card (k : ℕ) (o : SharedOutput k)
    (F : Finset (SharedCoordinates.Ambient (sharedLayout k)))
    (h : FiniteCompiler.Tiles F (Set.range (SharedCoordinates.point (sharedLayout k) o))) :
    F.card = sharedMass (sharedRows k) := by
  let L := sharedLayout k
  let p := baseProjection L
  let f (v : F) : {w : SharedCoordinates.Ambient L // p w = 0} :=
    ⟨v.val + SharedCoordinates.point L o (-p v.val),by
      rw [map_add,baseProjection_point,add_neg_cancel]⟩
  have hc (w : SharedCoordinates.Ambient L) :
      ∃! x : SharedBase k, w - SharedCoordinates.point L o x ∈ F :=
    (tiles_range_iff_unique_base _ (SharedCoordinates.point_injective L o) _).mp h w
  have hf (v : F) : (f v).val - SharedCoordinates.point L o (-p v.val) = v.val :=
    add_sub_cancel_right _ _
  have hb : Function.Bijective f := by
    constructor
    · intro v w he
      obtain ⟨x,hx,hu⟩ := hc (f v).val
      have hv := hu (-p v.val) (by change (f v).val - SharedCoordinates.point L o (-p v.val) ∈ F; rw [hf]; exact v.property)
      have hw := hu (-p w.val) (by
        change (f v).val - SharedCoordinates.point L o (-p w.val) ∈ F
        rw [congrArg Subtype.val he,hf]
        exact w.property)
      apply Subtype.ext
      rw [← hf v, ← hf w, congrArg Subtype.val he,hv,hw]
    · intro w
      obtain ⟨x,hx,_⟩ := hc w.val
      let v : F := ⟨w.val - SharedCoordinates.point L o x,hx⟩
      have hp : -p v.val = x := by
        change -p (w.val - SharedCoordinates.point L o x) = x
        rw [map_sub,w.property,baseProjection_point,zero_sub,neg_neg]
      refine ⟨v,Subtype.ext ?_⟩
      change w.val - SharedCoordinates.point L o x + SharedCoordinates.point L o (-p v.val) = w.val
      rw [hp,sub_add_cancel]
  have hmass : Fintype.card (Fixed ×
      (∀ i, ZMod (L.firstSize i) × ZMod (L.secondSize i)) × (∀ i, SharedCoordinates.Low L i)) =
      sharedMass (sharedRows k) := by
    simp only [Fintype.card_prod,Fintype.card_pi,ZMod.card,Fixed,SharedCoordinates.Low,sharedMass]
    rw [← Finset.prod_mul_distrib,← Fin.prod_ofFn]
    congr 1
    apply congrArg List.prod
    apply List.ext_getElem
    · simp
    · intro i hi hi'
      simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn,L,sharedLayout]
      ac_rfl
  have hcard := Fintype.card_congr ((Equiv.ofBijective f hb).trans (baseFibreEquiv L 0))
  rwa [Fintype.card_coe,hmass] at hcard

theorem sharedRaw_mass_of_tiles (k : ℕ) (F : CyclicTile)
    (h : ∃ o : SharedOutput k, FiniteCompiler.Tiles (F.toFinset.image (decodePoint (sharedLayout k)))
      (Set.range (SharedCoordinates.point (sharedLayout k) o))) :
    F ≠ [] ∧ (cyclicTileSet (sharedOrder (sharedRows k)) F).card =
      sharedMass (sharedRows k) := by
  obtain ⟨o,ho⟩ := h
  refine ⟨fun hn => ?_,?_⟩
  · have h := (tiles_range_iff_unique_base _ (SharedCoordinates.point_injective (sharedLayout k) o) _).mp ho 0
    obtain ⟨x,hx,_⟩ := h
    simp [hn] at hx
  · have he := sharedGraph_card k o _ ho
    rw [← cyclicTileSet_image (sharedLayout k) (sharedLayoutCRT k),Finset.card_image_of_injective] at he
    · exact (congrArg (fun m : ℕ => (cyclicTileSet m F).card) (sharedLayout_order k)).symm.trans he
    · exact (cyclicAmbientEquiv (sharedLayout k) (sharedLayoutCRT k)).injective

end
end TranslationTiling.FiniteCompiler.Packed
