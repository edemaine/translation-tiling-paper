import TranslationTiling.FiniteCompiler.Effective.FourValueDependence

namespace TranslationTiling.FiniteCompiler.Packed

open Compiler Compiler.Effective Effective SharedCoordinates
open scoped Classical BigOperators

noncomputable section

/-- A finite complement of a graph has exactly the mass of a base fibre.
The graph can be different for each individual test. -/
theorem fourValueGraph_card (k : ℕ) (o : FourValueOutputGraph k)
    (F : Finset (SharedCoordinates.Ambient (fourValueLayout k)))
    (h : FiniteCompiler.Tiles F (Set.range (SharedCoordinates.point (fourValueLayout k) o))) :
    F.card = sharedMass (fourValueRows k) := by
  let L := fourValueLayout k
  let p := baseProjection L
  let f (v : F) : {w : SharedCoordinates.Ambient L // p w = 0} :=
    ⟨v.val + SharedCoordinates.point L o (-p v.val),by
      rw [map_add,baseProjection_point,add_neg_cancel]⟩
  have hc (w : SharedCoordinates.Ambient L) :
      ∃! x : FourValueBase k, w - SharedCoordinates.point L o x ∈ F :=
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
      sharedMass (fourValueRows k) := by
    simp only [Fintype.card_prod,Fintype.card_pi,ZMod.card,Fixed,SharedCoordinates.Low,sharedMass]
    rw [← Finset.prod_mul_distrib,← Fin.prod_ofFn]
    congr 1
    apply congrArg List.prod
    apply List.ext_getElem
    · simp
    · intro i hi hi'
      simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn,L,fourValueLayout]
      ac_rfl
  have hcard := Fintype.card_congr ((Equiv.ofBijective f hb).trans (baseFibreEquiv L 0))
  rwa [Fintype.card_coe,hmass] at hcard

theorem fourValueRaw_mass_of_tiles (k : ℕ) (F : CyclicTile)
    (h : ∃ o : FourValueOutputGraph k, FiniteCompiler.Tiles (F.toFinset.image (decodePoint (fourValueLayout k)))
      (Set.range (SharedCoordinates.point (fourValueLayout k) o))) :
    F ≠ [] ∧ (cyclicTileSet (sharedOrder (fourValueRows k)) F).card =
      sharedMass (fourValueRows k) := by
  obtain ⟨o,ho⟩ := h
  refine ⟨fun hn => ?_,?_⟩
  · have h := (tiles_range_iff_unique_base _ (SharedCoordinates.point_injective (fourValueLayout k) o) _).mp ho 0
    obtain ⟨x,hx,_⟩ := h
    simp [hn] at hx
  · have he := fourValueGraph_card k o _ ho
    rw [← cyclicTileSet_image (fourValueLayout k) (fourValueLayoutCRT k),Finset.card_image_of_injective] at he
    · exact (congrArg (fun m : ℕ => (cyclicTileSet m F).card) (fourValueLayout_order k)).symm.trans he
    · exact (cyclicAmbientEquiv (fourValueLayout k) (fourValueLayoutCRT k)).injective

private theorem member_dvd_product {p : ℕ} {l : List ℕ} (hp : p ∈ l) : p ∣ l.prod := by
  induction l with
  | nil => simp at hp
  | cons a l ih =>
    rw [List.prod_cons]
    rcases List.mem_cons.mp hp with rfl|h
    · exact dvd_mul_right _ _
    · exact dvd_mul_of_dvd_right (ih h) a

/-- The kernel contains the full vertical lattice of the shared deck. -/
theorem fourValueKernel_column (k : ℕ) (t : ℤ) :
    let R := (guardedModuli (fourValueRows k)).prod
    let N := sharedOrder (fourValueRows k)
    (((0 : Plane),((R : ℤ)*t : ℤ)) : Plane × ZMod N) ∈
      cyclicTileSet N (kernelCodes N (guardedModuli (fourValueRows k))) := by
  let R := (guardedModuli (fourValueRows k)).prod
  let N := sharedOrder (fourValueRows k)
  let z : ZMod N := ((R : ℤ)*t : ℤ)
  have hRN : R ∣ N := ⟨sharedMass (fourValueRows k),(shared_input_mul_mass (fourValueRows k)).symm⟩
  letI : NeZero N := ⟨by unfold N; rw [← fourValueLayout_order]; exact (fourValueOrder_pos k).ne'⟩
  change ((0:Plane),z) ∈ cyclicTileSet N (kernelCodes N (guardedModuli (fourValueRows k)))
  apply Finset.mem_image.mpr
  refine ⟨((0,0),z.val),List.mem_toFinset.mpr ?_,Prod.ext rfl (ZMod.natCast_zmod_val z)⟩
  unfold kernelCodes
  apply List.mem_map.mpr
  refine ⟨z.val,List.mem_filter.mpr ⟨List.mem_range.mpr (ZMod.val_lt z),decide_eq_true ?_⟩,rfl⟩
  intro r hr
  have hrR : r ∣ R := member_dvd_product hr
  let f := ZMod.castHom (hrR.trans hRN) (ZMod r)
  have hn : (z.val : ZMod r) = f z := by
    rw [← map_natCast f,ZMod.natCast_zmod_val]
  have hf : f z = 0 := by
    change f (((R : ℤ)*t : ℤ) : ZMod N) = 0
    rw [map_intCast,Int.cast_mul,Int.cast_natCast,(ZMod.natCast_eq_zero_iff _ _).mpr hrR,zero_mul]
  exact Nat.dvd_iff_mod_eq_zero.mp ((ZMod.natCast_eq_zero_iff _ _).mp (hn.trans hf))


end
end TranslationTiling.FiniteCompiler.Packed
