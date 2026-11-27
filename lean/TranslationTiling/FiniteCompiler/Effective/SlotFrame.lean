import TranslationTiling.FiniteCompiler.Effective.SlotFinite
import TranslationTiling.FiniteCompiler.Effective.SlotInvariance
import TranslationTiling.FiniteCompiler.Effective.FourValueDeckCorrect
import TranslationTiling.FiniteCompiler.Effective.FourValueStrip

namespace TranslationTiling.FiniteCompiler.Packed.SlotParameters

open Compiler Compiler.Effective Effective SharedCoordinates
open scoped Classical
noncomputable section

variable {k m : ℕ} (s : SlotParameters k m)

def arithmeticTiles : List (Finset (SharedCoordinates.Ambient s.layout)) :=
  arithmeticBaseline.map fun F => s.oldTileLift (F.toFinset.image (decodePoint (fourValueLayout 0)))

def anchorTests : List (Finset (SharedCoordinates.Ambient s.layout)) :=
  (Finset.univ : Finset (FourValueRow 0 × AddedRow k m)).toList.map fun (i,j) =>
    productInvariance s.layout (privateUseful s.layout (.inl i)) (lowStep s.layout (.inr j))

variable (o : SharedCoordinates.Outputs s.layout)
local notation "Holds" => fun F => Tiles F (Set.range (SharedCoordinates.point s.layout o))

private theorem tiles_map_translate_iff {G : Type*} [AddCommGroup G]
    (A : Finset G) (B : Set G) (d : G) :
    Tiles (A.map (Equiv.addRight d).toEmbedding) B ↔ Tiles A B := by
  let e := Equiv.addRight d
  let E := (A.equivMap e.toEmbedding).prodCongr (Equiv.refl B)
  change Function.Bijective (fun p : ↥(A.map e.toEmbedding) × B => p.1.val + p.2.val) ↔
    Function.Bijective (fun p : ↥A × B => p.1.val + p.2.val)
  have hm : (fun p : ↥(A.map e.toEmbedding) × B => p.1.val + p.2.val) ∘ E =
      e ∘ (fun p : ↥A × B => p.1.val + p.2.val) := by
    funext p
    change p.1.val + d + p.2.val = p.1.val + p.2.val + d
    exact add_right_comm _ _ _
  exact (Function.Bijective.of_comp_iff _ E.bijective).symm.trans
    (hm.symm ▸ e.bijective.of_comp_iff' _)

theorem fourValueHolds_shift (d : Plane) (F : CyclicTile) (a : FourValueOutputGraph 0) :
    fourValueHolds 0 a (shiftCyclicMask d F) ↔ fourValueHolds 0 a F := by
  let G := SharedCoordinates.Ambient (fourValueLayout 0)
  let t : G := (d,0)
  let e : G ≃ G := Equiv.addRight t
  let A : Finset G := F.toFinset.image (decodePoint (fourValueLayout 0))
  let B : Set G := Set.range (SharedCoordinates.point (fourValueLayout 0) a)
  have hd (f : CyclicPoint) : e (decodePoint (fourValueLayout 0) f) =
      decodePoint (fourValueLayout 0) (f.1+d,f.2) :=
    Prod.ext rfl (add_zero _)
  have he : (shiftCyclicMask d F).toFinset.image (decodePoint (fourValueLayout 0)) =
      A.map e.toEmbedding := by
    ext w
    constructor
    · intro hw
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hw
      obtain ⟨f,hf,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hv)
      exact Finset.mem_map.mpr ⟨decodePoint (fourValueLayout 0) f,
        Finset.mem_image.mpr ⟨f,List.mem_toFinset.mpr hf,rfl⟩,hd f⟩
    · intro hw
      obtain ⟨v,hv,rfl⟩ := Finset.mem_map.mp hw
      obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp hv
      exact Finset.mem_image.mpr ⟨(f.1+d,f.2),
        List.mem_toFinset.mpr (List.mem_map.mpr ⟨f,List.mem_toFinset.mp hf,rfl⟩),(hd f).symm⟩
  change Tiles _ B ↔ Tiles A B
  rw [he]
  exact tiles_map_translate_iff A B t

theorem arithmetic_holds (h : ∀ F ∈ s.arithmeticTiles, Holds F) (F : CyclicTile)
    (hF : F ∈ sharedDependence (fourValueRows 0) (tailSlopes 0) ++ fourValueActivation 0)
    (v : s.ExtraLow) : fourValueHolds 0 (s.oldSlice o v) F := by
  rw [← arithmeticMaskRecords_original] at hF
  obtain ⟨⟨d,F'⟩,hentry,he⟩ := List.mem_map.mp hF
  change F' = F at he
  subst F'
  have hmask : shiftCyclicMask d F ∈ arithmeticBaseline := by
    unfold arithmeticBaseline
    exact List.mem_map.mpr ⟨(d,F),hentry,rfl⟩
  apply (fourValueHolds_shift d F (s.oldSlice o v)).mp
  exact (s.oldTileLift_iff _ o).mp
    (h _ (List.mem_map.mpr ⟨shiftCyclicMask d F,hmask,rfl⟩)) v

theorem arithmetic_dependence (h : ∀ F ∈ s.arithmeticTiles, Holds F) (v : s.ExtraLow) :
    HasFourValueDependence 0 (tailSlopes 0) (s.oldSlice o v) :=
  (fourValueDependence_iff _ _ _).mp (fun F hF =>
    s.arithmetic_holds o h F (List.mem_append_left _ hF) v)

theorem arithmetic_privateAt (h : ∀ F ∈ s.arithmeticTiles, Holds F)
    (ha : ∀ F ∈ s.anchorTests, Holds F) (x : SharedCoordinates.Base s.layout) (i : FourValueRow 0) :
    o.privateOutput x (.inl i) = fourValuePrivateAt (s.oldSlice o 0) x.1 i (x.2 (.inl i)) := by
  let f (x : SharedCoordinates.Base s.layout) := o.privateOutput x (.inl i)
  let x₀ : FourValueBase 0 := (x.1,fun j => x.2 (.inl j))
  let J : Set (SlotRow k m) := Set.range Sum.inl
  have hl : ∀ j ∉ J, ∀ b, f (b-lowStep s.layout j) = f b := by
    intro j hj
    rcases j with j | j
    · exact (hj ⟨j,rfl⟩).elim
    · exact (productInvariance_iff s.layout _ _ o).mp
        (ha _ (List.mem_map.mpr ⟨(i,j),by simp,rfl⟩))
  have hx := factor_selected_lows s.layout f J hl x.1 x.2 (s.joinBase x₀ 0).2 (by
    rintro _ ⟨j,rfl⟩
    rfl)
  exact hx.trans ((s.arithmetic_dependence o h 0).privateAt_eq x₀ i)

theorem arithmetic_active (h : ∀ F ∈ s.arithmeticTiles, Holds F)
    (i : FourValueRow 0) (hi : i.val < 18) (x : Plane) :
    ∃ j : FourValueLabel i, DigitActive (fourValuePrivateAt (s.oldSlice o 0) x i)
      (fourValueDigitSubgroup i j) := by
  apply fourValue_fixed_active i hi (s.arithmetic_dependence o h 0)
  apply s.arithmetic_holds o h
  exact List.mem_append_right _ ((fourValueActivation_members _ _).mpr
    (Or.inl (Or.inl ⟨i,hi,rfl⟩)))

theorem arithmetic_seed_active (h : ∀ F ∈ s.arithmeticTiles, Holds F) (t : Fin 2) :
    ∃ x : Plane, DigitActive (fourValuePrivateAt (s.oldSlice o 0) x (fourValueSeedRow 0 t)) ⊤ := by
  apply fourValue_seed_active (s.arithmetic_dependence o h 0) t
  apply s.arithmetic_holds o h
  exact List.mem_append_right _ ((fourValueActivation_members _ _).mpr (Or.inr ⟨t,rfl⟩))

end
end TranslationTiling.FiniteCompiler.Packed.SlotParameters
