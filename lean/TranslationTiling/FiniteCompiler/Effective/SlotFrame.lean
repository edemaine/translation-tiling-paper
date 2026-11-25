import TranslationTiling.FiniteCompiler.Effective.SlotFinite
import TranslationTiling.FiniteCompiler.Effective.SlotInvariance
import TranslationTiling.FiniteCompiler.Effective.FourValueDeckCorrect

namespace TranslationTiling.FiniteCompiler.Packed.SlotParameters

open Compiler Compiler.Effective Effective SharedCoordinates
open scoped Classical
noncomputable section

variable {k m : ℕ} (s : SlotParameters k m)

def arithmeticBaseline : List CyclicTile :=
  sharedDependence (fourValueRows 0) (tailSlopes 0) ++ fourValueActivation 0

def arithmeticTiles : List (Finset (SharedCoordinates.Ambient s.layout)) :=
  arithmeticBaseline.map fun F => s.oldTileLift (F.toFinset.image (decodePoint (fourValueLayout 0)))

def anchorTests : List (Finset (SharedCoordinates.Ambient s.layout)) :=
  (Finset.univ : Finset (FourValueRow 0 × AddedRow k m)).toList.map fun (i,j) =>
    productInvariance s.layout (privateUseful s.layout (.inl i)) (lowStep s.layout (.inr j))

variable (o : SharedCoordinates.Outputs s.layout)
local notation "Holds" => fun F => Tiles F (Set.range (SharedCoordinates.point s.layout o))

theorem arithmetic_holds (h : ∀ F ∈ s.arithmeticTiles, Holds F) (F : CyclicTile)
    (hF : F ∈ arithmeticBaseline) (v : s.ExtraLow) :
    fourValueHolds 0 (s.oldSlice o v) F :=
  (s.oldTileLift_iff _ o).mp (h _ (List.mem_map.mpr ⟨F,hF,rfl⟩)) v

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
