import TranslationTiling.FiniteCompiler.Effective.AxisSlotDeck
import TranslationTiling.FiniteCompiler.Effective.AxisSlotAssembly
import TranslationTiling.FiniteCompiler.Effective.AxisSlotStrip

namespace TranslationTiling.FiniteCompiler.Packed.AxisParameters

open PairSmall GuardedCompiler SharedCoordinates Compiler Compiler.Effective Effective Compiler.StripLift
open Compiler.Size
open scoped Classical
noncomputable section

local instance slotPolycubeFrame : SeedFrame := compactSeedFrame
set_option maxRecDepth 8000

variable {k m w : ℕ} {T : LeanWang.TileSet} (c : Code T ((axisRadix m w)^k))
local instance slotPolycubeAlphabet : AlphabetFamily (system c) := GuardedCompiler.alphabet c
variable (s : AxisParameters k m)

private theorem slotDeck_strip_of (hwm : w ≤ m) {H : ℕ → ℕ}
    (hArith : ∀ j < 17, arithmeticStripRadii.getD j 0 ≤ H j)
    (hmask : ∀ (g : Bool) (d : Fin k) (S : Finset (Fin m)) (hS : S.card = m+1-w)
      (v : SharedCoordinates.Ambient s.layout),
      v ∈ s.activationTest g d S (selected_nonempty hwm hS) →
        TestSupportAt 35 H v.1)
    (F : Finset (SharedCoordinates.Ambient s.layout)) (hF : F ∈ s.slotDeck c hwm)
    (v : SharedCoordinates.Ambient s.layout) (hv : v ∈ F) :
    TestSupportAt 35 H v.1 := by
  have hH : 1 ≤ H 0 := (by decide : 1 ≤ arithmeticStripRadii.getD 0 0).trans (hArith 0 (by decide))
  have hz : TestSupportAt 35 H 0 := Or.inl (by simp)
  rcases (s.slotDeck_membership c hwm F).mp hF with
    rfl | ha | hb | ⟨i,j,hj⟩ | ⟨g,i,b,hi⟩ | ⟨g,d,S,hS,rfl⟩ | ⟨t,i,a,_,rfl⟩ | ⟨p,hp,rfl⟩
  · simp only [productKernel,Finset.mem_filter,Finset.mem_map,Finset.mem_univ,true_and] at hv
    obtain ⟨⟨a,ha⟩,_⟩ := hv
    have hh : (0 : Plane) = v.1 := congrArg Prod.fst ha
    exact hh ▸ hz
  · exact s.arithmetic_strip hArith F ha v hv
  · exact s.anchor_strip H F hb v hv
  · exact s.marker_strip hH i j F hj v hv
  · exact s.fallback_strip hH g i b F hi v hv
  · exact hmask g d S hS v hv
  · rw [(s.exists_seedMask c t i a).choose_spec.1 v hv]
    exact hz
  · rw [(s.exists_guardMask c p hp).choose_spec.1 v hv]
    exact hz

def axisRadius (P m w : ℕ) :=
  max (fourValueRadius 0) (P^(9*(m+1-w)))

theorem slotDeck_strip (hwm : w ≤ m) {Q : ℕ}
    (hQ : ∀ j, s.prime j ≤ Q)
    (F : Finset (SharedCoordinates.Ambient s.layout)) (hF : F ∈ s.slotDeck c hwm)
    (v : SharedCoordinates.Ambient s.layout) (hv : v ∈ F) :
    TestSupportAt 35 (fun _ => axisRadius Q m w) v.1 := by
  apply s.slotDeck_strip_of c hwm
    (fun j _ => (SlotParameters.arithmeticStripRadii_le j).trans (le_max_left ..)) _ F hF v hv
  intro g d S hS v hv
  have := shiftCount_neZero (selected_nonempty hwm hS)
  apply strip_mono (le_max_right ..)
  simpa only [hS] using s.mask_strip_bound hQ g d S v hv

private def fixedPicker : FourValuePicker 0 where
  fixed i _ _ := ⟨0,(by decide +kernel : ∀ i : FourValueRow 0,
    0 < (rowDigits (fourValueRows 0) i).length) i⟩
  wang i _ := Fin.elim0 i

theorem slotDeck_has_mass (hwm : w ≤ m)
    (F : Finset (SharedCoordinates.Ambient s.layout)) (hF : F ∈ s.slotDeck c hwm) :
    ∃ o : SharedCoordinates.Outputs s.layout, Tiles F (Set.range (SharedCoordinates.point s.layout o)) := by
  let old := fourValueModel fixedPicker
  let pick : SlotPicker k m := fun _ _ => some (false,0)
  let o := s.slotModel old pick
  have h := s.model_dependencies fixedPicker pick
  rcases (s.slotDeck_membership c hwm F).mp hF with
    rfl | ha | hb | ⟨i,j,hj⟩ | ⟨g,i,b,hi⟩ | ⟨g,d,S,hS,rfl⟩ | ⟨t,i,a,_,rfl⟩ | ⟨p,hp,rfl⟩
  · exact ⟨o,(productKernel_iff s.layout _).mpr ⟨o,rfl⟩⟩
  · exact ⟨o,h.1 F ha⟩
  · exact ⟨o,h.2.1 F hb⟩
  · exact ⟨o,h.2.2 i j F hj⟩
  · exact ⟨o,s.model_fallbackTests old pick g i b F hi⟩
  · refine ⟨o,?_⟩
    have := shiftCount_neZero (selected_nonempty hwm hS)
    change Tiles (s.mask g d S) _
    apply s.model_mask
    intro _
    obtain ⟨i,hi⟩ := selected_nonempty hwm hS
    exact ⟨⟨i,hi⟩,by simp [stateAt,pick]⟩
  · exact (s.exists_seedMask c t i a).choose_spec.2.1
  · exact (s.exists_guardMask c p hp).choose_spec.2.1

/-- The constant-weight simulation and the geometric assembly agree on
the same ordinary positive masks. -/
theorem slot_polycube (hwm : w ≤ m) {P Q : ℕ}
    (hPr : PrimeBound (order s.layout) P) (hP : 3 < P) (hQ : ∀ j, s.prime j ≤ Q) :
    ∃ U : Tile 3, U ≠ [] ∧ FaceConnected U ∧ (LeanWang.TilesPlane T ↔ TranslationTiling.Tiles U) ∧
      U.length ≤ reservedVolumeCap 35 (fun _ => axisRadius Q m w) s.period (order s.layout / s.period)
        (reservedCap (SlotParameters.stackTestCap P (s.slotDeck c hwm).length) P) := by
  let Fs := (s.slotDeck c hwm).tail
  have hmem (F : Finset (SharedCoordinates.Ambient s.layout)) (hF : F ∈ Fs) :
      F ∈ s.slotDeck c hwm := List.mem_of_mem_tail hF
  obtain ⟨U,hU,hcon,he,hsize⟩ := s.slot_assembly Fs hPr hP
    (fun F hF => s.slotDeck_strip c hwm hQ F (hmem F hF))
    (fun F hF => s.slotDeck_has_mass c hwm F (hmem F hF))
  refine ⟨U,hU,hcon,(s.slotDeck_iff c hwm).trans ?_,?_⟩
  · exact he
  · exact hsize

end
end TranslationTiling.FiniteCompiler.Packed.AxisParameters
