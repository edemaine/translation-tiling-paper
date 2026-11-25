import TranslationTiling.FiniteCompiler.Effective.SlotDeck
import TranslationTiling.FiniteCompiler.Effective.SlotAssembly

namespace TranslationTiling.FiniteCompiler.Packed.SlotParameters

open PairSmall GuardedCompiler SharedCoordinates Compiler Compiler.Effective Effective Compiler.StripLift
open scoped Classical
noncomputable section

local instance slotPolycubeFrame : SeedFrame := compactSeedFrame
set_option maxRecDepth 8000

variable {k m w : ℕ} {T : LeanWang.TileSet} (c : Code T ((slotRadix m w)^k))
local instance slotPolycubeAlphabet : AlphabetFamily (system c) := GuardedCompiler.alphabet c
variable (s : SlotParameters k m)

theorem slotDeck_strip (hwm : w ≤ m) {Q : ℕ}
    (hQ : ∀ j, s.prime j ≤ Q)
    (F : Finset (SharedCoordinates.Ambient s.layout)) (hF : F ∈ s.slotDeck c hwm)
    (v : SharedCoordinates.Ambient s.layout) (hv : v ∈ F) :
    TestSupportAt 35 (fun _ => slotRadius Q m) v.1 := by
  let H := slotRadius Q m
  have hH : 1 ≤ H := radius_pos Q m
  rcases (s.slotDeck_membership c hwm F).mp hF with
    rfl | ha | hb | ⟨i,j,hj⟩ | ⟨g,i,hi⟩ | ⟨g,d,S,hS,rfl⟩ | ⟨t,i,a,_,rfl⟩ | ⟨p,hp,rfl⟩
  · simp only [productKernel,Finset.mem_filter,Finset.mem_map,Finset.mem_univ,true_and] at hv
    obtain ⟨⟨a,ha⟩,_⟩ := hv
    have hh : (0 : Plane) = v.1 := congrArg Prod.fst ha
    exact hh ▸ zero_strip H
  · exact s.arithmetic_strip (le_max_left ..) F ha v hv
  · exact s.anchor_strip H F hb v hv
  · exact s.marker_strip hH i j F hj v hv
  · exact s.fallback_strip hH g i F hi v hv
  · have := shiftCount_neZero (selected_nonempty hwm hS)
    change v ∈ s.mask g d S at hv
    have h := s.mask_strip hQ g d S v hv
    rcases h with ⟨h₁,h₂⟩ | ⟨j,hj,h₁,h₂⟩
    · exact Or.inl ⟨h₁.trans (le_max_right ..),h₂⟩
    · exact Or.inr ⟨j,hj,h₁.trans (le_max_right ..),h₂⟩
  · rw [(s.exists_seedMask c t i a).choose_spec.1 v hv]
    exact zero_strip H
  · rw [(s.exists_guardMask c p hp).choose_spec.1 v hv]
    exact zero_strip H

private def fixedPicker : FourValuePicker 0 where
  fixed i _ _ := ⟨0,(by decide +kernel : ∀ i : FourValueRow 0,
    0 < (rowDigits (fourValueRows 0) i).length) i⟩
  wang i _ := Fin.elim0 i

theorem slotDeck_has_mass (hwm : w ≤ m)
    (F : Finset (SharedCoordinates.Ambient s.layout)) (hF : F ∈ s.slotDeck c hwm) :
    ∃ o : SharedCoordinates.Outputs s.layout, Tiles F (Set.range (SharedCoordinates.point s.layout o)) := by
  let old := fourValueModel fixedPicker
  let pick : SlotPicker k m := fun _ _ => some 0
  let o := s.slotModel old pick
  have h := s.model_dependencies fixedPicker pick
  rcases (s.slotDeck_membership c hwm F).mp hF with
    rfl | ha | hb | ⟨i,j,hj⟩ | ⟨g,i,hi⟩ | ⟨g,d,S,hS,rfl⟩ | ⟨t,i,a,_,rfl⟩ | ⟨p,hp,rfl⟩
  · exact ⟨o,(productKernel_iff s.layout _).mpr ⟨o,rfl⟩⟩
  · exact ⟨o,h.1 F ha⟩
  · exact ⟨o,h.2.1 F hb⟩
  · exact ⟨o,h.2.2 i j F hj⟩
  · exact ⟨o,s.model_fallbackTests old pick g i F hi⟩
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
      U.length ≤ reservedVolumeCap 35 (fun _ => slotRadius Q m) s.period (order s.layout / s.period)
        (reservedCap (stackTestCap P (s.slotDeck c hwm).length) P) := by
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
end TranslationTiling.FiniteCompiler.Packed.SlotParameters
