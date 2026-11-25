import TranslationTiling.FiniteCompiler.Effective.SlotModel
import TranslationTiling.FiniteCompiler.Effective.SlotDependence

namespace TranslationTiling.FiniteCompiler.Packed.SlotParameters

open SharedCoordinates
open scoped Classical BigOperators
noncomputable section

variable {k m : ℕ} (s : SlotParameters k m)
variable (old : FourValueOutputGraph 0) (pick : SlotPicker k m)

theorem model_marker_active (g : Bool) (d : Fin k) (line : ℤ) (i : Fin m) (b : Fin 3) :
    s.Active (s.slotModel old pick) g d line i b ↔ pick (g,d,i) line = some b := by
  have h (u : ZMod (s.low (g,d,i))) :
      s.markerAt (s.slotModel old pick) (g,d,i) b line u =
        s.markerValue (g,d,i) (pick (g,d,i) line) b u := by
    unfold markerAt outputAt
    rw [observeMarker_model]
    simp [slotMarkerAt,stateAt,slotLine]
    exact congrArg _ (Function.update_self (β := SharedCoordinates.Low s.layout) ..)
  simp only [Active,h]
  exact s.markerValue_active_iff _ _ _

section Invariance
variable [Fintype (Factor s.layout)]

theorem model_markerTests (i : WangSlot k m) (j : Fin 3) :
    ∀ F ∈ s.markerTests i j, Tiles F (Set.range (SharedCoordinates.point s.layout (s.slotModel old pick))) := by
  intro F hF
  simp only [markerTests,List.mem_cons,List.mem_map,Finset.mem_toList,Finset.mem_erase,
    Finset.mem_univ,and_true] at hF
  rcases hF with rfl | ⟨a,ha,rfl⟩
  · apply (productInvariance_iff _ _ _ _).mpr
    intro x
    simp only [observeMarker_model,slotMarkerAt,stateAt]
    have hline := slotLine_sub i.1 x.1 ((1,-slopeNumber i.1) : Plane) (by simp)
    change slotLine i.1 (x.1-((1,-slopeNumber i.1) : Plane)) = slotLine i.1 x.1 at hline
    simp only [Prod.fst_sub,Prod.snd_sub,sub_zero,hline]
  · apply (productInvariance_iff _ _ _ _).mpr
    intro x
    simp only [observeMarker_model,slotMarkerAt,stateAt,lowStep,Prod.fst_sub,Prod.snd_sub,
      sub_zero,Pi.sub_apply,Function.update_of_ne ha.symm,Pi.zero_apply]

theorem model_fallbackTests (g : Bool) (i : Fin m) :
    ∀ F ∈ s.fallbackTests g i, Tiles F (Set.range (SharedCoordinates.point s.layout (s.slotModel old pick))) := by
  intro F hF
  simp only [fallbackTests,List.mem_cons,List.mem_map,Finset.mem_toList,Finset.mem_filter,
    Finset.mem_univ,true_and] at hF
  rcases hF with rfl | ⟨a,ha,rfl⟩
  · apply (productInvariance_iff _ _ _ _).mpr
    intro x
    simp only [observeFallback_model,fallbackContribution,stateAt]
    have hline := slotLine_sub g x.1 ((1,-slopeNumber g) : Plane) (by simp)
    change slotLine g (x.1-((1,-slopeNumber g) : Plane)) = slotLine g x.1 at hline
    simp only [Prod.fst_sub,Prod.snd_sub,sub_zero,hline]
  · apply (productInvariance_iff _ _ _ _).mpr
    intro x
    simp only [observeFallback_model]
    apply Finset.sum_congr rfl
    intro d _
    have hne : wangRow (g,d,i) ≠ a := fun h => ha ⟨d,h⟩
    simp only [fallbackContribution,stateAt,lowStep,Prod.fst_sub,Prod.snd_sub,sub_zero,
      Pi.sub_apply,Function.update_of_ne hne,Pi.zero_apply]
    rfl

end Invariance
end
end TranslationTiling.FiniteCompiler.Packed.SlotParameters
