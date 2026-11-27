import TranslationTiling.FiniteCompiler.Effective.AxisSlotModel
import TranslationTiling.FiniteCompiler.Effective.AxisSlotDependence

namespace TranslationTiling.FiniteCompiler.Packed.AxisParameters

open SharedCoordinates
open scoped Classical BigOperators
noncomputable section

set_option allowUnsafeReducibility true
attribute [local reducible] AxisParameters.layout AxisParameters.low AxisParameters.lowEquiv AxisParameters.firstBlock


variable {k m : ℕ} (s : AxisParameters k m)
variable (old : FourValueOutputGraph 0) (pick : SlotPicker k m)

theorem model_marker_active (g : Bool) (d : Fin k) (line : ℤ) (i : Fin m) (b : AxisSlot.Label) :
    s.Active (s.slotModel old pick) g d line i b ↔ pick (g,d,i) line = some b := by
  have h (u : ZMod (s.low (g,d,i))) :
      s.markerAt (s.slotModel old pick) (g,d,i) b.2 line u =
        s.markerValue (g,d,i) (pick (g,d,i) line) b.2 u := by
    unfold markerAt outputAt
    rw [observeMarker_model]
    simp [slotMarkerAt,stateAt,slotLine]
  unfold Active
  rw [funext h]
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

theorem model_fallbackTests (g : Bool) (i : Fin m) (b : Bool) :
    ∀ F ∈ s.fallbackTests g i b, Tiles F (Set.range (SharedCoordinates.point s.layout (s.slotModel old pick))) := by
  intro F hF
  simp only [fallbackTests,List.mem_cons,List.mem_append,List.mem_map,Finset.mem_toList,Finset.mem_filter,
    Finset.mem_univ,true_and] at hF
  rcases hF with rfl | ⟨a,ha,rfl⟩ | ⟨e,_,rfl⟩
  · apply (productInvariance_iff _ _ _ _).mpr
    intro x
    simp only [observeFallback_model,fallbackContribution,stateAt]
    have hline := slotLine_sub g x.1 ((1,-slopeNumber g) : Plane) (by simp)
    change slotLine g (x.1-((1,-slopeNumber g) : Plane)) = slotLine g x.1 at hline
    simp only [Prod.fst_sub,Prod.snd_sub,sub_zero]
    rw [hline]
  · apply (productInvariance_iff _ _ _ _).mpr
    intro x
    simp only [observeFallback_model]
    apply Finset.sum_congr rfl
    intro d _
    have hne : wangRow (g,d,i) ≠ a := fun h => ha ⟨d,h⟩
    simp only [fallbackContribution,stateAt,lowStep,Prod.fst_sub,Prod.snd_sub,sub_zero,
      Pi.sub_apply,Function.update_of_ne hne,Pi.zero_apply]
    rw [sub_zero (x.1 : Plane)]

  · apply (productInvariance_iff _ _ _ _).mpr
    intro x
    simp only [observeFallback_model]
    apply Finset.sum_congr rfl
    intro d _
    by_cases hd : d = e
    · subst e
      have ha : s.axisInput (g,d,i) b
          (AxisSlot.axisGenerator (s.lowAxis_coprime (g,d,i)) (!b)) = 0 := by
        cases b
        · exact congrArg Prod.fst ((s.lowEquiv (g,d,i)).apply_symm_apply (0,1))
        · exact congrArg Prod.snd ((s.lowEquiv (g,d,i)).apply_symm_apply (1,0))
      simp only [fallbackContribution,stateAt,axisStep,Prod.fst_sub,Prod.snd_sub,sub_zero,
        Pi.sub_apply,Function.update_self,s.axisInput_sub,ha]
      rw [sub_zero (x.1 : Plane)]
    · have hn : wangRow (g,d,i) ≠ wangRow (g,e,i) := by
        intro h
        exact hd (congrArg (fun r : WangSlot k m => r.2.1) (Sum.inl.inj (Sum.inr.inj h)))
      simp only [fallbackContribution,stateAt,axisStep,Prod.fst_sub,Prod.snd_sub,sub_zero,
        Pi.sub_apply,Function.update_of_ne hn,Pi.zero_apply]
      rw [sub_zero (x.1 : Plane)]

end Invariance
end
end TranslationTiling.FiniteCompiler.Packed.AxisParameters
