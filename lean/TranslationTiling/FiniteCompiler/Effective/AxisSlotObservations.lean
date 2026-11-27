import TranslationTiling.FiniteCompiler.Effective.AxisSlotCycle
import TranslationTiling.FiniteCompiler.SlotActivation

namespace TranslationTiling.FiniteCompiler.Packed

open SharedCoordinates
open scoped Classical BigOperators

noncomputable section

namespace AxisParameters

variable {k m : ℕ} (s : AxisParameters k m)

abbrev SlotIndex (S : Finset (Fin m)) := {i : Fin m // i ∈ S} × (Bool ⊕ Fin 3)

def observationPrime (g : Bool) (d : Fin k) {S : Finset (Fin m)} (i : SlotIndex S) : ℕ :=
  match i with
  | (i,.inl a) => s.fallback (g,i,a,false)
  | (i,.inr j) => s.marker (g,d,i) j

def observe (g : Bool) (d : Fin k) {S : Finset (Fin m)} (i : SlotIndex S) :
    Factor s.layout →+ ZMod (s.observationPrime g d i) :=
  match i with
  | (i,.inl a) => s.observeFallback (g,i,a,false)
  | (i,.inr j) => s.observeMarker (g,d,i) j

private theorem extendDependent {A B : Type*} [Fintype A] (e : A ↪ B) {D : B → Type*}
    [∀ i, Zero (D i)] (v : ∀ i, D (e i)) :
    ∃ f : ∀ i, D i, ∀ i, f (e i) = v i := by
  have h (S : Finset A) : ∃ f : ∀ i, D i, ∀ i ∈ S, f (e i) = v i := by
    induction S using Finset.induction_on with
    | empty => exact ⟨0,by simp⟩
    | @insert a S ha ih =>
      obtain ⟨f,hf⟩ := ih
      refine ⟨Function.update f (e a) (v a),fun i hi => ?_⟩
      rcases Finset.mem_insert.mp hi with rfl|hi
      · exact Function.update_self _ _ _
      · have hne : e i ≠ e a := fun he => ha (e.injective he ▸ hi)
        rw [Function.update_of_ne hne,hf i hi]
  obtain ⟨f,hf⟩ := h Finset.univ
  exact ⟨f,fun i => hf i (Finset.mem_univ i)⟩

private def observedRow (g : Bool) (d : Fin k) (S : Finset (Fin m)) :
    ({i : Fin m // i ∈ S} × Option Bool) ↪ AxisRow k m where
  toFun
    | (i,some a) => fallbackRow (g,i,a,false)
    | (i,none) => wangRow (g,d,i)
  inj' := by
    rintro ⟨i,_ | a⟩ ⟨j,_ | b⟩ h
    · have hp := Sum.inl.inj (Sum.inr.inj h)
      exact Prod.ext (Subtype.ext (congrArg (fun x : WangSlot k m => x.2.2) hp)) rfl
    · cases h
    · cases h
    · have hp := Sum.inr.inj (Sum.inr.inj h)
      have hi := Subtype.ext (congrArg (fun x : AxisFallback m => x.2.1) hp)
      have ha := congrArg (fun x : AxisFallback m => x.2.2.1) hp
      exact Prod.ext hi (congrArg some ha)

/-- Observations and high coordinates can be prescribed independently
over every base point. -/
theorem observe_target (g : Bool) (d : Fin k) (S : Finset (Fin m))
    (x : SharedCoordinates.Base s.layout) (high : ∀ i, SharedCoordinates.Low s.layout i)
    (u : ∀ i : SlotIndex S, ZMod (s.observationPrime g d i)) :
    ∃ v : SharedCoordinates.Ambient s.layout, baseProjection s.layout v = x ∧
      (∀ i : SlotIndex S, s.observe g d i v.2 = u i) ∧
      ∀ i, highCoordinate s.layout i v = high i := by
  let e := observedRow g d S
  let useful (v : {i : Fin m // i ∈ S} × Option Bool) :
      ZMod (s.layout.firstSize (e v)) × ZMod (s.layout.secondSize (e v)) :=
    match v with
    | (i,some a) => (0,u (i,.inl a))
    | (i,none) => (0,(s.markerCRT (g,d,i)).symm (fun j => u (i,.inr j)))
  obtain ⟨f,hf⟩ := extendDependent e
    (D := fun i => ZMod (s.layout.firstSize i) × ZMod (s.layout.secondSize i)) useful
  let o : SharedCoordinates.Outputs s.layout := ⟨fun _ => 0,fun _ => f,fun _ => high⟩
  refine ⟨SharedCoordinates.point s.layout o x,baseProjection_point s.layout o x,fun j => ?_,
    fun i => highCoordinate_point s.layout i o x⟩
  rcases j with ⟨i,a | j⟩
  · exact congrArg Prod.snd (hf (i,some a))
  · have h := congrArg Prod.snd (hf (i,none))
    change s.markerCRT (g,d,i) (f (wangRow (g,d,i))).2 j = _
    change (f (wangRow (g,d,i))).2 =
      (s.markerCRT (g,d,i)).symm (fun j => u (i,.inr j)) at h
    rw [h]
    let v : ∀ j, ZMod (s.marker (g,d,i) j) := fun j => u (i,.inr j)
    exact congrFun ((s.markerCRT (g,d,i)).apply_symm_apply v) j

end AxisParameters
end
end TranslationTiling.FiniteCompiler.Packed
