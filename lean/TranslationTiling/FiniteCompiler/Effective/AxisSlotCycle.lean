import TranslationTiling.FiniteCompiler.Effective.SlotCycle
import TranslationTiling.FiniteCompiler.Effective.FourValueDigits
import TranslationTiling.FiniteCompiler.Effective.AxisSlotLayout

namespace TranslationTiling.FiniteCompiler.Packed.AxisParameters

open SharedCoordinates
open scoped Classical
noncomputable section

variable {k m : ℕ} (s : AxisParameters k m)

def markerCRT (i : WangSlot k m) :
    ZMod (s.layout.secondSize (wangRow i)) ≃+* (∀ j, ZMod (s.marker i j)) := by
  change ZMod (∏ j, s.marker i j) ≃+* _
  apply ZMod.prodEquivPi (s.marker i)
  intro a b h
  apply s.prime_coprime (i := .inl (i,.inr a)) (j := .inl (i,.inr b))
  intro he
  cases he
  exact h rfl

def observeMarker (i : WangSlot k m) (j : Fin 3) :
    Factor s.layout →+ ZMod (s.marker i j) :=
  (Pi.evalAddMonoidHom _ j).comp (s.markerCRT i).toAddMonoidHom |>.comp
    ((AddMonoidHom.snd ..).comp (privateUseful s.layout (wangRow i)))

def observeFallback (i : AxisFallback m) : Factor s.layout →+ ZMod (s.fallback i) :=
  (AddMonoidHom.snd ..).comp (privateUseful s.layout (fallbackRow i))

abbrev RowLabel : AxisRow k m → Type
  | .inl i => FourValueLabel i
  | .inr (.inl _) => AxisSlot.Label
  | .inr (.inr _) => Unit

def Observed (i : AxisRow k m) (a : RowLabel i) : Type :=
  match i with
  | .inl j => ZMod ((fourValueLayout 0).firstSize j) × ZMod ((fourValueLayout 0).secondSize j)
  | .inr (.inl j) => ZMod (s.marker j a.2)
  | .inr (.inr _) => ZMod 1

instance observed_add (i : AxisRow k m) (a : RowLabel i) : AddCommGroup (s.Observed i a) := by
  rcases i with i | i | i <;> unfold Observed <;> infer_instance

instance observed_fintype (i : AxisRow k m) (a : RowLabel i) : Fintype (s.Observed i a) := by
  rcases i with i | i | i
  · unfold Observed
    infer_instance
  · haveI : NeZero (s.marker i a.2) := ⟨(s.prime_isPrime (.inl (i,.inr a.2))).ne_zero⟩
    exact inferInstanceAs (Fintype (ZMod (s.marker i a.2)))
  · exact inferInstanceAs (Fintype (ZMod 1))

instance observed_decEq (i : AxisRow k m) (a : RowLabel i) : DecidableEq (s.Observed i a) :=
  Classical.decEq _

def readForRow (i : AxisRow k m) (a : RowLabel i) : Factor s.layout →+ s.Observed i a :=
  match i with
  | .inl j => privateUseful s.layout (.inl j)
  | .inr (.inl j) => s.observeMarker j a.2
  | .inr (.inr _) => 0

def cycleRead (a : ∀ i : AxisRow k m, RowLabel i) : Factor s.layout →+ (∀ i, s.Observed i (a i)) :=
  AddMonoidHom.pi fun i => s.readForRow i (a i)

theorem cycleRead_target (a : ∀ i : AxisRow k m, RowLabel i) : Function.Surjective
    (fun v : SharedCoordinates.Ambient s.layout => (baseProjection s.layout v,s.cycleRead a v.2)) := by
  rintro ⟨x,y⟩
  let f (i : AxisRow k m) : ZMod (s.layout.firstSize i) × ZMod (s.layout.secondSize i) :=
    match i with
    | .inl j => y (.inl j)
    | .inr (.inl j) =>
      let b := a (.inr (.inl j))
      (0,(s.markerCRT j).symm (Function.update 0 b.2 (y (.inr (.inl j)))))
    | .inr (.inr _) => 0
  let o : SharedCoordinates.Outputs s.layout := ⟨0,fun _ => f,0⟩
  refine ⟨SharedCoordinates.point s.layout o x,Prod.ext (baseProjection_point s.layout o x) ?_⟩
  funext i
  rcases i with i | i | i
  · rfl
  · let j := a (.inr (.inl i))
    let u : ∀ v, ZMod (s.marker i v) := Function.update 0 j.2 (y (.inr (.inl i)))
    change s.markerCRT i ((s.markerCRT i).symm u) j.2 = y (.inr (.inl i))
    rw [RingEquiv.apply_symm_apply]
    exact Function.update_self ..
  · exact Subsingleton.elim (α := ZMod 1) _ _

def labelSubgroup (i : AxisRow k m) (a : RowLabel i) : AddSubgroup (SharedCoordinates.Low s.layout i) :=
  match i with
  | .inl j => fourValueDigitSubgroup j a
  | .inr (.inl j) => AxisSlot.axisSubgroup (s.lowAxis_coprime j) a.1
  | .inr (.inr _) => ⊥

def labelStep (i : AxisRow k m) (a : RowLabel i) : s.labelSubgroup i a :=
  match i with
  | .inl j => ⟨(fourValueStep j a : SharedCoordinates.Low (fourValueLayout 0) j),fourValueStep_mem j a⟩
  | .inr (.inl j) => AxisSlot.axisGenerator (s.lowAxis_coprime j) a.1
  | .inr (.inr _) => 0

theorem labelStep_spans (i : AxisRow k m) (a : RowLabel i) (u : SharedCoordinates.Low s.layout i)
    (hu : u ∈ s.labelSubgroup i a) :
    ∃ n : ℕ, n • (s.labelStep i a : SharedCoordinates.Low s.layout i) = u := by
  rcases i with i | i | i
  · exact fourValueStep_spans i a u hu
  · exact AxisSlot.axisGenerator_spans (s.lowAxis_coprime i) a.1 u hu
  · have h : u = 0 := AddSubgroup.mem_bot.mp hu
    exact ⟨0,by simp [h]⟩

section Cycle
variable [Fintype (Factor s.layout)]

def rowCycleMask {t : ℕ} [NeZero t] (cycle : ZMod t ↪ AxisRow k m)
    (a : ∀ i : AxisRow k m, RowLabel i) : Finset (SharedCoordinates.Ambient s.layout) :=
  productCycle s.layout cycle (fun j => s.labelSubgroup (cycle j) (a (cycle j)))
    (fun j => s.labelStep (cycle j) (a (cycle j))) (s.cycleRead a)

theorem rowCycleMask_vertical {t : ℕ} [NeZero t] (cycle : ZMod t ↪ AxisRow k m)
    (a : ∀ i : AxisRow k m, RowLabel i) {q : SharedCoordinates.Ambient s.layout}
    (hq : q ∈ s.rowCycleMask cycle a) : q.1 = 0 := by
  have h := @productCycle_vertical (AxisRow k m) _ s.layout _
    (fun i => s.Observed i (a i)) _ _ _ t _ cycle
    (fun j => s.labelSubgroup (cycle j) (a (cycle j)))
    (fun j => s.labelStep (cycle j) (a (cycle j))) (s.cycleRead a) q
  exact h hq

theorem rowCycleMask_iff {t : ℕ} [NeZero t] (cycle : ZMod t ↪ AxisRow k m)
    (a : ∀ i : AxisRow k m, RowLabel i)
    (o : SharedCoordinates.Outputs s.layout) (f : Plane → ∀ i, SharedCoordinates.Low s.layout i → s.Observed i (a i))
    (h : ∀ x k i, s.cycleRead a (SharedCoordinates.point s.layout o (x,k)).2 i = f x i (k i)) :
    Tiles (s.rowCycleMask cycle a) (Set.range (SharedCoordinates.point s.layout o)) ↔
      ∀ x, ∃ j, ¬ DigitActive (f x (cycle j)) (s.labelSubgroup (cycle j) (a (cycle j))) :=
  productCycle_iff s.layout cycle _ _ (fun j => s.labelStep_spans (cycle j) (a (cycle j)))
    _ (s.cycleRead_target a) o f h

/-- The mask has the graph-kernel mass even when the surrounding tests
have no common solution. The graph with zero outputs suffices here. -/
theorem rowCycleMask_satisfiable {t : ℕ} [NeZero t] (cycle : ZMod t ↪ AxisRow k m)
    (a : ∀ i : AxisRow k m, RowLabel i) :
    ∃ o : SharedCoordinates.Outputs s.layout,
      Tiles (s.rowCycleMask cycle a) (Set.range (SharedCoordinates.point s.layout o)) := by
  let o : SharedCoordinates.Outputs s.layout := ⟨0,0,0⟩
  refine ⟨o,(s.rowCycleMask_iff cycle a o (fun _ _ _ => 0) ?_).mpr ?_⟩
  · intro x v i
    rcases i with i | i | i
    · rfl
    · change s.markerCRT i 0 (a (.inr (.inl i))).2 = 0
      simp
    · rfl
  · intro x
    exact ⟨0,fun ⟨_,_,_,hn⟩ => hn rfl⟩

end Cycle
end
end TranslationTiling.FiniteCompiler.Packed.AxisParameters
