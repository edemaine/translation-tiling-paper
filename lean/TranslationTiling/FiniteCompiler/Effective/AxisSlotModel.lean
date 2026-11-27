import TranslationTiling.FiniteCompiler.Effective.AxisSlotArithmetic
import TranslationTiling.FiniteCompiler.Effective.AxisSlotMasks

namespace TranslationTiling.FiniteCompiler.Packed.AxisParameters

open SharedCoordinates
open scoped Classical BigOperators

noncomputable section
set_option allowUnsafeReducibility true
attribute [local reducible] AxisParameters.low AxisParameters.lowAxis AxisParameters.lowEquiv
  AxisParameters.marker AxisParameters.secondBlock AxisParameters.firstBlock

variable {k m : ℕ} (s : AxisParameters k m)

abbrev SlotPicker (k m : ℕ) := WangSlot k m → ℤ → Option AxisSlot.Label

def stateAt (pick : SlotPicker k m) (i : WangSlot k m) (x : Plane) :=
  pick i (slotLine i.1 x)

def axisState (σ : Option AxisSlot.Label) (a : Bool) : Option (Fin 3) :=
  σ.bind fun (b,j) => if b = a then some j else none

def axisInput (i : WangSlot k m) (a : Bool) (v : ZMod (s.low i)) :
    ZMod (s.lowAxis i a) :=
  match a with
  | false => (s.lowEquiv i v).1
  | true => (s.lowEquiv i v).2

def markerValue (i : WangSlot k m) (σ : Option AxisSlot.Label) (j : Fin 3)
    (v : ZMod (s.low i)) : ZMod (s.marker i j) :=
  if σ = some (false,j) then ((s.blocks i false (some j)).C (s.axisInput i false v)).2
  else if σ = some (true,j) then ((s.blocks i true (some j)).C (s.axisInput i true v)).2
  else 0

def slotMarkerAt (pick : SlotPicker k m) (i : WangSlot k m) (j : Fin 3)
    (x : SharedCoordinates.Base s.layout) : ZMod (s.marker i j) :=
  s.markerValue i (stateAt pick i x.1) j (x.2 (wangRow i))

def fallbackContribution (pick : SlotPicker k m) (g : Bool) (d : Fin k) (i : Fin m)
    (a : Bool) (x : SharedCoordinates.Base s.layout) : ZMod (s.fallback (g,i,a,false)) :=
  let row : WangSlot k m := (g,d,i)
  ((s.blocks row a (axisState (stateAt pick row x.1) a)).C (s.axisInput row a (x.2 (wangRow row)))).1

def blockRotation (i : WangSlot k m) (σ : Option AxisSlot.Label) (x : ℤ) :
    Equiv.Perm (ZMod (s.low i)) :=
  (s.lowEquiv i).toEquiv.trans
    ((((s.blocks i false (axisState σ false)).T x).prodCongr
      ((s.blocks i true (axisState σ true)).T x)).trans (s.lowEquiv i).symm.toEquiv)

@[simp] theorem axisInput_blockRotation (i : WangSlot k m) (σ : Option AxisSlot.Label)
    (a : Bool) (x : ℤ) (v : ZMod (s.low i)) :
    s.axisInput i a (s.blockRotation i σ x v) =
      (s.blocks i a (axisState σ a)).T x (s.axisInput i a v) := by
  cases a <;> simp [axisInput,blockRotation]

def oldBase (x : SharedCoordinates.Base s.layout) : FourValueBase 0 :=
  (x.1,fun i => x.2 (.inl i))

def slotModel (old : FourValueOutputGraph 0) (pick : SlotPicker k m) :
    SharedCoordinates.Outputs s.layout where
  fixed x := old.fixed (s.oldBase x)
  privateOutput x
    | .inl i => old.privateOutput (s.oldBase x) i
    | .inr (.inl i) => (0,(s.markerCRT i).symm (fun j => s.slotMarkerAt pick i j x))
    | .inr (.inr (g,i,a,false)) => (0,∑ d : Fin k, s.fallbackContribution pick g d i a x)
    | .inr (.inr (_,_,_,true)) => 0
  high x
    | .inl i => old.high (s.oldBase x) i
    | .inr (.inl i) => s.blockRotation i (stateAt pick i x.1) x.1.1 (x.2 (wangRow i))
    | .inr (.inr _) => 0

@[simp] theorem observeMarker_model (old : FourValueOutputGraph 0) (pick : SlotPicker k m)
    (i : WangSlot k m) (j : Fin 3) (x : SharedCoordinates.Base s.layout) :
    s.observeMarker i j (SharedCoordinates.point s.layout (s.slotModel old pick) x).2 =
      s.slotMarkerAt pick i j x := by
  change s.markerCRT i ((s.markerCRT i).symm (fun j => s.slotMarkerAt pick i j x)) j = _
  exact congrFun ((s.markerCRT i).apply_symm_apply (fun j => s.slotMarkerAt pick i j x)) j

@[simp] theorem observeFallback_model (old : FourValueOutputGraph 0) (pick : SlotPicker k m)
    (g : Bool) (i : Fin m) (a : Bool) (x : SharedCoordinates.Base s.layout) :
    s.observeFallback (g,i,a,false) (SharedCoordinates.point s.layout (s.slotModel old pick) x).2 =
      ∑ d : Fin k, s.fallbackContribution pick g d i a x :=
  rfl

@[simp] theorem high_model (old : FourValueOutputGraph 0) (pick : SlotPicker k m)
    (i : WangSlot k m) (x : SharedCoordinates.Base s.layout) :
    (s.slotModel old pick).high x (wangRow i) =
      s.blockRotation i (stateAt pick i x.1) x.1.1 (x.2 (wangRow i)) :=
  rfl

private theorem activeBlock_nonconstant (i : WangSlot k m) (a : Bool) (j : Fin 3) :
    ∃ u v, ((s.blocks i a (some j)).C u).2 ≠ ((s.blocks i a (some j)).C v).2 := by
  let D := s.blocks i a (some j)
  let b : Fin (s.rightCount i a (some j)) := ⟨0,s.rightCount_pos i a _⟩
  have : Fact (1 < s.marker i j) := ⟨(s.marker_prime i j).one_lt⟩
  refine ⟨D.decode.symm (.inr (b,0)),D.decode.symm (.inr (b,1)),?_⟩
  change (D.C _).2 ≠ (D.C _).2
  simp only [LabeledBlocks.C_decode_symm_inr]
  exact zero_ne_one

/-- The model exposes exactly the chosen axis and marker. -/
theorem markerValue_active_iff (i : WangSlot k m) (σ : Option AxisSlot.Label) (l : AxisSlot.Label) :
    DigitActive (s.markerValue i σ l.2) (AxisSlot.axisSubgroup (s.lowAxis_coprime i) l.1) ↔
      σ = some l := by
  rcases l with ⟨a,j⟩
  by_cases h₀ : σ = some (false,j)
  · subst σ
    have e : s.markerValue i (some (false,j)) j =
        (fun v => ((s.blocks i false (some j)).C (s.lowEquiv i v).1).2) := by
      funext v
      simp [markerValue,axisInput]
    rw [e]
    simpa only [Option.some.injEq,Prod.mk.injEq,true_and,and_true,eq_comm,lowEquiv] using
      AxisSlot.firstAxisOnly (s.lowAxis_coprime i) _ (s.activeBlock_nonconstant i false j) a
  by_cases h₁ : σ = some (true,j)
  · subst σ
    have e : s.markerValue i (some (true,j)) j =
        (fun v => ((s.blocks i true (some j)).C (s.lowEquiv i v).2).2) := by
      funext v
      simp [markerValue,axisInput]
    rw [e]
    simpa only [Option.some.injEq,Prod.mk.injEq,true_and,and_true,eq_comm,lowEquiv] using
      AxisSlot.secondAxisOnly (s.lowAxis_coprime i) _ (s.activeBlock_nonconstant i true j) a
  cases a <;> simp [DigitActive,markerValue,h₀,h₁]

end
end TranslationTiling.FiniteCompiler.Packed.AxisParameters
