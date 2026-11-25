import TranslationTiling.FiniteCompiler.Effective.SlotMasks
import TranslationTiling.FiniteCompiler.Effective.SlotBlocks

namespace TranslationTiling.FiniteCompiler.Packed.SlotParameters

open SharedCoordinates
open scoped Classical BigOperators
noncomputable section

variable {k m : ℕ} (s : SlotParameters k m)

abbrev SlotPicker (k m : ℕ) := WangSlot k m → ℤ → Option (Fin 3)

def oldBase (x : SharedCoordinates.Base s.layout) : FourValueBase 0 :=
  (x.1,fun i => x.2 (.inl i))

def markerValue (i : WangSlot k m) (state : Option (Fin 3)) (j : Fin 3)
    (u : ZMod (s.low i)) : ZMod (s.marker i j) :=
  if state = some j then ((s.blocks i (some j)).C u).2 else 0

def firstValue (i : WangSlot k m) (state : Option (Fin 3))
    (u : ZMod (s.low i)) : ZMod (s.firstBlock i) :=
  ((s.blocks i state).C u).1

def stateAt (pick : SlotPicker k m) (i : WangSlot k m) (x : Plane) :=
  pick i (slotLine i.1 x)

def slotMarkerAt (pick : SlotPicker k m) (i : WangSlot k m) (j : Fin 3)
    (x : SharedCoordinates.Base s.layout) : ZMod (s.marker i j) :=
  s.markerValue i (stateAt pick i x.1) j (x.2 (wangRow i))

def fallbackContribution (pick : SlotPicker k m) (g : Bool) (d : Fin k) (i : Fin m)
    (x : SharedCoordinates.Base s.layout) : ZMod (s.fallback (g,i,false)) :=
  s.firstValue (g,d,i) (stateAt pick (g,d,i) x.1) (x.2 (wangRow (g,d,i)))

def slotModel (old : FourValueOutputGraph 0) (pick : SlotPicker k m) :
    SharedCoordinates.Outputs s.layout where
  fixed x := old.fixed (s.oldBase x)
  privateOutput x
    | .inl i => old.privateOutput (s.oldBase x) i
    | .inr (.inl i) => (0,(s.markerCRT i).symm (fun j => s.slotMarkerAt pick i j x))
    | .inr (.inr (g,i,false)) => (0,∑ d : Fin k, s.fallbackContribution pick g d i x)
    | .inr (.inr (_,_,true)) => 0
  high x
    | .inl i => old.high (s.oldBase x) i
    | .inr (.inl i) => (s.blocks i (stateAt pick i x.1)).T x.1.1 (x.2 (wangRow i))
    | .inr (.inr _) => 0

@[simp] theorem observeMarker_model (old : FourValueOutputGraph 0) (pick : SlotPicker k m)
    (i : WangSlot k m) (j : Fin 3) (x : SharedCoordinates.Base s.layout) :
    s.observeMarker i j (SharedCoordinates.point s.layout (s.slotModel old pick) x).2 =
      s.slotMarkerAt pick i j x := by
  change s.markerRead i j ((s.markerCRT i).symm (fun j => s.slotMarkerAt pick i j x)) = _
  rw [← markerCRT_apply]
  exact congrFun ((s.markerCRT i).apply_symm_apply (fun j => s.slotMarkerAt pick i j x)) j

@[simp] theorem observeFallback_model (old : FourValueOutputGraph 0) (pick : SlotPicker k m)
    (g : Bool) (i : Fin m) (x : SharedCoordinates.Base s.layout) :
    s.observeFallback (g,i,false) (SharedCoordinates.point s.layout (s.slotModel old pick) x).2 =
      ∑ d : Fin k, s.fallbackContribution pick g d i x :=
  rfl

@[simp] theorem high_model (old : FourValueOutputGraph 0) (pick : SlotPicker k m)
    (i : WangSlot k m) (x : SharedCoordinates.Base s.layout) :
    (s.slotModel old pick).high x (wangRow i) =
      (s.blocks i (stateAt pick i x.1)).T x.1.1 (x.2 (wangRow i)) :=
  rfl

theorem markerValue_active_iff (i : WangSlot k m) (state : Option (Fin 3)) (j : Fin 3) :
    (∃ u v, s.markerValue i state j u ≠ s.markerValue i state j v) ↔ state = some j := by
  constructor
  · rintro ⟨u,v,huv⟩
    by_contra hn
    exact huv (by simp [markerValue,hn])
  · rintro rfl
    let D := s.blocks i (some j)
    let a : Fin (s.rightCount i (some j)) := ⟨0,s.rightCount_pos i (some j)⟩
    refine ⟨D.decode.symm (.inr (a,0)),D.decode.symm (.inr (a,1)),?_⟩
    have : Fact (1 < s.marker i j) := ⟨(s.prime_isPrime (.inl (i,some j))).one_lt⟩
    change (if (some j : Option (Fin 3)) = some j then (D.C (D.decode.symm (.inr (a,0)))).2 else 0) ≠ _
    simp [markerValue,D]
    change (0 : ZMod (s.marker i j)) ≠ 1
    exact zero_ne_one

end
end TranslationTiling.FiniteCompiler.Packed.SlotParameters
