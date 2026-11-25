import TranslationTiling.FiniteCompiler.Effective.SlotCycleData
import TranslationTiling.FiniteCompiler.Effective.SlotDependence
import TranslationTiling.FiniteCompiler.Effective.SlotFrame

namespace TranslationTiling.FiniteCompiler.Packed.SlotParameters

open SharedCoordinates Effective
open scoped Classical
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
noncomputable section

variable {k m : ℕ} (s : SlotParameters k m)

def rowFunction (o : SharedCoordinates.Outputs s.layout) (x : Plane) (i : SlotRow k m)
    (a : RowLabel i) (u : SharedCoordinates.Low s.layout i) : s.Observed i a :=
  match i with
  | .inl j => fourValuePrivateAt (s.oldSlice o 0) x j u
  | .inr (.inl j) => s.markerAt o j a (slotLine j.1 x) u
  | .inr (.inr _) => 0

def labelActive (o : SharedCoordinates.Outputs s.layout) (x : Plane) (i : SlotRow k m) (a : RowLabel i) :=
  DigitActive (s.rowFunction o x i a) (s.labelSubgroup i a)

theorem labelActive_wang (o : SharedCoordinates.Outputs s.layout) (x : Plane)
    (i : WangSlot k m) (a : Fin 3) :
    s.labelActive o x (wangRow i) a ↔ s.Active o i.1 i.2.1 (slotLine i.1 x) i.2.2 a := by
  constructor
  · rintro ⟨u,v,_,h⟩
    exact ⟨u,v,h⟩
  · rintro ⟨u,v,h⟩
    exact ⟨u,v,AddSubgroup.mem_top _,h⟩

def cycleDependencies (o : SharedCoordinates.Outputs s.layout) : Prop :=
  let Holds := fun F => Tiles F (Set.range (SharedCoordinates.point s.layout o))
  (∀ F ∈ s.arithmeticTiles, Holds F) ∧
  (∀ F ∈ s.anchorTests, Holds F) ∧
  (∀ i j, ∀ F ∈ s.markerTests i j, Holds F)

theorem cycleRead_local (o : SharedCoordinates.Outputs s.layout) (h : s.cycleDependencies o)
    (a : ∀ i : SlotRow k m, RowLabel i) (x : Plane) (u : ∀ i, SharedCoordinates.Low s.layout i)
    (i : SlotRow k m) :
    s.cycleRead a (SharedCoordinates.point s.layout o (x,u)).2 i =
      s.rowFunction o x i (a i) (u i) := by
  rcases i with i | i | i
  · exact s.arithmetic_privateAt o h.1 h.2.1 (x,u) i
  · exact s.marker_factors o i (a (wangRow i)) (h.2.2 i _) (x,u)
  · rfl

private def defaultLabel : ∀ i : SlotRow k m, RowLabel i
  | .inl i => ⟨0,(by decide +kernel : ∀ i : FourValueRow 0,
        0 < (rowDigits (fourValueRows 0) i).length) i⟩
  | .inr (.inl _) => 0
  | .inr (.inr _) => ()

def assignLabels {W : Type*} (rows : W ↪ SlotRow k m)
    (label : ∀ w, RowLabel (rows w)) (i : SlotRow k m) : RowLabel i :=
  if ha : ∃ w, rows w = i then ha.choose_spec ▸ label ha.choose else defaultLabel i

@[simp] theorem assignLabels_selected {W : Type*} (rows : W ↪ SlotRow k m)
    (label : ∀ w, RowLabel (rows w)) (w : W) :
    assignLabels rows label (rows w) = label w := by
  unfold assignLabels
  let h : ∃ j, rows j = rows w := ⟨w,rfl⟩
  rw [dite_eq_left h]
  have he := rows.injective h.choose_spec
  have hh (u : W) (hu : rows u = rows w) (he : u = w) :
      (hu ▸ label u) = label w := by subst u; rfl
  exact hh _ h.choose_spec he

/-- In any cyclic ordering, the mask forbids simultaneous activation
of all rows in the pattern. -/
theorem pattern_cycle_spec {W : Type} {t : ℕ} [NeZero t] (e : ZMod t ≃ W)
    (rows : W ↪ SlotRow k m) (label : ∀ w, RowLabel (rows w))
    (o : SharedCoordinates.Outputs s.layout) (hd : s.cycleDependencies o) :
    Tiles (s.rowCycleMask (e.toEmbedding.trans rows) (assignLabels rows label))
        (Set.range (SharedCoordinates.point s.layout o)) ↔
      ∀ x, ∃ w, ¬ s.labelActive o x (rows w) (label w) := by
  let cycle : ZMod t ↪ SlotRow k m := e.toEmbedding.trans rows
  let a : (i : SlotRow k m) → RowLabel i := assignLabels rows label
  change (Tiles (s.rowCycleMask cycle a) _ ↔ _)
  rw [s.rowCycleMask_iff cycle a o (fun x i => s.rowFunction o x i (a i)) (s.cycleRead_local o hd a)]
  constructor
  · intro h x
    obtain ⟨j,hj⟩ := h x
    refine ⟨e j,?_⟩
    change ¬ s.labelActive o x (rows (e j)) (assignLabels rows label (rows (e j))) at hj
    rwa [assignLabels_selected] at hj
  · intro h x
    obtain ⟨w,hw⟩ := h x
    refine ⟨e.symm w,?_⟩
    change ¬ s.labelActive o x (rows (e (e.symm w))) (assignLabels rows label (rows (e (e.symm w))))
    rw [e.apply_symm_apply,assignLabels_selected]
    exact hw

/-- A nonempty partial pattern of distinct rows uses one vertical mask. -/
theorem exists_pattern_mask {W : Type} [Fintype W] [Nonempty W]
    (rows : W ↪ SlotRow k m) (label : ∀ w, RowLabel (rows w)) :
    ∃ F : Finset (SharedCoordinates.Ambient s.layout),
      (∀ x ∈ F, x.1 = 0) ∧
      (∃ o : SharedCoordinates.Outputs s.layout, Tiles F (Set.range (SharedCoordinates.point s.layout o))) ∧
      ∀ (o : SharedCoordinates.Outputs s.layout), s.cycleDependencies o →
        (Tiles F (Set.range (SharedCoordinates.point s.layout o)) ↔
          ∀ x, ∃ w, ¬ s.labelActive o x (rows w) (label w)) := by
  have : NeZero (Fintype.card W) := ⟨Fintype.card_ne_zero⟩
  let e := (ZMod.finEquiv (Fintype.card W)).toEquiv.symm.trans (Fintype.equivFin W).symm
  let cycle := e.toEmbedding.trans rows
  let a := assignLabels rows label
  let F := @rowCycleMask k m s (s.finiteFactor) (Fintype.card W) _ cycle a
  refine ⟨F,fun x => @rowCycleMask_vertical k m s (s.finiteFactor) (Fintype.card W) _ cycle a x,
    @rowCycleMask_satisfiable k m s (s.finiteFactor) (Fintype.card W) _ cycle a,?_⟩
  exact s.pattern_cycle_spec e rows label

end
end TranslationTiling.FiniteCompiler.Packed.SlotParameters
