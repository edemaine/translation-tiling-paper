import TranslationTiling.FiniteCompiler.Effective.AxisSlotMaskSound
import TranslationTiling.FiniteCompiler.Effective.SlotInvariance
import TranslationTiling.FiniteCompiler.SlotWords

namespace TranslationTiling.FiniteCompiler.Packed.AxisParameters

open SharedCoordinates
open scoped Classical
noncomputable section

set_option allowUnsafeReducibility true
attribute [local reducible] AxisParameters.layout AxisParameters.low AxisParameters.lowEquiv

variable {k m : ℕ} (s : AxisParameters k m)

def controls (g : Bool) (i : Fin m) : Set (AxisRow k m) :=
  Set.range fun d : Fin k => wangRow (g,d,i)

def outputAt {Y : Type*} [AddCommGroup Y] (o : SharedCoordinates.Outputs s.layout)
    (ψ : Factor s.layout →+ Y) (x : SharedCoordinates.Base s.layout) : Y :=
  ψ (SharedCoordinates.point s.layout o x).2

def markerAt (o : SharedCoordinates.Outputs s.layout)
    (i : WangSlot k m) (j : Fin 3) (line : ℤ) (v : ZMod (s.low i)) :=
  s.outputAt o (s.observeMarker i j)
    ((0,line),Function.update 0 (wangRow i) v)

def Active (o : SharedCoordinates.Outputs s.layout)
    (g : Bool) (d : Fin k) (line : ℤ) (i : Fin m) (b : AxisSlot.Label) : Prop :=
  DigitActive (s.markerAt o (g,d,i) b.2 line) (AxisSlot.axisSubgroup (s.lowAxis_coprime (g,d,i)) b.1)

/-- The step along an axis changes only one CRT component of one low row. -/
def axisStep (i : WangSlot k m) (a : Bool) : SharedCoordinates.Base s.layout :=
  (0, Function.update 0 (wangRow i) (AxisSlot.axisGenerator (s.lowAxis_coprime i) a : ZMod (s.low i)))

section Invariance
variable [Fintype (Factor s.layout)]

def markerTests (i : WangSlot k m) (j : Fin 3) :
    List (Finset (SharedCoordinates.Ambient s.layout)) :=
  productInvariance s.layout (s.observeMarker i j) ((1,-slopeNumber i.1),0) ::
    ((Finset.univ.erase (wangRow i)).toList.map fun a =>
      productInvariance s.layout (s.observeMarker i j) (lowStep s.layout a))

def fallbackTests (g : Bool) (i : Fin m) (a : Bool) :
    List (Finset (SharedCoordinates.Ambient s.layout)) :=
  let ψ := s.observeFallback (g,i,a,false)
  productInvariance s.layout ψ ((1,-slopeNumber g),0) ::
    (((Finset.univ.filter fun j => j ∉ controls g i).toList.map fun j =>
      productInvariance s.layout ψ (lowStep s.layout j)) ++
      (List.finRange k).map fun d => productInvariance s.layout ψ (s.axisStep (g,d,i) (!a)))

variable (o : SharedCoordinates.Outputs s.layout)
local notation "Holds" => fun F => Tiles F (Set.range (SharedCoordinates.point s.layout o))

theorem marker_factors (i : WangSlot k m) (j : Fin 3)
    (h : ∀ F ∈ s.markerTests i j, Holds F) (x : SharedCoordinates.Base s.layout) :
    s.outputAt o (s.observeMarker i j) x = s.markerAt o i j (slotLine i.1 x.1) (x.2 (wangRow i)) := by
  let f := s.outputAt o (s.observeMarker i j)
  have hs := (productInvariance_iff s.layout _ _ o).mp (h _
    (List.mem_cons_self ..))
  have hl : ∀ a, a ≠ wangRow i → ∀ x, f (x-lowStep s.layout a) = f x := by
    intro a ha
    exact (productInvariance_iff s.layout _ _ o).mp
      (h _ (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨a,by simpa using ha,rfl⟩)))
  exact (factor_line s.layout f (slopeNumber i.1) hs x.1 x.2).trans
    (factor_own_low s.layout f (wangRow i) hl _ _)

omit [Fintype (Factor s.layout)] in
private theorem axis_diff_mem (i : WangSlot k m) (a : Bool) (u v : ZMod (s.low i))
    (h : s.axisInput i a u = s.axisInput i a v) :
    u-v ∈ AxisSlot.axisSubgroup (s.lowAxis_coprime i) (!a) := by
  cases a
  · exact (AxisSlot.mem_secondAxis_iff (s.lowAxis_coprime i)).mpr h
  · exact (AxisSlot.mem_firstAxis_iff (s.lowAxis_coprime i)).mpr h

theorem fallback_factors (g : Bool) (i : Fin m) (a : Bool)
    (h : ∀ F ∈ s.fallbackTests g i a, Holds F)
    (x y : SharedCoordinates.Base s.layout)
    (hline : slotLine g x.1 = slotLine g y.1)
    (hkeep : ∀ d : Fin k,
      s.axisInput (g,d,i) a (x.2 (wangRow (g,d,i))) =
        s.axisInput (g,d,i) a (y.2 (wangRow (g,d,i)))) :
    s.outputAt o (s.observeFallback (g,i,a,false)) x = s.outputAt o (s.observeFallback (g,i,a,false)) y := by
  let f := s.outputAt o (s.observeFallback (g,i,a,false))
  have hs := (productInvariance_iff s.layout _ _ o).mp (h _
    (List.mem_cons_self ..))
  have hl : ∀ j ∉ controls g i, ∀ x, f (x-lowStep s.layout j) = f x := by
    intro j hj
    exact (productInvariance_iff s.layout _ _ o).mp
      (h _ (List.mem_cons_of_mem _ (List.mem_append_left _
        (List.mem_map.mpr ⟨j,by simpa using hj,rfl⟩))))
  have hp (d : Fin k) : Function.Periodic f (s.axisStep (g,d,i) (!a)) := by
    have hv : ∀ x, f (x-s.axisStep (g,d,i) (!a)) = f x :=
      (productInvariance_iff s.layout _ _ o).mp
        (h _ (List.mem_cons_of_mem _ (List.mem_append_right _
          (List.mem_map.mpr ⟨d,by simp,rfl⟩))))
    intro x
    simpa using (hv (x+s.axisStep (g,d,i) (!a))).symm
  have hx := factor_line s.layout f (slopeNumber g) hs x.1 x.2
  have hy := factor_line s.layout f (slopeNumber g) hs y.1 y.2
  change f x = f ((0,slotLine g x.1),x.2) at hx
  change f y = f ((0,slotLine g y.1),y.2) at hy
  change f x = f y
  rw [hx,hy,hline]
  let p : Plane := (0,slotLine g y.1)
  let J : Finset (AxisRow k m) := Finset.univ.filter (· ∈ controls g i)
  have hj : ∀ j, j ∈ J ↔ j ∈ controls g i := by simp [J]
  have hxy : f (p,J.piecewise x.2 y.2) = f (p,y.2) := by
    have hsub (J' : Finset (AxisRow k m)) (hs : J' ⊆ J) :
        f (p,J'.piecewise x.2 y.2) = f (p,y.2) := by
      induction J' using Finset.induction_on with
      | empty => simp
      | @insert j J' hn ih =>
        have hmem := (hj j).mp (hs (Finset.mem_insert_self ..))
        obtain ⟨d,rfl⟩ := hmem
        let r := wangRow (g,d,i)
        let w := J'.piecewise x.2 y.2
        have hw : w r = y.2 r := by simp [w,hn,r]
        have hd := s.axis_diff_mem (g,d,i) a (w r) (x.2 r) (by rw [hw, hkeep d])
        obtain ⟨b,hb⟩ := AxisSlot.axisGenerator_spans (s.lowAxis_coprime (g,d,i)) (!a) _ hd
        have hb' : (b : ℤ) • (AxisSlot.axisGenerator (s.lowAxis_coprime (g,d,i)) (!a) :
            ZMod (s.low (g,d,i))) = w r-x.2 r := by exact_mod_cast hb
        have he : (p,Function.update w r (x.2 r)) =
            (p,w) - (b : ℤ) • s.axisStep (g,d,i) (!a) := by
          refine Prod.ext (by simp [axisStep]) (funext fun t => ?_)
          by_cases ht : t = r
          · subst t
            simp [axisStep,r]
            rw [zsmul_eq_mul] at hb'
            calc
              x.2 r = w r - (w r-x.2 r) := (sub_sub_cancel _ _).symm
              _ = _ := by simpa only [Int.cast_natCast] using congrArg (w r - ·) hb'.symm
          · simp [axisStep,r,ht]
        rw [Finset.piecewise_insert]
        change f (p,Function.update w r (x.2 r)) = _
        rw [he,(hp d).sub_zsmul_eq (b : ℤ)]
        exact ih (fun j h => hs (Finset.mem_insert_of_mem h))
    exact hsub J (fun _ => id)
  exact (factor_selected_lows s.layout f (controls g i) hl p _ _ (by
    intro j h
    simp [Finset.piecewise,(hj j).mpr h])).trans hxy

private def shiftOneAxis (i : WangSlot k m) (a : Bool)
    (z : ZMod (s.low i)) : ZMod (s.lowAxis i a) → ZMod (s.low i) :=
  match a with
  | false => fun v => (s.lowEquiv i).symm ((s.lowEquiv i z).1-v,(s.lowEquiv i z).2)
  | true => fun v => (s.lowEquiv i).symm ((s.lowEquiv i z).1,(s.lowEquiv i z).2-v)

omit [Fintype (Factor s.layout)] in
private theorem axisInput_shiftOneAxis (i : WangSlot k m) (a : Bool)
    (z : ZMod (s.low i)) (v : ZMod (s.lowAxis i a)) :
    s.axisInput i a (s.shiftOneAxis i a z v) = s.axisInput i a z-v := by
  cases a
  · exact congrArg Prod.fst ((s.lowEquiv i).apply_symm_apply _)
  · exact congrArg Prod.snd ((s.lowEquiv i).apply_symm_apply _)

omit [Fintype (Factor s.layout)] in
theorem axisInput_sub (i : WangSlot k m) (a : Bool) (u v : ZMod (s.low i)) :
    s.axisInput i a (u-v) = s.axisInput i a u-s.axisInput i a v := by
  have h := map_sub (s.lowEquiv i) u v
  cases a
  · exact congrArg Prod.fst h
  · exact congrArg Prod.snd h

/-- Every selected family of slots contains a marker varying along at least
one of its two axes. -/
theorem mask_forces_active (g : Bool) (d : Fin k) (S : Finset (Fin m))
    [NeZero (ShiftCount S)]
    (hm : ∀ i : SelectedSlot S, ∀ b, ∀ F ∈ s.markerTests (g,d,i) b, Holds F)
    (hf : ∀ i : SelectedSlot S, ∀ a, ∀ F ∈ s.fallbackTests g i a, Holds F)
    (ht : Holds (s.mask g d S)) (x : SharedCoordinates.Base s.layout) :
    ∃ i : SelectedSlot S, ∃ b : AxisSlot.Label, s.Active o g d (slotLine g x.1) i b := by
  by_contra! hn
  let reference (i : SelectedSlot S) (a : Bool) (v : ZMod (s.lowAxis (g,d,i) a)) :
      SharedCoordinates.Base s.layout :=
    (x.1,Function.update x.2 (wangRow (g,d,i))
      (s.shiftOneAxis (g,d,i) a (x.2 (wangRow (g,d,i))) v))
  let f (i : SelectedSlot S) (a : Bool) (v : ZMod (s.lowAxis (g,d,i) a)) :=
    s.outputAt o (s.observeFallback (g,i,a,false)) (reference i a v)
  let c (i : SelectedSlot S) (b : Fin 3) :=
    s.markerAt o (g,d,i) b (slotLine g x.1) 0
  apply s.mask_fails_of_constant g d S o x f c ?_ ?_ ht
  · intro v i a
    refine s.fallback_factors o g i a (hf i a) _ (reference i a (s.axisInput (g,d,i) a (v.1 i)))
      (s.source_line g d S x v) ?_
    intro d'
    by_cases hd : d' = d
    · subst d'
      rw [s.source_selected g d S x v i]
      dsimp only [reference]
      rw [Function.update_self,s.axisInput_sub,s.axisInput_shiftOneAxis]
    · have hrow : wangRow (g,d',i) ∉ selectedRows g d S := by
        intro hh
        obtain ⟨j,_,he⟩ := Finset.mem_map.mp hh
        exact hd (congrArg (fun a : WangSlot k m => a.2.1) (Sum.inl.inj (Sum.inr.inj he))).symm
      have hne : wangRow (g,d',i) ≠ wangRow (g,d,i) := fun hh =>
        hd (congrArg (fun a : WangSlot k m => a.2.1) (Sum.inl.inj (Sum.inr.inj hh)))
      dsimp only [reference]
      rw [s.source_other g d S x v hrow, Function.update_of_ne hne]
  · intro v i b
    have hs := s.marker_factors o (g,d,i) b (hm i b) (s.source g d S x v)
    rw [s.source_line g d S x v] at hs
    apply hs.trans
    by_contra hne
    obtain ⟨a,ha⟩ := AxisSlot.exists_active_axis (s.lowAxis_coprime (g,d,i))
      (s.markerAt o (g,d,i) b (slotLine g x.1)) ⟨_,0,hne⟩
    exact hn i (a,b) ha

/-- Alphabet index used for the six possible nonconstant axis-marker pairs. -/
def axisLabelEquiv : Fin 6 ≃ AxisSlot.Label :=
  finProdFinEquiv.symm.trans (finTwoEquiv.prodCongr (.refl (Fin 3)))

omit [Fintype (Factor s.layout)] in
theorem exists_word_at (g : Bool) (d : Fin k) (w : ℕ) (hw : w ≤ m)
    (h : ∀ S : Finset (Fin m), S.card = m+1-w →
      ∀ z : ℤ, ∃ i : SelectedSlot S, ∃ b : AxisSlot.Label, s.Active o g d z i b)
    (z : ℤ) :
    ∃ a : SlotWords.Word m w 6,
      SlotWords.Reads (fun i j => s.Active o g d z i (axisLabelEquiv j)) a := by
  apply SlotWords.exists_reads hw
  intro S hS
  obtain ⟨i,b,hb⟩ := h S hS z
  exact ⟨i,i.property,axisLabelEquiv.symm b,by simpa⟩

end Invariance
end
end TranslationTiling.FiniteCompiler.Packed.AxisParameters
