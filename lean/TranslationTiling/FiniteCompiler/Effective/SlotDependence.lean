import TranslationTiling.FiniteCompiler.Effective.SlotMaskSound
import TranslationTiling.FiniteCompiler.Effective.SlotInvariance
import TranslationTiling.FiniteCompiler.SlotWords

namespace TranslationTiling.FiniteCompiler.Packed.SlotParameters

open SharedCoordinates
open scoped Classical
noncomputable section

variable {k m : ℕ} (s : SlotParameters k m)

def controls (g : Bool) (i : Fin m) : Set (SlotRow k m) :=
  Set.range fun d : Fin k => wangRow (g,d,i)

def outputAt {Y : Type*} [AddCommGroup Y] (o : SharedCoordinates.Outputs s.layout)
    (ψ : Factor s.layout →+ Y) (x : SharedCoordinates.Base s.layout) : Y :=
  ψ (SharedCoordinates.point s.layout o x).2

def markerAt (o : SharedCoordinates.Outputs s.layout)
    (i : WangSlot k m) (j : Fin 3) (line : ℤ) (v : ZMod (s.low i)) :=
  s.outputAt o (s.observeMarker i j)
    ((0,line),Function.update 0 (wangRow i)
      (show SharedCoordinates.Low s.layout (wangRow i) from v))

def Active (o : SharedCoordinates.Outputs s.layout)
    (g : Bool) (d : Fin k) (line : ℤ) (i : Fin m) (j : Fin 3) : Prop :=
  ∃ u v, s.markerAt o (g,d,i) j line u ≠ s.markerAt o (g,d,i) j line v

section Invariance
variable [Fintype (Factor s.layout)]

def markerTests (i : WangSlot k m) (j : Fin 3) :
    List (Finset (SharedCoordinates.Ambient s.layout)) :=
  productInvariance s.layout (s.observeMarker i j) ((1,-slopeNumber i.1),0) ::
    ((Finset.univ.erase (wangRow i)).toList.map fun a =>
      productInvariance s.layout (s.observeMarker i j) (lowStep s.layout a))

def fallbackTests (g : Bool) (i : Fin m) :
    List (Finset (SharedCoordinates.Ambient s.layout)) :=
  productInvariance s.layout (s.observeFallback (g,i,false)) ((1,-slopeNumber g),0) ::
    ((Finset.univ.filter fun a => a ∉ controls g i).toList.map fun a =>
      productInvariance s.layout (s.observeFallback (g,i,false)) (lowStep s.layout a))

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

theorem fallback_factors (g : Bool) (i : Fin m)
    (h : ∀ F ∈ s.fallbackTests g i, Holds F)
    (x y : SharedCoordinates.Base s.layout)
    (hline : slotLine g x.1 = slotLine g y.1)
    (hkeep : ∀ d : Fin k, x.2 (wangRow (g,d,i)) = y.2 (wangRow (g,d,i))) :
    s.outputAt o (s.observeFallback (g,i,false)) x = s.outputAt o (s.observeFallback (g,i,false)) y := by
  let f := s.outputAt o (s.observeFallback (g,i,false))
  have hs := (productInvariance_iff s.layout _ _ o).mp (h _
    (List.mem_cons_self ..))
  have hl : ∀ a ∉ controls g i, ∀ x, f (x-lowStep s.layout a) = f x := by
    intro a ha
    exact (productInvariance_iff s.layout _ _ o).mp
      (h _ (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨a,by simpa using ha,rfl⟩)))
  have hx := factor_line s.layout f (slopeNumber g) hs x.1 x.2
  have hy := factor_line s.layout f (slopeNumber g) hs y.1 y.2
  change f x = f ((0,slotLine g x.1),x.2) at hx
  change f y = f ((0,slotLine g y.1),y.2) at hy
  change f x = f y
  rw [hx,hy,hline]
  exact factor_selected_lows s.layout f (controls g i) hl _ _ _ (by
    rintro a ⟨d,rfl⟩
    exact hkeep d)

/-- A selected-slot mask forces a varying marker in at least one of
its tested slots on every line. -/
theorem mask_forces_active (g : Bool) (d : Fin k) (S : Finset (Fin m))
    [NeZero (ShiftCount S)]
    (hm : ∀ i : SelectedSlot S, ∀ b, ∀ F ∈ s.markerTests (g,d,i) b, Holds F)
    (hf : ∀ i : SelectedSlot S, ∀ F ∈ s.fallbackTests g i, Holds F)
    (ht : Holds (s.mask g d S)) (x : SharedCoordinates.Base s.layout) :
    ∃ i : SelectedSlot S, ∃ b : Fin 3, s.Active o g d (slotLine g x.1) i b := by
  by_contra! hn
  let reference (i : SelectedSlot S) (a : ZMod (s.low (g,d,i))) :
      SharedCoordinates.Base s.layout :=
    (x.1,Function.update x.2 (wangRow (g,d,i))
      (x.2 (wangRow (g,d,i)) - (show SharedCoordinates.Low s.layout (wangRow (g,d,i)) from a)))
  let f (i : SelectedSlot S) (a : ZMod (s.low (g,d,i))) :=
    s.outputAt o (s.observeFallback (g,i,false)) (reference i a)
  let c (i : SelectedSlot S) (b : Fin 3) :=
    s.markerAt o (g,d,i) b (slotLine g x.1) 0
  apply s.mask_fails_of_constant g d S o x f c ?_ ?_ ht
  · intro v i
    refine s.fallback_factors o g i (hf i) _ (reference i (v.1 i)) (s.source_line g d S x v) ?_
    intro d'
    by_cases hd : d' = d
    · subst d'
      exact (s.source_selected g d S x v i).trans (Function.update_self ..).symm
    · have hrow : wangRow (g,d',i) ∉ selectedRows g d S := by
        intro hh
        obtain ⟨j,_,he⟩ := Finset.mem_map.mp hh
        exact hd (congrArg (fun a : WangSlot k m => a.2.1) (Sum.inl.inj (Sum.inr.inj he))).symm
      have hne : wangRow (g,d',i) ≠ wangRow (g,d,i) := fun hh =>
        hd (congrArg (fun a : WangSlot k m => a.2.1) (Sum.inl.inj (Sum.inr.inj hh)))
      exact (s.source_other g d S x v hrow).trans (Function.update_of_ne hne ..).symm
  · intro v i b
    have hs := s.marker_factors o (g,d,i) b (hm i b) (s.source g d S x v)
    rw [s.source_line g d S x v] at hs
    exact hs.trans (by
      by_contra hne
      exact hn i b ⟨_,0,hne⟩)

omit [Fintype (Factor s.layout)] in
theorem exists_word_at (g : Bool) (d : Fin k) (w : ℕ) (hw : w ≤ m)
    (h : ∀ S : Finset (Fin m), S.card = m+1-w →
      ∀ z : ℤ, ∃ i : SelectedSlot S, ∃ b : Fin 3, s.Active o g d z i b)
    (z : ℤ) :
    ∃ a : SlotWords.Word m w 3, SlotWords.Reads (s.Active o g d z) a := by
  apply SlotWords.exists_reads hw
  intro S hS
  obtain ⟨i,b,hb⟩ := h S hS z
  exact ⟨i,i.property,b,hb⟩

end Invariance
end
end TranslationTiling.FiniteCompiler.Packed.SlotParameters
