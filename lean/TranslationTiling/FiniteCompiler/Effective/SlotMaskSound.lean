import TranslationTiling.FiniteCompiler.Effective.SlotMasks

namespace TranslationTiling.FiniteCompiler.Packed.SlotParameters

open SharedCoordinates
open scoped Classical
noncomputable section

variable {k m : ℕ} (s : SlotParameters k m) (g : Bool) (d : Fin k)
  (S : Finset (Fin m)) [NeZero (ShiftCount S)]

private def independentInput (i : SlotIndex S) : Type :=
  match i with
  | (i,none) => ZMod (s.low (g,d,i))
  | (_,some _) => Unit

private instance (i : SlotIndex S) : Fintype (independentInput s g d S i) := by
  rcases i with ⟨i,_ | _⟩
  · change Fintype (ZMod (s.low (g,d,i)))
    infer_instance
  · exact inferInstanceAs (Fintype Unit)

private def dropSingletons : (∀ i, independentInput s g d S i) ≃ LowShifts s g d S where
  toFun f i := f (i,none)
  invFun f
    | (i,none) => f i
    | (_,some _) => ()
  left_inv f := by
    funext i
    rcases i with ⟨i,_ | j⟩
    · rfl
    · exact Subsingleton.elim (α := Unit) _ _
  right_inv _ := rfl

private def independentEquiv :
    (∀ j, independentInput s g d S (shiftIndex S j)) ≃ LowShifts s g d S :=
  (Equiv.piCongrLeft (independentInput s g d S) (shiftIndex S)).trans (dropSingletons s g d S)

omit [NeZero (ShiftCount S)] in
private theorem independentModulus (i : SlotIndex S) :
    ¬ s.observationPrime g d i ∣ Fintype.card (independentInput s g d S i) := by
  rcases i with ⟨i,_ | b⟩
  · change ¬ s.fallback (g,i,false) ∣ Fintype.card (ZMod (s.low (g,d,i)))
    rw [ZMod.card]
    have ha := s.prime_isPrime (.inr (g,i,false))
    have hr := s.prime_isPrime (.inl ((g,d,i),none))
    have hne : s.fallback (g,i,false) ≠ s.low (g,d,i) := by
      intro he
      cases s.prime_injective he
    exact ha.coprime_iff_not_dvd.mp ((Nat.coprime_primes ha hr).mpr hne)
  · have hp := s.prime_isPrime (.inl ((g,d,i),some b))
    change ¬ s.marker (g,d,i) b ∣ Fintype.card Unit
    rw [Fintype.card_unit]
    exact Nat.not_dvd_of_pos_of_lt Nat.one_pos hp.one_lt

/-- If the observed private outputs are constant on the tested slice,
independence of the fallback outputs prevents exact coverage. -/
theorem mask_fails_of_constant [Fintype (Factor s.layout)]
    (o : SharedCoordinates.Outputs s.layout) (x : SharedCoordinates.Base s.layout)
    (f : ∀ i : SelectedSlot S, ZMod (s.low (g,d,i)) → ZMod (s.fallback (g,i,false)))
    (c : ∀ i : SelectedSlot S, ∀ b : Fin 3, ZMod (s.marker (g,d,i) b))
    (hf : ∀ v (i : SelectedSlot S), s.observeFallback (g,i,false)
      (SharedCoordinates.point s.layout o (s.source g d S x v)).2 = f i (v.1 i))
    (hc : ∀ v (i : SelectedSlot S) b, s.observeMarker (g,d,i) b
      (SharedCoordinates.point s.layout o (s.source g d S x v)).2 = c i b) :
    ¬ Tiles (s.mask g d S) (Set.range (SharedCoordinates.point s.layout o)) := by
  intro ht
  let K := fun j : ZMod (ShiftCount S) => independentInput s g d S (shiftIndex S j)
  let E := independentEquiv s g d S
  let W (i : SlotIndex S) : independentInput s g d S i → ZMod (s.observationPrime g d i) :=
    match i with
    | (i,none) => f i
    | (i,some b) => fun _ => c i b
  let H (v : (∀ j, K j) × ShiftType s g d S) : ∀ j, K j :=
    E.symm (fun i => o.high (s.source g d S x (E v.1,v.2)) (wangRow (g,d,i)))
  apply SlotShift.independent_inputs_not_bijective (fun j => (s.shiftModulus_prime g d S j).one_lt)
    (fun j => independentModulus s g d S (shiftIndex S j)) (fun j => W (shiftIndex S j)) H
  have hb := (s.mask_iff g d S o).mp ht x
  let e := E.prodCongr (Equiv.refl (ShiftType s g d S))
  let e' := (Equiv.refl (ShiftType s g d S)).prodCongr E.symm
  have he := e'.bijective.comp (hb.comp e.bijective)
  convert he using 1
  funext v
  let y : ShiftType s g d S := fun j => W (shiftIndex S j) (v.1 j)
  change (y + SlotShift.shift v.2,H v) =
    (s.projection g d S (SharedCoordinates.point s.layout o
      (s.source g d S x (E v.1,v.2))).2 + SlotShift.shift v.2,H v)
  refine Prod.ext ?_ rfl
  apply congrArg (· + SlotShift.shift v.2)
  funext j
  have hv := Equiv.piCongrLeft_apply_apply (independentInput s g d S) (shiftIndex S) v.1 j
  let a := Equiv.piCongrLeft (independentInput s g d S) (shiftIndex S) v.1
  change a (shiftIndex S j) = v.1 j at hv
  change W (shiftIndex S j) (v.1 j) =
    s.observe g d (shiftIndex S j) (SharedCoordinates.point s.layout o
      (s.source g d S x (E v.1,v.2))).2
  rw [← hv]
  have hW (z : SlotIndex S) :
      W z (a z) = s.observe g d z (SharedCoordinates.point s.layout o
        (s.source g d S x (E v.1,v.2))).2 := by
    rcases z with ⟨i,_ | b⟩
    · exact (hf (E v.1,v.2) i).symm
    · exact (hc (E v.1,v.2) i b).symm
  exact hW (shiftIndex S j)

end
end TranslationTiling.FiniteCompiler.Packed.SlotParameters
