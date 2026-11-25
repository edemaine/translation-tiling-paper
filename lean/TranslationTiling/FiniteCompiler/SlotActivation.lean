import TranslationTiling.FiniteCompiler.SlotActivationBatch
import TranslationTiling.FiniteCompiler.SlotActivationComplete
import TranslationTiling.FiniteCompiler.SlotActivationOffsets
import TranslationTiling.FiniteCompiler.SlotActivationSound

namespace TranslationTiling.FiniteCompiler.SharedCoordinates

open scoped Classical

noncomputable section

variable {I : Type*} [Fintype I] (L : Layout I) (S : Finset I)
variable {d : ℕ} [NeZero d] {m : ZMod d → ℕ} [∀ j, NeZero (m j)]

abbrev SlotHigh := ∀ i : {i : I // i ∈ S}, Low L i

/-- The activation mask in the finite group, indexed by a low shift for
each selected slot and a shift in the observed useful outputs. -/
def selectedSlotTile [Fintype (Factor L)]
    (ψ : Factor L →+ SlotShift.Shift m) (h : SlotHigh L S × SlotShift.Shift m → Plane) :
    Finset (Ambient L) :=
  slotActivationTile L S ψ h (fun v => SlotShift.shift v.2)

theorem selectedSlotTile_iff [Fintype (Factor L)]
    (ψ : Factor L →+ SlotShift.Shift m) (h : SlotHigh L S × SlotShift.Shift m → Plane)
    (hh : Function.Injective h) (o : Outputs L)
    (htarget : ∀ x : Base L, ∀ y : SlotShift.Shift m × SlotHigh L S, ∃ v : Ambient L,
      baseProjection L v = x ∧ (ψ v.2,fun i : {i : I // i ∈ S} => highCoordinate L i v) = y) :
    Tiles (selectedSlotTile L S ψ h) (Set.range (point L o)) ↔
      ∀ x, Function.Bijective (fun v =>
        let u := slotActivationSource L S (h v) x
        (ψ (point L o u).2 + SlotShift.shift v.2, fun i : {i : I // i ∈ S} => o.high u i)) :=
  slotActivationTile_iff L S ψ h hh _ o htarget

/-- The mask tiles when the high outputs identify blocks whose
observed coordinates restore a nonempty set of the shift coordinates. -/
theorem selectedSlotTile_of_blocks [Fintype (Factor L)] (hm : ∀ j, 1 < m j)
    (ψ : Factor L →+ SlotShift.Shift m) (h : SlotHigh L S × SlotShift.Shift m → Plane)
    (hh : Function.Injective h) (o : Outputs L)
    (htarget : ∀ x : Base L, ∀ y : SlotShift.Shift m × SlotHigh L S, ∃ v : Ambient L,
      baseProjection L v = x ∧ (ψ v.2,fun i : {i : I // i ∈ S} => highCoordinate L i v) = y)
    (high : Base L → SlotShift.Shift m → SlotHigh L S ≃ SlotHigh L S)
    (R : Base L → SlotHigh L S → Set (ZMod d))
    (hne : ∀ x k, (R x k).Nonempty) (c : Base L → SlotHigh L S → SlotShift.Shift m)
    (hblock : ∀ x v,
      let u := slotActivationSource L S (h v) x
      let k := high x v.2 v.1
      (ψ (point L o u).2 + SlotShift.shift v.2, fun i : {i : I // i ∈ S} => o.high u i) =
        (c x k + SlotShift.restore (R x k) v.2,k)) :
    Tiles (selectedSlotTile L S ψ h) (Set.range (point L o)) := by
  apply (selectedSlotTile_iff L S ψ h hh o htarget).mpr
  intro x
  rw [funext (hblock x)]
  exact SlotShift.block_map_bijective hm (high x) (R x) (hne x) (c x)

/-- If the useful outputs split into independent inputs on some base
fibre, then the positive mask cannot tile. Typically the private
outputs are constant and the fallback outputs read separate slots. -/
theorem selectedSlotTile_obstructed [Fintype (Factor L)] (hm : ∀ j, 1 < m j)
    {K : ZMod d → Type*} [∀ j, Fintype (K j)]
    (hdiv : ∀ j, ¬ m j ∣ Fintype.card (K j))
    (index : (∀ j, K j) ≃ SlotHigh L S)
    (ψ : Factor L →+ SlotShift.Shift m) (h : SlotHigh L S × SlotShift.Shift m → Plane)
    (hh : Function.Injective h) (o : Outputs L)
    (htarget : ∀ x : Base L, ∀ y : SlotShift.Shift m × SlotHigh L S, ∃ v : Ambient L,
      baseProjection L v = x ∧ (ψ v.2,fun i : {i : I // i ∈ S} => highCoordinate L i v) = y)
    (x : Base L) (c : ∀ j, K j → ZMod (m j))
    (hsep : ∀ (v : (∀ j, K j) × SlotShift.Shift m),
      ψ (point L o (slotActivationSource L S (h (index v.1,v.2)) x)).2 =
        fun j => c j (v.1 j)) :
    ¬ Tiles (selectedSlotTile L S ψ h) (Set.range (point L o)) := by
  intro ht
  let H (v : (∀ j, K j) × SlotShift.Shift m) : ∀ j, K j :=
    index.symm (fun i => o.high (slotActivationSource L S (h (index v.1,v.2)) x) i)
  apply SlotShift.independent_inputs_not_bijective hm hdiv c H
  let e := index.prodCongr (Equiv.refl (SlotShift.Shift m))
  let e' := (Equiv.refl (SlotShift.Shift m)).prodCongr index.symm
  have hb := (selectedSlotTile_iff L S ψ h hh o htarget).mp ht x
  have hcomp := e'.bijective.comp (hb.comp e.bijective)
  convert hcomp using 1
  funext v
  apply Prod.ext
  · exact congrArg (· + SlotShift.shift v.2) (hsep v).symm
  · rfl

end

end TranslationTiling.FiniteCompiler.SharedCoordinates
