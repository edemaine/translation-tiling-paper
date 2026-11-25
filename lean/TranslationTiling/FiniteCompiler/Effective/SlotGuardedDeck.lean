import TranslationTiling.FiniteCompiler.Effective.SlotGuardMasks
import TranslationTiling.FiniteCompiler.Effective.SlotCompleteness

namespace TranslationTiling.FiniteCompiler.Packed.SlotParameters

open PairSmall GuardedCompiler SharedCoordinates Effective
open scoped Classical
noncomputable section

local instance slotGuardedDeckFrame : SeedFrame := compactSeedFrame
set_option maxRecDepth 6000
set_option maxHeartbeats 4000000

variable {k m w : ℕ} {T : LeanWang.TileSet} (c : Code T ((slotRadix m w)^k))
local instance slotGuardedDeckAlphabet : AlphabetFamily (system c) := GuardedCompiler.alphabet c
variable (s : SlotParameters k m)

def guardMask (p : PartialTest (system c)) (hp : p ∈ patterns c) :=
  (s.exists_guardMask c p hp).choose

theorem guardMask_spec (p : PartialTest (system c)) (hp : p ∈ patterns c) (o : SharedCoordinates.Outputs s.layout) (hd : s.cycleDependencies o) :
    Tiles (s.guardMask c p hp) (Set.range (SharedCoordinates.point s.layout o)) ↔
      ∀ x, ¬ (∀ i (hi : columnIndex i ∈ p.columns),
        s.letterActive c o x i (p.label ⟨columnIndex i,hi⟩)) :=
  (s.exists_guardMask c p hp).choose_spec.2.2 o hd

def seedMask (t : Fin 2) (i : Fin 18) (a : Letter (system c) (arithmeticColumn i)) :=
  (s.exists_seedMask c t i a).choose

theorem seedMask_spec (t : Fin 2) (i : Fin 18) (a : Letter (system c) (arithmeticColumn i))
    (o : SharedCoordinates.Outputs s.layout) (hd : s.cycleDependencies o) :
    Tiles (s.seedMask c t i a) (Set.range (SharedCoordinates.point s.layout o)) ↔
      ∀ x, ¬ (s.labelActive o x (.inl (fourValueSeedRow 0 t)) (seedLabel t) ∧
        s.letterActive c o x (.inl i) a) :=
  (s.exists_seedMask c t i a).choose_spec.2.2 o hd

def slotGuardsHold (o : SharedCoordinates.Outputs s.layout) : Prop :=
  ∀ p (hp : p ∈ patterns c),
    Tiles (s.guardMask c p hp) (Set.range (SharedCoordinates.point s.layout o))

def slotSeedsHold (o : SharedCoordinates.Outputs s.layout) : Prop :=
  ∀ t i a, ¬ LetterSeedSet (system c) t (arithmeticColumn i) a →
    Tiles (s.seedMask c t i a) (Set.range (SharedCoordinates.point s.layout o))

theorem slot_sound (hwm : w ≤ m) (o : SharedCoordinates.Outputs s.layout)
    (hd : s.cycleDependencies o) (hf : s.fallbackHolds o) (ha : s.activationHolds o hwm)
    (hs : s.slotSeedsHold c o) (hp : s.slotGuardsHold c o) : LeanWang.TilesPlane T := by
  obtain ⟨W,hW⟩ := s.decode_letters c o hwm hd hf ha
  apply guarded_of_slot_selection c W
  · intro t
    obtain ⟨x,hx⟩ := s.arithmetic_seed_active o hd.1 t
    refine ⟨x,fun n => ?_⟩
    obtain ⟨i,rfl⟩ := columnIndex_bijective.2 n
    rcases i with i | g
    · by_contra hn
      exact (s.seedMask_spec c t i _ o hd).mp (hs _ _ _ hn) x
        ⟨(s.seedLabel_active o t x).mpr hx,hW x (.inl i)⟩
    · exact wang_has_all_seed_labels c g t _
  · intro x p hpat _ hm
    apply (s.guardMask_spec c p hpat o hd).mp (hp p hpat) x
    intro i hi
    simpa only [hm ⟨columnIndex i,hi⟩] using hW x i

theorem slot_complete (hwm : w ≤ m) (h : LeanWang.TilesPlane T) :
    ∃ o : SharedCoordinates.Outputs s.layout,
      s.cycleDependencies o ∧ s.fallbackHolds o ∧ s.activationHolds o hwm ∧
        s.slotSeedsHold c o ∧ s.slotGuardsHold c o := by
  obtain ⟨W,hW,hseed⟩ := exists_wordArray_of_wang c h
  let p := arithmeticPicker c W
  let q := wordPicker c W
  let o := s.slotModel (fourValueModel p) q
  have hd := s.model_dependencies p q
  refine ⟨o,hd,s.model_fallbackTests (fourValueModel p) q,s.model_activations c W hwm,?_,?_⟩
  · intro t i a ha
    apply (s.seedMask_spec c t i a o hd).mpr
    intro x hx
    have hz := (s.seedLabel_active o t x).mp hx.1
    change DigitActive (fourValuePrivateAt (s.oldSlice (s.slotModel (fourValueModel p) q) 0) x
      (fourValueSeedRow 0 t)) ⊤ at hz
    rw [s.slice_model] at hz
    have hr := (fourValueModel_seed_active p t x).mp hz
    have he := (s.model_letter c W x (.inl i) a).mp hx.2
    exact ha (he.symm ▸ hseed t (arithmeticColumn i) x hr)
  · intro b hb
    apply (s.guardMask_spec c b hb o hd).mpr
    intro x hx
    apply patterns_sound c b hb _ (hW x)
    intro i
    obtain ⟨j,hj⟩ := columnIndex_bijective.2 i.val
    have hi : columnIndex j ∈ b.columns := hj.symm ▸ i.property
    have he := ((s.model_letter c W x j _).mp (hx j hi)).symm
    have hsub : (⟨columnIndex j,hi⟩ : ↥b.columns) = i := Subtype.ext hj
    change W i.val (lineValue (system c) i.val x) = b.label i
    exact (congrArg (fun u : ↥b.columns =>
      W u.val (lineValue (system c) u.val x) = b.label u) hsub) ▸ he

end
end TranslationTiling.FiniteCompiler.Packed.SlotParameters
