import TranslationTiling.FiniteCompiler.Effective.SlotWordCoordinates

namespace TranslationTiling.FiniteCompiler.Packed.SlotParameters

open PairSmall GuardedCompiler SharedCoordinates Effective
open scoped Classical
noncomputable section

local instance slotGuardMasksFrame : SeedFrame := compactSeedFrame
set_option maxRecDepth 5000

variable {k m w : ℕ} {T : LeanWang.TileSet} (c : Code T ((slotRadix m w)^k))
local instance slotGuardMasksAlphabet : AlphabetFamily (system c) := GuardedCompiler.alphabet c

private abbrev APart (p : PartialTest (system c)) :=
  {i : Fin 18 // arithmeticColumn i ∈ p.columns}

abbrev WColumn (p : PartialTest (system c)) := {g : Bool // wangColumn g ∈ p.columns}

def patternDigit (p : PartialTest (system c)) (g : WColumn c p) (d : Fin k) :
    SlotWords.Word m w 3 :=
  wangLetterEquiv c g.val (p.label ⟨wangColumn g.val,g.property⟩) d

private abbrev WPart (p : PartialTest (system c)) :=
  Σ g : WColumn c p, Σ d : Fin k, ↥(patternDigit c p g d).1.val

abbrev Support (p : PartialTest (system c)) := APart c p ⊕ WPart c p

def patternRow (p : PartialTest (system c)) : Support c p → SlotRow k m
  | .inl i => .inl (arithmeticRow i.val)
  | .inr ⟨g,d,i⟩ => wangRow (g.val,d,i.val)

theorem patternRow_inj (p : PartialTest (system c)) :
    Function.Injective (patternRow c p) := by
  rintro (i | ⟨g,d,i⟩) (j | ⟨h,e,j⟩) he
  · apply congrArg Sum.inl
    apply Subtype.ext
    have hh : arithmeticRow i.val = arithmeticRow j.val := Sum.inl.inj he
    exact Fin.ext (congrArg (fun a : FourValueRow 0 => a.val) hh)
  · cases he
  · cases he
  · have hs : (g.val,d,i.val) = ((h.val,e,j.val) : WangSlot k m) :=
      Sum.inl.inj (Sum.inr.inj he)
    have hg : g = h := Subtype.ext (congrArg Prod.fst hs)
    subst h
    have hd : d = e := congrArg (fun v : WangSlot k m => v.2.1) hs
    subst e
    have hi : i = j := Subtype.ext (congrArg (fun v : WangSlot k m => v.2.2) hs)
    subst j
    rfl

def patternLabel (p : PartialTest (system c)) (i : Support c p) :
    RowLabel (patternRow c p i) :=
  match i with
  | .inl i => arithmeticLetterEquiv c i.val (p.label ⟨arithmeticColumn i.val,i.property⟩)
  | .inr ⟨g,d,i⟩ => (patternDigit c p g d).2 i

theorem support_nonempty (p : PartialTest (system c)) (hp : p ∈ patterns c) :
    Nonempty (Support c p) := by
  obtain ⟨i,hi,hm⟩ := patterns_has_arithmetic c p hp
  exact ⟨.inl ⟨⟨i.val,hi⟩,hm⟩⟩

variable (s : SlotParameters k m)

theorem patternActive_iff (p : PartialTest (system c))
    (o : SharedCoordinates.Outputs s.layout) (x : Plane) :
    (∀ a : Support c p, s.labelActive o x (patternRow c p a) (patternLabel c p a)) ↔
      ∀ i (hi : columnIndex i ∈ p.columns),
        s.letterActive c o x i (p.label ⟨columnIndex i,hi⟩) := by
  constructor
  · intro h i hi
    rcases i with i | g
    · exact h (.inl ⟨i,hi⟩)
    · intro d j
      exact (s.labelActive_wang o x (g,d,j.val) _).mp (h (.inr ⟨⟨g,hi⟩,d,j⟩))
  · intro h i
    rcases i with i | ⟨g,d,j⟩
    · exact h (.inl i.val) i.property
    · exact (s.labelActive_wang o x (g.val,d,j.val) _).mpr (h (.inr g.val) g.property d j)

theorem exists_guardMask (p : PartialTest (system c)) (hp : p ∈ patterns c) :
    ∃ F : Finset (SharedCoordinates.Ambient s.layout),
      (∀ x ∈ F, x.1 = 0) ∧
      (∃ o : SharedCoordinates.Outputs s.layout, Tiles F (Set.range (SharedCoordinates.point s.layout o))) ∧
      ∀ (o : SharedCoordinates.Outputs s.layout), s.cycleDependencies o →
        (Tiles F (Set.range (SharedCoordinates.point s.layout o)) ↔
          ∀ x, ¬ (∀ i (hi : columnIndex i ∈ p.columns),
            s.letterActive c o x i (p.label ⟨columnIndex i,hi⟩))) := by
  have := support_nonempty c p hp
  let rows : Support c p ↪ SlotRow k m := ⟨patternRow c p,patternRow_inj c p⟩
  obtain ⟨F,hF,hmass,h⟩ := s.exists_pattern_mask rows (patternLabel c p)
  refine ⟨F,hF,hmass,fun o ho => ?_⟩
  rw [h o ho]
  simp only [← s.patternActive_iff c p o,not_forall]
  rfl

def seedRow (t : Fin 2) (i : Fin 18) (b : Bool) : SlotRow k m :=
  .inl (if b then fourValueSeedRow 0 t else arithmeticRow i)

theorem seedRow_inj (t : Fin 2) (i : Fin 18) :
    Function.Injective (seedRow (k := k) (m := m) t i) := by
  intro b b' h
  have distinct : (arithmeticRow i).val < (fourValueSeedRow 0 t).val := by
    change i.val < (fourValueSeedRow 0 t).val
    rw [fourValueSeedRow_val]
    have := i.isLt
    omega
  cases b <;> cases b'
  · rfl
  · exact False.elim (distinct.ne (congrArg Fin.val (Sum.inl.inj h)))
  · exact False.elim (distinct.ne (congrArg Fin.val (Sum.inl.inj h)).symm)
  · rfl

def seedTestLabel (t : Fin 2) (i : Fin 18)
    (a : Letter (system c) (arithmeticColumn i)) :
    (b : Bool) → RowLabel (seedRow (k := k) (m := m) t i b)
  | true => seedLabel t
  | false => arithmeticLetterEquiv c i a

theorem exists_seedMask (t : Fin 2) (i : Fin 18) (a : Letter (system c) (arithmeticColumn i)) :
    ∃ F : Finset (SharedCoordinates.Ambient s.layout),
      (∀ x ∈ F, x.1 = 0) ∧
      (∃ o : SharedCoordinates.Outputs s.layout, Tiles F (Set.range (SharedCoordinates.point s.layout o))) ∧
      ∀ (o : SharedCoordinates.Outputs s.layout), s.cycleDependencies o →
        (Tiles F (Set.range (SharedCoordinates.point s.layout o)) ↔
          ∀ x, ¬ (s.labelActive o x (.inl (fourValueSeedRow 0 t)) (seedLabel t) ∧
            s.letterActive c o x (.inl i) a)) := by
  let rows : Bool ↪ SlotRow k m := ⟨seedRow t i,seedRow_inj t i⟩
  obtain ⟨F,hF,hmass,h⟩ := s.exists_pattern_mask rows (seedTestLabel c t i a)
  refine ⟨F,hF,hmass,fun o ho => ?_⟩
  rw [h o ho]
  constructor
  · intro h x hx
    obtain ⟨b,hb⟩ := h x
    cases b
    · exact hb hx.2
    · exact hb hx.1
  · intro h x
    by_cases hseed : s.labelActive o x (.inl (fourValueSeedRow 0 t)) (seedLabel t)
    · exact ⟨false,fun ha => h x ⟨hseed,ha⟩⟩
    · exact ⟨true,hseed⟩

end
end TranslationTiling.FiniteCompiler.Packed.SlotParameters
