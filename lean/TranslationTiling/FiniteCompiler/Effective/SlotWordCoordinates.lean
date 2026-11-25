import TranslationTiling.FiniteCompiler.Effective.SlotWordBridge
import TranslationTiling.FiniteCompiler.Effective.SlotPatternCycle

namespace TranslationTiling.FiniteCompiler.Packed.SlotParameters

open PairSmall GuardedCompiler SharedCoordinates Effective
open scoped Classical
noncomputable section

local instance slotWordCoordinatesFrame : SeedFrame := compactSeedFrame

def columnIndex : Fin 18 ⊕ Bool → Fin 20 :=
  Sum.elim arithmeticColumn wangColumn

theorem columnIndex_bijective : Function.Bijective columnIndex := by
  decide +kernel

variable {k m w : ℕ} {T : LeanWang.TileSet} (c : Code T ((slotRadix m w)^k))
local instance slotWordCoordinatesAlphabet : AlphabetFamily (system c) := GuardedCompiler.alphabet c

def arithmeticLetterEquiv (i : Fin 18) :
    Letter (system c) (arithmeticColumn i) ≃ FourValueLabel (arithmeticRow i) :=
  finCongr (arithmetic_arity _ i).symm

private theorem wangArity (g : Bool) : PairSmall.arity ((slotRadix m w)^k) (wangColumn g) =
    (slotRadix m w)^k := by
  cases g <;> rfl

def wangLetterEquiv (g : Bool) :
    Letter (system c) (wangColumn g) ≃ (Fin k → SlotWords.Word m w 3) :=
  (finCongr (wangArity (k := k) (m := m) (w := w) g)).trans (slotWordEquiv k m w)

theorem arithmeticLine (i : Fin 18) (x : Plane) :
    fourValueLineValue (arithmeticRow i) x = lineValue (system c) (arithmeticColumn i) x := by
  simp only [fourValueLineValue,lineValue,arithmetic_slope]

theorem wangLine (g : Bool) (x : Plane) :
    slotLine g x = lineValue (system c) (wangColumn g) x := by
  simp only [slotLine,lineValue,wang_slope,slopeNumber]

variable (s : SlotParameters k m)

theorem arithmetic_active_on_line (o : SharedCoordinates.Outputs s.layout)
    (hd : s.cycleDependencies o) (i : Fin 18) (x : Plane) (a : FourValueLabel (arithmeticRow i)) :
    s.labelActive o x (.inl (arithmeticRow i)) a ↔
      s.labelActive o (0,lineValue (system c) (arithmeticColumn i) x) (.inl (arithmeticRow i)) a := by
  have he : s.rowFunction o x (.inl (arithmeticRow i)) a =
      s.rowFunction o (0,lineValue (system c) (arithmeticColumn i) x) (.inl (arithmeticRow i)) a := by
    funext u
    apply (s.arithmetic_dependence o hd.1 0).privateAt_line
    · change i.val < (fourValueRows 0).length-2
      rw [fourValueRows_length]
      exact i.isLt
    · rw [← arithmeticLine c]
      simp [fourValueLineValue]
  unfold labelActive
  rw [he]

def seedLabel (t : Fin 2) : FourValueLabel (fourValueSeedRow 0 t) :=
  ⟨0,by rw [seedRow_digits]; decide⟩

theorem seedLabel_active (o : SharedCoordinates.Outputs s.layout) (t : Fin 2) (x : Plane) :
    s.labelActive o x (.inl (fourValueSeedRow 0 t)) (seedLabel t) ↔
      DigitActive (fourValuePrivateAt (s.oldSlice o 0) x (fourValueSeedRow 0 t)) ⊤ := by
  have ht : fourValueDigitSubgroup (fourValueSeedRow 0 t) (seedLabel t) = ⊤ := by
    ext z
    simp only [fourValueDigitSubgroup_iff,AddSubgroup.mem_top,iff_true]
    intro j hj
    exfalso
    apply hj
    apply Fin.ext
    have hh := j.isLt
    have hd := seedRow_digits (k := 0) t
    change j.val = 0
    omega
  change DigitActive _ (fourValueDigitSubgroup _ _) ↔ _
  rw [ht]
  rfl

/-- Reading a letter means that each of its selected rows is active. -/
def letterActive (o : SharedCoordinates.Outputs s.layout) (x : Plane) :
    (i : Fin 18 ⊕ Bool) → Letter (system c) (columnIndex i) → Prop
  | .inl i, a => s.labelActive o x (.inl (arithmeticRow i)) (arithmeticLetterEquiv c i a)
  | .inr g, a => ∀ d, SlotWords.Reads (s.Active o g d (slotLine g x)) (wangLetterEquiv c g a d)

end
end TranslationTiling.FiniteCompiler.Packed.SlotParameters
