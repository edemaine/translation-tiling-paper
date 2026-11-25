import TranslationTiling.FiniteCompiler.Effective.SlotWordCoordinates

namespace TranslationTiling.FiniteCompiler.Packed.SlotParameters

open PairSmall GuardedCompiler SharedCoordinates Effective
open scoped Classical
noncomputable section

local instance slotDecodeFrame : SeedFrame := compactSeedFrame
set_option maxRecDepth 5000

variable {k m w : ℕ} {T : LeanWang.TileSet} (c : Code T ((slotRadix m w)^k))
local instance slotDecodeAlphabet : AlphabetFamily (system c) := GuardedCompiler.alphabet c
variable (s : SlotParameters k m)

theorem shiftCount_neZero {S : Finset (Fin m)} (hS : S.Nonempty) :
    NeZero (ShiftCount S) := by
  obtain ⟨i,hi⟩ := hS
  have : Nonempty (SlotIndex S) := ⟨⟨⟨i,hi⟩,none⟩⟩
  exact ⟨Fintype.card_ne_zero⟩

def activationTest (g : Bool) (d : Fin k) (S : Finset (Fin m)) (hS : S.Nonempty) :
    Finset (SharedCoordinates.Ambient s.layout) :=
  let _ := shiftCount_neZero hS
  s.mask g d S

theorem selected_nonempty (hw : w ≤ m) {S : Finset (Fin m)} (hS : S.card = m+1-w) :
    S.Nonempty := Finset.card_pos.mp (by omega)

def activationHolds (o : SharedCoordinates.Outputs s.layout) (hw : w ≤ m) : Prop :=
  ∀ g d S (hS : (S : Finset (Fin m)).card = m+1-w),
    Tiles (s.activationTest g d S (selected_nonempty hw hS))
      (Set.range (SharedCoordinates.point s.layout o))

def fallbackHolds (o : SharedCoordinates.Outputs s.layout) : Prop :=
  ∀ g i F, F ∈ s.fallbackTests g i →
    Tiles F (Set.range (SharedCoordinates.point s.layout o))

theorem decode_letters (o : SharedCoordinates.Outputs s.layout) (hw : w ≤ m)
    (hd : s.cycleDependencies o) (hf : s.fallbackHolds o) (ha : s.activationHolds o hw) :
    ∃ W : WordArray (system c), ∀ x i,
      s.letterActive c o x i (W (columnIndex i) (lineValue (system c) (columnIndex i) x)) := by
  have selected (g : Bool) (d : Fin k) (S : Finset (Fin m)) (hS : S.card = m+1-w) (z : ℤ) :
      ∃ i : SelectedSlot S, ∃ b, s.Active o g d z i b := by
    have := shiftCount_neZero (selected_nonempty hw hS)
    have hs := s.mask_forces_active o g d S
      (fun i b => hd.2.2 (g,d,i) b) (fun i => hf g i) (ha g d S hS)
      ((0,z),0)
    simpa [slotLine] using hs
  have hex (n : Fin 20) (z : ℤ) : ∃ a : Letter (system c) n,
      ∀ i, ∀ hi : columnIndex i = n,
        s.letterActive c o (0,z) i (hi.symm ▸ a) := by
    obtain ⟨i,rfl⟩ := columnIndex_bijective.2 n
    have hh : ∃ a, s.letterActive c o (0,z) i a := by
      rcases i with i | g
      · obtain ⟨a,ha⟩ := s.arithmetic_active o hd.1 (arithmeticRow i) i.isLt (0,z)
        refine ⟨(arithmeticLetterEquiv c i).symm a,?_⟩
        change s.labelActive o (0,z) (.inl (arithmeticRow i))
          (arithmeticLetterEquiv c i ((arithmeticLetterEquiv c i).symm a))
        rw [Equiv.apply_symm_apply]
        exact ha
      · choose a ha using fun d => s.exists_word_at o g d w hw (selected g d) z
        refine ⟨(wangLetterEquiv c g).symm a,?_⟩
        intro d
        rw [Equiv.apply_symm_apply]
        simpa [slotLine] using ha d
    obtain ⟨a,ha⟩ := hh
    refine ⟨a,fun j hj => ?_⟩
    obtain rfl := columnIndex_bijective.1 hj
    exact ha
  choose W hW using hex
  refine ⟨W,?_⟩
  intro x i
  have hl := hW (columnIndex i) (lineValue (system c) (columnIndex i) x) i rfl
  rcases i with i | g
  · exact (s.arithmetic_active_on_line c o hd i x _).mpr hl
  · change ∀ d, SlotWords.Reads (s.Active o g d (slotLine g x))
      (wangLetterEquiv c g (W (wangColumn g) (lineValue (system c) (wangColumn g) x)) d)
    rw [wangLine c]
    change ∀ d, SlotWords.Reads
      (s.Active o g d (slotLine g (0,lineValue (system c) (wangColumn g) x)))
      (wangLetterEquiv c g (W (wangColumn g) (lineValue (system c) (wangColumn g) x)) d) at hl
    simpa [slotLine] using hl

end
end TranslationTiling.FiniteCompiler.Packed.SlotParameters
