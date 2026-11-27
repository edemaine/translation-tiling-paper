import TranslationTiling.FiniteCompiler.Effective.AxisSlotRankedWords
import TranslationTiling.FiniteCompiler.Effective.SlotWordBridge
import TranslationTiling.FiniteCompiler.GuardedSystem
import TranslationTiling.FiniteCompiler.Effective.PackedPatternCorrect
import TranslationTiling.FiniteCompiler.Effective.FourValueDigits

namespace TranslationTiling.FiniteCompiler.Packed

open PairSmall GuardedCompiler Effective
open scoped Classical

noncomputable section

local instance axisWordFrame : SeedFrame := compactSeedFrame

def axisRadix (m w : ℕ) := m.choose w * 6^w

/-- Choose the number of seven-slot groups. -/
def axisLengthParameter (n : ℕ) : ℕ :=
  let b := Nat.log 2 (Nat.log 2 n)
  max 1 (b * Nat.log 2 b / 7)

def axisPackedDigits (n t : ℕ) : ℕ := max 1 (Nat.clog (axisRadix (7*t) (6*t)) n)

theorem axisRadix_one_lt {t : ℕ} (ht : 0 < t) : 1 < axisRadix (7*t) (6*t) := by
  have h : 0 < (7*t).choose (6*t) := Nat.choose_pos (by omega)
  have hpow : 6 ≤ 6^(6*t) := by
    convert Nat.pow_le_pow_right (by decide : 0 < (6 : ℕ)) (show 1 ≤ 6*t by omega) using 1
  exact (by decide : 1 < 6).trans_le (hpow.trans (Nat.le_mul_of_pos_left _ h))

theorem axisPackedDigits_capacity (n t : ℕ) (ht : 0 < t) :
    n ≤ (axisRadix (7*t) (6*t))^axisPackedDigits n t := by
  have hD := axisRadix_one_lt ht
  apply (Nat.le_pow_clog hD _).trans
  exact Nat.pow_le_pow_right (by omega) (le_max_right ..)

def axisWordEquiv (k m w : ℕ) :
    Fin ((axisRadix m w)^k) ≃ (Fin k → SlotWords.Word m w 6) :=
  AxisSlotWords.rankedWordTuple k m w

def axisStateOfWord {m w : ℕ} (v : SlotWords.Word m w 6) (i : Fin m) : Option (Fin 6) :=
  if h : i ∈ v.1.val then some (v.2 ⟨i,h⟩) else none

theorem axisStateOfWord_uses {m w : ℕ} (v : SlotWords.Word m w 6) (i : Fin m) (j : Fin 6) :
    axisStateOfWord v i = some j ↔ SlotWords.Uses v i j := by
  unfold axisStateOfWord SlotWords.Uses
  split
  · rename_i h
    exact ⟨fun he => ⟨h,Option.some.inj he⟩,fun ⟨_,he⟩ => congrArg some he⟩
  · rename_i h
    constructor
    · intro he
      cases he
    · rintro ⟨hi,_⟩
      exact (h hi).elim

theorem axisStateOfWord_meets {m w : ℕ} (hw : w ≤ m) (v : SlotWords.Word m w 6)
    (S : Finset (Fin m)) (hS : S.card = m+1-w) :
    ∃ i : {i // i ∈ S}, axisStateOfWord v i ≠ none := by
  by_contra! h
  have hd : Disjoint S v.1.val := by
    apply Finset.disjoint_left.mpr
    intro i hi hv
    have he := h ⟨i,hi⟩
    simp [axisStateOfWord,hv] at he
  have hcard := Finset.card_union_of_disjoint hd
  have hc := Finset.card_le_card (Finset.subset_univ (S ∪ v.1.val))
  rw [Finset.card_univ,Fintype.card_fin] at hc
  have hv := v.1.property
  omega

end
end TranslationTiling.FiniteCompiler.Packed
