import TranslationTiling.FiniteCompiler.Effective.SlotRankedWords
import TranslationTiling.FiniteCompiler.GuardedSystem
import TranslationTiling.FiniteCompiler.Effective.PackedPatternCorrect
import TranslationTiling.FiniteCompiler.Effective.FourValueDigits

namespace TranslationTiling.FiniteCompiler.Packed

open PairSmall GuardedCompiler Effective
open scoped Classical

noncomputable section

local instance slotWordFrame : SeedFrame := compactSeedFrame

def slotRadix (m w : ℕ) := m.choose w * 3^w

/-- Choose a positive digit length divisible by four, including at
one input tile. -/
def slotLengthParameter (n : ℕ) : ℕ := max 1 (Nat.log 2 (Nat.log 2 n)/4)

def slotPackedDigits (n t : ℕ) : ℕ := max 1 (Nat.clog (slotRadix (4*t) (3*t)) n)

theorem slotRadix_one_lt {t : ℕ} (ht : 0 < t) : 1 < slotRadix (4*t) (3*t) := by
  have h : 0 < (4*t).choose (3*t) := Nat.choose_pos (by omega)
  have hpow : 3 ≤ 3^(3*t) := by
    convert Nat.pow_le_pow_right (by decide : 0 < (3 : ℕ)) (show 1 ≤ 3*t by omega) using 1
  exact (by decide : 1 < 3).trans_le (hpow.trans (Nat.le_mul_of_pos_left _ h))

theorem slotPackedDigits_capacity (n t : ℕ) (ht : 0 < t) :
    n ≤ (slotRadix (4*t) (3*t))^slotPackedDigits n t := by
  have hD := slotRadix_one_lt ht
  apply (Nat.le_pow_clog hD _).trans
  exact Nat.pow_le_pow_right (by omega) (le_max_right ..)

def slotWordEquiv (k m w : ℕ) :
    Fin ((slotRadix m w)^k) ≃ (Fin k → SlotWords.Word m w 3) :=
  SlotWords.rankedWordTuple k m w

def slotState {m w : ℕ} (v : SlotWords.Word m w 3) (i : Fin m) : Option (Fin 3) :=
  if h : i ∈ v.1.val then some (v.2 ⟨i,h⟩) else none

theorem slotState_uses {m w : ℕ} (v : SlotWords.Word m w 3) (i : Fin m) (j : Fin 3) :
    slotState v i = some j ↔ SlotWords.Uses v i j := by
  unfold slotState SlotWords.Uses
  split
  · rename_i h
    exact ⟨fun he => ⟨h,Option.some.inj he⟩,fun ⟨_,he⟩ => congrArg some he⟩
  · rename_i h
    constructor
    · intro he
      cases he
    · rintro ⟨hi,_⟩
      exact (h hi).elim

theorem slotState_meets {m w : ℕ} (hw : w ≤ m) (v : SlotWords.Word m w 3)
    (S : Finset (Fin m)) (hS : S.card = m+1-w) :
    ∃ i : {i // i ∈ S}, slotState v i ≠ none := by
  by_contra! h
  have hd : Disjoint S v.1.val := by
    apply Finset.disjoint_left.mpr
    intro i hi hv
    have he := h ⟨i,hi⟩
    simp [slotState,hv] at he
  have hcard := Finset.card_union_of_disjoint hd
  have hc := Finset.card_le_card (Finset.subset_univ (S ∪ v.1.val))
  rw [Finset.card_univ,Fintype.card_fin] at hc
  have hv := v.1.property
  omega

def arithmeticRow (i : Fin 18) : FourValueRow 0 :=
  ⟨i.val,by have := i.isLt; rw [fourValueRows_length]; omega⟩

def arithmeticColumn (i : Fin 18) : Fin 20 := ⟨i.val,by have := i.isLt; omega⟩

def wangColumn (g : Bool) : Fin 20 := atC (if g then 0 else 1)

theorem arithmeticColumn_val (i : Fin 18) : (arithmeticColumn i).val = i.val := rfl

theorem wangColumn_val (g : Bool) : (wangColumn g).val = if g then 18 else 19 := by
  cases g <;> decide +kernel

theorem arithmetic_arity (D : ℕ) (i : Fin 18) :
    (rowDigits (fourValueRows 0) (arithmeticRow i)).length = PairSmall.arity D (arithmeticColumn i) := by
  have hbase : ∀ i : Fin 18,
      (rowDigits (fourValueRows 0) (arithmeticRow i)).length = PairSmall.arity 1 (arithmeticColumn i) :=
    by decide +kernel
  rw [hbase]
  unfold PairSmall.arity
  generalize h : roleEquiv.symm (arithmeticColumn i) = j
  rcases j with j | j | j
  · rfl
  · rfl
  · have he : atC j = arithmeticColumn i := by
      change roleEquiv (.inr (.inr j)) = _
      rw [← h,Equiv.apply_symm_apply]
    have hc : ∀ j : Fin 2, 18 ≤ (atC j).val := by decide +kernel
    have := hc j
    rw [he,arithmeticColumn_val] at this
    omega

theorem arithmetic_slope (i : Fin 18) :
    ((tailSlopes 0).getD (arithmeticRow i).val 0 : ℤ) = PairSmall.slope (arithmeticColumn i) :=
  (by decide +kernel : ∀ i : Fin 18, ((tailSlopes 0).getD (arithmeticRow i).val 0 : ℤ) =
    PairSmall.slope (arithmeticColumn i)) i

theorem wang_slope (g : Bool) : PairSmall.slope (wangColumn g) = if g then 0 else 2 := by
  cases g <;> decide +kernel

theorem wang_has_all_seed_labels {T : LeanWang.TileSet} {D : ℕ} (c : Code T D)
    (g : Bool) (t : Fin 2) (a : Fin (PairSmall.arity D (wangColumn g))) :
    @LetterSeedSet (system c) (GuardedCompiler.alphabet c) t (wangColumn g) a := by
  cases g <;> trivial

variable {T : LeanWang.TileSet} {D : ℕ} (c : Code T D)
local instance : AlphabetFamily (system c) := GuardedCompiler.alphabet c

/-- The recovered arithmetic and Wang lines may be passed directly to
the guarded board theorem, before any encoding into slot words. -/
theorem guarded_of_slot_selection (W : WordArray (system c))
    (hs : ∀ t : Fin 2, ∃ x : Plane, ∀ i, LetterSeedSet (system c) t i
      (W i (lineValue (system c) i x)))
    (hp : ∀ x p, p ∈ patterns c → p.columns.Nonempty →
      ¬ p.Matches (fun i => W i (lineValue (system c) i x))) :
    LeanWang.TilesPlane T := by
  obtain ⟨hp5,hp7,hg⟩ := patterns_complete c W hp
  exact Sudoku.PairBoard.guarded_soundness T _ hg hp5 hp7 (nonconstant_of_seeds c W hs)

end
end TranslationTiling.FiniteCompiler.Packed
