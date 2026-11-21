import TranslationTiling.FiniteCompiler.Effective.SharedLayout
import TranslationTiling.FiniteCompiler.Effective.SharedPrimeTags

namespace TranslationTiling.FiniteCompiler.Packed

open Effective

/-- The rows in the same order as the compiler, with the Wang rows
distinguished from the fixed arithmetic and seed rows. -/
abbrev SharedRowSource (k : ℕ) := Fin 18 ⊕ (Fin (2*k) ⊕ Fin 2)

def sharedRowSource {k : ℕ} (i : Fin (sharedRows k).length) : SharedRowSource k :=
  if h : i.val < 18 then .inl ⟨i.val,h⟩
  else if hj : i.val < 18+2*k then .inr (.inl ⟨i.val-18,by omega⟩)
  else .inr (.inr ⟨i.val-(18+2*k),by
    have hi : i.val < 20+2*k := i.isLt.trans_le (sharedRows_length k).le
    omega⟩)

private def sourceNumber {k : ℕ} : SharedRowSource k → ℕ
  | .inl i => i
  | .inr (.inl j) => 18+j
  | .inr (.inr t) => 18+2*k+t

@[simp] theorem sourceNumber_sharedRowSource {k : ℕ} (i : Fin (sharedRows k).length) :
    sourceNumber (sharedRowSource i) = i.val := by
  unfold sharedRowSource
  split_ifs <;> dsimp [sourceNumber] <;> omega

theorem sharedRowSource_injective (k : ℕ) :
    Function.Injective (sharedRowSource (k := k)) :=
  fun _ _ h => Fin.ext (by simpa using congrArg sourceNumber h)

def sourceData {k : ℕ} : SharedRowSource k → ℕ × ℕ × List ℕ
  | .inl i => sharedArithmeticRow i
  | .inr (.inl j) => sharedWangRow k j
  | .inr (.inr t) => sharedSeedRows.getD t (0,0,[])

def sourceFirst {k : ℕ} (src : SharedRowSource k) : ℕ :=
  match src with
  | .inr (.inl _) => 1
  | _ => (sourceData src).1

theorem sharedRowSource_data {k : ℕ} (i : Fin (sharedRows k).length) :
    (sharedRows k).getD i.val (0,0,[]) = sourceData (sharedRowSource i) := by
  unfold sharedRowSource
  split_ifs with h hj
  · exact sharedRows_fixed_at h
  · change _ = sharedWangRow k (i.val-18)
    have he := sharedRows_wang_at (by omega : i.val-18 < 2*k)
    rwa [show 18+(i.val-18) = i.val by omega] at he
  · change _ = sharedSeedRows.getD (i.val-(18+2*k)) (0,0,[])
    have he := sharedRows_seed_at k (i.val-(18+2*k))
    rwa [show 18+2*k+(i.val-(18+2*k)) = i.val by omega] at he

theorem sharedRowSource_first {k : ℕ} (i : Fin (sharedRows k).length) :
    sharedObservedA (sharedRows k) i = sourceFirst (sharedRowSource i) := by
  have hd := congrArg Prod.fst (sharedRowSource_data i)
  change rowA (sharedRows k) i = (sourceData (sharedRowSource i)).1 at hd
  have hlen := sharedRows_length k
  by_cases hlo : i.val < 18
  · rw [sharedObservedA,ite_eq_right (by omega)]
    simpa only [sharedRowSource,dite_eq_left hlo,sourceFirst] using hd
  · by_cases hhi : i.val < 18+2*k
    · rw [sharedObservedA,ite_eq_left (by omega)]
      simp [sharedRowSource,hlo,hhi,sourceFirst]
    · rw [sharedObservedA,ite_eq_right (by omega)]
      simpa only [sharedRowSource,dite_eq_right hlo,dite_eq_right hhi,sourceFirst] using hd

end TranslationTiling.FiniteCompiler.Packed
