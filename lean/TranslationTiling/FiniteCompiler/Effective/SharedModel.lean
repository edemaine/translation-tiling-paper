import TranslationTiling.FiniteCompiler.Effective.SharedBlockForward
import TranslationTiling.FiniteCompiler.Effective.SharedCycle
import TranslationTiling.FiniteCompiler.Effective.SharedSeedCorrect

namespace TranslationTiling.FiniteCompiler.Packed

open Effective SharedCoordinates
open scoped Classical BigOperators
noncomputable section

set_option maxHeartbeats 3000000

def sharedLineValue (k : ℕ) (i : SharedRow k) (x : Plane) : ℤ :=
  x.2 + ((tailSlopes k).getD i.val 0 : ℤ)*x.1

abbrev SharedPicker (k : ℕ) :=
  ∀ i : SharedRow k, i.val < (sharedRows k).length-2 → ℤ → SharedLabel i

variable {k : ℕ} (pick : SharedPicker k)

def sharedBlockPair (i : SharedRow k) (hi : i.val < (sharedRows k).length-2) (x : SharedBase k) :
    ZMod (OrdinaryA i) × ZMod (OrdinaryB i) :=
  (sharedBlocks i hi (pick i hi (sharedLineValue k i x.1))).C (x.2 i)

def sharedBlockHigh (i : SharedRow k) (hi : i.val < (sharedRows k).length-2) (x : SharedBase k) :
    RowLow i :=
  (sharedBlocks i hi (pick i hi (sharedLineValue k i x.1))).T x.1.1 (x.2 i)

def sharedOrdinaryPair (i : SharedRow k) (hi : i.val < (sharedRows k).length-2) (x : SharedBase k) :
    SharedCoordinates.Useful (sharedLayout k) i :=
  if hf : i.val < 18 then (adjustFirst (ordinaryFirst_fixed i hf)).symm (sharedBlockPair pick i hi x)
  else (0,(sharedBlockPair pick i hi x).2)

private def seedIndex (i : SharedRow k) (hi : ¬ i.val < (sharedRows k).length-2) : Fin 2 :=
  ⟨i.val - ((sharedRows k).length-2),by have := i.isLt; have := sharedRows_length k; omega⟩

private theorem seedIndex_row (i : SharedRow k) (hi : ¬ i.val < (sharedRows k).length-2) :
    sharedSeedRow k (seedIndex i hi) = i := by
  apply Fin.ext
  have := i.isLt
  change (sharedRows k).length-2 + (i.val-((sharedRows k).length-2)) = i.val
  omega

def sharedContribution (s : Bool) (i : SharedRow k) (x : SharedBase k) : ZMod (sharedPrime s) :=
  if h : 18 ≤ i.val ∧ i.val < (sharedRows k).length-2 ∧ sharedSlope k i = s then
    (ZMod.ringEquivCongr ((congrArg sharedPrime h.2.2.symm).trans
      (ordinaryFirst_shared i h.1 h.2.1))).symm (sharedBlockPair pick i h.2.1 x).1
  else 0

def sharedSum (s : Bool) (x : SharedBase k) : ZMod (sharedPrime s) :=
  ∑ i : SharedRow k, sharedContribution pick s i x

def sharedModel : SharedOutput k where
  fixed x := ((sharedSeedZ k x,sharedSum pick true x),sharedSum pick false x)
  privateOutput x i :=
    if hi : i.val < (sharedRows k).length-2 then sharedOrdinaryPair pick i hi x
    else (seedIndex_row i hi) ▸ sharedSeedPair k (seedIndex i hi) x
  high x i :=
    if hi : i.val < (sharedRows k).length-2 then sharedBlockHigh pick i hi x
    else (seedIndex_row i hi) ▸ sharedSeedHigh k (seedIndex i hi) x

@[simp] theorem sharedModel_line (s : Bool) (x : SharedBase k) :
    sharedLine s ((sharedModel pick).fixed x) = sharedSum pick s x := by
  cases s <;> rfl

@[simp] theorem sharedModel_pair (i : SharedRow k) (hi : i.val < (sharedRows k).length-2)
    (x : SharedBase k) : (sharedModel pick).privateOutput x i = sharedOrdinaryPair pick i hi x := by
  dsimp only [sharedModel]
  rw [dite_eq_left hi]

@[simp] theorem sharedModel_high (i : SharedRow k) (hi : i.val < (sharedRows k).length-2)
    (x : SharedBase k) : (sharedModel pick).high x i = sharedBlockHigh pick i hi x := by
  dsimp only [sharedModel]
  rw [dite_eq_left hi]

private theorem seedIndex_self (t : Fin 2)
    (ht : ¬ (sharedSeedRow k t).val < (sharedRows k).length-2) :
    seedIndex (sharedSeedRow k t) ht = t := by
  apply Fin.ext
  exact Nat.add_sub_cancel_left _ _

theorem sharedModel_seedPair (t : Fin 2) (x : SharedBase k) :
    (sharedModel pick).privateOutput x (sharedSeedRow k t) = sharedSeedPair k t x := by
  have ht : ¬ (sharedSeedRow k t).val < (sharedRows k).length-2 := by
    change ¬ (sharedRows k).length-2+t.val < _
    omega
  dsimp only [sharedModel]
  rw [dite_eq_right ht]
  have castSame (u : Fin 2) (e : sharedSeedRow k u = sharedSeedRow k t) (he : u = t) :
      (e ▸ sharedSeedPair k u x) = sharedSeedPair k t x := by
    subst u
    rfl
  exact castSame _ _ (seedIndex_self t ht)

theorem sharedModel_seedHigh (t : Fin 2) (x : SharedBase k) :
    (sharedModel pick).high x (sharedSeedRow k t) = sharedSeedHigh k t x := by
  have ht : ¬ (sharedSeedRow k t).val < (sharedRows k).length-2 := by
    change ¬ (sharedRows k).length-2+t.val < _
    omega
  dsimp only [sharedModel]
  rw [dite_eq_right ht]
  have castSame (u : Fin 2) (e : sharedSeedRow k u = sharedSeedRow k t) (he : u = t) :
      (e ▸ sharedSeedHigh k u x) = sharedSeedHigh k t x := by
    subst u
    rfl
  exact castSame _ _ (seedIndex_self t ht)

theorem sharedModel_seedTiles (t : Fin 2) : seedDeck k t (sharedModel pick) (seedRaw k t) :=
  seedRaw_complete k t _ (sharedModel_seedPair pick t) (sharedModel_seedHigh pick t) (fun _ => rfl)

end
end TranslationTiling.FiniteCompiler.Packed
