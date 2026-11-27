import TranslationTiling.FiniteCompiler.AxisSlotGuard
import TranslationTiling.FiniteCompiler.Effective.SlotBlocks

namespace TranslationTiling.FiniteCompiler.Packed

open SharedCoordinates
open scoped Classical BigOperators

noncomputable section

abbrev AxisFallback (m : ℕ) := Bool × Fin m × Bool × Bool
abbrev AxisAddedRow (k m : ℕ) := WangSlot k m ⊕ AxisFallback m
abbrev AxisRow (k m : ℕ) := FourValueRow 0 ⊕ AxisAddedRow k m
abbrev AxisPrime (k m : ℕ) := (WangSlot k m × (Bool ⊕ Fin 3)) ⊕ AxisFallback m

/-- Each slot has two low primes and three markers. The two fallbacks
for each axis and position are shared across digits of the same slope. -/
structure AxisParameters (k m : ℕ) where
  prime : AxisPrime k m → ℕ
  prime_isPrime : ∀ i, (prime i).Prime
  prime_injective : Function.Injective prime
  coprime_arithmetic : ∀ i, (prime i).Coprime (order (fourValueLayout 0))
  block_counts : ∀ (i : WangSlot k m) (a : Bool) (j : Option (Fin 3)),
    let p := prime (.inr (i.1,i.2.2,a,false))
    let q := match j with
      | none => prime (.inr (i.1,i.2.2,a,true))
      | some j => prime (.inl (i,.inr j))
    ∃ l r : ℕ, 0 < l ∧ 0 < r ∧ prime (.inl (i,.inl a)) = l*p+r*q

namespace AxisParameters

variable {k m : ℕ} (s : AxisParameters k m)

abbrev wangRow (i : WangSlot k m) : AxisRow k m := .inr (.inl i)
abbrev fallbackRow (i : AxisFallback m) : AxisRow k m := .inr (.inr i)

def lowAxis (i : WangSlot k m) (a : Bool) := s.prime (.inl (i,.inl a))
def low (i : WangSlot k m) := s.lowAxis i false * s.lowAxis i true
def marker (i : WangSlot k m) (j : Fin 3) := s.prime (.inl (i,.inr j))
def fallback (i : AxisFallback m) := s.prime (.inr i)

theorem prime_coprime {i j : AxisPrime k m} (h : i ≠ j) :
    (s.prime i).Coprime (s.prime j) :=
  (Nat.coprime_primes (s.prime_isPrime i) (s.prime_isPrime j)).mpr
    (fun e => h (s.prime_injective e))

theorem lowAxis_prime (i : WangSlot k m) (a : Bool) : (s.lowAxis i a).Prime :=
  s.prime_isPrime (.inl (i,.inl a))

theorem marker_prime (i : WangSlot k m) (j : Fin 3) : (s.marker i j).Prime :=
  s.prime_isPrime (.inl (i,.inr j))

theorem fallback_prime (i : AxisFallback m) : (s.fallback i).Prime :=
  s.prime_isPrime (.inr i)

theorem lowAxis_coprime (i : WangSlot k m) :
    (s.lowAxis i false).Coprime (s.lowAxis i true) :=
  s.prime_coprime (by intro h; cases h)

instance lowAxis_neZero (i : WangSlot k m) (a : Bool) : NeZero (s.lowAxis i a) :=
  ⟨(s.lowAxis_prime i a).ne_zero⟩

def lowEquiv (i : WangSlot k m) :
    ZMod (s.low i) ≃+* (ZMod (s.lowAxis i false) × ZMod (s.lowAxis i true)) :=
  ZMod.chineseRemainder (s.lowAxis_coprime i)

def layout : SharedCoordinates.Layout (AxisRow k m) where
  lowSize
    | .inl i => (fourValueLayout 0).lowSize i
    | .inr (.inl i) => s.low i
    | .inr (.inr _) => 1
  firstSize
    | .inl i => (fourValueLayout 0).firstSize i
    | .inr _ => 1
  secondSize
    | .inl i => (fourValueLayout 0).secondSize i
    | .inr (.inl i) => ∏ j, s.marker i j
    | .inr (.inr i) => s.fallback i
  lowSize_pos
    | .inl i => (fourValueLayout 0).lowSize_pos i
    | .inr (.inl i) => Nat.mul_pos (s.lowAxis_prime i false).pos (s.lowAxis_prime i true).pos
    | .inr (.inr _) => Nat.one_pos

def firstBlock (i : WangSlot k m) (a : Bool) := s.fallback (i.1,i.2.2,a,false)

def secondBlock (i : WangSlot k m) (a : Bool) : Option (Fin 3) → ℕ
  | none => s.fallback (i.1,i.2.2,a,true)
  | some j => s.marker i j

theorem blockCounts_exist (i : WangSlot k m) (a : Bool) (σ : Option (Fin 3)) :
    ∃ u v : ℕ, 0 < u ∧ 0 < v ∧ s.lowAxis i a = u*s.firstBlock i a+v*s.secondBlock i a σ :=
  s.block_counts i a σ

def leftCount (i : WangSlot k m) (a : Bool) (σ : Option (Fin 3)) :=
  (s.blockCounts_exist i a σ).choose

def rightCount (i : WangSlot k m) (a : Bool) (σ : Option (Fin 3)) :=
  (s.blockCounts_exist i a σ).choose_spec.choose

theorem rightCount_pos (i : WangSlot k m) (a : Bool) (σ : Option (Fin 3)) :
    0 < s.rightCount i a σ :=
  (s.blockCounts_exist i a σ).choose_spec.choose_spec.2.1

instance firstBlock_neZero (i : WangSlot k m) (a : Bool) : NeZero (s.firstBlock i a) :=
  ⟨(s.fallback_prime _).ne_zero⟩

instance secondBlock_neZero (i : WangSlot k m) (a : Bool) (σ : Option (Fin 3)) :
    NeZero (s.secondBlock i a σ) := by
  cases σ with
  | none => exact ⟨(s.fallback_prime _).ne_zero⟩
  | some j => exact ⟨(s.marker_prime i j).ne_zero⟩

def blocks (i : WangSlot k m) (a : Bool) (σ : Option (Fin 3)) :
    LabeledBlocks (ZMod (s.lowAxis i a))
      (Fin (s.leftCount i a σ)) (Fin (s.rightCount i a σ))
      (s.firstBlock i a) (s.secondBlock i a σ) :=
  LabeledBlocks.digit _ _ _ _ _ (s.blockCounts_exist i a σ).choose_spec.choose_spec.2.2

end AxisParameters
end
end TranslationTiling.FiniteCompiler.Packed
