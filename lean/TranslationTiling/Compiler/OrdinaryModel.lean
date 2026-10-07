/- Adapted from openai/math, OAI/Geometry/PeriodicTiling, commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a. Apache 2.0; see
third_party/openai-math.LICENSE. Decorated alphabet and two-prime residue size;
namespace and imports changed for Lean 4.31. -/
import TranslationTiling.Compiler.ChannelDigitBlocks
import TranslationTiling.Proofs.CanonicalLineRule
import TranslationTiling.Compiler.ActivationOffsets
import TranslationTiling.Compiler.SharedSeedRegions
import Mathlib.Tactic.Ring

namespace TranslationTiling

noncomputable section

namespace Compiler.CommonModel

variable {T : LeanWang.TileSet} (E : EncodingParameters T) (W : WordArray T)

def ordinarySymbol (n : Column T) (x : Plane) : Symbol T :=
  W n (lineValue n x)

def ordinaryUseful (n : Column T) (x : Plane) (w : K E (.inl n)) : P E (.inl n) :=
  (channelDigitBlocks E (.inl n) (ordinarySymbol W n x)).C w

def ordinaryHigh (n : Column T) (x : Plane) (w : K E (.inl n)) : K E (.inl n) :=
  (channelDigitBlocks E (.inl n) (ordinarySymbol W n x)).T x.1 w

def ordinaryWord (x : Plane) : Word T := fun n => ordinarySymbol W n x

theorem ordinaryWord_allowed (hrule : Sudoku.LineRule W)
    (x : Plane) : Allowed T (ordinaryWord W x) := by
  have hword : ordinaryWord W x =
      (fun n : Column T => W n (x.1 * (n.val : ℤ) + x.2)) := by
    funext n
    change W n (lineValue n x) = _
    congr 1
    unfold lineValue
    ring
  rw [hword]
  exact hrule x.1 x.2

theorem ordinaryUseful_eq_of_lineValue_eq (n : Column T) {x y : Plane}
    (hxy : lineValue n x = lineValue n y) (w : K E (.inl n)) :
    ordinaryUseful E W n x w = ordinaryUseful E W n y w := by
  exact congrArg
    (fun t : ℤ => (channelDigitBlocks E (.inl n) (W n t)).C w) hxy

theorem ordinaryUseful_active_iff (n : Column T) (x : Plane) (j : Symbol T) :
    (∃ w w' : K E (.inl n), w - w' ∈ digitSubgroup E (.inl n) j ∧
      ordinaryUseful E W n x w ≠ ordinaryUseful E W n x w') ↔
        j = ordinarySymbol W n x :=
  channelDigitBlocks_active_iff E (.inl n) (ordinarySymbol W n x) j

theorem ordinarySymbol_offset (n : Column T) (x : Plane)
    (j : ActivationIndex E (.inl n)) :
    ordinarySymbol W n (x - ordinaryOffset E n j) = ordinarySymbol W n x := by
  unfold ordinarySymbol
  congr 1
  simp only [lineValue, ordinaryOffset, Prod.fst_sub, Prod.snd_sub]
  ring

theorem ordinaryUseful_offset (n : Column T) (x : Plane)
    (j : ActivationIndex E (.inl n)) (w : K E (.inl n)) :
    ordinaryUseful E W n (x - ordinaryOffset E n j) w = ordinaryUseful E W n x w := by
  exact congrArg (fun s : Symbol T => (channelDigitBlocks E (.inl n) s).C w)
    (ordinarySymbol_offset E W n x j)

theorem ordinaryHigh_offset (n : Column T) (x : Plane)
    (j : ActivationIndex E (.inl n)) (w : K E (.inl n)) :
    ordinaryHigh E W n (x - ordinaryOffset E n j) w =
      (channelDigitBlocks E (.inl n) (ordinarySymbol W n x)).T
        (x.1 - (ordinaryOffset E n j).1) w := by
  exact congrArg (fun s : Symbol T => (channelDigitBlocks E (.inl n) s).T
    (x.1 - (ordinaryOffset E n j).1) w) (ordinarySymbol_offset E W n x j)

end Compiler.CommonModel

end

end TranslationTiling
