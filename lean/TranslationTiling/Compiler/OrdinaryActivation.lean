/- Adapted from openai/math, OAI/Geometry/PeriodicTiling, commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a. Apache 2.0; see
third_party/openai-math.LICENSE. Decorated alphabet and two-prime residue size;
namespace and imports changed for Lean 4.31. -/
import TranslationTiling.Compiler.OrdinaryModel
import TranslationTiling.Compiler.BlockActivationInverse

namespace TranslationTiling

noncomputable section

namespace Compiler.CommonModel

variable {T : LeanWang.TileSet} (E : EncodingParameters T) (W : WordArray T)

def ordinaryForward (n : Column T) (x : Plane) (k : K E (.inl n))
    (j : ActivationIndex E (.inl n)) : P E (.inl n) × K E (.inl n) :=
  (ordinaryUseful E W n (x - ordinaryOffset E n j) (k - j.1) +
    shift (E.a (.inl n)) (E.b (.inl n)) j.2,
    ordinaryHigh E W n (x - ordinaryOffset E n j) (k - j.1))

theorem ordinaryForward_bijective (n : Column T) (x : Plane) (k : K E (.inl n)) :
    Function.Bijective (ordinaryForward E W n x k) := by
  let D := channelDigitBlocks E (.inl n) (ordinarySymbol W n x)
  let S := BlockShiftData.ofMultiplicity
    (E.a_two_le (.inl n)) (E.b_two_le (.inl n))
  let e := BlockShiftData.blockInverseEquiv D S
    (fun j => (ordinaryOffset E n j).1)
    (fun j => ordinaryOffset_rhoA E n j)
    (fun j => ordinaryOffset_rhoB E n j) x.1 k
  have he : ordinaryForward E W n x k = e := by
    funext j
    simp only [ordinaryForward, ordinaryUseful_offset, ordinaryHigh_offset]
    rfl
  rw [he]
  exact e.bijective

end Compiler.CommonModel

end

end TranslationTiling
