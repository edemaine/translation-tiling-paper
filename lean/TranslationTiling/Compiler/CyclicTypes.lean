/- Adapted from openai/math, OAI/Geometry/PeriodicTiling, commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a. Apache 2.0; see
third_party/openai-math.LICENSE. Decorated alphabet and two-prime residue size;
namespace and imports changed for Lean 4.31. -/
import TranslationTiling.Compiler.EncodingParameters

set_option maxRecDepth 1000

namespace TranslationTiling

namespace Compiler


variable {T : LeanWang.TileSet}


abbrev K (E : EncodingParameters T) (i : Channel T) := ZMod (E.r i)
abbrev P (E : EncodingParameters T) (i : Channel T) := ZMod (E.a i) × ZMod (E.b i)
abbrev Input (E : EncodingParameters T) := ∀ i : Channel T, K E i
abbrev Useful (E : EncodingParameters T) := ∀ i : Channel T, P E i

abbrev V (E : EncodingParameters T) :=
  ZMod (D T) × (∀ i : Channel T, ZMod ((E.r i) ^ 2) × P E i)

abbrev Ambient (E : EncodingParameters T) := Plane × V E
abbrev Base (E : EncodingParameters T) := Plane × Input E

abbrev Low (E : EncodingParameters T) := Input E
abbrev G (E : EncodingParameters T) := Ambient E

structure GraphOutputs (E : EncodingParameters T) where
  c : Base E → Useful E
  beta : Base E → Input E
  z : Base E → ZMod (D T)

abbrev Outputs (E : EncodingParameters T) := GraphOutputs E

end Compiler

end TranslationTiling
