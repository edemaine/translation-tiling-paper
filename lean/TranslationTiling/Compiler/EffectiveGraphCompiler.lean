import TranslationTiling.Compiler.EffectiveNumericParameters
import TranslationTiling.Compiler.EffectiveGraphTiles

set_option maxRecDepth 1000
set_option maxHeartbeats 100000

namespace TranslationTiling.Compiler.Effective

open scoped Classical

/-- The fixed channel table is independent of the Wang input. -/
noncomputable def channelModuli (T : LeanWang.TileSet) : List ℕ :=
  (Finset.univ : Finset FixedChannel).toList.map (numericalR T)

theorem channelModuli_computable : Computable channelModuli := by
  have hm := computableListMap
    (f := fun _ : LeanWang.TileSet => (Finset.univ : Finset FixedChannel).toList)
    (g := fun T i => numericalR T i) (Computable.const _) numericalR_computable
  exact hm

theorem channelModuli_eq (T : LeanWang.TileSet) :
    channelModuli T = (Finset.univ : Finset (Channel T)).toList.map (parameters T).r := by
  unfold channelModuli
  apply List.map_congr_left
  intro i _
  exact numericalR_eq T i

noncomputable def kernelCompiler (T : LeanWang.TileSet) : List NumericalPoint :=
  kernelCodes (numericalOrder T) (channelModuli T)

theorem kernelCompiler_computable : Computable kernelCompiler := by
  have h := kernelCodes_primrec.to_comp.comp (numericalOrder_computable.pair channelModuli_computable)
  exact h

theorem kernelCompiler_correct (T : LeanWang.TileSet) :
    (kernelCompiler T).toFinset.image (decodeNumericalPoint (parameters T)) =
      kernelTile (parameters T) := by
  unfold kernelCompiler
  rw [numericalOrder_eq, channelModuli_eq]
  exact kernelCodes_correct _

end TranslationTiling.Compiler.Effective
