import TranslationTiling.FiniteCompiler.Effective.SparseCompiler
import TranslationTiling.Compiler.ShortLogBound

namespace TranslationTiling.FiniteCompiler.Effective
open Compiler Compiler.Effective
open scoped Classical
noncomputable section
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

 theorem shortCompileCore_real_bound (T : LeanWang.TileSet) (hn : 21≤T.length) :
    ((sparseCompileCore T).length:ℝ)≤((T.length:ℝ)+4)^
      (1000*Real.logb 2 (Real.logb 2 ((T.length:ℝ)+4))) := by
  by_cases hb : 252≤T.length
  · exact Compiler.Size.short_bulk_real_bound hb (sparseCompileCore_channel_bound T (by omega)).2.2.2
  · by_cases hm : T.length≤242
    · have hw : (SparseTernary.system T).width=SmallProfiles.width 1 := by
        simpa [SparseTernary.system,SmallProfiles.width] using Compiler.Size.short_width64 (by omega : 11≤T.length) hm
      exact Compiler.Size.short_dyadic_real_bound (sparseCompileCore_small_bound T (by omega) 1 hw)
        (Compiler.Size.short_medium_exponent hn)
    · have hw : (SparseTernary.system T).width=SmallProfiles.width 2 := by
        simpa [SparseTernary.system,SmallProfiles.width] using Compiler.Size.short_width80 (by omega : 243≤T.length) (by omega : T.length≤251)
      exact Compiler.Size.short_dyadic_real_bound (sparseCompileCore_small_bound T (by omega) 2 hw)
        (Compiler.Size.short_later_exponent (by omega))

end
end TranslationTiling.FiniteCompiler.Effective
