import Mathlib.Data.List.GetD
import TranslationTiling.Compiler.FiveTileSymmetry
import TranslationTiling.Compiler.FiveTileCaseBlock0
import TranslationTiling.Compiler.FiveTileCaseBlock1
import TranslationTiling.Compiler.FiveTileCaseBlock2
import TranslationTiling.Compiler.FiveTileCaseBlock3
import TranslationTiling.Compiler.FiveTileCaseBlock4
import TranslationTiling.Compiler.FiveTileCaseBlock5
import TranslationTiling.Compiler.FiveTileCaseBlock6
import TranslationTiling.Compiler.FiveTileCaseBlock7
import TranslationTiling.Compiler.FiveTileCaseBlock8
import TranslationTiling.Compiler.FiveTileCaseBlock9
import TranslationTiling.Compiler.FiveTileCaseBlock10
import TranslationTiling.Compiler.FiveTileCaseBlock11
import TranslationTiling.Compiler.FiveTileCaseBlock12
import TranslationTiling.Compiler.FiveTileCaseBlock13
import TranslationTiling.Compiler.FiveTileCaseBlock14
import TranslationTiling.Compiler.FiveTileCaseBlock15
import TranslationTiling.Compiler.FiveTileCaseBlock16
import TranslationTiling.Compiler.FiveTileCaseBlock17
import TranslationTiling.Compiler.FiveTileCaseBlock18
import TranslationTiling.Compiler.FiveTileCaseBlock19
import TranslationTiling.Compiler.FiveTileCaseBlock20
import TranslationTiling.Compiler.FiveTileCaseBlock21

namespace TranslationTiling.Compiler.FiveTile
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def checkedCases : List CheckedCase := caseBlock0 ++ caseBlock1 ++ caseBlock2 ++ caseBlock3 ++ caseBlock4 ++ caseBlock5 ++ caseBlock6 ++ caseBlock7 ++ caseBlock8 ++ caseBlock9 ++ caseBlock10 ++ caseBlock11 ++ caseBlock12 ++ caseBlock13 ++ caseBlock14 ++ caseBlock15 ++ caseBlock16 ++ caseBlock17 ++ caseBlock18 ++ caseBlock19 ++ caseBlock20 ++ caseBlock21

theorem checkedCases_masks : checkedCases.map CheckedCase.mask=caseMasks := by decide +kernel

def checkedCase (i : Fin 676) : CheckedCase := checkedCases.getD i.val Cases.checked0

theorem checkedCase_mask (i : Fin 676) : (checkedCase i).mask=caseMask i := by
  unfold caseMask
  rw [←checkedCases_masks]
  change (checkedCase i).mask=(checkedCases.map CheckedCase.mask).getD i.val Cases.checked0.mask
  simpa only [List.getD_map,checkedCase]

end TranslationTiling.Compiler.FiveTile
