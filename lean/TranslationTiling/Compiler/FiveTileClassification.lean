import TranslationTiling.Compiler.FiveTileCases
import TranslationTiling.Compiler.FiveTileCoverCase0
import TranslationTiling.Compiler.FiveTileCoverCase1
import TranslationTiling.Compiler.FiveTileCoverCase2
import TranslationTiling.Compiler.FiveTileCoverCase3
import TranslationTiling.Compiler.FiveTileCoverCase4
import TranslationTiling.Compiler.FiveTileCoverCase5
import TranslationTiling.Compiler.FiveTileCoverCase6
import TranslationTiling.Compiler.FiveTileCoverCase7
import TranslationTiling.Compiler.FiveTileCoverCase8
import TranslationTiling.Compiler.FiveTileCoverCase9
import TranslationTiling.Compiler.FiveTileCoverCase10
import TranslationTiling.Compiler.FiveTileCoverCase11
import TranslationTiling.Compiler.FiveTileCoverCase12
import TranslationTiling.Compiler.FiveTileCoverCase13
import TranslationTiling.Compiler.FiveTileCoverCase14
import TranslationTiling.Compiler.FiveTileCoverCase15
import TranslationTiling.Compiler.FiveTileCoverCase16
import TranslationTiling.Compiler.FiveTileCoverCase17
import TranslationTiling.Compiler.FiveTileCoverCase18
import TranslationTiling.Compiler.FiveTileCoverCase19
import TranslationTiling.Compiler.FiveTileCoverCase20
import TranslationTiling.Compiler.FiveTileCoverCase21
import TranslationTiling.Compiler.FiveTileCoverCase22
import TranslationTiling.Compiler.FiveTileCoverCase23
import TranslationTiling.Compiler.FiveTileCoverCase24
import TranslationTiling.Compiler.FiveTileCoverCase25
import TranslationTiling.Compiler.FiveTileCoverCase26
import TranslationTiling.Compiler.FiveTileCoverCase27
import TranslationTiling.Compiler.FiveTileCoverCase28
import TranslationTiling.Compiler.FiveTileCoverCase29
import TranslationTiling.Compiler.FiveTileCoverCase30
import TranslationTiling.Compiler.FiveTileCoverCase31
namespace TranslationTiling.Compiler.FiveTile

def covers : Fin 32 → CheckedCover := ![CoverCases.checkedCover0, CoverCases.checkedCover1, CoverCases.checkedCover2, CoverCases.checkedCover3, CoverCases.checkedCover4, CoverCases.checkedCover5, CoverCases.checkedCover6, CoverCases.checkedCover7, CoverCases.checkedCover8, CoverCases.checkedCover9, CoverCases.checkedCover10, CoverCases.checkedCover11, CoverCases.checkedCover12, CoverCases.checkedCover13, CoverCases.checkedCover14, CoverCases.checkedCover15, CoverCases.checkedCover16, CoverCases.checkedCover17, CoverCases.checkedCover18, CoverCases.checkedCover19, CoverCases.checkedCover20, CoverCases.checkedCover21, CoverCases.checkedCover22, CoverCases.checkedCover23, CoverCases.checkedCover24, CoverCases.checkedCover25, CoverCases.checkedCover26, CoverCases.checkedCover27, CoverCases.checkedCover28, CoverCases.checkedCover29, CoverCases.checkedCover30, CoverCases.checkedCover31]

theorem covers_row : ∀ i, (covers i).row=i := by decide +kernel

theorem plane_of_patch {H : ℕ} {V : Matrix} {W : ℕ → ℕ → Letter}
    (hrH : Rectangular (edge H)) (hrV : Rectangular V) (hp : Patch H V W) :
    Plane H V := by
  obtain ⟨r,hr⟩ := row_representable (edge H 0)
  apply (covers r).complete checkedCase checkedCase_mask H V W hrH hrV hp
  rw [covers_row]
  exact hr

end TranslationTiling.Compiler.FiveTile
