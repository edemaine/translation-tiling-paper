import TranslationTiling.SudokuArithmetic.ShortRecovery
import TranslationTiling.SudokuArithmetic.ShortSeedCertificate5
import TranslationTiling.SudokuArithmetic.ShortSeedCertificate7

namespace TranslationTiling.Sudoku.ShortRule
noncomputable section

theorem global_affine_approximation {p : ℕ} (hp : p=5 ∨ p=7)
    {W : WordArray p} (hW : LineRule p W) :
    ∃ A B C : ZMod p, AffineApproximation W A B C := by
  rcases hp with rfl|rfl
  · exact Seed.global_affine_of_certificates (by decide) (by decide)
      Seed.seed5_unsat Seed.third5 Seed.mid5_1 Seed.mid5_3 hW
  · exact Seed.global_affine_of_certificates (by decide) (by decide)
      Seed.seed7_unsat Seed.third7 Seed.mid7_1 Seed.mid7_3 hW

end
end TranslationTiling.Sudoku.ShortRule
