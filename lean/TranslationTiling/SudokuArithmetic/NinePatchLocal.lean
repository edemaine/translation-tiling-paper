import TranslationTiling.SudokuArithmetic.NinePatchModel
import TranslationTiling.SudokuArithmetic.NinePatchCertificate5
import TranslationTiling.SudokuArithmetic.NinePatchCertificate7

namespace TranslationTiling.Sudoku.NinePatch

/-- The finite nine-column classification, stated for a normalized patch of
nonzero symbols rather than for SAT valuations. The line hypotheses are just
primitive affine explanations restricted to the tested patch cells. -/
theorem normalized_patch_affine {p : Nat} (hp : p=5 ∨ p=7)
    (W : Nat → Nat → Nat)
    (hw : ∀ n<9, ∀ y<7, 0<W n y ∧ W n y<p)
    (hnorm : W 0 0=1)
    (hl : ∀ i<(lines p).length, ∃ ab∈forms p, lineAgrees p W (lineAt p i) ab) :
    ∃ abc∈triples p, ∀ n<9, ∀ y<7, affineValue p abc n y≠0 →
      W n y=affineValue p abc n y := by
  have hu : Sat.Fmla.proof (formula p) [] := by
    rcases hp with rfl | rfl
    · exact patch5_unsat
    · exact patch7_unsat
  exact classify_patch hu W (assignment p W) (hypotheses_hold W hw hnorm hl)
    (fun n hn y hy z hz => assignment_cell W hn hy hz)
    (by have := hw 0 (by decide) 0 (by decide); omega)

end TranslationTiling.Sudoku.NinePatch
