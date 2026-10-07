import TranslationTiling.Statements
import TranslationTiling.Proofs.Wang
import TranslationTiling.Proofs.SudokuSoundness
import TranslationTiling.Proofs.Graph
import TranslationTiling.Proofs.Stacking
import TranslationTiling.Proofs.CyclicStacking
import TranslationTiling.Proofs.Histogram
import TranslationTiling.Proofs.PeriodicGrid
import TranslationTiling.Proofs.ShellAssembly
import TranslationTiling.Proofs.Translation
import TranslationTiling.Proofs.ComputableSearch
import TranslationTiling.Proofs.Decidability
import TranslationTiling.Proofs.Canonical
import TranslationTiling.Proofs.FiniteWordRule
import Lean.Util.CollectAxioms

/-! Reject unfinished proofs, native evaluation axioms, and undeclared mathematical
assumptions in every public theorem and the main construction lemmas. Imported
mathematical statements occur as explicit parameters, never as Lean axioms. -/

open Lean Elab Command in
run_cmd do
  for name in [``TranslationTiling.membership,
      ``TranslationTiling.sudoku_equivalence,
      ``TranslationTiling.planar_decidability,
      ``TranslationTiling.rounding,
      ``TranslationTiling.completeness,
      ``TranslationTiling.undecidability,
      ``TranslationTiling.higher_dimension,
      ``TranslationTiling.real_membership,
      ``TranslationTiling.real_completeness,
      ``TranslationTiling.dimension_optimality,
      ``TranslationTiling.connected_output,
      ``TranslationTiling.connected_hardness,
      ``TranslationTiling.connected_membership,
      ``TranslationTiling.connected_completeness,
      ``TranslationTiling.faceConnected_computable,
      ``TranslationTiling.wang_plane_iff_quadrant,
      ``TranslationTiling.Sudoku.activeSystem_tilesPlane,
      ``TranslationTiling.graph_equation_iff,
      ``TranslationTiling.Stacking.exists_tiles_stack_iff,
      ``TranslationTiling.Stacking.exists_cyclic_stack,
      ``TranslationTiling.Activation.histogram_mass_dvd,
      ``TranslationTiling.planar_grid_of_periodicity,
      ``TranslationTiling.periodicCertificate_tiles,
      ``TranslationTiling.periodicCertificate_of_grid,
      ``TranslationTiling.periodicCertificate_primrec,
      ``TranslationTiling.shell_assembly_iff,
      ``TranslationTiling.tiles_translate_iff,
      ``TranslationTiling.leastWitness_computable,
      ``TranslationTiling.primeAbove_computable,
      ``TranslationTiling.decidability_of_certificates,
      ``TranslationTiling.Sudoku.lowValuation_sound,
      ``TranslationTiling.Sudoku.canonical_nonconstantColumns,
      ``TranslationTiling.Sudoku.canonical_lineRule,
      ``TranslationTiling.Sudoku.exists_twoPrime_residue,
      ``TranslationTiling.Sudoku.allowed_iff_bounded,
      ``TranslationTiling.Sudoku.allowedBool_eq_true,
      ``TranslationTiling.Sudoku.mem_allowedWords] do
    let axioms ← Lean.collectAxioms name
    let extra := axioms.filter fun ax =>
      ax != ``propext && ax != ``Classical.choice && ax != ``Quot.sound
    unless extra.isEmpty do
      throwError "{name} depends on unexpected axioms: {extra}"
