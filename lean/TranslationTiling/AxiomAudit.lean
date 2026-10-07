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
import TranslationTiling.Compiler.EffectiveGraphCompiler
import TranslationTiling.Compiler.EffectiveActivationOffsets
import TranslationTiling.Compiler.EffectiveStacking
import Lean.Util.CollectAxioms

/-! Reject unfinished proofs, native evaluation axioms, and undeclared mathematical
assumptions in every public theorem and the main construction lemmas. Imported
mathematical statements occur as explicit parameters, never as Lean axioms. -/

open Lean Elab Command in
run_cmd do
  for name in [``TranslationTiling.membership,
      ``TranslationTiling.compilation,
      ``TranslationTiling.lattice_effectivity,
      ``TranslationTiling.shell_effectivity,
      ``TranslationTiling.Compiler.EncodingPrimeSelection.primeSequence_computable,
      ``TranslationTiling.Compiler.finite_system_iff_wang,
      ``TranslationTiling.Compiler.exists_cyclic_tile,
      ``TranslationTiling.Compiler.exists_integer_tile,
      ``TranslationTiling.Compiler.exists_connected_tile,
      ``TranslationTiling.Compiler.LatticeGeometry.assembled_iff_quotient,
      ``TranslationTiling.Compiler.integerTile_correct,
      ``TranslationTiling.Compiler.connectedReduction_of_reduction,
      ``TranslationTiling.Compiler.Effective.partitionCode_computable,
      ``TranslationTiling.Compiler.Effective.partitionCertificate_valid,
      ``TranslationTiling.Compiler.Effective.certificateParts_correct,
      ``TranslationTiling.Compiler.Effective.allowedWordCodes_primrec,
      ``TranslationTiling.Compiler.Effective.mem_allowedWordCodes,
      ``TranslationTiling.Compiler.Effective.wordTest_iff,
      ``TranslationTiling.Compiler.Effective.positiveCombination_computable,
      ``TranslationTiling.Compiler.Effective.numericalR_computable,
      ``TranslationTiling.Compiler.Effective.numericalR_eq,
      ``TranslationTiling.Compiler.Effective.numericalOrder_computable,
      ``TranslationTiling.Compiler.Effective.numericalOrder_eq,
      ``TranslationTiling.Compiler.numericalFactor_surjective,
      ``TranslationTiling.Compiler.Effective.kernelCompiler_computable,
      ``TranslationTiling.Compiler.Effective.kernelCompiler_correct,
      ``TranslationTiling.Compiler.Effective.numericalActivationFirst_primrec,
      ``TranslationTiling.Compiler.Effective.numericalActivationFirst_eq,
      ``TranslationTiling.Compiler.integerTile_nonempty,
      ``TranslationTiling.Compiler.Effective.stackCompiler_computable,
      ``TranslationTiling.Compiler.Effective.stackCodes_correct,
      ``TranslationTiling.Compiler.Effective.stackCompiler_correct,
      ``TranslationTiling.Compiler.Effective.stackCompiler_pos,
      ``TranslationTiling.Compiler.Effective.stackCompiler_nonempty,
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
