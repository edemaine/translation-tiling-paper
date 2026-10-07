/- Adapted from openai/math, OAI/Geometry/PeriodicTiling, commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a. Apache 2.0; see
third_party/openai-math.LICENSE. Decorated alphabet and two-prime residue size;
namespace and imports changed for Lean 4.31. -/
import TranslationTiling.Compiler.CommonModel
import TranslationTiling.Compiler.EncodedSystem

namespace TranslationTiling

noncomputable section

namespace Compiler.CommonModel

variable {T : LeanWang.TileSet} (E : EncodingParameters T) (W : WordArray T)

theorem ordinaryActivationMap_outputs (n : Column T) (b : Base E) :
    ordinaryActivationMap E n (outputs E W) b =
      ordinaryForward E W n b.1 (b.2 (.inl n)) := by
  funext j
  simp [ordinaryActivationMap, ordinarySource, activationSource, outputs, ordinaryForward]

theorem seedActivationMap_outputs (t : Fin 2) (b : Base E) :
    seedActivationMap E t (outputs E W) b = seedActualForward E t b.1 b.2 := by
  rfl

theorem common_solution (hrule : Sudoku.LineRule W)
    (hseedW : ∀ t n x, SharedSeed.residue T x ∈ seedActiveRegion T t →
      SeedSet t (W n (lineValue n x))) : Solves E (commonGraph E W) := by
  apply (solves_iff E (commonGraph E W)).mpr
  refine ⟨commonGraph_tiles_kernel E W, ?_, ?_, ?_, ?_, ?_⟩
  · exact (dependenceTiles_iff E (outputs E W)).mpr (outputs_hasDependence E W)
  · exact (wordConstraintTiles_iff E (outputs E W) (outputs_hasDependence E W)).mpr
      (active_word_allowed E W hrule)
  · apply (seedConstraintTiles_iff E (outputs E W) (outputs_hasDependence E W)).mpr
    intro t n x j ht hj
    exact active_seed_forces_symbol E W hseedW t n x j ht hj
  · intro n
    apply (ordinaryActivationTile_iff E n (outputs E W)).mpr
    intro b
    rw [ordinaryActivationMap_outputs]
    exact ordinaryForward_bijective E W n b.1 (b.2 (.inl n))
  · intro t
    apply (seedActivationTile_iff E t (outputs E W)).mpr
    intro b
    rw [seedActivationMap_outputs]
    exact seedActualForward_bijective E t b.1 b.2

end Compiler.CommonModel

end

end TranslationTiling
