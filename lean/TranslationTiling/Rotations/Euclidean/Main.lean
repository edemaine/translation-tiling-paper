import TranslationTiling.Rotations.Euclidean.Assembly
import TranslationTiling.Rotations.Main
import TranslationTiling.Rotations.Volume
import Mathlib.LinearAlgebra.Determinant

namespace TranslationTiling.Rotations.Euclidean

noncomputable section
open SixKeys

/-- Orientation-preserving Euclidean rotations; translations remain arbitrary. -/
def Proper (r : Rotation) : Prop := LinearMap.det r.toLinearEquiv.toLinearMap=1

theorem proper_ident : Proper (LinearIsometryEquiv.refl ℝ EPoint) := by
  simp [Proper]

def ProtectedEuclideanTileable (allowed : Set Rotation) (P : Tile 3) : Prop :=
  FaceConnected P ∧ AllowedEuclideanTiles allowed P.toFinset

theorem protect_correct (E : Tile 3) (hE : E≠[])
    (allowed : Set Rotation) (hid : LinearIsometryEquiv.refl ℝ EPoint ∈ allowed) :
    TranslationTiling.Tiles E ↔ AllowedEuclideanTiles allowed (protect E).toFinset := by
  have hn : E.toFinset.Nonempty := by
    obtain ⟨e,he⟩ := List.exists_mem_of_ne_nil E hE
    exact ⟨e,by simpa using he⟩
  have ht : FiniteTiles E.toFinset ↔ TranslationTiling.Tiles E := by
    simp [FiniteTiles,TranslationTiling.Tiles]
  rw [protect_toFinset]
  exact ht.symm.trans (assembly_allowed_iff E.toFinset hn allowed hid)

theorem rotationCompile_correct (allowed : Set Rotation)
    (hid : LinearIsometryEquiv.refl ℝ EPoint ∈ allowed) (T : LeanWang.TileSet) :
    LeanWang.TilesPlane T ↔ ProtectedEuclideanTileable allowed (rotationCompile T) := by
  have h := (Compiler.connectedCompile_correct T).trans
    (protect_correct _ (Compiler.connectedCompile_nonempty T) allowed hid)
  exact ⟨fun ht => ⟨rotationCompile_connected T,h.mp ht⟩,fun ht => h.mpr ht.2⟩

/-- A single face-connected polycube is already co-RE-hard when copies may
use arbitrary real translations and any prescribed rotations containing 1. -/
theorem rotation_coRE_hard (allowed : Set Rotation)
    (hid : LinearIsometryEquiv.refl ℝ EPoint ∈ allowed) :
    LeanWang.CoREHard (ProtectedEuclideanTileable allowed) := by
  intro α _ P hP
  exact (LeanWang.Kari.domino_problem_coRE_hard P hP).trans
    ⟨rotationCompile,rotationCompile_computable,rotationCompile_correct allowed hid⟩

theorem rotation_undecidable (allowed : Set Rotation)
    (hid : LinearIsometryEquiv.refl ℝ EPoint ∈ allowed) :
    ¬ ComputablePred (ProtectedEuclideanTileable allowed) := by
  intro h
  exact LeanWang.Kari.domino_problem_undecidable
    (ComputablePred.computable_of_manyOneReducible
      ⟨rotationCompile,rotationCompile_computable,rotationCompile_correct allowed hid⟩ h)

theorem arbitrary_proper_rotation_coRE_hard :
    LeanWang.CoREHard (ProtectedEuclideanTileable {r | Proper r}) :=
  rotation_coRE_hard _ proper_ident

theorem arbitrary_proper_rotation_undecidable :
    ¬ ComputablePred (ProtectedEuclideanTileable {r | Proper r}) :=
  rotation_undecidable _ proper_ident

theorem arbitrary_orthogonal_coRE_hard :
    LeanWang.CoREHard (ProtectedEuclideanTileable Set.univ) :=
  rotation_coRE_hard _ (Set.mem_univ _)

theorem arbitrary_orthogonal_undecidable :
    ¬ ComputablePred (ProtectedEuclideanTileable Set.univ) :=
  rotation_undecidable _ (Set.mem_univ _)

theorem protect_card (E : Tile 3) : (protect E).toFinset.card=64000*E.toFinset.card := by
  rw [protect_toFinset,assembly_card]

end
end TranslationTiling.Rotations.Euclidean
