import TranslationTiling.Rotations.General.Real.Assembly
import TranslationTiling.Rotations.General.ProtectedSize
import Mathlib.LinearAlgebra.Determinant

namespace TranslationTiling.Rotations.General.Real
noncomputable section
variable {d : ℕ} [NeZero d]

/-- Orientation-preserving Euclidean rotations; translations remain arbitrary. -/
def Proper (r : Rotation d) : Prop := LinearMap.det r.toLinearEquiv.toLinearMap=1

theorem proper_ident : Proper (LinearIsometryEquiv.refl ℝ (EPoint d)) := by
  simp [Proper]

def ProtectedEuclideanTileable (allowed : Set (Rotation d)) (P : Tile d) : Prop :=
  FaceConnected P ∧ AllowedEuclideanTiles allowed P.toFinset

theorem protect_correct (hd : 3 ≤ d) (E : Tile d) (hE : E≠[])
    (allowed : Set (Rotation d)) (hid : LinearIsometryEquiv.refl ℝ (EPoint d) ∈ allowed) :
    TranslationTiling.Tiles E ↔ AllowedEuclideanTiles allowed (protect E).toFinset := by
  have hn : E.toFinset.Nonempty := by
    obtain ⟨e,he⟩ := List.exists_mem_of_ne_nil E hE
    exact ⟨e,by simpa using he⟩
  have ht : FiniteTiles E.toFinset ↔ TranslationTiling.Tiles E := by
    simp [FiniteTiles,TranslationTiling.Tiles]
  rw [protect_toFinset]
  exact ht.symm.trans (assembly_allowed_iff hd E.toFinset hn allowed hid)


end
end TranslationTiling.Rotations.General.Real

namespace TranslationTiling.Rotations.General.Real

/-- A dimension-preserving black-box wrapper for arbitrary nonempty lattice
tiles. It handles all Euclidean rotations, optionally reflections, and any
other allowed rotation set containing the identity, using the same output. -/
theorem protection (d : ℕ) (hd : 3 ≤ d) :
    ∃ R : Tile d → Tile d, Computable R ∧ ∀ E, E ≠ [] →
      R E ≠ [] ∧ (FaceConnected E → FaceConnected (R E)) ∧
      (∀ allowed : Set (Rotation d), LinearIsometryEquiv.refl ℝ (EPoint d) ∈ allowed →
        (TranslationTiling.Tiles E ↔ AllowedEuclideanTiles allowed (R E).toFinset)) ∧
      (R E).toFinset.card=(cubeSide d)^d*E.toFinset.card ∧
      (R E).length ≤ 2^(10*(d+1)^2)*E.length := by
  letI : NeZero d := ⟨by omega⟩
  refine ⟨General.protect,General.protect_primrec.to_comp,fun E hE => ?_⟩
  exact ⟨General.protect_nonempty hd E hE,General.protect_connected hd E,
    fun allowed hid => protect_correct hd E hE allowed hid,
    General.protect_card E,General.protect_length_bound E⟩

end TranslationTiling.Rotations.General.Real
