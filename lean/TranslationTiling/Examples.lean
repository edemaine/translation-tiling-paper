import TranslationTiling.Proofs.FiniteSearch
import TranslationTiling.Proofs.Euclidean
import TranslationTiling.Proofs.FiniteConnectivity
import TranslationTiling.Proofs.PeriodicCertificates

namespace TranslationTiling

/-- A translated unit lattice tile always tiles. -/
theorem tiles_singleton {d : ℕ} (f : Lattice d) : Tiles [f] := by
  refine ⟨Set.univ, (exactTiling_iff _ _).mpr ?_⟩
  intro x
  refine ⟨⟨f, by simp⟩, Set.mem_univ _, ?_⟩
  intro g _
  exact Subtype.ext (by simpa using g.property)

example : finiteTest ([0] : Tile 1) [-1, 0, 1] := by decide

example : ¬ finiteTest ([] : Tile 1) [0] := by decide

-- A repeated entry does not introduce a second representation of a lattice point.
example : finiteTest ([0, 0] : Tile 1) [-1, 0, 1] := by decide

example : RealTiles ([0] : Tile 3) := realTiles_of_tiles (tiles_singleton 0)

example : finiteConnectedTest ([] : Tile 1) := by decide

example : finiteConnectedTest ([0, 1, 1] : Tile 1) := by decide

example : ¬ finiteConnectedTest ([0, 2] : Tile 1) := by decide

example : PeriodicCertificate ([0] : Tile 1) 1 [0] := by decide

example : ¬ PeriodicCertificate ([0] : Tile 1) 0 [0] := by decide

-- Folding two distinct tile points to the same residue creates an overlap.
example : ¬ PeriodicCertificate ([0, 1] : Tile 1) 1 [0] := by decide

example : PeriodicCertificate ([0, 1] : Tile 1) 2 [0] := by decide

end TranslationTiling
