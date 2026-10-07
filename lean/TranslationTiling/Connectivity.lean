import TranslationTiling.Definitions

namespace TranslationTiling

/-- Two lattice points share a unit-cube face. -/
def FaceAdjacent {d : ℕ} (x y : Lattice d) : Prop :=
  ∃ i : Fin d, (y = x + Pi.single i 1 ∨ x = y + Pi.single i 1)

/-- Paths use signed coordinate steps and remain inside the finite tile. -/
def FaceConnected {d : ℕ} (F : Tile d) : Prop :=
  ∀ x ∈ F, ∀ y ∈ F,
    Relation.ReflTransGen (fun a b => a ∈ F ∧ b ∈ F ∧ FaceAdjacent a b) x y

def ConnectedTiles {d : ℕ} (F : Tile d) : Prop := FaceConnected F ∧ Tiles F

/-- The compiler required by the current paper, including face-connected output. -/
structure ConnectedWangReduction extends WangReduction where
  connected : ∀ T, T ≠ [] → FaceConnected (tile T)

end TranslationTiling
