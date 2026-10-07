import LeanWang.CoRE
import LeanWang.Basic
import Mathlib.Computability.Primrec.List
import Mathlib.Data.Finset.Basic

/-! Concrete meanings of the public statements. Lists encode finite tiles;
membership ignores repeated entries. Translation sets may be infinite. -/

namespace TranslationTiling

abbrev Lattice (d : ℕ) := Fin d → ℤ
abbrev Tile (d : ℕ) := List (Lattice d)

/-- Use the same encoding for finite tiles in enumeration and computability proofs. -/
instance (priority := 2000) tileEncodable (d : ℕ) : Encodable (Tile d) :=
  (inferInstance : Primcodable (Tile d)).toEncodable

/-- Every point has exactly one representation as a translation plus a tile point. -/
def ExactTiling {G : Type*} [Add G] (A F : Set G) : Prop :=
  Function.Bijective (fun p : A × F => p.1.val + p.2.val)

/-- Tilability of the entire lattice by translations of one finite tile. -/
def Tiles {d : ℕ} (F : Tile d) : Prop :=
  ∃ A : Set (Lattice d), ExactTiling A {f | f ∈ F}

/-- A finite computable Wang-to-lattice compiler, with both tilability directions. -/
structure WangReduction where
  tile : LeanWang.TileSet → Tile 3
  computable : Computable tile
  nonempty : ∀ T, T ≠ [] → tile T ≠ []
  correct : ∀ T, LeanWang.TilesPlane T ↔ Tiles (tile T)

end TranslationTiling
