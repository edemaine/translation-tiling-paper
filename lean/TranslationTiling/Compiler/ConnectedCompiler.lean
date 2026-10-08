import TranslationTiling.Compiler.ConnectedAssembly
import TranslationTiling.ExternalInputs
import TranslationTiling.Proofs.KimGeometry
import Mathlib.Data.Finset.Lattice.Fold

namespace TranslationTiling.Compiler

open scoped Classical
noncomputable section

theorem mem_cube_iff (l : ℕ) (x : Lattice 3) :
    x ∈ Kim.cube l ↔ ∀ i, 0 ≤ x i ∧ x i < (l : ℤ) :=
  Kim.mem_cube_iff l x

def pointBound (x : Lattice 3) : ℕ :=
  max (x 0).natAbs (max (x 1).natAbs (x 2).natAbs)

/-- A single coordinate bound, computed by a list fold, suffices to translate
a finite tile into a cube. -/
def coordinateBound (E : Tile 3) : ℕ :=
  E.foldr (fun x b => max (pointBound x) b) 0

theorem coordinateBound_spec (E : Tile 3) {x : Lattice 3} (hx : x ∈ E) (i : Fin 3) :
    (x i).natAbs ≤ coordinateBound E := by
  have hpoint : (x i).natAbs ≤ pointBound x := by
    fin_cases i <;> simp only [pointBound]
    · exact le_max_left _ _
    · exact (le_max_left _ _).trans (le_max_right _ _)
    · exact (le_max_right _ _).trans (le_max_right _ _)
  apply hpoint.trans
  induction E with
  | nil => simp at hx
  | cons y E ih =>
    rcases List.mem_cons.mp hx with rfl | hx
    · exact le_max_left _ _
    · exact (ih hx).trans (le_max_right _ _)

def positiveTile (E : Tile 3) : Tile 3 :=
  E.map fun x => x + fun _ => (coordinateBound E : ℤ)

def cubeSize (E : Tile 3) : ℕ := 2 * coordinateBound E + 3

theorem positiveTile_in_cube (E : Tile 3) :
    ∀ x ∈ positiveTile E, x ∈ Kim.cube (cubeSize E) := by
  intro x hx
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hx
  apply (mem_cube_iff _ _).mpr
  intro i
  have hbound : ((u i).natAbs : ℤ) ≤ coordinateBound E := by
    exact_mod_cast coordinateBound_spec E hu i
  have hupper : u i ≤ (u i).natAbs := Int.le_natAbs
  have hlower : -u i ≤ (u i).natAbs := by
    simpa only [Int.natAbs_neg] using (Int.le_natAbs (a := -u i))
  change 0 ≤ u i + (coordinateBound E : ℤ) ∧
    u i + (coordinateBound E : ℤ) < (cubeSize E : ℤ)
  simp only [cubeSize, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  omega

/-- The connected geometric compiler, before the separate uniform computability proof. -/
def connectedTile (E : Tile 3) : Tile 3 :=
  connectedAssembly (positiveTile E) (cubeSize E)

theorem connectedTile_correct (rigid : Kim.CosetRigidity) (E : Tile 3) :
    TranslationTiling.Tiles (connectedTile E) ↔ TranslationTiling.Tiles E :=
  (connectedAssembly_tiles_iff_of_cosets _ _ (by unfold cubeSize; omega)
    (rigid (cubeSize E) (by unfold cubeSize; omega))).trans
    (tiles_translate_iff E _)

theorem connectedTile_connected (E : Tile 3) :
    FaceConnected (connectedTile E) :=
  connectedAssembly_connected _ _ (by unfold cubeSize; omega)
    (positiveTile_in_cube E)

theorem connectedTile_nonempty (E : Tile 3) (hE : E ≠ []) :
    connectedTile E ≠ [] :=
  connectedAssembly_nonempty _ _ (by unfold cubeSize; omega)
    (by intro he; exact hE (List.map_eq_nil_iff.mp he))

/-- Both tilability directions and connectedness of the concrete construction,
conditional only on the paper's three explicitly named mathematical inputs. -/
theorem exists_connected_tile (h : ReductionInputs) (T : LeanWang.TileSet) :
    ∃ F : Tile 3, F ≠ [] ∧ FaceConnected F ∧
      (LeanWang.TilesPlane T ↔ TranslationTiling.Tiles F) := by
  obtain ⟨F, hF, hcorrect⟩ := exists_integer_tile Sudoku.soundness h.rigidity T
  have hlist : F.toList ≠ [] := by
    intro he
    obtain ⟨x, hx⟩ := hF
    have hm : x ∈ F.toList := Finset.mem_toList.mpr hx
    simpa only [he, List.not_mem_nil] using hm
  have hlistcorrect : (∃ A : Set (Lattice 3), Tiles F A) ↔
      TranslationTiling.Tiles F.toList := by
    simp only [Tiles, TranslationTiling.Tiles, Stacking.covers_iff_exactTiling]
    have he : {f : Lattice 3 | f ∈ F.toList} = (F : Set (Lattice 3)) := by
      ext f; exact Finset.mem_toList
    rw [he]
  exact ⟨connectedTile F.toList, connectedTile_nonempty _ hlist,
    connectedTile_connected _,
    (hcorrect.trans hlistcorrect).trans (connectedTile_correct h.shellRigidity _).symm⟩

end
end TranslationTiling.Compiler
