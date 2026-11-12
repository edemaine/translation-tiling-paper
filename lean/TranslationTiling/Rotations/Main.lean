import TranslationTiling.Rotations.ConnectedAssembly
import TranslationTiling.Compiler.Main
import TranslationTiling.Proofs.Complexity
import Mathlib.GroupTheory.Perm.Sign

namespace TranslationTiling.Rotations.SixKeys

noncomputable section
open Compiler.Effective

/-- Determinant +1 selects the proper grid rotations from the signed permutations. -/
def Proper (r : Orientation) : Prop :=
  (r.axes.sign : ℤ) * ∏ i : Fin 3, r.sign i = 1

theorem proper_ident : Proper Orientation.ident := by
  simp [Proper, Orientation.ident, Orientation.sign]

/-- Replace every input voxel by one translated copy of the fixed gadget. -/
def protect (E : Tile 3) : Tile 3 :=
  E.flatMap fun e => gadget.toList.map fun u => grid e + u

theorem protect_mem (E : Tile 3) (x : Point) :
    x ∈ protect E ↔ x ∈ assembly E.toFinset := by
  simp only [protect, List.mem_flatMap, List.mem_map, Finset.mem_toList,
    mem_assembly, List.mem_toFinset]
  constructor
  · rintro ⟨e, he, u, hu, h⟩
    exact ⟨e, he, u, hu, h.symm⟩
  · rintro ⟨e, he, u, hu, h⟩
    exact ⟨e, he, u, hu, h.symm⟩

theorem protect_toFinset (E : Tile 3) : (protect E).toFinset = assembly E.toFinset := by
  ext x
  simp [protect_mem]

theorem protect_primrec : Primrec protect := by
  unfold protect grid
  fun_prop

theorem protect_connected (E : Tile 3) (hE : FaceConnected E) : FaceConnected (protect E) := by
  have hset : Connected (E.toFinset : Set Point) := by
    intro x hx y hy
    have hxE : x ∈ E := by simpa using hx
    have hyE : y ∈ E := by simpa using hy
    exact FacePath.mono (hE x hxE y hyE) (by intro z hz; simpa using hz)
  intro x hx y hy
  have p := assembly_connected E.toFinset hset x ((protect_mem _ _).mp hx)
    y ((protect_mem _ _).mp hy)
  exact FacePath.mono p (fun z hz => (protect_mem E z).mpr hz)

theorem protect_nonempty (E : Tile 3) (hE : E ≠ []) : protect E ≠ [] := by
  obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil E hE
  have hx : grid e ∈ protect E := (protect_mem _ _).mpr
    ((mem_assembly _ _).mpr ⟨e, by simpa using he, 0, body_subset_gadget zero_body, by simp⟩)
  intro hn
  simpa [hn] using hx

theorem protect_correct (E : Tile 3) (hE : E ≠ [])
    (allowed : Set Orientation) (hid : Orientation.ident ∈ allowed) :
    TranslationTiling.Tiles E ↔ AllowedGridTiles allowed (protect E).toFinset := by
  have hn : E.toFinset.Nonempty := by
    obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil E hE
    exact ⟨e, by simpa using he⟩
  have ht : FiniteTiles E.toFinset ↔ TranslationTiling.Tiles E := by
    simp [FiniteTiles, TranslationTiling.Tiles]
  rw [protect_toFinset]
  exact ht.symm.trans (assembly_allowed_iff E.toFinset hn allowed hid)

def ProtectedTileable (allowed : Set Orientation) (P : Tile 3) : Prop :=
  FaceConnected P ∧ AllowedGridTiles allowed P.toFinset

def rotationCompile (T : LeanWang.TileSet) : Tile 3 := protect (Compiler.connectedCompile T)

theorem rotationCompile_computable : Computable rotationCompile :=
  (Primrec.to_comp protect_primrec).comp Compiler.connectedCompile_computable

theorem rotationCompile_nonempty (T : LeanWang.TileSet) : rotationCompile T ≠ [] :=
  protect_nonempty _ (Compiler.connectedCompile_nonempty T)

theorem rotationCompile_connected (T : LeanWang.TileSet) : FaceConnected (rotationCompile T) :=
  protect_connected _ (Compiler.connectedCompile_connected T)

theorem rotationCompile_correct (allowed : Set Orientation) (hid : Orientation.ident ∈ allowed)
    (T : LeanWang.TileSet) : LeanWang.TilesPlane T ↔ ProtectedTileable allowed (rotationCompile T) := by
  have h := (Compiler.connectedCompile_correct T).trans
    (protect_correct _ (Compiler.connectedCompile_nonempty T) allowed hid)
  exact ⟨fun ht => ⟨rotationCompile_connected T, h.mp ht⟩, fun ht => h.mpr ht.2⟩

/-- The same computable reduction works for any prescribed set of signed
coordinate permutations containing the identity. -/
theorem rotation_coRE_hard (allowed : Set Orientation) (hid : Orientation.ident ∈ allowed) :
    LeanWang.CoREHard (ProtectedTileable allowed) := by
  intro α _ P hP
  exact (LeanWang.Kari.domino_problem_coRE_hard P hP).trans
    ⟨rotationCompile, rotationCompile_computable, rotationCompile_correct allowed hid⟩

/-- Hardness for one face-connected polycube with the proper grid rotations. -/
theorem proper_rotation_coRE_hard : LeanWang.CoREHard (ProtectedTileable {r | Proper r}) :=
  rotation_coRE_hard _ proper_ident

theorem proper_rotation_undecidable : ¬ ComputablePred (ProtectedTileable {r | Proper r}) := by
  intro h
  exact LeanWang.Kari.domino_problem_undecidable
    (ComputablePred.computable_of_manyOneReducible
      ⟨rotationCompile, rotationCompile_computable, rotationCompile_correct _ proper_ident⟩ h)

end
end TranslationTiling.Rotations.SixKeys
