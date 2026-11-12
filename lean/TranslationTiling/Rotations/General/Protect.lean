import TranslationTiling.Rotations.General.ConnectedAssembly
import TranslationTiling.Compiler.EffectiveArithmetic

namespace TranslationTiling.Rotations.General
noncomputable section
open Compiler.Effective
variable {d : ℕ} [NeZero d]

/-- Replace every input voxel by one translated copy of the fixed gadget. -/
def protect (E : Tile d) : Tile d :=
  E.flatMap fun e => gadget.toList.map fun u => grid e + u

theorem protect_mem (E : Tile d) (x : Lattice d) :
    x ∈ protect E ↔ x ∈ assembly E.toFinset := by
  simp only [protect, List.mem_flatMap, List.mem_map, Finset.mem_toList,
    mem_assembly, List.mem_toFinset]
  constructor
  · rintro ⟨e, he, u, hu, h⟩
    exact ⟨e, he, u, hu, h.symm⟩
  · rintro ⟨e, he, u, hu, h⟩
    exact ⟨e, he, u, hu, h.symm⟩

theorem protect_toFinset (E : Tile d) : (protect E).toFinset = assembly E.toFinset := by
  ext x
  simp [protect_mem]

theorem protect_primrec : Primrec (protect (d := d)) := by
  unfold protect grid
  apply flatMapList Primrec.id
  apply mapList (Primrec.const (gadget.toList : List (Lattice d)))
  apply piValue
  intro i
  change Primrec (fun z : (Tile d × Lattice d) × Lattice d =>
    (cubeSide d : ℤ)*z.1.2 i+z.2 i)
  fun_prop

theorem protect_connected (hd : 3 ≤ d) (E : Tile d) (hE : FaceConnected E) : FaceConnected (protect E) := by
  have hset : Connected (E.toFinset : Set (Lattice d)) := by
    intro x hx y hy
    have hxE : x ∈ E := by simpa using hx
    have hyE : y ∈ E := by simpa using hy
    exact FacePath.mono (hE x hxE y hyE) (by intro z hz; simpa using hz)
  intro x hx y hy
  have p := assembly_connected hd E.toFinset hset x ((protect_mem _ _).mp hx)
    y ((protect_mem _ _).mp hy)
  exact FacePath.mono p (fun z hz => (protect_mem E z).mpr hz)

theorem protect_nonempty (hd : 3 ≤ d) (E : Tile d) (hE : E ≠ []) : protect E ≠ [] := by
  obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil E hE
  have hx : grid e ∈ protect E := (protect_mem _ _).mpr
    ((mem_assembly _ _).mpr ⟨e, by simpa using he, 0, body_subset_gadget (zero_body (by omega : 2 ≤ d)), by simp⟩)
  intro hn
  simpa [hn] using hx

theorem protect_correct (hd : 3 ≤ d) (E : Tile d) (hE : E ≠ [])
    (allowed : Set (Orientation d)) (hid : Orientation.ident ∈ allowed) :
    TranslationTiling.Tiles E ↔ AllowedGridTiles allowed (protect E).toFinset := by
  have hn : E.toFinset.Nonempty := by
    obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil E hE
    exact ⟨e, by simpa using he⟩
  have ht : FiniteTiles E.toFinset ↔ TranslationTiling.Tiles E := by
    simp [FiniteTiles, TranslationTiling.Tiles]
  rw [protect_toFinset]
  exact ht.symm.trans (assembly_allowed_iff hd E.toFinset hn allowed hid)


end
end TranslationTiling.Rotations.General
