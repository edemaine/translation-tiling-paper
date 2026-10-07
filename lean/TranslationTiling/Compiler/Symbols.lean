import TranslationTiling.Proofs.FiniteWordRule
import TranslationTiling.Proofs.FiniteTiling
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Sigma

set_option maxRecDepth 1000

namespace TranslationTiling.Compiler

abbrev Plane := ℤ × ℤ
abbrev Column (_T : LeanWang.TileSet) := Sudoku.Column
abbrev Symbol (T : LeanWang.TileSet) := Sudoku.Symbol T
abbrev Word (T : LeanWang.TileSet) := Column T → Symbol T
abbrev WordArray (T : LeanWang.TileSet) := Sudoku.Array T
abbrev Channel (T : LeanWang.TileSet) := Column T ⊕ Fin 2
-- A symbolic copy of the fixed modulus avoids reducing billion-step casts in
-- the kernel. Its value is proved, and only used to construct tiling witnesses.
noncomputable def residueModulus : ℕ :=
  Classical.choose (show ∃ m : ℕ, m = Sudoku.Width from ⟨Sudoku.Width, rfl⟩)
theorem residueModulus_eq : residueModulus = Sudoku.Width :=
  Classical.choose_spec (show ∃ m : ℕ, m = Sudoku.Width from ⟨Sudoku.Width, rfl⟩)
noncomputable abbrev D (_T : LeanWang.TileSet) := residueModulus ^ 2
abbrev Residues (_T : LeanWang.TileSet) := ZMod residueModulus × ZMod residueModulus

-- Keep the huge fixed finite universes symbolic during kernel checking.
-- These enumerations are used in proofs, not as the executable compiler.
noncomputable abbrev columnFintype : Fintype Sudoku.Column := Fintype.ofFinite _
attribute [instance 2000] columnFintype
noncomputable abbrev channelFintype : Fintype (Sudoku.Column ⊕ Fin 2) := Fintype.ofFinite _
attribute [instance 2000] channelFintype
noncomputable instance (priority := 2000) symbolFintype (T : LeanWang.TileSet) :
    Fintype (Sudoku.Symbol T) := Fintype.ofFinite _

instance widthNeZero : NeZero Sudoku.Width := ⟨by decide⟩
instance residueModulusNeZero : NeZero residueModulus :=
  ⟨by rw [residueModulus_eq]; decide⟩
instance dNeZero (T : LeanWang.TileSet) : NeZero (D T) :=
  ⟨by change residueModulus ^ 2 ≠ 0; rw [residueModulus_eq]; decide⟩

def Label (T : LeanWang.TileSet) : Channel T → Type
  | .inl _ => Symbol T
  | .inr _ => Unit

noncomputable instance labelFintype (T : LeanWang.TileSet) (i : Channel T) : Fintype (Label T i) := by
  cases i <;> dsimp [Label] <;> infer_instance

instance labelDecidableEq (T : LeanWang.TileSet) (i : Channel T) : DecidableEq (Label T i) := by
  cases i <;> dsimp [Label] <;> infer_instance

abbrev Tiles {G : Type*} [AddCommGroup G] (F : Finset G) (A : Set G) := Stacking.Covers F A
abbrev tiles_iff_unique_tile := @Stacking.covers_iff_unique_tile
abbrev Allowed := Sudoku.Allowed
abbrev allowedWords := Sudoku.allowedWords
abbrev mem_allowedWords := Sudoku.mem_allowedWords

def lineValue (n : Sudoku.Column) (x : Plane) : ℤ :=
  x.2 + (n.val : ℤ) * x.1

def lineKernelStep (n : Sudoku.Column) : Plane := (1, -(n.val : ℤ))

@[simp] theorem lineValue_vertical {T : LeanWang.TileSet} (n : Column T) (m : ℤ) :
    lineValue n (0, m) = m := by simp [lineValue]

end TranslationTiling.Compiler
