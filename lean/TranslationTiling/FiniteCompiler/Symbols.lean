import TranslationTiling.Compiler.Symbols

/-! A finite line-rule system with two seed predicates. Column slopes may repeat. -/

namespace TranslationTiling.FiniteCompiler

structure System where
  width : ℕ
  width_pos : 0 < width
  alphabet : ℕ
  slope : Fin width → ℤ
  allowed : Set (Fin width → Fin alphabet)
  seed : Fin 2 → Fin alphabet → Prop

abbrev Plane := ℤ × ℤ
abbrev Column (T : System) := Fin T.width
abbrev Symbol (T : System) := Fin T.alphabet
abbrev Word (T : System) := Column T → Symbol T
abbrev WordArray (T : System) := Column T → ℤ → Symbol T
abbrev Channel (T : System) := Column T ⊕ Fin 2
noncomputable abbrev residueModulus := Compiler.residueModulus
theorem residueModulus_eq : residueModulus = Sudoku.Width := Compiler.residueModulus_eq
noncomputable abbrev D (_T : System) := residueModulus ^ 2
abbrev Residues (_T : System) := ZMod residueModulus × ZMod residueModulus

instance widthNeZero (T : System) : NeZero T.width := ⟨T.width_pos.ne'⟩
instance residueModulusNeZero : NeZero residueModulus := Compiler.residueModulusNeZero
instance dNeZero (T : System) : NeZero (D T) := inferInstanceAs (NeZero (residueModulus ^ 2))

def Label (T : System) : Channel T → Type
  | .inl _ => Symbol T
  | .inr _ => Unit

instance labelFintype (T : System) (i : Channel T) : Fintype (Label T i) := by
  cases i <;> dsimp [Label] <;> infer_instance

instance labelDecidableEq (T : System) (i : Channel T) : DecidableEq (Label T i) := by
  cases i <;> dsimp [Label] <;> infer_instance

abbrev Tiles {G : Type*} [AddCommGroup G] (F : Finset G) (A : Set G) := Stacking.Covers F A
abbrev tiles_iff_unique_tile := @Stacking.covers_iff_unique_tile
def Allowed (T : System) (w : Word T) : Prop := w ∈ T.allowed
noncomputable def allowedWords (T : System) : Finset (Word T) := by
  classical
  exact Finset.univ.filter (Allowed T)

@[simp] theorem mem_allowedWords (T : System) (w : Word T) :
    w ∈ allowedWords T ↔ Allowed T w := by classical simp [allowedWords]

def SeedSet (T : System) (t : Fin 2) (j : Symbol T) : Prop := T.seed t j
def lineValue (T : System) (n : Column T) (x : Plane) : ℤ := x.2 + T.slope n * x.1
def lineKernelStep (T : System) (n : Column T) : Plane := (1, -T.slope n)

@[simp] theorem lineValue_vertical (T : System) (n : Column T) (m : ℤ) :
    lineValue T n (0, m) = m := by simp [lineValue]

def LineRule (T : System) (W : WordArray T) : Prop :=
  ∀ x : Plane, Allowed T (fun n => W n (lineValue T n x))

end TranslationTiling.FiniteCompiler
