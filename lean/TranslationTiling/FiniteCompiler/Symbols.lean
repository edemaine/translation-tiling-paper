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
/-- Finite label families, including the allowed words and seed predicates.
The default family recovers the original homogeneous-alphabet interface. -/
class AlphabetFamily (T : System) where
  size : Column T → ℕ
  allowed : Set ((n : Column T) → Fin (size n))
  seed : Fin 2 → (n : Column T) → Fin (size n) → Prop

instance (priority := low) uniformAlphabetFamily (T : System) : AlphabetFamily T where
  size _ := T.alphabet
  allowed := T.allowed
  seed t _ := T.seed t

@[simp] theorem uniform_size (T : System) (n : Column T) :
    @AlphabetFamily.size T (uniformAlphabetFamily T) n=T.alphabet := rfl
@[simp] theorem uniform_allowed (T : System) :
    @AlphabetFamily.allowed T (uniformAlphabetFamily T)=T.allowed := rfl
@[simp] theorem uniform_seed (T : System) (t : Fin 2) (n : Column T) (j : Symbol T) :
    @AlphabetFamily.seed T (uniformAlphabetFamily T) t n j=T.seed t j := rfl

abbrev Letter (T : System) [AlphabetFamily T] (n : Column T) :=
  Fin (AlphabetFamily.size (T:=T) n)
abbrev Word (T : System) [AlphabetFamily T] := (n : Column T) → Letter T n
abbrev WordArray (T : System) [AlphabetFamily T] := (n : Column T) → ℤ → Letter T n
abbrev Channel (T : System) := Column T ⊕ Fin 2
noncomputable abbrev residueModulus := Compiler.residueModulus
theorem residueModulus_eq : residueModulus = Sudoku.SeedModulus := Compiler.residueModulus_eq
noncomputable abbrev D (_T : System) := residueModulus ^ 2
abbrev Residues (_T : System) := ZMod residueModulus × ZMod residueModulus

instance widthNeZero (T : System) : NeZero T.width := ⟨T.width_pos.ne'⟩
instance residueModulusNeZero : NeZero residueModulus := Compiler.residueModulusNeZero
instance dNeZero (T : System) : NeZero (D T) := inferInstanceAs (NeZero (residueModulus ^ 2))

def Label (T : System) [AlphabetFamily T] : Channel T → Type
  | .inl n => Letter T n
  | .inr _ => Unit

instance labelFintype (T : System) [AlphabetFamily T] (i : Channel T) : Fintype (Label T i) := by
  cases i <;> dsimp [Label] <;> infer_instance

instance labelDecidableEq (T : System) [AlphabetFamily T] (i : Channel T) : DecidableEq (Label T i) := by
  cases i <;> dsimp [Label] <;> infer_instance

abbrev Tiles {G : Type*} [AddCommGroup G] (F : Finset G) (A : Set G) := Stacking.Covers F A
abbrev tiles_iff_unique_tile := @Stacking.covers_iff_unique_tile
def Allowed (T : System) [AlphabetFamily T] (w : Word T) : Prop :=
  w ∈ AlphabetFamily.allowed (T:=T)
noncomputable def allowedWords (T : System) [AlphabetFamily T] : Finset (Word T) := by
  classical
  exact Finset.univ.filter (Allowed T)

@[simp] theorem mem_allowedWords (T : System) [AlphabetFamily T] (w : Word T) :
    w ∈ allowedWords T ↔ Allowed T w := by classical simp [allowedWords]

def SeedSet (T : System) (t : Fin 2) (j : Symbol T) : Prop := T.seed t j
def LetterSeedSet (T : System) [AlphabetFamily T] (t : Fin 2) (n : Column T)
    (j : Letter T n) : Prop := AlphabetFamily.seed (T:=T) t n j

def lineValue (T : System) (n : Column T) (x : Plane) : ℤ := x.2 + T.slope n * x.1
def lineKernelStep (T : System) (n : Column T) : Plane := (1, -T.slope n)

@[simp] theorem lineValue_vertical (T : System) (n : Column T) (m : ℤ) :
    lineValue T n (0, m) = m := by simp [lineValue]

def LineRule (T : System) [AlphabetFamily T] (W : WordArray T) : Prop :=
  ∀ x : Plane, Allowed T (fun n => W n (lineValue T n x))

end TranslationTiling.FiniteCompiler
