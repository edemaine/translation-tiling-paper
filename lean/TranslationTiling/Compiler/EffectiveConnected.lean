import TranslationTiling.Compiler.ConnectedCompiler
import TranslationTiling.Compiler.EffectiveArithmetic

namespace TranslationTiling.Compiler

open Effective

@[fun_prop] theorem latticePlus {α : Type*} [Primcodable α]
    {f g : α → Lattice 3} (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun a => f a + g a) := by
  apply piValue
  intro i
  change Primrec (fun a => f a i + g a i)
  fun_prop

@[fun_prop] theorem latticeScale {α : Type*} [Primcodable α]
    {f : α → ℤ} {g : α → Lattice 3} (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun a => f a • g a) := by
  apply piValue
  intro i
  change Primrec (fun a => f a * g a i)
  fun_prop

@[fun_prop] theorem cube_primrec : Primrec Kim.cube := by
  unfold Kim.cube
  fun_prop

private theorem boundary_condition (l : ℕ) (x : Lattice 3) :
    (∃ i : Fin 3, x i = 0 ∨ x i = (l : ℤ) - 1) ↔
      (x 0 = 0 ∨ x 0 = (l : ℤ) - 1) ∨
      (x 1 = 0 ∨ x 1 = (l : ℤ) - 1) ∨
      (x 2 = 0 ∨ x 2 = (l : ℤ) - 1) := by
  constructor
  · rintro ⟨i, hi⟩
    fin_cases i
    · exact Or.inl hi
    · exact Or.inr (Or.inl hi)
    · exact Or.inr (Or.inr hi)
  · rintro (hi | hi | hi)
    · exact ⟨0, hi⟩
    · exact ⟨1, hi⟩
    · exact ⟨2, hi⟩

@[fun_prop] theorem boundary_primrec : Primrec Kim.boundary := by
  have hp : PrimrecPred (fun z : ℕ × Lattice 3 =>
      ∃ i : Fin 3, z.2 i = 0 ∨ z.2 i = (z.1 : ℤ) - 1) := by
    apply (show PrimrecPred (fun z : ℕ × Lattice 3 =>
      (z.2 0 = 0 ∨ z.2 0 = (z.1 : ℤ) - 1) ∨
      (z.2 1 = 0 ∨ z.2 1 = (z.1 : ℤ) - 1) ∨
      (z.2 2 = 0 ∨ z.2 2 = (z.1 : ℤ) - 1)) from by fun_prop).of_eq
    intro z
    exact (boundary_condition z.1 z.2).symm
  exact filterList cube_primrec hp

@[fun_prop] theorem color_primrec : Primrec (fun z : ℕ × Lattice 3 => Kim.color z.1 z.2) := by
  unfold Kim.color
  fun_prop

@[fun_prop] theorem scale_primrec : Primrec Kim.scale := by unfold Kim.scale; fun_prop

@[fun_prop] theorem dents_primrec : Primrec Kim.dents := by
  unfold Kim.dents
  -- A fixed-length list is assembled from its primitive-recursive entries.
  apply Primrec.list_cons.comp
  · fun_prop
  · apply Primrec.list_cons.comp
    · fun_prop
    · apply Primrec.list_cons.comp
      · fun_prop
      · exact Primrec.const []

@[fun_prop] theorem piece_primrec : Primrec (fun z : ℕ × ℕ => Kim.piece z.1 z.2) := by
  have hc : PrimrecPred (fun z : (ℕ × ℕ) × Lattice 3 => Kim.color z.1.1 z.2 = z.1.2) := by
    fun_prop
  have hR : Primrec (fun z : ℕ × ℕ =>
      ((Kim.cube (z.1 + 2)).filter fun v => Kim.color z.1 v == z.2).flatMap
        fun q => (Kim.cube 3).map fun c => (3 : ℤ) • q + c) := by
    have hf : Primrec (fun z : ℕ × ℕ =>
        (Kim.cube (z.1 + 2)).filter fun v => decide (Kim.color z.1 v = z.2)) := by
      exact filterList (by fun_prop) hc
    have hf' : Primrec (fun z : ℕ × ℕ =>
        (Kim.cube (z.1 + 2)).filter fun v => Kim.color z.1 v == z.2) := by
      simpa only [Bool.beq_eq_decide_eq] using hf
    exact flatMapList hf' (by fun_prop)
  unfold Kim.piece
  apply iteValue (by fun_prop)
  · apply appendList
    · exact filterList hR (by fun_prop)
    · exact Primrec.const _
  · exact hR

@[fun_prop] theorem shell_primrec : Primrec Kim.shell := by
  unfold Kim.shell
  apply flatMapList ((zipIdx_primrec (0 : Lattice 3)).comp boundary_primrec)
  fun_prop

@[fun_prop] theorem pointBound_primrec : Primrec pointBound := by unfold pointBound; fun_prop

@[fun_prop] theorem coordinateBound_primrec : Primrec coordinateBound := by
  unfold coordinateBound
  exact foldList (h := fun (_ : Tile 3) (z : Lattice 3 × ℕ) => max (pointBound z.1) z.2)
    Primrec.id (Primrec.const 0) (by fun_prop)

@[fun_prop] theorem cubeSize_primrec : Primrec cubeSize := by unfold cubeSize; fun_prop

@[fun_prop] theorem positiveTile_primrec : Primrec positiveTile := by
  unfold positiveTile
  apply mapList Primrec.id
  apply latticePlus Primrec.snd
  apply piValue
  intro i
  fun_prop

@[fun_prop] theorem connectedAssembly_primrec :
    Primrec (fun z : Tile 3 × ℕ => connectedAssembly z.1 z.2) := by
  unfold connectedAssembly
  fun_prop

/-- Kim's complete finite construction is primitive recursive in the input tile. -/
theorem connectedTile_primrec : Primrec connectedTile := by unfold connectedTile; fun_prop

theorem connectedTile_computable : Computable connectedTile := connectedTile_primrec.to_comp

/-- Any computable lattice compiler extends to a computable connected compiler;
all shell effectivity is proved here, rather than imported with rigidity. -/
theorem connectedReduction_of_reduction (rigid : Kim.Rigidity) (r : WangReduction) :
    Nonempty ConnectedWangReduction := by
  exact ⟨{
    tile := fun T => connectedTile (r.tile T)
    computable := connectedTile_computable.comp r.computable
    nonempty := fun T hT => connectedTile_nonempty rigid _ (r.nonempty T hT)
    correct := fun T => (r.correct T).trans (connectedTile_correct rigid _).symm
    connected := fun T _ => connectedTile_connected rigid (r.tile T)
  }⟩

end TranslationTiling.Compiler
