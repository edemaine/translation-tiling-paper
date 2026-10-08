import TranslationTiling.Connectivity
import TranslationTiling.External.Geometry
import Mathlib.Data.Fin.VecNotation

/-! Kim's explicitly constructed shell and its imported rigidity statement.
The connectedness reduction itself is not assumed here. -/

namespace TranslationTiling.Kim

/-- Lexicographic enumeration of the nonnegative lattice cube. -/
def cube (l : ℕ) : Tile 3 :=
  (List.range l).flatMap fun x : ℕ => (List.range l).flatMap fun y : ℕ =>
    (List.range l).map fun z : ℕ => ![(x : ℤ), (y : ℤ), (z : ℤ)]

def boundary (l : ℕ) : Tile 3 :=
  (cube l).filter fun x => decide (∃ i : Fin 3, x i = 0 ∨ x i = (l : ℤ) - 1)

/-- Kim's partition, with colors indexed from one. -/
def color (m : ℕ) (v : Lattice 3) : ℕ :=
  let x := v 0; let y := v 1; let z := v 2
  if 0 ≤ x ∧ x ≤ m ∧ 1 ≤ y ∧ y ≤ m ∧ z = 0 then y.toNat
  else if 1 ≤ x ∧ x ≤ m ∧ 0 ≤ y ∧ y ≤ m ∧ z = (m : ℤ) + 1 then x.toNat
  else if x = 0 ∧ 1 ≤ y ∧ y ≤ m ∧ 1 ≤ z ∧ z ≤ m then y.toNat
  else if 1 ≤ x ∧ x ≤ m ∧ y = 0 ∧ 1 ≤ z ∧ z ≤ m then x.toNat
  else if 1 ≤ x ∧ x ≤ (m : ℤ) + 1 ∧ 1 ≤ y ∧ y ≤ (m : ℤ) + 1 ∧
      1 ≤ z ∧ z ≤ m then z.toNat
  else 1

def scale (m : ℕ) : ℕ := 3 * m + 6

def bumps : Tile 3 := [![-1, 1, 1], ![1, -1, 1], ![1, 1, -1]]

def dents (m : ℕ) : Tile 3 :=
  let s : ℤ := scale m
  [![s - 1, 1, 1], ![1, s - 1, 1], ![1, 1, s - 1]]

def piece (m i : ℕ) : Tile 3 :=
  let R := ((cube (m + 2)).filter fun v => color m v == i).flatMap
    fun q => (cube 3).map fun c => 3 • q + c
  if i = 1 then (R.filter fun v => decide (v ∉ dents m)) ++ bumps else R

def shell (l : ℕ) : Tile 3 :=
  let X := boundary l
  X.zipIdx |>.flatMap fun p =>
    (piece X.length (p.2 + 1)).map fun q => (scale X.length : ℤ) • p.1 + q

def gridCoset (s : ℕ) (t : Lattice 3) : Set (Lattice 3) :=
  {a | ∃ z : Lattice 3, a = t + (s : ℤ) • z}

/-- The remaining shell input: every tiling complement is a grid coset. -/
def CosetRigidity : Prop :=
  ∀ l : ℕ, 3 ≤ l → ∀ A : Set (Lattice 3),
    ExactTiling A {x | x ∈ shell l} →
      ∃ t, A = gridCoset (scale (boundary l).length) t

/-- The precise shell input from Kim, arXiv:2508.11725v2, Section 2.
Both the grid fundamental domain and arbitrary-tiling rigidity are exposed. -/
def Rigidity : Prop :=
  ∀ l : ℕ, 3 ≤ l →
    let S := shell l
    let s := scale (boundary l).length
    FaceConnected S ∧
    ExactTiling (gridCoset s 0) {x | x ∈ S} ∧
    (∀ u ∈ cube l, ∀ v ∈ cube l, u ≠ v →
      Disjoint {x | ∃ a ∈ S, x = (s : ℤ) • u + a}
        {x | ∃ b ∈ S, x = (s : ℤ) • v + b} ∧
      ∃ a ∈ S, ∃ b ∈ S, FaceAdjacent ((s : ℤ) • u + a) ((s : ℤ) • v + b)) ∧
    (∀ A : Set (Lattice 3), ExactTiling A {x | x ∈ S} →
      ∃ t, A = gridCoset s t)

end TranslationTiling.Kim
