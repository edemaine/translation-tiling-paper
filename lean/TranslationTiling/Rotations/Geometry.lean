import TranslationTiling.Proofs.FacePaths
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Pi
import Mathlib.Data.Int.Interval
import Mathlib.Data.Fintype.Pi

/-! The six-key gadget. Coordinates name voxels by their lower corners.
`i / 2` is the face axis, and even indices name its negative face. -/

namespace TranslationTiling.Rotations.SixKeys

abbrev Point := Lattice 3
abbrev Face := Fin 6

def axis (i : Face) : Fin 3 := ⟨i.val / 2, by omega⟩
def negative (i : Face) : Bool := i.val % 2 == 0
def normal (i : Face) : Point := Pi.single (axis i) (if negative i then 1 else -1)
def gate (i : Face) : Point := fun j =>
  if j = axis i then (if negative i then 0 else 39)
  else if negative i then 12 else 13
def tangent₁ (i : Face) : Fin 3 := if axis i = 0 then 1 else 0
def tangent₂ (i : Face) : Fin 3 := if axis i = 2 then 1 else 2
def dimensions (i : Face) : ℕ × ℕ × ℕ :=
  ![(3,8,15), (3,10,12), (4,6,15), (4,9,10), (5,6,12), (5,8,9)] i
def localPoint (i : Face) (k u v : ℕ) : Point :=
  gate i + (k : ℤ) • normal i +
    (u : ℤ) • Pi.single (tangent₁ i) 1 + (v : ℤ) • Pi.single (tangent₂ i) 1

def recess (i : Face) : Finset Point :=
  ((Finset.range 5).image fun k => localPoint i k 0 0) ∪
  ((Finset.range (dimensions i).1).biUnion fun k =>
    (Finset.range (dimensions i).2.1).biUnion fun u =>
      (Finset.range (dimensions i).2.2).image fun v => localPoint i (5+k) u v)
def chamber (i : Face) : Finset Point := (recess i).erase (gate i)
def cube : Finset Point :=
  Fintype.piFinset fun _ : Fin 3 => Finset.Icc (0 : ℤ) 39
def removed : Finset Point := Finset.univ.biUnion recess
def body : Finset Point := cube \ removed
def shift (i : Face) : Point := (40 : ℤ) • normal i
def protrusion (i : Face) : Finset Point :=
  (recess i).image (shift i + ·)
def gadget : Finset Point := body ∪ Finset.univ.biUnion protrusion

/-- Flattening a voxel in the 40-cube, used only to check finite certificates. -/
def encode (x : Point) : ℕ := (1600 * x 0 + 40 * x 1 + x 2).toNat
def decode (j : ℕ) : Point := ![(j / 1600 : ℕ), ((j / 40) % 40 : ℕ), (j % 40 : ℕ)]

theorem decode_bounds {j : ℕ} (hj : j < 64000) (i : Fin 3) :
    0 ≤ decode j i ∧ decode j i ≤ 39 := by
  fin_cases i <;> simp [decode] <;> omega

theorem encode_decode {j : ℕ} (hj : j < 64000) : encode (decode j) = j := by
  have h₀ := Nat.mod_add_div j 40
  have h₁ := Nat.mod_add_div (j / 40) 40
  have h₂ : j / 40 / 40 = j / 1600 := by omega
  change ((1600 : ℤ) * ↑(j / 1600) + 40 * ↑((j / 40) % 40) + ↑(j % 40)).toNat = j
  have he : (1600 : ℤ) * (↑(j / 1600) : ℤ) + 40 * ↑((j / 40) % 40) + ↑(j % 40) = ↑j := by
    omega
  rw [he]
  exact Int.toNat_natCast j

theorem decode_encode {x : Point} (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 39) :
    decode (encode x) = x := by
  have h₀ := hx 0; have h₁ := hx 1; have h₂ := hx 2
  have hpos : 0 ≤ 1600 * x 0 + 40 * x 1 + x 2 := by omega
  have he := Int.toNat_of_nonneg hpos
  ext i
  fin_cases i <;> simp [decode, encode] <;> omega

theorem encode_lt {x : Point} (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 39) : encode x < 64000 := by
  have h₀ := hx 0; have h₁ := hx 1; have h₂ := hx 2
  unfold encode
  omega

end TranslationTiling.Rotations.SixKeys
