import TranslationTiling.Rotations.General.MatrixAlignment
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace TranslationTiling.Rotations.General
noncomputable section
open scoped BigOperators

abbrev EPoint (d : ℕ) := EuclideanSpace ℝ (Fin d)

abbrev Rotation (d : ℕ) := EPoint d ≃ₗᵢ[ℝ] EPoint d

variable {d : ℕ}

def castPoint (z : Lattice d) : EPoint d := WithLp.toLp 2 fun i => (z i : ℝ)

@[simp] theorem castPoint_apply (z : Lattice d) (i : Fin d) : castPoint z i = (z i : ℝ) := rfl
@[simp] theorem castPoint_zero : castPoint (0 : Lattice d) = 0 := by ext i; simp
@[simp] theorem castPoint_add (z w : Lattice d) : castPoint (z+w) = castPoint z + castPoint w := by
  ext i; simp

theorem sign_real_sq (r : Orientation d) (i : Fin d) :
    (r.sign i : ℝ) * (r.sign i : ℝ) = 1 := by exact_mod_cast r.sign_sq i

theorem sign_real_abs (r : Orientation d) (i : Fin d) : |(r.sign i : ℝ)| = 1 := by
  unfold Orientation.sign; split_ifs <;> norm_num

/-- Embed a signed coordinate permutation into the full Euclidean orthogonal group. -/
def gridRotation (r : Orientation d) : Rotation d where
  toFun x := WithLp.toLp 2 fun i => (r.sign i : ℝ) * x (r.axes i)
  invFun y := WithLp.toLp 2 fun i => (r.sign (r.axes.symm i) : ℝ) * y (r.axes.symm i)
  left_inv x := by
    ext i
    simp only [PiLp.toLp_apply, Equiv.apply_symm_apply, ← mul_assoc, sign_real_sq, one_mul]
  right_inv y := by
    ext i
    simp only [PiLp.toLp_apply, Equiv.symm_apply_apply, ← mul_assoc, sign_real_sq, one_mul]
  map_add' x y := by ext i; simp only [PiLp.toLp_apply, PiLp.add_apply]; ring
  map_smul' c x := by
    ext i
    simp only [PiLp.toLp_apply, PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring
  norm_map' x := by
    change ‖WithLp.toLp 2 (fun i => (r.sign i : ℝ) * x (r.axes i))‖ = ‖x‖
    have hs (i : Fin d) : (r.sign i : ℝ) ^ 2 = 1 := by simpa only [pow_two] using sign_real_sq r i
    have he : ‖WithLp.toLp 2 (fun i => (r.sign i : ℝ) * x (r.axes i))‖ ^ 2 = ‖x‖ ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
      simp only [PiLp.toLp_apply, mul_pow, hs, one_mul]
      exact Equiv.sum_comp r.axes (fun i => (x i)^2)
    nlinarith [norm_nonneg x, norm_nonneg (WithLp.toLp 2 (fun i => (r.sign i : ℝ) * x (r.axes i)))]

@[simp] theorem gridRotation_apply (r : Orientation d) (x : EPoint d) (i : Fin d) :
    gridRotation r x i = (r.sign i : ℝ) * x (r.axes i) := rfl


def unitCube : Set (EPoint d) := {x | ∀ i, |x i| ≤ (1:ℝ)/2}

def row (R : Rotation d) : RealMatrix d := fun i j =>
  R.symm (EuclideanSpace.single i (1 : ℝ)) j

theorem row_action (R : Rotation d) (x : EPoint d) (i : Fin d) :
    R x i = ∑ j, row R i j * x j := by
  have h := R.inner_map_map (R.symm (EuclideanSpace.single i (1:ℝ))) x
  simpa [row, PiLp.inner_apply, EuclideanSpace.inner_single_left, mul_comm] using h

theorem row_orthogonal (R : Rotation d) : OrthonormalRows (row R) := by
  intro i j
  have h := R.symm.inner_map_map (EuclideanSpace.single i (1:ℝ)) (EuclideanSpace.single j (1:ℝ))
  rw [PiLp.inner_apply] at h
  simpa only [row, RCLike.inner_apply, conj_trivial,
    EuclideanSpace.inner_single_left, one_mul, PiLp.single_apply, mul_one, mul_comm] using h

/-- The full width of an orthogonally rotated unit cube in a coordinate
direction is the one-norm of the corresponding matrix row. -/
theorem row_width_le_one (R : Rotation d) (t : EPoint d) (i : Fin d) (a : ℝ)
    (h : ∀ x ∈ unitCube, a ≤ t i + R x i ∧ t i + R x i ≤ a+1) :
    ∑ j, |row R i j| ≤ 1 := by
  let p : EPoint d := WithLp.toLp 2 fun j => if 0 ≤ row R i j then (1:ℝ)/2 else -1/2
  have hp : p ∈ unitCube := by
    intro j
    dsimp [p]
    split_ifs <;> norm_num
  have hm : -p ∈ unitCube := by intro j; simpa only [PiLp.neg_apply, abs_neg] using hp j
  have he : R p i = (1:ℝ)/2 * ∑ j, |row R i j| := by
    rw [row_action, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : 0 ≤ row R i j
    · simp [p, hj, abs_of_nonneg hj]
      ring
    · simp [p, hj, abs_of_neg (by linarith : row R i j < 0)]
      ring
  have hb := h p hp
  have hc := h (-p) hm
  simp only [map_neg, PiLp.neg_apply, he] at hc
  rw [he] at hb
  linarith


/-- Fitting a Euclidean unit cube into an axial neck forces its complete
orientation to preserve the grid, even when reflections are permitted. -/
theorem cube_alignment (R : Rotation d) (t : EPoint d) (a : Fin d)
    (lower : Fin d → ℝ)
    (hw : ∀ i, i ≠ a → ∀ x ∈ unitCube,
      lower i ≤ t i + R x i ∧ t i + R x i ≤ lower i + 1) :
    ∃ r : Orientation d, R = gridRotation r := by
  obtain ⟨r,hr⟩ := matrix_alignment (row_orthogonal R) a
    (fun i hi => row_width_le_one R t i (lower i) (hw i hi))
  refine ⟨r,?_⟩
  ext x i
  rw [row_action,hr]
  simp [gridMatrix]

/-- A convenient dimension-dependent upper bound for the Euclidean diameter. -/
theorem unitCube_diameter {x y : EPoint d} (hx : x ∈ unitCube) (hy : y ∈ unitCube) :
    dist x y < (d : ℝ) + 1 := by
  have bound (i : Fin d) : (x i - y i)^2 ≤ 1 := by
    have hxi := abs_le.mp (hx i)
    have hyi := abs_le.mp (hy i)
    nlinarith [sq_nonneg (x i - y i - 1),sq_nonneg (x i - y i + 1)]
  have hs : ∑ i, (x i - y i)^2 ≤ (d : ℝ) := by
    calc
      _ ≤ ∑ _i : Fin d, (1 : ℝ) := Finset.sum_le_sum (fun i _ => bound i)
      _ = _ := by simp
  have he := EuclideanSpace.real_norm_sq_eq (x-y)
  simp only [PiLp.sub_apply] at he
  rw [dist_eq_norm]
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  nlinarith [norm_nonneg (x-y)]

end
end TranslationTiling.Rotations.General
