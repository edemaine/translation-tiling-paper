import TranslationTiling.Rotations.Euclidean.Definitions

namespace TranslationTiling.Rotations.Euclidean

noncomputable section

open Set
open scoped BigOperators

def row (R : Rotation) : Matrix3 := fun i j =>
  R.symm (EuclideanSpace.single i (1 : ℝ)) j

theorem row_action (R : Rotation) (x : EPoint) (i : Fin 3) :
    R x i = ∑ j, row R i j * x j := by
  have h := R.inner_map_map (R.symm (EuclideanSpace.single i (1:ℝ))) x
  simpa [row, PiLp.inner_apply, EuclideanSpace.inner_single_left, mul_comm] using h

theorem row_orthogonal (R : Rotation) : OrthonormalRows (row R) := by
  intro i j
  have h := R.symm.inner_map_map (EuclideanSpace.single i (1:ℝ)) (EuclideanSpace.single j (1:ℝ))
  rw [PiLp.inner_apply] at h
  simpa only [row, RCLike.inner_apply, conj_trivial,
    EuclideanSpace.inner_single_left, one_mul, PiLp.single_apply, mul_one, mul_comm] using h

/-- The full width of an orthogonally rotated unit cube in a coordinate
direction is the one-norm of the corresponding matrix row. -/
theorem row_width_le_one (R : Rotation) (t : EPoint) (i : Fin 3) (a : ℝ)
    (h : ∀ x ∈ unitCube, a ≤ t i + R x i ∧ t i + R x i ≤ a+1) :
    ∑ j, |row R i j| ≤ 1 := by
  let p : EPoint := WithLp.toLp 2 fun j => if 0 ≤ row R i j then (1:ℝ)/2 else -1/2
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

/-- Fitting the whole unit cube into a one-by-one cross-section forces its
complete orientation to preserve the cubic grid. The axial direction is free. -/
theorem cube_alignment (R : Rotation) (t : EPoint) (a b : ℝ)
    (h1 : ∀ x ∈ unitCube, a ≤ t 1 + R x 1 ∧ t 1 + R x 1 ≤ a+1)
    (h2 : ∀ x ∈ unitCube, b ≤ t 2 + R x 2 ∧ t 2 + R x 2 ≤ b+1) :
    ∃ r : Orientation, R = gridRotation r := by
  obtain ⟨r, hr⟩ := matrix_alignment (row_orthogonal R)
    (row_width_le_one R t 1 a h1) (row_width_le_one R t 2 b h2)
  refine ⟨r, ?_⟩
  ext x i
  rw [row_action, hr]
  simp [gridMatrix]

theorem unitCube_diameter {x y : EPoint} (hx : x ∈ unitCube) (hy : y ∈ unitCube) :
    dist x y < 2 := by
  have bound (i : Fin 3) : (x i - y i)^2 ≤ 1 := by
    have hxi := abs_le.mp (hx i)
    have hyi := abs_le.mp (hy i)
    nlinarith [mul_nonneg (show 0 ≤ 1 - (x i - y i) by linarith)
      (show 0 ≤ 1 + (x i - y i) by linarith)]
  have he := EuclideanSpace.real_norm_sq_eq (x-y)
  simp only [Fin.sum_univ_three, PiLp.sub_apply] at he
  rw [dist_eq_norm]
  nlinarith [bound 0, bound 1, bound 2, norm_nonneg (x-y)]

theorem RigidMotion.cube_coordinate_diameter (m : RigidMotion) {x y : EPoint}
    (hx : x ∈ unitCube) (hy : y ∈ unitCube) (i : Fin 3) :
    |m.apply x i - m.apply y i| < 2 := by
  have hcoord := PiLp.norm_apply_le (m.apply x - m.apply y) i
  simp only [Real.norm_eq_abs, PiLp.sub_apply] at hcoord
  have he : m.apply x - m.apply y = m.rotation (x-y) := by
    simp [RigidMotion.apply, map_sub]
  rw [he, m.rotation.norm_map] at hcoord
  have hd := unitCube_diameter hx hy
  rw [dist_eq_norm] at hd
  exact hcoord.trans_lt hd

end
end TranslationTiling.Rotations.Euclidean
