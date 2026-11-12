import TranslationTiling.Rotations.General.Real.Definitions
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Tactic

/-! Orthogonal matrices give the bounded real parameters used by the compact
constraint model. Their coordinates and motion restrictions are polynomial. -/
namespace TranslationTiling.EuclideanMembership

open Rotations.General
open scoped BigOperators Matrix
noncomputable section
variable {d : ℕ}

/-- The allowed linear parts, with a single arbitrary hyperplane reflection
permitted when rotations are disabled and reflections enabled. -/
def AllowedLinear (allowRotations allowReflections : Bool) (r : Rotation d) : Prop :=
  if allowRotations then
    allowReflections = true ∨ LinearMap.det r.toLinearMap = 1
  else
    r = LinearIsometryEquiv.refl ℝ (EPoint d) ∨
      (allowReflections = true ∧ ∃ v : EPoint d, v ≠ 0 ∧
        r = (Submodule.span ℝ {v}).orthogonal.reflection)

def matrixAction (R : RealMatrix d) (x : EPoint d) : EPoint d :=
  WithLp.toLp 2 (R *ᵥ x.ofLp)

/-- Recover a genuine Euclidean linear isometry from the polynomial equations
`Rᵀ R = I`. -/
def matrixRotation (R : RealMatrix d) (h : Rᵀ*R=1) : Rotation d where
  toFun := matrixAction R
  invFun := matrixAction Rᵀ
  left_inv x := by
    ext i
    change (Rᵀ *ᵥ R *ᵥ x.ofLp) i=x i
    rw [Matrix.mulVec_mulVec,h,Matrix.one_mulVec]
  right_inv x := by
    have hh : R*Rᵀ=1 := (mul_eq_one_comm).mp h
    ext i
    change (R *ᵥ Rᵀ *ᵥ x.ofLp) i=x i
    rw [Matrix.mulVec_mulVec,hh,Matrix.one_mulVec]
  map_add' x y := by
    ext i
    change (R *ᵥ (x.ofLp+y.ofLp)) i=(R *ᵥ x.ofLp) i+(R *ᵥ y.ofLp) i
    rw [Matrix.mulVec_add]
    rfl
  map_smul' c x := by
    ext i
    change (R *ᵥ (c • x.ofLp)) i=c*(R *ᵥ x.ofLp) i
    rw [Matrix.mulVec_smul]
    rfl
  norm_map' x := by
    change ‖matrixAction R x‖=‖x‖
    have he : (R *ᵥ x.ofLp) ⬝ᵥ (R *ᵥ x.ofLp)=x.ofLp ⬝ᵥ x.ofLp := by
      rw [← Matrix.dotProduct_transpose_mulVec R x.ofLp (R *ᵥ x.ofLp),
        Matrix.mulVec_mulVec,h,Matrix.one_mulVec]
    have hs : ‖matrixAction R x‖^2=‖x‖^2 := by
      rw [EuclideanSpace.real_norm_sq_eq,EuclideanSpace.real_norm_sq_eq]
      simpa only [matrixAction,PiLp.toLp_apply,pow_two,dotProduct] using he
    nlinarith [norm_nonneg (matrixAction R x),norm_nonneg x]

@[simp] theorem matrixRotation_apply (R : RealMatrix d) (h : Rᵀ*R=1)
    (x : EPoint d) (i : Fin d) : matrixRotation R h x i=∑ j, R i j*x j := rfl

theorem row_transpose_mul (r : Rotation d) : (row r)ᵀ*row r=1 := by
  apply mul_eq_one_comm.mp
  ext i j
  simpa only [Matrix.mul_apply,Matrix.transpose_apply,Matrix.one_apply]
    using row_orthogonal r i j

theorem matrixRotation_row (r : Rotation d) : matrixRotation (row r) (row_transpose_mul r)=r := by
  ext x i
  exact (row_action r x i).symm

theorem row_abs_le_one (r : Rotation d) (i j : Fin d) : |row r i j| ≤ 1 := by
  have h := PiLp.norm_apply_le (p := 2) (r.symm (EuclideanSpace.single i (1 : ℝ))) j
  simpa only [row,Real.norm_eq_abs,LinearIsometryEquiv.norm_map,
    EuclideanSpace.single,PiLp.norm_single,norm_one] using h

end
end TranslationTiling.EuclideanMembership
