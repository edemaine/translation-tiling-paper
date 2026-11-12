import TranslationTiling.EuclideanMembership.Matrices
import Mathlib.LinearAlgebra.Determinant

/-! Polynomial descriptions of the four allowed-orientation classes. A unit
normal represents a hyperplane reflection, so its parameters stay compact. -/
namespace TranslationTiling.EuclideanMembership

open Rotations.General
open scoped BigOperators Matrix
noncomputable section
variable {d : ℕ}

theorem row_injective : Function.Injective (@row d) := by
  intro r s h
  ext x i
  rw [row_action r,row_action s,h]

theorem row_identity : row (LinearIsometryEquiv.refl ℝ (EPoint d))=(1 : RealMatrix d) := by
  ext i j
  change (EuclideanSpace.single i (1 : ℝ)) j=(if i=j then 1 else 0)
  simp [EuclideanSpace.single,PiLp.single_apply,eq_comm]

theorem row_matrixRotation (R : RealMatrix d) (h : Rᵀ*R=1) : row (matrixRotation R h)=R := by
  ext i j
  change (Rᵀ *ᵥ (EuclideanSpace.single i (1 : ℝ)).ofLp) j=R i j
  simp [Matrix.mulVec,dotProduct,Matrix.transpose_apply,EuclideanSpace.single,PiLp.single_apply]

theorem det_row (r : Rotation d) : LinearMap.det r.toLinearMap=(row r).det := by
  have he : Matrix.toEuclideanLin (row r)=r.toLinearMap := by
    ext x i
    change (∑ j, row r i j*x j)=r x i
    exact (row_action r x i).symm
  rw [← he,Matrix.toEuclideanLin_eq_toLin_orthonormal,LinearMap.det_toLin]

theorem normalized_reflection (v : EPoint d) (hv : v ≠ 0) :
    ∃ u : EPoint d, ‖u‖=1 ∧
      (Submodule.span ℝ {u}).orthogonal.reflection=(Submodule.span ℝ {v}).orthogonal.reflection := by
  let u := ‖v‖⁻¹ • v
  have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  refine ⟨u,?_,?_⟩
  · simp [u,norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr (norm_nonneg v)),hn]
  · have he : Submodule.span ℝ {u}=Submodule.span ℝ {v} :=
      Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr (inv_ne_zero hn)) v
    exact congrArg (fun K : Submodule ℝ (EPoint d) => K.orthogonal.reflection) he

theorem row_reflection (v : EPoint d) (hv : ‖v‖=1) (i j : Fin d) :
    row ((Submodule.span ℝ {v}).orthogonal.reflection) i j =
      (if i=j then 1 else 0)-2*v i*v j := by
  unfold row
  rw [Submodule.reflection_symm,Submodule.reflection_orthogonal_apply,
    Submodule.reflection_singleton_apply]
  by_cases hij : i=j
  · subst j
    simp [hv,EuclideanSpace.inner_single_right,EuclideanSpace.single,PiLp.single_apply]
    ring
  · simp [hv,EuclideanSpace.inner_single_right,EuclideanSpace.single,PiLp.single_apply,hij,Ne.symm hij]
    ring

/-- A bounded, polynomial orientation test. The vector `v` is used only for
reflections without rotations; other cases can set it to zero. -/
def AllowedRows (allowRotations allowReflections : Bool) (R : RealMatrix d) (v : Fin d → ℝ) : Prop :=
  if allowRotations then allowReflections=true ∨ R.det=1
  else R=1 ∨ (allowReflections=true ∧ (∑ i, v i^2)=1 ∧
    ∀ i j, R i j=(if i=j then 1 else 0)-2*v i*v j)

theorem allowedLinear_iff_rows (allowRotations allowReflections : Bool)
    (R : RealMatrix d) (h : Rᵀ*R=1) :
    AllowedLinear allowRotations allowReflections (matrixRotation R h) ↔
      ∃ v : Fin d → ℝ, (∀ i, |v i| ≤ 1) ∧ AllowedRows allowRotations allowReflections R v := by
  cases allowRotations
  · simp only [AllowedLinear,AllowedRows,Bool.false_eq_true,ite_false]
    constructor
    · rintro (hi | ⟨hf,v,hv,hr⟩)
      · refine ⟨0,by simp,Or.inl ?_⟩
        have he := congrArg row hi
        simpa only [row_matrixRotation,row_identity] using he
      · obtain ⟨u,hu,he⟩ := normalized_reflection v hv
        refine ⟨fun i => u i,?_,Or.inr ⟨hf,?_,?_⟩⟩
        · intro i
          have hh := PiLp.norm_apply_le (p := 2) u i
          simpa only [Real.norm_eq_abs,hu] using hh
        · rw [← EuclideanSpace.real_norm_sq_eq,hu]
          norm_num
        · intro i j
          have hh := congrArg (fun r => row r i j) (hr.trans he.symm)
          simpa only [row_matrixRotation,row_reflection u hu] using hh
    · rintro ⟨v,hv,hi | ⟨hf,hn,hr⟩⟩
      · left
        apply row_injective
        rw [row_matrixRotation,row_identity,hi]
      · let u : EPoint d := WithLp.toLp 2 v
        have hu : ‖u‖=1 := by
          have hh : ‖u‖^2=1 := by simpa only [EuclideanSpace.real_norm_sq_eq,PiLp.toLp_apply] using hn
          nlinarith [norm_nonneg u]
        refine Or.inr ⟨hf,u,?_,?_⟩
        · intro he
          simp [he] at hu
        · apply row_injective
          rw [row_matrixRotation]
          ext i j
          exact (hr i j).trans (row_reflection u hu i j).symm
  · simp only [AllowedLinear,AllowedRows,ite_true]
    rw [det_row,row_matrixRotation]
    constructor
    · intro hi
      exact ⟨0,by simp,hi⟩
    · rintro ⟨v,hv,hi⟩
      exact hi

end
end TranslationTiling.EuclideanMembership
