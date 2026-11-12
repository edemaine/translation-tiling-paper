import TranslationTiling.Rotations.Euclidean.MatrixAlignment
import TranslationTiling.Rotations.Geometry
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Topology.Bases
import Mathlib.Tactic.FunProp

namespace TranslationTiling.Rotations.Euclidean

noncomputable section

open Set MeasureTheory
open scoped BigOperators

abbrev EPoint := EuclideanSpace ℝ (Fin 3)
abbrev Rotation := EPoint ≃ₗᵢ[ℝ] EPoint

def castPoint (z : Lattice 3) : EPoint := WithLp.toLp 2 fun i => (z i : ℝ)

@[simp] theorem castPoint_apply (z : Lattice 3) (i : Fin 3) : castPoint z i = (z i : ℝ) := rfl
@[simp] theorem castPoint_zero : castPoint 0 = 0 := by ext i; simp
@[simp] theorem castPoint_add (z w : Lattice 3) : castPoint (z+w) = castPoint z + castPoint w := by
  ext i; simp

theorem sign_real_sq (r : Orientation) (i : Fin 3) :
    (r.sign i : ℝ) * (r.sign i : ℝ) = 1 := by exact_mod_cast r.sign_sq i

theorem sign_real_abs (r : Orientation) (i : Fin 3) : |(r.sign i : ℝ)| = 1 := by
  unfold Orientation.sign; split_ifs <;> norm_num

/-- Embed a signed coordinate permutation into the full Euclidean orthogonal group. -/
def gridRotation (r : Orientation) : Rotation where
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
    have hs (i : Fin 3) : (r.sign i : ℝ) ^ 2 = 1 := by simpa only [pow_two] using sign_real_sq r i
    have he : ‖WithLp.toLp 2 (fun i => (r.sign i : ℝ) * x (r.axes i))‖ ^ 2 = ‖x‖ ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
      simp only [PiLp.toLp_apply, mul_pow, hs, one_mul]
      exact Equiv.sum_comp r.axes (fun i => (x i)^2)
    nlinarith [norm_nonneg x, norm_nonneg (WithLp.toLp 2 (fun i => (r.sign i : ℝ) * x (r.axes i)))]

@[simp] theorem gridRotation_apply (r : Orientation) (x : EPoint) (i : Fin 3) :
    gridRotation r x i = (r.sign i : ℝ) * x (r.axes i) := rfl

@[simp] theorem gridRotation_castPoint (r : Orientation) (z : Lattice 3) :
    gridRotation r (castPoint z) = castPoint (r.linear z) := by
  ext i
  simp [Orientation.linear_apply]

structure RigidMotion where
  rotation : Rotation
  offset : EPoint

def RigidMotion.apply (m : RigidMotion) (x : EPoint) : EPoint := m.offset + m.rotation x

def RigidMotion.homeomorph (m : RigidMotion) : EPoint ≃ₜ EPoint :=
  m.rotation.toHomeomorph.trans (Homeomorph.addLeft m.offset)

@[simp] theorem RigidMotion.homeomorph_apply (m : RigidMotion) (x : EPoint) :
    m.homeomorph x = m.apply x := rfl

theorem RigidMotion.injective (m : RigidMotion) : Function.Injective m.apply := m.homeomorph.injective

def RigidMotion.inverse (m : RigidMotion) : RigidMotion :=
  ⟨m.rotation.symm, -m.rotation.symm m.offset⟩

@[simp] theorem RigidMotion.apply_inverse (m : RigidMotion) (x : EPoint) :
    m.apply (m.inverse.apply x) = x := by
  simp [RigidMotion.apply, inverse, map_add]

@[simp] theorem RigidMotion.inverse_apply (m : RigidMotion) (x : EPoint) :
    m.inverse.apply (m.apply x) = x := by
  simp [RigidMotion.apply, inverse, map_add]

theorem RigidMotion.measurePreserving (m : RigidMotion) : MeasurePreserving m.apply :=
  (measurePreserving_add_left volume m.offset).comp m.rotation.measurePreserving

def unitCube : Set EPoint := {x | ∀ i, |x i| ≤ (1:ℝ)/2}
def openVoxel (p : Lattice 3) : Set EPoint := {x | ∀ i, |x i - (p i : ℝ)| < (1:ℝ)/2}
def voxel (p : Lattice 3) : Set EPoint := {x | ∀ i, |x i - (p i : ℝ)| ≤ (1:ℝ)/2}
def solid (F : Finset (Lattice 3)) : Set EPoint := {x | ∃ p ∈ F, x ∈ voxel p}

theorem isOpen_openVoxel (p : Lattice 3) : IsOpen (openVoxel p) := by
  have he : openVoxel p = ⋂ i : Fin 3, {x : EPoint | |x i - (p i : ℝ)| < (1:ℝ)/2} := by
    ext x; simp [openVoxel]
  rw [he]
  apply isOpen_iInter_of_finite
  intro i
  exact isOpen_lt (by fun_prop) continuous_const

theorem isClosed_voxel (p : Lattice 3) : IsClosed (voxel p) := by
  have he : voxel p = ⋂ i : Fin 3, {x : EPoint | |x i - (p i : ℝ)| ≤ (1:ℝ)/2} := by
    ext x; simp [voxel]
  rw [he]
  apply isClosed_iInter
  intro i
  exact isClosed_le (by fun_prop) continuous_const

theorem isClosed_solid (F : Finset (Lattice 3)) : IsClosed (solid F) := by
  have he : solid F = ⋃ p ∈ F, voxel p := by ext x; simp [solid]
  rw [he]
  exact F.finite_toSet.isClosed_biUnion (fun p _ => isClosed_voxel p)

theorem openVoxel_subset_voxel (p : Lattice 3) : openVoxel p ⊆ voxel p :=
  fun _ hx i => (hx i).le

theorem openVoxel_subset_interior {F : Finset (Lattice 3)} {p : Lattice 3} (hp : p ∈ F) :
    openVoxel p ⊆ interior (solid F) := by
  apply (isOpen_openVoxel p).subset_interior_iff.mpr
  intro x hx
  exact ⟨p, hp, openVoxel_subset_voxel p hx⟩

theorem castPoint_openVoxel (p : Lattice 3) : castPoint p ∈ openVoxel p := by
  intro i
  simp

theorem solid_interior_nonempty {F : Finset (Lattice 3)} (hF : F.Nonempty) :
    (interior (solid F)).Nonempty := by
  obtain ⟨p, hp⟩ := hF
  exact ⟨castPoint p, openVoxel_subset_interior hp (castPoint_openVoxel p)⟩

abbrev Placed (F : Finset (Lattice 3)) (m : RigidMotion) : Set EPoint := m.apply '' solid F

def AECover {ι : Type*} (P : ι → Set EPoint) : Prop := ∀ᵐ x ∂volume, ∃! i, x ∈ P i

/-- Arbitrary orthogonal orientations and arbitrary real translations. Boundaries
are handled by almost-everywhere exact coverage, as in `RealTiles`. -/
def EuclideanTiles (F : Finset (Lattice 3)) : Prop :=
  ∃ C : Set RigidMotion, AECover (fun m : C => Placed F m.val)

end
end TranslationTiling.Rotations.Euclidean
