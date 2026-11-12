import TranslationTiling.Rotations.General.Euclidean
import TranslationTiling.Rotations.General.Assembly
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Topology.Bases
import Mathlib.Tactic.FunProp

namespace TranslationTiling.Rotations.General.Real
noncomputable section
open Set MeasureTheory
open scoped BigOperators
variable {d : ℕ}

structure RigidMotion (d : ℕ) where
  rotation : (Rotation d)
  offset : (EPoint d)

def RigidMotion.apply (m : (RigidMotion d)) (x : (EPoint d)) : (EPoint d) := m.offset + m.rotation x

def RigidMotion.homeomorph (m : (RigidMotion d)) : (EPoint d) ≃ₜ (EPoint d) :=
  m.rotation.toHomeomorph.trans (Homeomorph.addLeft m.offset)

@[simp] theorem RigidMotion.homeomorph_apply (m : (RigidMotion d)) (x : (EPoint d)) :
    m.homeomorph x = m.apply x := rfl

theorem RigidMotion.injective (m : (RigidMotion d)) : Function.Injective m.apply := m.homeomorph.injective

def RigidMotion.inverse (m : (RigidMotion d)) : (RigidMotion d) :=
  ⟨m.rotation.symm, -m.rotation.symm m.offset⟩

@[simp] theorem RigidMotion.apply_inverse (m : (RigidMotion d)) (x : (EPoint d)) :
    m.apply (m.inverse.apply x) = x := by
  simp [RigidMotion.apply, inverse, map_add]

@[simp] theorem RigidMotion.inverse_apply (m : (RigidMotion d)) (x : (EPoint d)) :
    m.inverse.apply (m.apply x) = x := by
  simp [RigidMotion.apply, inverse, map_add]

theorem RigidMotion.measurePreserving (m : (RigidMotion d)) : MeasurePreserving m.apply :=
  (measurePreserving_add_left volume m.offset).comp m.rotation.measurePreserving

def unitCube : Set (EPoint d) := {x | ∀ i, |x i| ≤ (1:ℝ)/2}
def openVoxel (p : Lattice d) : Set (EPoint d) := {x | ∀ i, |x i - (p i : ℝ)| < (1:ℝ)/2}
def voxel (p : Lattice d) : Set (EPoint d) := {x | ∀ i, |x i - (p i : ℝ)| ≤ (1:ℝ)/2}
def solid (F : Finset (Lattice d)) : Set (EPoint d) := {x | ∃ p ∈ F, x ∈ voxel p}

theorem isOpen_openVoxel (p : Lattice d) : IsOpen (openVoxel p) := by
  have he : openVoxel p = ⋂ i : Fin d, {x : (EPoint d) | |x i - (p i : ℝ)| < (1:ℝ)/2} := by
    ext x; simp [openVoxel]
  rw [he]
  apply isOpen_iInter_of_finite
  intro i
  exact isOpen_lt (by fun_prop) continuous_const

theorem isClosed_voxel (p : Lattice d) : IsClosed (voxel p) := by
  have he : voxel p = ⋂ i : Fin d, {x : (EPoint d) | |x i - (p i : ℝ)| ≤ (1:ℝ)/2} := by
    ext x; simp [voxel]
  rw [he]
  apply isClosed_iInter
  intro i
  exact isClosed_le (by fun_prop) continuous_const

theorem isClosed_solid (F : Finset (Lattice d)) : IsClosed (solid F) := by
  have he : solid F = ⋃ p ∈ F, voxel p := by ext x; simp [solid]
  rw [he]
  exact F.finite_toSet.isClosed_biUnion (fun p _ => isClosed_voxel p)

theorem openVoxel_subset_voxel (p : Lattice d) : openVoxel p ⊆ voxel p :=
  fun _ hx i => (hx i).le

theorem openVoxel_subset_interior {F : Finset (Lattice d)} {p : Lattice d} (hp : p ∈ F) :
    openVoxel p ⊆ interior (solid F) := by
  apply (isOpen_openVoxel p).subset_interior_iff.mpr
  intro x hx
  exact ⟨p, hp, openVoxel_subset_voxel p hx⟩

theorem castPoint_openVoxel (p : Lattice d) : castPoint p ∈ openVoxel p := by
  intro i
  simp

theorem solid_interior_nonempty {F : Finset (Lattice d)} (hF : F.Nonempty) :
    (interior (solid F)).Nonempty := by
  obtain ⟨p, hp⟩ := hF
  exact ⟨castPoint p, openVoxel_subset_interior hp (castPoint_openVoxel p)⟩

abbrev Placed (F : Finset (Lattice d)) (m : (RigidMotion d)) : Set (EPoint d) := m.apply '' solid F

def AECover {ι : Type*} (P : ι → Set (EPoint d)) : Prop := ∀ᵐ x ∂volume, ∃! i, x ∈ P i

/-- Arbitrary orthogonal orientations and arbitrary real translations. Boundaries
are handled by almost-everywhere exact coverage, as in `RealTiles`. -/
def EuclideanTiles (F : Finset (Lattice d)) : Prop :=
  ∃ C : Set (RigidMotion d), AECover (fun m : C => Placed F m.val)


end
end TranslationTiling.Rotations.General.Real
