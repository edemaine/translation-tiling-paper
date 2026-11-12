import TranslationTiling.EuclideanMembership.SlotParameters
import TranslationTiling.Rotations.General.Real.MotionAlgebra

/-! A countable compact-parameter model of a Euclidean tiling. Every condition
is either a finite closed polynomial condition or a countable conjunction of
such conditions. -/
namespace TranslationTiling.EuclideanMembership

open Rotations.General (EPoint RealMatrix castPoint Rotation row)
open Rotations.General.Real (RigidMotion Placed openVoxel solid voxel)
open scoped BigOperators Matrix
noncomputable section
variable {d : ℕ}

def anchorPoint (P : Tile d) : Lattice d := P.getD 0 0

theorem anchorPoint_mem {P : Tile d} (h : P ≠ []) : anchorPoint P ∈ P := by
  cases P with
  | nil => exact (h rfl).elim
  | cons p ps => simp [anchorPoint]

def Enabled (x : Assignment) (z : Lattice d) : Prop := presence x z=1

def inversePoint (x : Assignment) (P : Tile d) (z : Lattice d) (y : EPoint d) : EPoint d :=
  WithLp.toLp 2 fun i => (anchorPoint P i : ℝ)+
    ∑ j, slotRows x z j i*(y j-slotCenter x z j)

def ClosedAt (x : Assignment) (P : Tile d) (z : Lattice d) (y : EPoint d) (p : Lattice d) : Prop :=
  ∀ i, |inversePoint x P z y i-(p i : ℝ)| ≤ 1/2

def OpenAt (x : Assignment) (P : Tile d) (z : Lattice d) (y : EPoint d) (p : Lattice d) : Prop :=
  ∀ i, |inversePoint x P z y i-(p i : ℝ)| < 1/2

def SlotCorrect (allowRotations allowReflections : Bool) (x : Assignment) (z : Lattice d) : Prop :=
  (presence x z=0 ∨ presence x z=1) ∧
    (Enabled x z → (slotRows x z)ᵀ*slotRows x z=1 ∧
      AllowedRows allowRotations allowReflections (slotRows x z) (slotNormal x z))

structure Model (allowRotations allowReflections : Bool) (P : Tile d) (x : Assignment) : Prop where
  reciprocal : ReciprocalCorrect (d := d) x
  slots : ∀ z : Lattice d, SlotCorrect allowRotations allowReflections x z
  packing : ∀ z w : Lattice d, z ≠ w → Enabled x z → Enabled x w →
    ∀ p ∈ P, ∀ q ∈ P, ∀ a : Probe d,
      ¬ (OpenAt x P z (probeValue x a) p ∧ OpenAt x P w (probeValue x a) q)
  coverage : ∀ a : Probe d, ∃ z ∈ probeCells P a,
    Enabled x z ∧ ∃ p ∈ P, ClosedAt x P z (probeValue x a) p

def motionOfSlot (x : Assignment) (P : Tile d) (z : Lattice d)
    (h : (slotRows x z)ᵀ*slotRows x z=1) : RigidMotion d :=
  ⟨matrixRotation (slotRows x z) h,
    slotCenter x z-matrixRotation (slotRows x z) h (castPoint (anchorPoint P))⟩

theorem inversePoint_eq (x : Assignment) (P : Tile d) (z : Lattice d)
    (h : (slotRows x z)ᵀ*slotRows x z=1) (y : EPoint d) :
    inversePoint x P z y=castPoint (anchorPoint P)+
      (matrixRotation (slotRows x z) h).symm (y-slotCenter x z) := by
  ext i
  rfl

theorem motionOfSlot_inverse (x : Assignment) (P : Tile d) (z : Lattice d)
    (h : (slotRows x z)ᵀ*slotRows x z=1) (y : EPoint d) :
    (motionOfSlot x P z h).inverse.apply y=inversePoint x P z y := by
  rw [inversePoint_eq x P z h y]
  let r := matrixRotation (slotRows x z) h
  change -r.symm (slotCenter x z-r (castPoint (anchorPoint P)))+r.symm y=
    castPoint (anchorPoint P)+r.symm (y-slotCenter x z)
  simp only [map_sub,LinearIsometryEquiv.symm_apply_apply]
  abel

theorem motionOfSlot_closed_iff (x : Assignment) (P : Tile d) (z : Lattice d)
    (h : (slotRows x z)ᵀ*slotRows x z=1) (y : EPoint d) :
    y ∈ Placed P.toFinset (motionOfSlot x P z h) ↔ ∃ p ∈ P, ClosedAt x P z y p := by
  have hi : y ∈ Placed P.toFinset (motionOfSlot x P z h) ↔
      (motionOfSlot x P z h).inverse.apply y ∈ solid P.toFinset := by
    constructor
    · rintro ⟨t,ht,rfl⟩
      simpa only [RigidMotion.inverse_apply] using ht
    · intro ht
      exact ⟨_,ht,RigidMotion.apply_inverse _ y⟩
  rw [hi,motionOfSlot_inverse]
  simp only [solid,List.mem_toFinset,ClosedAt,voxel,Set.mem_setOf_eq]

theorem motionOfSlot_open_iff (x : Assignment) (P : Tile d) (z : Lattice d)
    (h : (slotRows x z)ᵀ*slotRows x z=1) (y : EPoint d) (p : Lattice d) :
    y ∈ (motionOfSlot x P z h).apply '' openVoxel p ↔ OpenAt x P z y p := by
  have hi : y ∈ (motionOfSlot x P z h).apply '' openVoxel p ↔
      (motionOfSlot x P z h).inverse.apply y ∈ openVoxel p := by
    constructor
    · rintro ⟨t,ht,rfl⟩
      simpa only [RigidMotion.inverse_apply] using ht
    · intro ht
      exact ⟨_,ht,RigidMotion.apply_inverse _ y⟩
  rw [hi,motionOfSlot_inverse]
  rfl

theorem motionOfSlot_eq [NeZero d] (x : Assignment) (P : Tile d) (z : Lattice d)
    (h : (slotRows x z)ᵀ*slotRows x z=1) (m : RigidMotion d)
    (hr : slotRows x z=row m.rotation) (hc : slotCenter x z=m.apply (castPoint (anchorPoint P))) :
    motionOfSlot x P z h=m := by
  have he : matrixRotation (slotRows x z) h=m.rotation := by
    apply row_injective
    rw [row_matrixRotation,hr]
  apply RigidMotion.ext_apply
  intro y
  change (slotCenter x z-matrixRotation (slotRows x z) h (castPoint (anchorPoint P)))+
    matrixRotation (slotRows x z) h y=m.apply y
  rw [he,hc]
  simp only [RigidMotion.apply]
  abel

namespace Model

variable {allowRotations allowReflections : Bool} {P : Tile d} {x : Assignment}

theorem nonempty (h : Model allowRotations allowReflections P x) : P ≠ [] := by
  obtain ⟨z,hz,he,p,hp,hv⟩ := h.coverage (0,0)
  intro ht
  simpa only [ht,List.not_mem_nil] using hp

def Active (d : ℕ) (x : Assignment) := {z : Lattice d // Enabled x z}

def motion (h : Model allowRotations allowReflections P x) (z : Active d x) : RigidMotion d :=
  motionOfSlot x P z.val ((h.slots z.val).2 z.property).1

theorem motion_allowed (h : Model allowRotations allowReflections P x) (z : Active d x) :
    AllowedLinear allowRotations allowReflections (h.motion z).rotation := by
  apply (allowedLinear_iff_rows allowRotations allowReflections (slotRows x z.val)
    ((h.slots z.val).2 z.property).1).mpr
  refine ⟨slotNormal x z.val,fun i => ?_,((h.slots z.val).2 z.property).2⟩
  exact abs_le.mpr (x _).property

end Model
end
end TranslationTiling.EuclideanMembership
