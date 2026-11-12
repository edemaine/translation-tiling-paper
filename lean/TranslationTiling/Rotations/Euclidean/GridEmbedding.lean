import TranslationTiling.Rotations.Euclidean.Definitions
import TranslationTiling.Rotations.Motions

namespace TranslationTiling.Rotations.Euclidean

noncomputable section
open Set

def embedMotion (m : Motion) : RigidMotion := ⟨gridRotation m.orientation, castPoint m.offset⟩

@[simp] theorem embedMotion_castPoint (m : Motion) (p : Lattice 3) :
    (embedMotion m).apply (castPoint p) = castPoint (m.apply p) := by
  simp [embedMotion, RigidMotion.apply, Motion.apply]

theorem embedMotion_voxel (m : Motion) (p : Lattice 3) :
    (embedMotion m).apply '' voxel p = voxel (m.apply p) := by
  have forward (m : Motion) (p : Lattice 3) :
      (embedMotion m).apply '' voxel p ⊆ voxel (m.apply p) := by
    rintro _ ⟨x, hx, rfl⟩ i
    have he : (embedMotion m).apply x i - (m.apply p i : ℝ) =
        (m.orientation.sign i : ℝ) * (x (m.orientation.axes i) - (p (m.orientation.axes i) : ℝ)) := by
      simp [embedMotion, RigidMotion.apply, Motion.apply, Orientation.linear_apply]
      ring
    rw [he, abs_mul, sign_real_abs, one_mul]
    exact hx _
  apply subset_antisymm (forward m p)
  intro x hx
  obtain ⟨y, hy⟩ := (embedMotion m).homeomorph.surjective x
  change (embedMotion m).apply y = x at hy
  refine ⟨y, ?_, hy⟩
  have hrev := forward m.inverse (m.apply p)
    (mem_image_of_mem (embedMotion m.inverse).apply hx)
  have hinv : (embedMotion m.inverse).apply x = y := by
    apply (embedMotion m).injective
    rw [hy]
    change (embedMotion m).apply ((embedMotion m.inverse).apply x) = x
    ext i
    simp [embedMotion, RigidMotion.apply, Motion.inverse, Orientation.inverse,
      gridRotation, Orientation.linear, Orientation.sign]
    split_ifs <;> ring
  simpa only [Motion.inverse_apply_apply, hinv] using hrev

theorem embedMotion_solid (m : Motion) (F : Finset (Lattice 3)) :
    (embedMotion m).apply '' solid F = solid (F.image m.apply) := by
  ext x
  constructor
  · rintro ⟨y, ⟨p, hp, hy⟩, rfl⟩
    refine ⟨m.apply p, Finset.mem_image_of_mem _ hp, ?_⟩
    rw [← embedMotion_voxel m p]
    exact ⟨y, hy, rfl⟩
  · rintro ⟨_, hp, hx⟩
    obtain ⟨p, hpF, rfl⟩ := Finset.mem_image.mp hp
    rw [← embedMotion_voxel m p] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨y, ⟨p, hpF, hy⟩, rfl⟩

end
end TranslationTiling.Rotations.Euclidean
