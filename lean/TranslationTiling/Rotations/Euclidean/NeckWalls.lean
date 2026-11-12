import TranslationTiling.Rotations.Euclidean.VoxelStars
import TranslationTiling.Rotations.Euclidean.GridEmbedding
import TranslationTiling.Rotations.Euclidean.CubeAlignment
import TranslationTiling.Rotations.NeckBoxes
import TranslationTiling.Rotations.BodyPaths

namespace TranslationTiling.Rotations.Euclidean

noncomputable section
open Set SixKeys

theorem neck_wall_voxel (i : Face) (p : Lattice 3)
    (hp : 0 ≤ p 0 ∧ p 0 ≤ 4 ∧ -2 ≤ p 1 ∧ p 1 ≤ 2 ∧ -2 ≤ p 2 ∧ p 2 ≤ 2)
    (hne : p 1 ≠ 0 ∨ p 2 ≠ 0) : (frameMotion i).apply p ∈ body := by
  apply (mem_body_iff _).mpr
  fin_cases i <;>
    simp [frameMotion, frameOrientation, Motion.apply, Orientation.linear_apply,
      Orientation.sign, Equiv.swap_apply_def, BodyPred, InCube,
      gate, axis, negative, Fin.forall_fin_succ] <;> omega

theorem far_wall_voxel (i : Face) :
    localPoint i (5+(dimensions i).1) 0 0 ∈ body := by
  apply (mem_body_iff _).mpr
  fin_cases i <;>
    simp [localPoint, dimensions, gate, normal, axis, negative,
      tangent₁, tangent₂, BodyPred, InCube, Fin.forall_fin_succ]

/-- The five-voxel neck has solid walls, including at seams between voxels. -/
theorem neck_wall (i : Face) {x : EPoint}
    (h0 : -(1:ℝ)/2 < x 0 ∧ x 0 < 9/2)
    (h1 : |x 1| < (5:ℝ)/2) (h2 : |x 2| < (5:ℝ)/2)
    (hout : (1:ℝ)/2 < |x 1| ∨ (1:ℝ)/2 < |x 2|) :
    (embedMotion (frameMotion i)).apply x ∈ interior (solid body) := by
  let F := body.image (frameMotion i).inverse.apply
  have hs : star x ⊆ F := by
    intro p hp
    have hv := (mem_star x p).mp hp
    have hp0 := abs_le.mp (hv 0)
    have hp1 := abs_le.mp (hv 1)
    have hp2 := abs_le.mp (hv 2)
    have hx1 := abs_lt.mp h1
    have hx2 := abs_lt.mp h2
    have b0 : 0 ≤ p 0 ∧ p 0 ≤ 4 := by
      constructor
      · have : (-1:ℝ) < (p 0:ℝ) := by linarith
        have : (-1:ℤ) < p 0 := by exact_mod_cast this
        omega
      · have : (p 0:ℝ) < 5 := by linarith
        have : p 0 < (5:ℤ) := by exact_mod_cast this
        omega
    have b1 : -2 ≤ p 1 ∧ p 1 ≤ 2 := by
      have hl : (-3:ℝ) < (p 1:ℝ) := by linarith
      have hu : (p 1:ℝ) < 3 := by linarith
      have hl' : (-3:ℤ) < p 1 := by exact_mod_cast hl
      have hu' : p 1 < (3:ℤ) := by exact_mod_cast hu
      omega
    have b2 : -2 ≤ p 2 ∧ p 2 ≤ 2 := by
      have hl : (-3:ℝ) < (p 2:ℝ) := by linarith
      have hu : (p 2:ℝ) < 3 := by linarith
      have hl' : (-3:ℤ) < p 2 := by exact_mod_cast hl
      have hu' : p 2 < (3:ℤ) := by exact_mod_cast hu
      omega
    have hne : p 1 ≠ 0 ∨ p 2 ≠ 0 := by
      by_contra! he
      rcases hout with h | h
      · have hh := hv 1; simp only [he.1, Int.cast_zero, sub_zero] at hh
        exact not_lt_of_ge hh h
      · have hh := hv 2; simp only [he.2, Int.cast_zero, sub_zero] at hh
        exact not_lt_of_ge hh h
    exact Finset.mem_image.mpr ⟨(frameMotion i).apply p,
      neck_wall_voxel i p ⟨b0.1,b0.2,b1.1,b1.2,b2.1,b2.2⟩ hne,
      Motion.inverse_apply_apply _ _⟩
  have hx := star_interior x hs
  have he : F.image (frameMotion i).apply = body := by
    simp [F, Finset.image_image, Function.comp_def]
  have him : (embedMotion (frameMotion i)).apply '' solid F = solid body := by
    rw [embedMotion_solid, he]
  rw [← him]
  change (embedMotion (frameMotion i)).homeomorph x ∈
    interior ((embedMotion (frameMotion i)).homeomorph '' solid F)
  rw [← (embedMotion (frameMotion i)).homeomorph.image_interior]
  exact mem_image_of_mem _ hx

/-- A cube meeting the middle of the neck, and avoiding its walls, must have
a grid orientation. No hypothesis on its initial angle or phase is used. -/
theorem neck_cube_alignment (m : RigidMotion) {u : EPoint} (hu : u ∈ unitCube)
    (h0 : (7:ℝ)/4 < m.apply u 0 ∧ m.apply u 0 < 9/4)
    (h1 : |m.apply u 1| < (1:ℝ)/2) (h2 : |m.apply u 2| < (1:ℝ)/2)
    (walls : ∀ x ∈ unitCube,
      (-(1:ℝ)/2 < m.apply x 0 ∧ m.apply x 0 < 9/2) →
      |m.apply x 1| < (5:ℝ)/2 → |m.apply x 2| < (5:ℝ)/2 →
      ¬ ((1:ℝ)/2 < |m.apply x 1| ∨ (1:ℝ)/2 < |m.apply x 2|)) :
    ∃ r : Orientation, m.rotation = gridRotation r := by
  have hc (x : EPoint) (hx : x ∈ unitCube) :
      |m.apply x 1| ≤ (1:ℝ)/2 ∧ |m.apply x 2| ≤ (1:ℝ)/2 := by
    have hd0 := abs_lt.mp (m.cube_coordinate_diameter hx hu 0)
    have hd1 := abs_lt.mp (m.cube_coordinate_diameter hx hu 1)
    have hd2 := abs_lt.mp (m.cube_coordinate_diameter hx hu 2)
    have hu1 := abs_lt.mp h1
    have hu2 := abs_lt.mp h2
    have hn := walls x hx ⟨by linarith, by linarith⟩
      (abs_lt.mpr ⟨by linarith, by linarith⟩)
      (abs_lt.mpr ⟨by linarith, by linarith⟩)
    push_neg at hn
    exact hn
  apply cube_alignment m.rotation m.offset (-(1:ℝ)/2) (-(1:ℝ)/2)
  · intro x hx
    have hh := abs_le.mp (hc x hx).1
    change -(1:ℝ)/2 ≤ m.apply x 1 ∧ m.apply x 1 ≤ -(1:ℝ)/2+1
    constructor <;> linarith
  · intro x hx
    have hh := abs_le.mp (hc x hx).2
    change -(1:ℝ)/2 ≤ m.apply x 2 ∧ m.apply x 2 ≤ -(1:ℝ)/2+1
    constructor <;> linarith

end
end TranslationTiling.Rotations.Euclidean
