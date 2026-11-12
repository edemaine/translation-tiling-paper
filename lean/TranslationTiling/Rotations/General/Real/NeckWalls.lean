import TranslationTiling.Rotations.General.NeckGeometry
import TranslationTiling.Rotations.General.Real.LocalChambers
import TranslationTiling.Rotations.General.Real.CubeAlignment

namespace TranslationTiling.Rotations.General.Real
noncomputable section
open Set
variable {d : ℕ} [NeZero d]

/-- Solid walls around the entire long axial neck, including voxel seams. -/
theorem local_neck_wall (f : Face d) {x : EPoint d}
    (h0 : -(1 : ℝ)/2 < x 0 ∧ x 0 < (neckLength d : ℝ)-(1 : ℝ)/2)
    (ht : ∀ j : Fin d, j ≠ 0 → |x j| < (d : ℝ)+3/2)
    (hout : ∃ j : Fin d, j ≠ 0 ∧ (1 : ℝ)/2 < |x j|) :
    x ∈ interior (solid (localBody f)) := by
  apply star_interior
  intro p hp
  have hv := (mem_star x p).mp hp
  have hp0 := abs_le.mp (hv 0)
  have hb0 : 0 ≤ p 0 ∧ p 0 < neckLength d := by
    have hl : (-1 : ℝ) < (p 0 : ℝ) := by linarith
    have hu : (p 0 : ℝ) < (neckLength d : ℝ) := by linarith
    have hl' : (-1 : ℤ) < p 0 := by exact_mod_cast hl
    have hu' : p 0 < (neckLength d : ℤ) := by exact_mod_cast hu
    omega
  have hbt (j : Fin d) (hj : j ≠ 0) : |p j| ≤ (d : ℤ)+1 := by
    have hxt := abs_lt.mp (ht j hj)
    have hpt := abs_le.mp (hv j)
    have hl : -((d : ℝ)+2) < (p j : ℝ) := by linarith
    have hu : (p j : ℝ) < (d : ℝ)+2 := by linarith
    have hl' : -((d : ℤ)+2) < p j := by exact_mod_cast hl
    have hu' : p j < (d : ℤ)+2 := by exact_mod_cast hu
    rw [abs_le]
    omega
  have hne : ∃ j : Fin d, j ≠ 0 ∧ p j ≠ 0 := by
    obtain ⟨j,hj,hout⟩ := hout
    refine ⟨j,hj,?_⟩
    intro he
    have hh := hv j
    simp only [he,Int.cast_zero,sub_zero] at hh
    exact not_lt_of_ge hh hout
  apply Finset.mem_image.mpr
  exact ⟨(frameMotion f).apply p,neck_wall_voxel f p hb0 hbt hne,Motion.inverse_apply_apply _ _⟩

end
end TranslationTiling.Rotations.General.Real
