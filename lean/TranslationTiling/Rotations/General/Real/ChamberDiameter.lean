import TranslationTiling.Rotations.General.Real.LocalChambers

namespace TranslationTiling.Rotations.General.Real
noncomputable section
open scoped BigOperators
variable {d : ℕ} [NeZero d]

/-- A coarse one-norm estimate leaves ample room below the body's diameter. -/
theorem chamber_diameter (f : Face d) {x y : EPoint d}
    (hx : x ∈ solid (localChamber f)) (hy : y ∈ solid (localChamber f)) :
    dist x y < (cubeSide d : ℝ)-1 := by
  have xb := (local_chamber_bounds f hx).2
  have yb := (local_chamber_bounds f hy).2
  have bounds (j : Fin d) : |x j-y j| ≤ (margin d : ℝ) := by
    rw [abs_le]
    have := xb j
    have := yb j
    constructor <;> linarith
  have he : x-y = ∑ j : Fin d, EuclideanSpace.single j (x j-y j) := by
    ext k
    simp [PiLp.single_apply]
  have hb : dist x y ≤ (d : ℝ)*(margin d : ℝ) := by
    calc
      dist x y = ‖x-y‖ := dist_eq_norm _ _
      _ = ‖∑ j : Fin d, EuclideanSpace.single j (x j-y j)‖ := congrArg norm he
      _ ≤ ∑ j : Fin d, ‖EuclideanSpace.single j (x j-y j)‖ := norm_sum_le _ _
      _ = ∑ j : Fin d, |x j-y j| := by simp [EuclideanSpace.single,PiLp.norm_single]
      _ ≤ ∑ _j : Fin d, (margin d : ℝ) := Finset.sum_le_sum (fun j _ => bounds j)
      _ = (d : ℝ)*(margin d : ℝ) := by simp
  have hp : (1 : ℝ) ≤ (margin d : ℝ) := by exact_mod_cast margin_pos (d := d)
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  have hL : (cubeSide d : ℝ) = 100*((d : ℝ)+1)*(margin d : ℝ) := by
    simp only [cubeSide,Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat]
  nlinarith

end
end TranslationTiling.Rotations.General.Real
