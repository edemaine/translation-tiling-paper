import TranslationTiling.Rotations.General.Real.Definitions

namespace TranslationTiling.Rotations.General.Real
noncomputable section
variable {d : ℕ}

theorem RigidMotion.cube_coordinate_diameter (m : RigidMotion d) {x y : EPoint d}
    (hx : x ∈ unitCube) (hy : y ∈ unitCube) (i : Fin d) :
    |m.apply x i-m.apply y i| < (d : ℝ)+1 := by
  have hc := PiLp.norm_apply_le (m.apply x-m.apply y) i
  simp only [Real.norm_eq_abs,PiLp.sub_apply] at hc
  have he : m.apply x-m.apply y = m.rotation (x-y) := by simp [RigidMotion.apply,map_sub]
  rw [he,m.rotation.norm_map] at hc
  have hd := unitCube_diameter hx hy
  rw [dist_eq_norm] at hd
  exact hc.trans_lt hd

end
end TranslationTiling.Rotations.General.Real
