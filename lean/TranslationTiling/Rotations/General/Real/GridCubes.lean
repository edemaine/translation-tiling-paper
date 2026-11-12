import TranslationTiling.Rotations.General.Real.CubeAlignment
import TranslationTiling.Rotations.General.Real.MotionAlgebra

namespace TranslationTiling.Rotations.General.Real
variable {d : ℕ} [NeZero d]

noncomputable section
open Set

theorem gridRotation_unitCube (r : (Orientation d)) (x : (EPoint d)) :
    gridRotation r x ∈ unitCube ↔ x ∈ unitCube := by
  have he (i : Fin d) : |gridRotation r x i| = |x (r.axes i)| := by
    rw [gridRotation_apply,abs_mul,sign_real_abs,one_mul]
  constructor
  · intro hx j
    have hh := hx (r.axes.symm j)
    simpa only [he,Equiv.apply_symm_apply] using hh
  · intro hx i
    rw [he]
    exact hx _

theorem unitCube_rotation_symm (r : (Orientation d)) {y : (EPoint d)} (hy : y ∈ unitCube) :
    (gridRotation r).symm y ∈ unitCube := by
  apply (gridRotation_unitCube r _).mp
  simpa using hy

theorem transverse_center (m : (RigidMotion d)) (r : (Orientation d)) (hr : m.rotation=gridRotation r)
    (k : Fin d) (h : ∀ x ∈ unitCube, |m.apply x k| ≤ (1:ℝ)/2) : m.offset k=0 := by
  have point (v : ℝ) (hv : |v| ≤ (1:ℝ)/2) :
      |m.offset k+v| ≤ (1:ℝ)/2 := by
    let y : (EPoint d) := EuclideanSpace.single k v
    have hy : y ∈ unitCube := by
      intro i
      by_cases hi : i=k
      · subst i; simpa [y] using hv
      · simp [y,PiLp.single_apply,hi]
    have hh := h ((gridRotation r).symm y) (unitCube_rotation_symm r hy)
    simpa [RigidMotion.apply,hr,y] using hh
  have hl := abs_le.mp (point (-(1:ℝ)/2) (by norm_num))
  have hu := abs_le.mp (point ((1:ℝ)/2) (by norm_num))
  linarith

def cubeAt (c : (EPoint d)) : Set (EPoint d) := {x | ∀ i, |x i-c i| ≤ (1:ℝ)/2}
def openCubeAt (c : (EPoint d)) : Set (EPoint d) := {x | ∀ i, |x i-c i| < (1:ℝ)/2}

theorem grid_voxel_image (m : (RigidMotion d)) (r : (Orientation d)) (hr : m.rotation=gridRotation r)
    (p : Lattice d) : m.apply '' voxel p = cubeAt (m.apply (castPoint p)) := by
  have he (x : (EPoint d)) (i : Fin d) :
      |m.apply x i-m.apply (castPoint p) i| = |x (r.axes i)-(p (r.axes i):ℝ)| := by
    have hh : m.apply x i-m.apply (castPoint p) i =
        (r.sign i:ℝ)*(x (r.axes i)-(p (r.axes i):ℝ)) := by
      simp [RigidMotion.apply,hr]
      ring
    rw [hh,abs_mul,sign_real_abs,one_mul]
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩ i
    rw [he]
    exact hx _
  · intro hy
    obtain ⟨x,rfl⟩ := m.homeomorph.surjective y
    change ∀ i, |m.apply x i-m.apply (castPoint p) i| ≤ (1:ℝ)/2 at hy
    refine ⟨x,?_,rfl⟩
    intro j
    have hh := hy (r.axes.symm j)
    simpa only [he,Equiv.apply_symm_apply] using hh

/-- A transverse integral phase and the closed end wall pin the axial phase. -/
theorem end_wall_pins_center (c : EPoint d) (N : ℤ)
    (hx : EuclideanSpace.single 0 ((N : ℝ)-(1:ℝ)/2) ∈ cubeAt c)
    (hc : ∀ j : Fin d, j ≠ 0 → ∃ z : ℤ, c j=(z : ℝ))
    (hd : Disjoint (cubeAt c) (openVoxel (Pi.single 0 N))) :
    c 0=(N : ℝ)-1 ∧ ∀ j : Fin d, j ≠ 0 → c j=0 := by
  have h0 := abs_le.mp (hx 0)
  simp only [PiLp.single_apply,ite_true] at h0
  have cz (j : Fin d) (hj : j ≠ 0) : c j=0 := by
    have hjx := abs_le.mp (hx j)
    simp only [PiLp.single_apply,ite_eq_right hj] at hjx
    obtain ⟨z,hz⟩ := hc j hj
    have hl : (-1 : ℝ) < (z : ℝ) := by rw [← hz]; linarith
    have hu : (z : ℝ) < 1 := by rw [← hz]; linarith
    have hl' : (-1 : ℤ) < z := by exact_mod_cast hl
    have hu' : z < (1 : ℤ) := by exact_mod_cast hu
    have he : z=0 := by omega
    simpa [he] using hz
  refine ⟨?_,cz⟩
  by_contra he
  have hb : (N : ℝ)-1 < c 0 ∧ c 0 ≤ N :=
    ⟨lt_of_le_of_ne (by linarith) (Ne.symm he),by linarith⟩
  let y : EPoint d := EuclideanSpace.single 0 (((N : ℝ)+c 0)/2)
  have hyc : y ∈ cubeAt c := by
    intro j
    by_cases hj : j=0
    · subst j
      simp only [y,PiLp.single_apply,ite_true]
      rw [abs_le]
      constructor <;> linarith
    · simp [y,PiLp.single_apply,hj,cz j hj]
  have hyv : y ∈ openVoxel (Pi.single 0 N) := by
    intro j
    by_cases hj : j=0
    · subst j
      simp only [y,PiLp.single_apply,ite_true,Pi.single_eq_same]
      rw [abs_lt]
      constructor <;> linarith
    · simp [y,PiLp.single_apply,hj,Pi.single_eq_of_ne hj]
  exact Set.disjoint_left.mp hd hyc hyv

end
end TranslationTiling.Rotations.General.Real
