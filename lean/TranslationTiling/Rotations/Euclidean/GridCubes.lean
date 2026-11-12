import TranslationTiling.Rotations.Euclidean.CubeAlignment
import TranslationTiling.Rotations.Euclidean.MotionAlgebra

namespace TranslationTiling.Rotations.Euclidean

noncomputable section
open Set

theorem gridRotation_unitCube (r : Orientation) (x : EPoint) :
    gridRotation r x ∈ unitCube ↔ x ∈ unitCube := by
  have he (i : Fin 3) : |gridRotation r x i| = |x (r.axes i)| := by
    rw [gridRotation_apply,abs_mul,sign_real_abs,one_mul]
  constructor
  · intro hx j
    have hh := hx (r.axes.symm j)
    simpa only [he,Equiv.apply_symm_apply] using hh
  · intro hx i
    rw [he]
    exact hx _

theorem unitCube_rotation_symm (r : Orientation) {y : EPoint} (hy : y ∈ unitCube) :
    (gridRotation r).symm y ∈ unitCube := by
  apply (gridRotation_unitCube r _).mp
  simpa using hy

theorem transverse_center (m : RigidMotion) (r : Orientation) (hr : m.rotation=gridRotation r)
    (k : Fin 3) (h : ∀ x ∈ unitCube, |m.apply x k| ≤ (1:ℝ)/2) : m.offset k=0 := by
  have point (v : ℝ) (hv : |v| ≤ (1:ℝ)/2) :
      |m.offset k+v| ≤ (1:ℝ)/2 := by
    let y : EPoint := EuclideanSpace.single k v
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

def cubeAt (c : EPoint) : Set EPoint := {x | ∀ i, |x i-c i| ≤ (1:ℝ)/2}
def openCubeAt (c : EPoint) : Set EPoint := {x | ∀ i, |x i-c i| < (1:ℝ)/2}

theorem grid_voxel_image (m : RigidMotion) (r : Orientation) (hr : m.rotation=gridRotation r)
    (p : Lattice 3) : m.apply '' voxel p = cubeAt (m.apply (castPoint p)) := by
  have he (x : EPoint) (i : Fin 3) :
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

/-- An integral transverse phase and contact with the closed end of the key
force the axial phase as well. Here `N` is the first solid wall voxel. -/
theorem end_wall_pins_center (c : EPoint) (N : ℤ)
    (hx : WithLp.toLp 2 (![((N:ℝ)-(1:ℝ)/2),0,0]) ∈ cubeAt c)
    (hc1 : ∃ z : ℤ, c 1=(z:ℝ)) (hc2 : ∃ z : ℤ, c 2=(z:ℝ))
    (hd : Disjoint (cubeAt c) (openVoxel (![N,0,0] : Lattice 3))) :
    c 0=(N:ℝ)-1 ∧ c 1=0 ∧ c 2=0 := by
  have h0 := abs_le.mp (hx 0)
  have h1 := abs_le.mp (hx 1)
  have h2 := abs_le.mp (hx 2)
  norm_num only [PiLp.toLp_apply,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] at h0 h1 h2
  obtain ⟨z1,hz1⟩ := hc1
  obtain ⟨z2,hz2⟩ := hc2
  have iz1 : z1=0 := by
    have hl : (-1:ℝ)<(z1:ℝ) := by rw [← hz1]; linarith
    have hu : (z1:ℝ)<1 := by rw [← hz1]; linarith
    have hl' : (-1:ℤ)<z1 := by exact_mod_cast hl
    have hu' : z1<(1:ℤ) := by exact_mod_cast hu
    omega
  have iz2 : z2=0 := by
    have hl : (-1:ℝ)<(z2:ℝ) := by rw [← hz2]; linarith
    have hu : (z2:ℝ)<1 := by rw [← hz2]; linarith
    have hl' : (-1:ℤ)<z2 := by exact_mod_cast hl
    have hu' : z2<(1:ℤ) := by exact_mod_cast hu
    omega
  have cz1 : c 1=0 := by simpa [iz1] using hz1
  have cz2 : c 2=0 := by simpa [iz2] using hz2
  refine ⟨?_,cz1,cz2⟩
  by_contra he
  have hc : (N:ℝ)-1<c 0 ∧ c 0≤N := by
    exact ⟨lt_of_le_of_ne (by linarith) (Ne.symm he),by linarith⟩
  let y : EPoint := WithLp.toLp 2 (![((N:ℝ)+c 0)/2,0,0])
  have hyc : y ∈ cubeAt c := by
    intro j
    fin_cases j
    · dsimp [y]
      apply abs_le.mpr; constructor <;> linarith
    · simp [y,cz1]
    · simp [y,cz2]
  have hyw : y ∈ openVoxel (![N,0,0] : Lattice 3) := by
    intro j
    fin_cases j
    · dsimp [y]
      apply abs_lt.mpr; constructor <;> linarith
    · norm_num [y]
    · norm_num [y]
  exact Set.disjoint_left.mp hd hyc hyw

end
end TranslationTiling.Rotations.Euclidean
