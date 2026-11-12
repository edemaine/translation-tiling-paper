import TranslationTiling.Rotations.General.Real.NeckCopy
import TranslationTiling.Rotations.General.Real.CappedChambers

namespace TranslationTiling.Rotations.General.Real
noncomputable section
open Set
variable {d : ℕ} [NeZero d]

theorem isOpen_openCubeAt (c : (EPoint d)) : IsOpen (openCubeAt c) := by
  have he : openCubeAt c = ⋂ i : Fin d, {x : (EPoint d) | |x i-c i| < (1:ℝ)/2} := by
    ext x; simp [openCubeAt]
  rw [he]
  apply isOpen_iInter_of_finite
  intro i
  exact isOpen_lt (by fun_prop) continuous_const

theorem grid_voxel_difference (m : (RigidMotion d)) (r : (Orientation d))
    (hr : m.rotation=gridRotation r) (p : Lattice d) (u : (EPoint d)) (j : Fin d) :
    |m.apply u j-m.apply (castPoint p) j|=|u (r.axes j)-(p (r.axes j):ℝ)| := by
  have he : m.apply u j-m.apply (castPoint p) j =
      (r.sign j:ℝ)*(u (r.axes j)-(p (r.axes j):ℝ)) := by
    simp [RigidMotion.apply,hr]
    ring
  rw [he,abs_mul,sign_real_abs,one_mul]

theorem integer_phase_motion (m : (RigidMotion d)) (r : (Orientation d)) (hr : m.rotation=gridRotation r)
    (ht : ∀ i : Fin d, ∃ z : ℤ, m.offset i=(z:ℝ)) :
    ∃ a : (Motion d), m=embedMotion a := by
  choose p hp using ht
  refine ⟨⟨r,p⟩,?_⟩
  apply RigidMotion.ext_apply
  intro x
  ext i
  simp [RigidMotion.apply,embedMotion,hr,hp]

theorem blocker_cap {F : Finset (Lattice d)} {p : Lattice d} (hp : p ∈ F)
    (m : RigidMotion d) (r : Orientation d) (hr : m.rotation=gridRotation r)
    {u : EPoint d} (hu : u ∈ openVoxel p) (f : Face d)
    (h0 : (neckCenter d : ℝ)-1/4 < m.apply u 0 ∧ m.apply u 0 < (neckCenter d : ℝ)+1/4)
    (hc : ∀ j : Fin d, j ≠ 0 → m.apply (castPoint p) j=0) :
    ∀ x ∈ interior (solid (localChamber f)), x 0=m.apply u 0 → x ∈ interior (Placed F m) := by
  intro x hx he
  have hxt := local_middle_section f hx (by rw [he]; constructor <;> linarith)
  have hxo : x ∈ openCubeAt (m.apply (castPoint p)) := by
    intro j
    by_cases hj : j=0
    · subst j
      rw [he,grid_voxel_difference m r hr]
      exact hu _
    · simpa only [hc j hj,sub_zero] using hxt j hj
  apply (isOpen_openCubeAt _).subset_interior_iff.mpr (show
    openCubeAt (m.apply (castPoint p)) ⊆ Placed F m from ?_) hxo
  intro y hy
  have hyc : y ∈ cubeAt (m.apply (castPoint p)) := fun j => (hy j).le
  rw [← grid_voxel_image m r hr p] at hyc
  obtain ⟨z,hz,rfl⟩ := hyc
  exact ⟨z,⟨p,hp,hz⟩,rfl⟩

theorem phase_of_end_contact {F : Finset (Lattice d)}
    (m : RigidMotion d) (r : Orientation d) (hr : m.rotation=gridRotation r)
    (f : Face d) (ht : ∀ j : Fin d, j ≠ 0 → ∃ z : ℤ, m.offset j=(z : ℝ))
    (hfar : EuclideanSpace.single 0 ((neckLength d : ℝ)+(boxSide f 0 : ℝ)-(1 : ℝ)/2) ∈ Placed F m)
    (packing : Disjoint (Placed F m) (interior (solid (localBody f)))) :
    ∃ a : Motion d, m=embedMotion a := by
  obtain ⟨x,⟨p,hp,hxp⟩,he⟩ := hfar
  let N : ℤ := (neckLength d : ℤ)+(boxSide f 0 : ℤ)
  let c := m.apply (castPoint p)
  have hx : EuclideanSpace.single 0 ((N : ℝ)-(1 : ℝ)/2) ∈ cubeAt c := by
    rw [← grid_voxel_image m r hr p]
    refine ⟨x,hxp,?_⟩
    simpa [N] using he
  have phase (k : Fin d) (hk : ∃ z : ℤ, m.offset k=(z : ℝ)) : ∃ z : ℤ, c k=(z : ℝ) := by
    obtain ⟨z,hz⟩ := hk
    refine ⟨z+r.sign k*p (r.axes k),?_⟩
    simp [c,RigidMotion.apply,hr,hz]
  have hw : (Pi.single 0 N : Lattice d) ∈ localBody f := by
    apply Finset.mem_image.mpr
    exact ⟨_,far_wall_voxel f,Motion.inverse_apply_apply _ _⟩
  have hd : Disjoint (cubeAt c) (openVoxel (Pi.single 0 N)) := by
    apply packing.mono
    · rw [← grid_voxel_image m r hr p]
      rintro _ ⟨y,hy,rfl⟩
      exact ⟨y,⟨p,hp,hy⟩,rfl⟩
    · exact openVoxel_subset_interior hw
  have hc := end_wall_pins_center c N hx (fun j hj => phase j (ht j hj)) hd
  apply integer_phase_motion m r hr
  intro k
  by_cases hk : k=0
  · subst k
    refine ⟨N-1-r.sign 0*p (r.axes 0),?_⟩
    have hh := hc.1
    dsimp [c] at hh
    simp only [RigidMotion.apply,hr,PiLp.add_apply,gridRotation_apply,castPoint_apply] at hh
    push_cast
    linarith
  · exact ht k hk

end
end TranslationTiling.Rotations.General.Real
