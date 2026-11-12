import TranslationTiling.Rotations.Euclidean.NeckCopy
import TranslationTiling.Rotations.Euclidean.CappedChambers
import TranslationTiling.Rotations.Euclidean.Monopoly

namespace TranslationTiling.Rotations.Euclidean

noncomputable section
open Set SixKeys

theorem isOpen_openCubeAt (c : EPoint) : IsOpen (openCubeAt c) := by
  have he : openCubeAt c = ⋂ i : Fin 3, {x : EPoint | |x i-c i| < (1:ℝ)/2} := by
    ext x; simp [openCubeAt]
  rw [he]
  apply isOpen_iInter_of_finite
  intro i
  exact isOpen_lt (by fun_prop) continuous_const

theorem grid_voxel_difference (m : RigidMotion) (r : Orientation)
    (hr : m.rotation=gridRotation r) (p : Lattice 3) (u : EPoint) (j : Fin 3) :
    |m.apply u j-m.apply (castPoint p) j|=|u (r.axes j)-(p (r.axes j):ℝ)| := by
  have he : m.apply u j-m.apply (castPoint p) j =
      (r.sign j:ℝ)*(u (r.axes j)-(p (r.axes j):ℝ)) := by
    simp [RigidMotion.apply,hr]
    ring
  rw [he,abs_mul,sign_real_abs,one_mul]

theorem blocker_cap {F : Finset (Lattice 3)} {p : Lattice 3} (hp : p ∈ F)
    (m : RigidMotion) (r : Orientation) (hr : m.rotation=gridRotation r)
    {u : EPoint} (hu : u ∈ openVoxel p) (i : Face)
    (h0 : (7:ℝ)/4<m.apply u 0 ∧ m.apply u 0<9/4)
    (hc1 : m.apply (castPoint p) 1=0) (hc2 : m.apply (castPoint p) 2=0) :
    ∀ x ∈ interior (solid (localChamber i)), x 0=m.apply u 0 →
      x ∈ interior (Placed F m) := by
  intro x hx he
  have hxt := local_middle_section i hx (by rw [he]; constructor <;> linarith)
  have hxo : x ∈ openCubeAt (m.apply (castPoint p)) := by
    intro j
    fin_cases j <;> dsimp
    · rw [he,grid_voxel_difference m r hr]
      exact hu _
    · simpa only [hc1,sub_zero] using hxt.1
    · simpa only [hc2,sub_zero] using hxt.2
  apply (isOpen_openCubeAt _).subset_interior_iff.mpr (show
    openCubeAt (m.apply (castPoint p)) ⊆ Placed F m from ?_) hxo
  intro y hy
  have hyc : y ∈ cubeAt (m.apply (castPoint p)) := fun j => (hy j).le
  rw [← grid_voxel_image m r hr p] at hyc
  obtain ⟨z,hz,rfl⟩ := hyc
  exact ⟨z,⟨p,hp,hz⟩,rfl⟩

theorem integer_phase_motion (m : RigidMotion) (r : Orientation) (hr : m.rotation=gridRotation r)
    (ht : ∀ i : Fin 3, ∃ z : ℤ, m.offset i=(z:ℝ)) :
    ∃ a : Motion, m=embedMotion a := by
  choose p hp using ht
  refine ⟨⟨r,p⟩,?_⟩
  apply RigidMotion.ext_apply
  intro x
  ext i
  simp [RigidMotion.apply,embedMotion,hr,hp]

theorem phase_of_end_contact {F : Finset (Lattice 3)}
    (m : RigidMotion) (r : Orientation) (hr : m.rotation=gridRotation r)
    (i : Face) (ht1 : ∃ z : ℤ,m.offset 1=(z:ℝ)) (ht2 : ∃ z : ℤ,m.offset 2=(z:ℝ))
    (hfar : WithLp.toLp 2 (![(((dimensions i).1:ℝ)+(9:ℝ)/2),0,0]) ∈ Placed F m)
    (packing : Disjoint (Placed F m) (interior (solid (localBody i)))) :
    ∃ a : Motion, m=embedMotion a := by
  obtain ⟨x,⟨p,hp,hxp⟩,he⟩ := hfar
  let N : ℤ := 5+(dimensions i).1
  let c := m.apply (castPoint p)
  have hx : WithLp.toLp 2 (![((N:ℝ)-(1:ℝ)/2),0,0]) ∈ cubeAt c := by
    rw [← grid_voxel_image m r hr p]
    refine ⟨x,hxp,?_⟩
    convert he using 1 <;> ext j <;> fin_cases j <;> simp [N] <;> ring
  have phase (k : Fin 3) (hk : ∃ z : ℤ,m.offset k=(z:ℝ)) : ∃ z : ℤ,c k=(z:ℝ) := by
    obtain ⟨z,hz⟩ := hk
    refine ⟨z+r.sign k*p (r.axes k),?_⟩
    simp [c,RigidMotion.apply,hr,hz]
  have hw : (![N,0,0] : Lattice 3) ∈ localBody i := by
    apply Finset.mem_image.mpr
    refine ⟨_,far_wall_voxel i,?_⟩
    apply (frameMotion i).injective
    rw [Motion.apply_inverse_apply]
    simpa [N] using (frame_localPoint i (5+(dimensions i).1) 0 0).symm
  have hd : Disjoint (cubeAt c) (openVoxel (![N,0,0] : Lattice 3)) := by
    apply packing.mono
    · rw [← grid_voxel_image m r hr p]
      rintro _ ⟨y,hy,rfl⟩
      exact ⟨y,⟨p,hp,hy⟩,rfl⟩
    · exact openVoxel_subset_interior hw
  have hc := end_wall_pins_center c N hx (phase 1 ht1) (phase 2 ht2) hd
  apply integer_phase_motion m r hr
  intro k
  fin_cases k
  · refine ⟨N-1-r.sign 0*p (r.axes 0),?_⟩
    have hec := hc.1
    dsimp [c] at hec
    simp only [RigidMotion.apply,hr,PiLp.add_apply,gridRotation_apply,castPoint_apply] at hec
    push_cast
    linarith
  · exact ht1
  · exact ht2

end
end TranslationTiling.Rotations.Euclidean
