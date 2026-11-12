import TranslationTiling.Rotations.Euclidean.CappedChambers
import TranslationTiling.Rotations.Euclidean.MotionAlgebra
import TranslationTiling.Rotations.Gadget

namespace TranslationTiling.Rotations.Euclidean

noncomputable section
open Set SixKeys

def localGadget (i : Face) := gadget.image (frameMotion i).inverse.apply

theorem localBody_subset_localGadget (i : Face) : localBody i ⊆ localGadget i :=
  Finset.image_mono _ body_subset_gadget

theorem localGadget_chamber_disjoint (i : Face) : Disjoint (localGadget i) (localChamber i) := by
  apply Finset.disjoint_left.mpr
  intro x hxG hxC
  obtain ⟨g,hg,heG⟩ := Finset.mem_image.mp hxG
  obtain ⟨c,hc,heC⟩ := Finset.mem_image.mp hxC
  have he : g=c := (frameMotion i).inverse.injective (heG.trans heC.symm)
  exact recess_free i (Finset.mem_of_mem_erase hc) (he ▸ hg)

theorem chamberAbove_avoids_host (i : Face) (h : ℝ) :
    Disjoint (chamberAbove i h) (solid (localGadget i)) :=
  (solid_disjoint_interior (localGadget_chamber_disjoint i)).symm.mono_left inter_subset_left

theorem local_host_solid (i : Face) :
    Placed gadget (embedMotion (frameMotion i)).inverse = solid (localGadget i) := by
  rw [← embedMotion_inverse]
  exact embedMotion_solid _ _

theorem chamber_center_above (i : Face) (h : ℝ) (hh : h < (5:ℝ)/2)
    (p : Lattice 3) (hp : p ∈ localChamber i) (h3 : 3 ≤ p 0) :
    castPoint p ∈ chamberAbove i h := by
  refine ⟨openVoxel_subset_interior hp (castPoint_openVoxel p),?_⟩
  change h < (p 0:ℝ)
  have h3r : (3:ℝ) ≤ (p 0:ℝ) := by exact_mod_cast h3
  linarith

def lastChamberVoxel (i : Face) : Lattice 3 := ![4+(dimensions i).1,0,0]
def farChamberPoint (i : Face) : EPoint := WithLp.toLp 2 (![(((dimensions i).1:ℝ)+(9:ℝ)/2),0,0])

theorem lastChamberVoxel_mem (i : Face) : lastChamberVoxel i ∈ localChamber i := by
  rw [mem_localChamber]
  right
  have hpos := dimensions_pos i
  simp only [lastChamberVoxel,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.head_cons,Matrix.tail_cons]
  omega

theorem farPoint_closure_above (i : Face) (h : ℝ) (hh : h < (5:ℝ)/2) :
    farChamberPoint i ∈ closure (chamberAbove i h) := by
  have hsub : openVoxel (lastChamberVoxel i) ⊆ chamberAbove i h := by
    intro x hx
    refine ⟨openVoxel_subset_interior (lastChamberVoxel_mem i) hx,?_⟩
    have hv := abs_lt.mp (hx 0)
    have hpos := (dimensions_pos i).1
    change h < x 0
    simp only [lastChamberVoxel,Matrix.cons_val_zero,Int.cast_add,Int.cast_ofNat] at hv
    push_cast at hv
    have hd : (1:ℝ) ≤ (dimensions i).1 := by exact_mod_cast hpos
    linarith
  have hx : farChamberPoint i ∈ voxel (lastChamberVoxel i) := by
    intro j
    fin_cases j <;> norm_num [farChamberPoint,lastChamberVoxel,abs_le] <;> constructor <;> linarith
  rw [← closure_openVoxel] at hx
  exact closure_mono hsub hx

theorem gadget_distant_voxel : (![39,0,0] : Lattice 3) ∈ gadget := by
  apply body_subset_gadget
  rw [mem_body_iff]
  simp [BodyPred,InCube,Fin.forall_fin_succ]

theorem distant_centers : dist (castPoint (0 : Lattice 3)) (castPoint (![39,0,0] : Lattice 3)) = 39 := by
  rw [dist_eq_norm,castPoint_zero,zero_sub,norm_neg]
  have he := EuclideanSpace.real_norm_sq_eq (castPoint (![39,0,0] : Lattice 3))
  norm_num [Fin.sum_univ_three] at he
  nlinarith [norm_nonneg (castPoint (![39,0,0] : Lattice 3))]

theorem copy_escapes_chamber (i : Face) (h : ℝ) (m : RigidMotion) :
    ¬ (∀ p ∈ gadget, m.apply (castPoint p) ∈ chamberAbove i h) := by
  intro hall
  have hx := hall 0 (body_subset_gadget zero_body)
  have hy := hall (![39,0,0]) gadget_distant_voxel
  have hd := chamber_diameter i (interior_subset hx.1) (interior_subset hy.1)
  rw [m.dist_apply,distant_centers] at hd
  norm_num at hd

end
end TranslationTiling.Rotations.Euclidean
