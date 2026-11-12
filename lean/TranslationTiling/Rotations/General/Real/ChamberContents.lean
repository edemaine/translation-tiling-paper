import TranslationTiling.Rotations.General.Real.CappedChambers
import TranslationTiling.Rotations.General.Real.ChamberDiameter
import TranslationTiling.Rotations.General.Real.MotionAlgebra
import TranslationTiling.Rotations.General.ConnectedAssembly

namespace TranslationTiling.Rotations.General.Real
noncomputable section
open Set
variable {d : ℕ} [NeZero d]

def localGadget (f : Face d) : Finset (Lattice d) := gadget.image (frameMotion f).inverse.apply

theorem localBody_subset_localGadget (f : Face d) : localBody f ⊆ localGadget f :=
  Finset.image_mono _ body_subset_gadget

theorem localGadget_chamber_disjoint (f : Face d) : Disjoint (localGadget f) (localChamber f) := by
  apply Finset.disjoint_left.mpr
  intro x hxG hxC
  obtain ⟨g,hg,he⟩ := Finset.mem_image.mp hxG
  have hh : g=(frameMotion f).apply x := by
    have h := congrArg (frameMotion f).apply he
    simpa only [Motion.apply_inverse_apply] using h
  have hx : (frameMotion f).apply x ∈ chamber f := ⟨x,(mem_localChamber f x).mp hxC,rfl⟩
  exact recess_free f (chamber_subset_recess f hx) (hh ▸ hg)

theorem chamberAbove_avoids_host (f : Face d) (h : ℝ) :
    Disjoint (chamberAbove f h) (solid (localGadget f)) :=
  (solid_disjoint_interior (localGadget_chamber_disjoint f)).symm.mono_left inter_subset_left

theorem local_host_solid (f : Face d) :
    Placed gadget (embedMotion (frameMotion f)).inverse=solid (localGadget f) := by
  rw [← embedMotion_inverse]
  exact embedMotion_solid _ _

theorem chamber_center_above (f : Face d) (h : ℝ) (hh : h < (neckCenter d : ℝ)+(1 : ℝ)/2)
    (p : Lattice d) (hp : p ∈ localChamber f) (h3 : (neckCenter d : ℤ)+1 ≤ p 0) :
    castPoint p ∈ chamberAbove f h := by
  refine ⟨openVoxel_subset_interior hp (castPoint_openVoxel p),?_⟩
  change h < (p 0 : ℝ)
  have h3r : (neckCenter d : ℝ)+1 ≤ (p 0 : ℝ) := by exact_mod_cast h3
  linarith

def lastChamberVoxel (f : Face d) : Lattice d :=
  Pi.single 0 ((neckLength d : ℤ)+(boxSide f 0 : ℤ)-1)

def farChamberPoint (f : Face d) : EPoint d :=
  EuclideanSpace.single 0 ((neckLength d : ℝ)+(boxSide f 0 : ℝ)-(1 : ℝ)/2)

theorem lastChamberVoxel_mem (f : Face d) : lastChamberVoxel f ∈ localChamber f := by
  rw [mem_localChamber]
  left
  intro j
  have hp := boxSide_two_le f j
  by_cases hj : j=0
  · subst j
    simp only [lastChamberVoxel,Pi.single_eq_same,keyLo,keyHi,ite_true]
    omega
  · simp only [lastChamberVoxel,Pi.single_eq_of_ne hj,keyLo,keyHi,ite_eq_right hj]
    omega

theorem farPoint_closure_above (f : Face d) (h : ℝ) (hh : h < (neckCenter d : ℝ)+(1 : ℝ)/2) :
    farChamberPoint f ∈ closure (chamberAbove f h) := by
  have hsub : openVoxel (lastChamberVoxel f) ⊆ chamberAbove f h := by
    intro x hx
    refine ⟨openVoxel_subset_interior (lastChamberVoxel_mem f) hx,?_⟩
    have hv := abs_lt.mp (hx 0)
    have hp : (2 : ℝ) ≤ (boxSide f 0 : ℝ) := by exact_mod_cast boxSide_two_le f (0 : Fin d)
    change h < x 0
    simp only [lastChamberVoxel,Pi.single_eq_same,Int.cast_sub,Int.cast_add,Int.cast_natCast,Int.cast_one] at hv
    have hn : (neckCenter d : ℝ)+(1 : ℝ)/2 < (neckLength d : ℝ) := by
      simp only [neckCenter,neckLength,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
      linarith [Nat.cast_nonneg (α := ℝ) d]
    linarith
  have hx : farChamberPoint f ∈ voxel (lastChamberVoxel f) := by
    intro j
    by_cases hj : j=0
    · subst j
      simp only [farChamberPoint,lastChamberVoxel,PiLp.single_apply,ite_true,Pi.single_eq_same,
        Int.cast_sub,Int.cast_add,Int.cast_natCast,Int.cast_one]
      rw [abs_le]
      constructor <;> linarith
    · simp [farChamberPoint,lastChamberVoxel,PiLp.single_apply,hj,Pi.single_eq_of_ne hj]
  rw [← closure_openVoxel] at hx
  exact closure_mono hsub hx

theorem distant_centers : dist (castPoint (0 : Lattice d))
    (castPoint (((cubeSide d : ℤ)-1) • (Pi.single 0 1 : Lattice d))) = (cubeSide d : ℝ)-1 := by
  rw [dist_eq_norm,castPoint_zero,zero_sub,norm_neg]
  have he : castPoint (((cubeSide d : ℤ)-1) • (Pi.single 0 1 : Lattice d)) =
      EuclideanSpace.single 0 ((cubeSide d : ℝ)-1) := by
    ext j
    by_cases hj : j=0 <;> simp [PiLp.single_apply,hj,Pi.single_apply]
  rw [he]
  have hp := cubeSide_pos (d := d)
  simp only [EuclideanSpace.single,PiLp.norm_single,Real.norm_eq_abs]
  rw [abs_of_nonneg (by exact_mod_cast (show 0 ≤ (cubeSide d : ℤ)-1 by omega))]

theorem copy_escapes_chamber (hd : 3 ≤ d) (f : Face d) (h : ℝ) (m : RigidMotion d) :
    ¬ (∀ p ∈ gadget, m.apply (castPoint p) ∈ chamberAbove f h) := by
  intro hall
  have hx := hall 0 (body_subset_gadget (zero_body (by omega : 2 ≤ d)))
  have hy := hall _ (corner_mem (by omega : 2 ≤ d) (0 : Fin d))
  have hdiam := chamber_diameter f (interior_subset hx.1) (interior_subset hy.1)
  rw [m.dist_apply,distant_centers] at hdiam
  exact (lt_irrefl _) hdiam

end
end TranslationTiling.Rotations.General.Real
