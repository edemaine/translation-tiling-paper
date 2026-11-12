import TranslationTiling.Rotations.Euclidean.GridEmbedding
import TranslationTiling.Rotations.Euclidean.VoxelPacking

namespace TranslationTiling.Rotations.Euclidean

noncomputable section
open Set

theorem castPoint_mem_voxel (p q : Lattice 3) : castPoint p ∈ voxel q ↔ p=q := by
  constructor
  · intro hx
    funext j
    have hh := abs_le.mp (hx j)
    change -((1:ℝ)/2) ≤ (p j:ℝ)-(q j:ℝ) ∧ (p j:ℝ)-(q j:ℝ) ≤ (1:ℝ)/2 at hh
    have hl : (-1:ℝ)<(p j:ℝ)-(q j:ℝ) := by linarith
    have hu : (p j:ℝ)-(q j:ℝ)<1 := by linarith
    have hl' : (-1:ℤ)<p j-q j := by exact_mod_cast hl
    have hu' : p j-q j<(1:ℤ) := by exact_mod_cast hu
    omega
  · intro he
    rw [he]
    exact openVoxel_subset_voxel q (castPoint_openVoxel q)

theorem castPoint_mem_solid (F : Finset (Lattice 3)) (p : Lattice 3) :
    castPoint p ∈ solid F ↔ p ∈ F := by
  constructor
  · rintro ⟨q,hq,hx⟩
    exact (castPoint_mem_voxel p q).mp hx ▸ hq
  · intro hp
    exact ⟨p,hp,(castPoint_mem_voxel p p).mpr rfl⟩

theorem castPoint_mem_placed (a : Motion) (F : Finset (Lattice 3)) (p : Lattice 3) :
    castPoint p ∈ Placed F (embedMotion a) ↔ p ∈ a.apply '' (F : Set (Lattice 3)) := by
  change castPoint p ∈ (embedMotion a).apply '' solid F ↔ _
  rw [embedMotion_solid,castPoint_mem_solid]
  simp only [Finset.mem_image,Set.mem_image,Finset.mem_coe]

theorem grid_footprint_avoids_body (a : Motion) (F H : Finset (Lattice 3))
    (hd : Disjoint (Placed F (embedMotion a)) (interior (solid H))) :
    Disjoint (a.apply '' (F : Set (Lattice 3))) (H : Set (Lattice 3)) := by
  apply Set.disjoint_left.mpr
  intro x hx hH
  exact Set.disjoint_left.mp hd ((castPoint_mem_placed a F x).mpr hx)
    (openVoxel_subset_interior hH (castPoint_openVoxel x))

end
end TranslationTiling.Rotations.Euclidean
