import TranslationTiling.Rotations.Euclidean.GridSampling
import TranslationTiling.Rotations.Assembly

namespace TranslationTiling.Rotations.Euclidean

noncomputable section
open Set MeasureTheory SixKeys

theorem voxel_centers_unique {x : EPoint}
    (hb : ∀ k : Fin 3, ∀ z : ℤ, x k ≠ (z:ℝ)+(1:ℝ)/2)
    {p q : Point} (hp : x ∈ voxel p) (hq : x ∈ voxel q) : p=q := by
  by_contra hn
  exact Set.disjoint_left.mp (openVoxel_voxel_disjoint hn) (voxel_open_of_nonboundary hb hp) hq

theorem grid_cover_of_ae_cover {ι : Type*} (F : Finset Point) (M : ι → Motion)
    (cover : AECover (fun j => Euclidean.Placed F (embedMotion (M j)))) :
    ExactCover (fun j => SixKeys.Placed F (M j)) := by
  intro p
  have hpos := (isOpen_openVoxel p).measure_ne_zero volume ⟨castPoint p,castPoint_openVoxel p⟩
  obtain ⟨x,hxp,j,⟨y,hy,he⟩,_⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hpos
    (ae_restrict_of_ae cover)
  have hximage : x ∈ solid (F.image (M j).apply) := by
    rw [← embedMotion_solid]
    exact ⟨y,hy,he⟩
  obtain ⟨q,hq,hxq⟩ := hximage
  have hpq : p=q := by
    by_contra hn
    exact Set.disjoint_left.mp (openVoxel_voxel_disjoint hn) hxp hxq
  have hpj : p ∈ SixKeys.Placed F (M j) := by
    rw [hpq]
    exact Finset.mem_image.mp hq
  refine ⟨j,hpj,?_⟩
  intro k hpk
  by_contra hne
  have center_interior (l : ι) (hpl : p ∈ SixKeys.Placed F (M l)) :
      castPoint p ∈ interior (Euclidean.Placed F (embedMotion (M l))) := by
    change castPoint p ∈ interior ((embedMotion (M l)).apply '' solid F)
    rw [embedMotion_solid]
    exact openVoxel_subset_interior (Finset.mem_image.mpr hpl) (castPoint_openVoxel p)
  exact Set.disjoint_left.mp (cover.interior_disjoint hne) (center_interior k hpk) (center_interior j hpj)

theorem ae_cover_of_grid_cover {ι : Type*} (F : Finset Point) (M : ι → Motion)
    (cover : ExactCover (fun j => SixKeys.Placed F (M j))) :
    AECover (fun j => Euclidean.Placed F (embedMotion (M j))) := by
  filter_upwards [ae_nonboundary] with x hb
  let p := starLo x
  have hxp : x ∈ voxel p := by
    apply (mem_star x p).mp
    apply (mem_block _ _ _).mpr
    intro k
    exact ⟨le_refl _,star_bounds x k⟩
  obtain ⟨j,hj,unique⟩ := cover p
  have hxj : x ∈ Euclidean.Placed F (embedMotion (M j)) := by
    change x ∈ (embedMotion (M j)).apply '' solid F
    rw [embedMotion_solid]
    exact ⟨p,Finset.mem_image.mpr hj,hxp⟩
  refine ⟨j,hxj,?_⟩
  intro k hxk
  apply unique k
  change x ∈ (embedMotion (M k)).apply '' solid F at hxk
  rw [embedMotion_solid] at hxk
  obtain ⟨q,hq,hxq⟩ := hxk
  have hpq := voxel_centers_unique hb hxp hxq
  rw [hpq]
  exact Finset.mem_image.mp hq

theorem ae_cover_range {ι : Type*} {F : Finset Point} (M : ι → RigidMotion)
    (cover : AECover (fun j => Euclidean.Placed F (M j))) :
    AECover (fun m : Set.range M => Euclidean.Placed F m.val) := by
  filter_upwards [cover] with x hx
  obtain ⟨j,hj,unique⟩ := hx
  refine ⟨⟨M j,j,rfl⟩,hj,?_⟩
  intro m hm
  obtain ⟨k,hk⟩ := m.property
  have hkj : k=j := unique k (by simpa only [hk] using hm)
  apply Subtype.ext
  exact hk.symm.trans (congrArg M hkj)

theorem euclideanTiles_of_cover {ι : Type*} {F : Finset Point} (M : ι → RigidMotion)
    (cover : AECover (fun j => Euclidean.Placed F (M j))) : EuclideanTiles F :=
  ⟨range M,ae_cover_range M cover⟩

end
end TranslationTiling.Rotations.Euclidean
