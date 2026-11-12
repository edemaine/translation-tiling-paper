import TranslationTiling.EuclideanMembership.SlotModel
import TranslationTiling.EuclideanMembership.AnchoredCovers

/-! A solution of the compact slot model gives an actual Euclidean tiling.
Density turns rational-probe packing into packing of open voxels. Local
finiteness then turns rational-probe coverage into coverage of all space. -/
namespace TranslationTiling.EuclideanMembership

open Rotations.General (EPoint castPoint)
open Rotations.General.Real
open Set MeasureTheory
noncomputable section
variable {d : ℕ} [NeZero d]

def MotionTiles (P : Tile d) (allowRotations allowReflections : Bool) : Prop :=
  ∃ C : Set (RigidMotion d), (∀ m ∈ C, AllowedLinear allowRotations allowReflections m.rotation) ∧
    AECover (fun m : C => Placed P.toFinset m.val)

private theorem probe_mem_open {U : Set (EPoint d)} (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ a : Probe d, probe a ∈ U := by
  obtain ⟨y,hy⟩ := hne
  obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp hU y hy
  obtain ⟨a,ha⟩ := Metric.denseRange_iff.mp probe_dense y r hr
  exact ⟨a,hball (by simpa only [Metric.mem_ball,dist_comm] using ha)⟩

namespace Model
variable {allowRotations allowReflections : Bool} {P : Tile d} {x : Assignment}

theorem openVoxel_disjoint (h : Model allowRotations allowReflections P x)
    (z w : Active d x) (hne : z ≠ w) {p q : Lattice d} (hp : p ∈ P) (hq : q ∈ P) :
    Disjoint ((h.motion z).apply '' openVoxel p) ((h.motion w).apply '' openVoxel q) := by
  apply Set.disjoint_left.mpr
  intro y hy hz
  have hU : IsOpen (((h.motion z).apply '' openVoxel p) ∩ ((h.motion w).apply '' openVoxel q)) :=
    ((h.motion z).homeomorph.isOpenMap _ (isOpen_openVoxel p)).inter
      ((h.motion w).homeomorph.isOpenMap _ (isOpen_openVoxel q))
  obtain ⟨a,haz,haw⟩ := probe_mem_open hU ⟨y,hy,hz⟩
  have hzw : z.val ≠ w.val := fun he => hne (Subtype.ext he)
  apply h.packing z.val w.val hzw z.property w.property p hp q hq a
  constructor
  · rw [probeValue_eq h.reciprocal]
    exact (motionOfSlot_open_iff x P z.val ((h.slots z.val).2 z.property).1 (probe a) p).mp haz
  · rw [probeValue_eq h.reciprocal]
    exact (motionOfSlot_open_iff x P w.val ((h.slots w.val).2 w.property).1 (probe a) q).mp haw

theorem covers_everywhere (h : Model allowRotations allowReflections P x) :
    ∀ y, ∃ z : Active d x, y ∈ Placed P.toFinset (h.motion z) := by
  have hp := anchorPoint_mem h.nonempty
  have hi : Function.Injective (fun z : Active d x => cellIndex ((h.motion z).apply (castPoint (anchorPoint P)))) := by
    apply cellIndex_injective_of_packing
    intro z w hne
    exact h.openVoxel_disjoint z w hne hp hp
  have hf := locallyFinite_placed P hp h.motion hi
  have hc := hf.isClosed_iUnion (fun z => isClosed_placed P.toFinset (h.motion z))
  have hprobe (a : Probe d) : ∃ z : Active d x, probe a ∈ Placed P.toFinset (h.motion z) := by
    obtain ⟨z,hz,he,p,hp,hv⟩ := h.coverage a
    refine ⟨⟨z,he⟩,(motionOfSlot_closed_iff x P z ((h.slots z).2 he).1 (probe a)).mpr ?_⟩
    exact ⟨p,hp,by simpa only [probeValue_eq h.reciprocal] using hv⟩
  intro y
  by_contra hy
  have hyn : y ∈ (⋃ z : Active d x, Placed P.toFinset (h.motion z))ᶜ := by simpa using hy
  obtain ⟨a,ha⟩ := probe_mem_open hc.isOpen_compl ⟨y,hyn⟩
  obtain ⟨z,hz⟩ := hprobe a
  exact ha (Set.mem_iUnion.mpr ⟨z,hz⟩)

theorem aeCover (h : Model allowRotations allowReflections P x) :
    AECover (fun z : Active d x => Placed P.toFinset (h.motion z)) := by
  haveI : Countable (Active d x) := inferInstanceAs (Countable {z : Lattice d // Enabled x z})
  have hb : ∀ᵐ y ∂volume, ∀ z : Active d x, ∀ i : Fin d, ∀ k : ℤ,
      (h.motion z).inverse.apply y i ≠ (k : ℝ)+1/2 := by
    apply ae_all_iff.mpr
    intro z
    exact (h.motion z).inverse.measurePreserving.quasiMeasurePreserving.ae ae_nonboundary
  filter_upwards [hb] with y hy
  have hopen (z : Active d x) (hz : y ∈ Placed P.toFinset (h.motion z)) :
      ∃ p ∈ P, y ∈ (h.motion z).apply '' openVoxel p := by
    obtain ⟨t,ht,rfl⟩ := hz
    obtain ⟨p,hp,hv⟩ := ht
    refine ⟨p,List.mem_toFinset.mp hp,t,voxel_open_of_nonboundary ?_ hv,rfl⟩
    simpa only [RigidMotion.inverse_apply] using hy z
  obtain ⟨z,hz⟩ := h.covers_everywhere y
  refine ⟨z,hz,fun w hw => ?_⟩
  by_contra hne
  obtain ⟨p,hp,hyp⟩ := hopen w hw
  obtain ⟨q,hq,hyq⟩ := hopen z hz
  exact Set.disjoint_left.mp (h.openVoxel_disjoint w z hne hp hq) hyp hyq

theorem realizes (h : Model allowRotations allowReflections P x) :
    MotionTiles P allowRotations allowReflections := by
  refine ⟨Set.range h.motion,?_,?_⟩
  · rintro m ⟨z,rfl⟩
    exact h.motion_allowed z
  · filter_upwards [h.aeCover] with y hy
    obtain ⟨z,hz,hu⟩ := hy
    refine ⟨⟨h.motion z,z,rfl⟩,hz,?_⟩
    intro m hm
    obtain ⟨w,hw⟩ := m.property
    have hwm : w=z := hu w (by simpa only [hw] using hm)
    apply Subtype.ext
    exact hw.symm.trans (congrArg h.motion hwm)

end Model
end
end TranslationTiling.EuclideanMembership
