import TranslationTiling.Rotations.General.Real.VoxelStars
import Mathlib.Analysis.Convex.Topology
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.AEDisjoint

namespace TranslationTiling.Rotations.General.Real
variable {d : ℕ} [NeZero d]

noncomputable section
open Set MeasureTheory

theorem convex_voxel (p : Lattice d) : Convex ℝ (voxel p) := by
  intro x hx y hy a b ha hb hab i
  have hx' := abs_le.mp (hx i)
  have hy' := abs_le.mp (hy i)
  apply abs_le.mpr
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  have h₁ := mul_le_mul_of_nonneg_left hx'.1 ha
  have h₂ := mul_le_mul_of_nonneg_left hy'.1 hb
  have h₃ := mul_le_mul_of_nonneg_left hx'.2 ha
  have h₄ := mul_le_mul_of_nonneg_left hy'.2 hb
  have he := congrArg (fun t : ℝ => t * (p i : ℝ)) hab
  constructor <;> nlinarith only [h₁, h₂, h₃, h₄, he, hab]

theorem closure_interior_voxel (p : Lattice d) : closure (interior (voxel p)) = voxel p := by
  have h : (interior (voxel p)).Nonempty := by
    refine ⟨castPoint p, (isOpen_openVoxel p).subset_interior_iff.mpr
      (openVoxel_subset_voxel p) (castPoint_openVoxel p)⟩
  rw [(convex_voxel p).closure_interior_eq_closure_of_nonempty_interior h,
    (isClosed_voxel p).closure_eq]

theorem closure_interior_solid (F : Finset (Lattice d)) :
    closure (interior (solid F)) = solid F := by
  apply subset_antisymm
  · exact (isClosed_solid F).closure_subset_iff.mpr interior_subset
  · rintro x ⟨p, hp, hx⟩
    rw [← closure_interior_voxel p] at hx
    exact closure_mono (interior_mono (show voxel p ⊆ solid F from
      fun y hy => ⟨p, hp, hy⟩)) hx

theorem closure_interior_placed (F : Finset (Lattice d)) (m : (RigidMotion d)) :
    closure (interior (Placed F m)) = Placed F m := by
  change closure (interior (m.homeomorph '' solid F)) = m.homeomorph '' solid F
  rw [← m.homeomorph.image_interior, ← m.homeomorph.image_closure, closure_interior_solid]

theorem isClosed_placed (F : Finset (Lattice d)) (m : (RigidMotion d)) : IsClosed (Placed F m) :=
  m.homeomorph.isClosedMap _ (isClosed_solid F)

theorem AECover.aedisjoint {ι : Type*} {P : ι → Set (EPoint d)} (h : AECover P)
    {i j : ι} (hne : i ≠ j) : AEDisjoint volume (P i) (P j) := by
  apply measure_mono_null ?_ (ae_iff.mp h)
  rintro x ⟨hx, hx'⟩ ⟨c, _, hu⟩
  exact hne ((hu i hx).trans (hu j hx').symm)

theorem AECover.interior_disjoint {ι : Type*} {P : ι → Set (EPoint d)} (h : AECover P) :
    Pairwise (fun i j => Disjoint (interior (P i)) (interior (P j))) := by
  intro i j hne
  have hn := measure_mono_null (inter_subset_inter interior_subset interior_subset)
    (h.aedisjoint hne)
  have he : interior (P i) ∩ interior (P j) = ∅ :=
    (isOpen_interior.inter isOpen_interior).eq_empty_of_measure_zero hn
  exact disjoint_iff_inter_eq_empty.mpr he

theorem AECover.countable {ι : Type*} {F : Finset (Lattice d)}
    (hF : F.Nonempty) (M : ι → (RigidMotion d)) (h : AECover (fun i => Placed F (M i))) :
    Countable ι := by
  apply h.interior_disjoint.countable_of_isOpen_disjoint (fun _ => isOpen_interior)
  intro i
  change (interior ((M i).homeomorph '' solid F)).Nonempty
  rw [← (M i).homeomorph.image_interior]
  exact (solid_interior_nonempty hF).image _

/-- A closed regular tile cannot even touch the interior of another tile in
an almost-everywhere packing. -/
theorem AECover.interior_solid_disjoint {ι : Type*} {F : Finset (Lattice d)}
    {M : ι → (RigidMotion d)} (h : AECover (fun i => Placed F (M i))) {i j : ι} (hne : i ≠ j) :
    Disjoint (interior (Placed F (M i))) (Placed F (M j)) := by
  rw [← closure_interior_placed F (M j)]
  exact h.interior_disjoint hne |>.closure_right isOpen_interior

theorem ae_nonboundary : ∀ᵐ x : (EPoint d) ∂volume,
    ∀ i : Fin d, ∀ z : ℤ, x i ≠ (z : ℝ)+(1:ℝ)/2 := by
  have h : ∀ᵐ x : Fin d → ℝ ∂volume,
      ∀ i : Fin d, ∀ z : ℤ, x i ≠ (z : ℝ)+(1:ℝ)/2 := by
    apply ae_all_iff.mpr
    intro i
    apply ae_all_iff.mpr
    intro z
    exact Measure.ae_eval_ne (fun _ : Fin d => (volume : Measure ℝ)) i _
  exact (PiLp.volume_preserving_ofLp (ι := Fin d)).quasiMeasurePreserving.ae h

theorem voxel_open_of_nonboundary {x : (EPoint d)}
    (hx : ∀ i : Fin d, ∀ z : ℤ, x i ≠ (z : ℝ)+(1:ℝ)/2)
    {p : Lattice d} (hp : x ∈ voxel p) : x ∈ openVoxel p := by
  intro i
  have hh := abs_le.mp (hp i)
  have hl := hx i (p i-1)
  have hu := hx i (p i)
  simp only [Int.cast_sub, Int.cast_one] at hl
  apply abs_lt.mpr
  constructor
  · exact lt_of_le_of_ne hh.1 (by intro he; exact hl (by linarith))
  · exact lt_of_le_of_ne hh.2 (by intro he; exact hu (by linarith))

theorem AECover.ae_open_voxel {ι : Type*} {F : Finset (Lattice d)}
    (hF : F.Nonempty) (M : ι → (RigidMotion d)) (h : AECover (fun i => Placed F (M i))) :
    ∀ᵐ x ∂volume, ∃ i, ∃ p ∈ F, x ∈ (M i).apply '' openVoxel p := by
  haveI := h.countable hF M
  have hb : ∀ᵐ x ∂volume, ∀ i, ∀ k : Fin d, ∀ z : ℤ,
      (M i).inverse.apply x k ≠ (z : ℝ)+(1:ℝ)/2 := by
    apply ae_all_iff.mpr
    intro i
    exact (M i).inverse.measurePreserving.quasiMeasurePreserving.ae ae_nonboundary
  filter_upwards [h, hb] with x hx hxb
  obtain ⟨i, ⟨y, ⟨p, hp, hy⟩, rfl⟩, _⟩ := hx
  refine ⟨i, p, hp, y, voxel_open_of_nonboundary ?_ hy, rfl⟩
  simpa only [RigidMotion.inverse_apply] using hxb i

end
end TranslationTiling.Rotations.General.Real
