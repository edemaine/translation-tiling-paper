import TranslationTiling.EuclideanMembership.BodyBounds
import Mathlib.Analysis.Normed.Affine.AddTorsor

/-! Spatial indexing of packings and exact coverage. The argument needs neither
facet-to-facet contacts nor a finite set of orientations. -/
namespace TranslationTiling.EuclideanMembership

open Rotations.General (EPoint castPoint)
open Rotations.General.Real
open Set MeasureTheory
noncomputable section
variable {d : ℕ} [NeZero d] {ι : Type*}

theorem motion_ball_subset_openVoxel (p : Lattice d) (m : RigidMotion d) :
    Metric.ball (m.apply (castPoint p)) (1/2) ⊆ m.apply '' openVoxel p := by
  intro x hx
  have hd : dist (m.inverse.apply x) (castPoint p) < 1/2 := by
    have he := motion_dist_eq m (m.inverse.apply x) (castPoint p)
    rw [RigidMotion.apply_inverse] at he
    exact he.symm.trans_lt hx
  refine ⟨m.inverse.apply x,?_,RigidMotion.apply_inverse m x⟩
  intro i
  have hi := PiLp.norm_apply_le (p := 2) (m.inverse.apply x-castPoint p) i
  simp only [Real.norm_eq_abs,PiLp.sub_apply,Rotations.General.castPoint_apply] at hi
  exact hi.trans_lt (by simpa only [dist_eq_norm] using hd)

theorem motion_openVoxel_subset_interior (P : Tile d) {p : Lattice d} (hp : p ∈ P)
    (m : RigidMotion d) : m.apply '' openVoxel p ⊆ interior (Placed P.toFinset m) := by
  change m.homeomorph '' openVoxel p ⊆ interior (m.homeomorph '' solid P.toFinset)
  rw [← m.homeomorph.image_interior]
  exact Set.image_mono (openVoxel_subset_interior (List.mem_toFinset.mpr hp))

/-- Packing one distinguished open cube already makes the spatial cell labels
injective. This supplies the uniform local finiteness needed by compactness. -/
theorem cellIndex_injective_of_packing (p : Lattice d) (M : ι → RigidMotion d)
    (hpack : Pairwise fun i j => Disjoint ((M i).apply '' openVoxel p) ((M j).apply '' openVoxel p)) :
    Function.Injective (fun i => cellIndex ((M i).apply (castPoint p))) := by
  intro i j he
  by_contra hne
  have hd := same_cell_dist_lt_one he
  let a := (M i).apply (castPoint p)
  let b := (M j).apply (castPoint p)
  let x := midpoint ℝ a b
  have hx : x ∈ Metric.ball a (1/2) := by
    change dist (midpoint ℝ a b) a < 1/2
    rw [dist_midpoint_left]
    norm_num
    exact hd
  have hy : x ∈ Metric.ball b (1/2) := by
    change dist (midpoint ℝ a b) b < 1/2
    rw [dist_midpoint_right]
    norm_num
    exact hd
  exact Set.disjoint_left.mp (hpack hne)
    (motion_ball_subset_openVoxel p (M i) hx) (motion_ball_subset_openVoxel p (M j) hy)

theorem cellIndex_injective_of_aeCover (P : Tile d) {p : Lattice d} (hp : p ∈ P)
    (M : ι → RigidMotion d) (h : AECover (fun i => Placed P.toFinset (M i))) :
    Function.Injective (fun i => cellIndex ((M i).apply (castPoint p))) := by
  apply cellIndex_injective_of_packing p M
  intro i j hij
  exact (h.interior_disjoint hij).mono
    (motion_openVoxel_subset_interior P hp (M i)) (motion_openVoxel_subset_interior P hp (M j))

theorem locallyFinite_placed (P : Tile d) {p : Lattice d} (hp : p ∈ P)
    (M : ι → RigidMotion d)
    (hi : Function.Injective (fun i => cellIndex ((M i).apply (castPoint p)))) :
    LocallyFinite (fun i => Placed P.toFinset (M i)) := by
  intro x
  let B : ℝ := 2*((d : ℝ)+1)*(‖x‖+1+(tileDiameter P : ℝ))+1
  let K : ℤ := ⌈B⌉
  have hbox : (Set.Icc (fun _ : Fin d => -K) (fun _ => K)).Finite := by
    have hh := Set.Finite.pi (fun _ : Fin d => Set.finite_Icc (-K) K)
    convert hh using 1
    ext z
    simp only [Set.mem_Icc,Set.mem_pi,Set.mem_univ,forall_const,Pi.le_def,forall_and]
  have hf : ((fun i => cellIndex ((M i).apply (castPoint p))) ⁻¹'
      Set.Icc (fun _ : Fin d => -K) (fun _ => K)).Finite :=
    hbox.preimage hi.injOn
  refine ⟨Metric.ball x 1,Metric.ball_mem_nhds x (by norm_num),hf.subset ?_⟩
  intro j hj
  obtain ⟨y,hy,hyx⟩ := hj
  have hnorm : ‖y‖ ≤ ‖x‖+1 := by
    have ht := dist_triangle y x 0
    simp only [dist_zero_right] at ht
    have hyx' : dist y x < 1 := hyx
    linarith
  have hz (i : Fin d) : |cellIndex ((M j).apply (castPoint p)) i| ≤ K := by
    have hb := placed_index_bound P hp (M j) hy i
    have hd : 0 ≤ 2*((d : ℝ)+1) := by positivity
    have hm := mul_le_mul_of_nonneg_left
      (add_le_add_right hnorm (tileDiameter P : ℝ)) hd
    have ht : |(cellIndex ((M j).apply (castPoint p)) i : ℝ)| ≤ B := by
      dsimp [B]
      linarith
    have hk : |(cellIndex ((M j).apply (castPoint p)) i : ℝ)| ≤ (K : ℝ) :=
      ht.trans (Int.le_ceil B)
    exact_mod_cast hk
  exact ⟨fun i => (abs_le.mp (hz i)).1,fun i => (abs_le.mp (hz i)).2⟩

/-- A locally finite union of closed polycubes with almost-everywhere full
coverage actually covers every point, including all boundary points. -/
theorem aeCover_covers_everywhere (P : Tile d) {p : Lattice d} (hp : p ∈ P)
    (M : ι → RigidMotion d) (h : AECover (fun i => Placed P.toFinset (M i))) :
    ∀ x, ∃ i, x ∈ Placed P.toFinset (M i) := by
  have hf := locallyFinite_placed P hp M (cellIndex_injective_of_aeCover P hp M h)
  have hc := hf.isClosed_iUnion (fun i => isClosed_placed P.toFinset (M i))
  have ha : ∀ᵐ x ∂volume, x ∈ ⋃ i, Placed P.toFinset (M i) := h.mono fun x hx => by
    obtain ⟨i,hi,hu⟩ := hx
    exact Set.mem_iUnion.mpr ⟨i,hi⟩
  have hz : volume (⋃ i, Placed P.toFinset (M i))ᶜ=0 := ae_iff.mp ha
  have he := hc.isOpen_compl.eq_empty_of_measure_zero hz
  intro x
  by_contra hn
  have hx : x ∈ (⋃ i, Placed P.toFinset (M i))ᶜ := by simpa using hn
  simpa only [he,Set.mem_empty_iff_false] using hx

end
end TranslationTiling.EuclideanMembership
