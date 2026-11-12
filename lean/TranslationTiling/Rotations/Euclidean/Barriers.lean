import TranslationTiling.Rotations.Euclidean.Covers
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Topology.Connected.Clopen

namespace TranslationTiling.Rotations.Euclidean

noncomputable section
open Set

theorem convex_openBox (lo hi : Fin 3 → ℝ) : Convex ℝ (openBox lo hi) := by
  intro x hx y hy a b ha hb hab i
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  have he₁ := congrArg (fun t : ℝ => t * lo i) hab
  have he₂ := congrArg (fun t : ℝ => t * hi i) hab
  have hpos : 0 < a ∨ 0 < b := by rcases eq_or_lt_of_le ha with he | he; right; linarith; exact Or.inl he
  constructor
  · have h₁ := mul_nonneg ha (sub_nonneg.mpr (hx i).1.le)
    have h₂ := mul_nonneg hb (sub_nonneg.mpr (hy i).1.le)
    rcases hpos with h | h
    · have := mul_pos h (sub_pos.mpr (hx i).1); nlinarith
    · have := mul_pos h (sub_pos.mpr (hy i).1); nlinarith
  · have h₁ := mul_nonneg ha (sub_nonneg.mpr (hx i).2.le)
    have h₂ := mul_nonneg hb (sub_nonneg.mpr (hy i).2.le)
    rcases hpos with h | h
    · have := mul_pos h (sub_pos.mpr (hx i).2); nlinarith
    · have := mul_pos h (sub_pos.mpr (hy i).2); nlinarith

theorem adjacent_block (p : Lattice 3) (k : Fin 3) :
    block p (p+Pi.single k 1) ⊆ {p, p+Pi.single k 1} := by
  intro z hz
  have hb := (mem_block _ _ _).mp hz
  by_cases hk : z k = p k
  · apply Finset.mem_insert.mpr; left
    funext j
    have hh := hb j
    by_cases hj : j = k
    · subst j; exact hk
    · simp [Pi.single_eq_of_ne hj] at hh
      omega
  · apply Finset.mem_insert.mpr; right
    apply Finset.mem_singleton.mpr
    funext j
    have hh := hb j
    by_cases hj : j = k
    · subst j; simp at hh; simp; omega
    · simp [Pi.single_eq_of_ne hj] at hh ⊢
      omega

theorem adjacent_joined {F : Finset (Lattice 3)} {p q : Lattice 3}
    (hp : p ∈ F) (hq : q ∈ F) (hadj : FaceAdjacent p q) :
    JoinedIn (interior (solid F)) (castPoint p) (castPoint q) := by
  have forward (p : Lattice 3) (k : Fin 3) (hp : p ∈ F) (hq : p+Pi.single k 1 ∈ F) :
      JoinedIn (interior (solid F)) (castPoint p) (castPoint (p+Pi.single k 1)) := by
    let q := p+Pi.single k 1
    let U := openBox (fun j => (p j : ℝ)-(1:ℝ)/2) (fun j => (q j : ℝ)+(1:ℝ)/2)
    have hle (j : Fin 3) : p j ≤ q j := by simp [q, Pi.single_apply]; split_ifs <;> omega
    have hpU : castPoint p ∈ U := by
      intro j
      have hh : (p j : ℝ) ≤ (q j : ℝ) := by exact_mod_cast hle j
      simp only [castPoint_apply]; constructor <;> linarith
    have hqU : castPoint q ∈ U := by
      intro j
      have hh : (p j : ℝ) ≤ (q j : ℝ) := by exact_mod_cast hle j
      simp only [castPoint_apply]; constructor <;> linarith
    have hUF : U ⊆ interior (solid F) := by
      apply (openBox_subset_interior_block p q hle).trans
      apply interior_mono
      rintro x ⟨z, hz, hx⟩
      have hz' := adjacent_block p k hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz'
      rcases hz' with hz' | hz'
      · exact ⟨z,hz'.symm ▸ hp,hx⟩
      · exact ⟨z,hz'.symm ▸ hq,hx⟩
    exact ((convex_openBox _ _).isPathConnected ⟨_,hpU⟩).joinedIn _ hpU _ hqU |>.mono hUF
  obtain ⟨k, he | he⟩ := hadj
  · subst q; exact forward p k hp hq
  · subst p; exact (forward q k hq hp).symm

theorem facePath_joined {F : Finset (Lattice 3)} {p q : Lattice 3}
    (hp : p ∈ F) (hpath : FacePath (· ∈ F) p q) :
    JoinedIn (interior (solid F)) (castPoint p) (castPoint q) := by
  induction hpath with
  | refl => exact JoinedIn.refl (openVoxel_subset_interior hp (castPoint_openVoxel p))
  | tail _ hab ih => exact ih.trans (adjacent_joined hab.1 hab.2.1 hab.2.2)

theorem openVoxel_joined_center {F : Finset (Lattice 3)} {p : Lattice 3}
    (hp : p ∈ F) {x : EPoint} (hx : x ∈ openVoxel p) :
    JoinedIn (interior (solid F)) x (castPoint p) := by
  have hp' : castPoint p ∈ interior (voxel p) :=
    (isOpen_openVoxel p).subset_interior_iff.mpr (openVoxel_subset_voxel p) (castPoint_openVoxel p)
  have hx' : x ∈ interior (voxel p) :=
    (isOpen_openVoxel p).subset_interior_iff.mpr (openVoxel_subset_voxel p) hx
  exact ((convex_voxel p).interior.isPathConnected ⟨_,hx'⟩).joinedIn _ hx' _ hp' |>.mono
    (interior_mono (show voxel p ⊆ solid F from fun y hy => ⟨p,hp,hy⟩))

/-- A connected path avoiding the boundary of an open chamber cannot leave it. -/
theorem joined_barrier {S U : Set EPoint} {x y : EPoint}
    (hu : IsOpen U) (hd : Disjoint (frontier U) S)
    (hxy : JoinedIn S x y) (hx : x ∈ U) : y ∈ U := by
  obtain ⟨p,hp⟩ := hxy
  have hs : IsPreconnected (range p) := isPreconnected_range p.continuous
  have hd' : Disjoint (frontier U) (range p) := hd.mono_right (by rintro _ ⟨t,rfl⟩; exact hp t)
  haveI : PreconnectedSpace (range p) := isPreconnected_iff_preconnectedSpace.mp hs
  have he := (isClopen_preimage_val hu hd').eq_univ
    (show (Subtype.val ⁻¹' U : Set (range p)).Nonempty from
      ⟨⟨x,⟨0,p.source⟩⟩,hx⟩)
  have hy : (⟨y,⟨1,p.target⟩⟩ : range p) ∈ (Subtype.val ⁻¹' U : Set (range p)) := by rw [he]; trivial
  exact hy

end
end TranslationTiling.Rotations.Euclidean
