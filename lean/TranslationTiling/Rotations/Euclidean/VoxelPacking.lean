import TranslationTiling.Rotations.Euclidean.Covers

namespace TranslationTiling.Rotations.Euclidean

noncomputable section
open Set

theorem interior_voxel (p : Lattice 3) : interior (voxel p) = openVoxel p := by
  let e := (PiLp.homeomorph 2 (fun _ : Fin 3 => ℝ)).symm
  have he : voxel p = e '' Set.pi Set.univ (fun i =>
      Set.Icc ((p i : ℝ)-(1:ℝ)/2) ((p i : ℝ)+(1:ℝ)/2)) := by
    ext x
    rw [e.image_eq_preimage_symm]
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ,
      forall_const, Set.mem_Icc]
    change (∀ i, |x i-(p i:ℝ)| ≤ (1:ℝ)/2) ↔
      (∀ i, (p i:ℝ)-(1:ℝ)/2 ≤ x i ∧ x i ≤ (p i:ℝ)+(1:ℝ)/2)
    constructor <;> intro hx i
    · have hh := abs_le.mp (hx i); constructor <;> linarith
    · apply abs_le.mpr; have hh := hx i; constructor <;> linarith
  rw [he, ← e.image_interior, interior_pi_set (Set.finite_univ)]
  ext x
  rw [e.image_eq_preimage_symm]
  simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ,
    forall_const, interior_Icc, Set.mem_Ioo]
  change (∀ i, (p i:ℝ)-(1:ℝ)/2 < x i ∧ x i < (p i:ℝ)+(1:ℝ)/2) ↔
    (∀ i, |x i-(p i:ℝ)| < (1:ℝ)/2)
  constructor <;> intro hx i
  · apply abs_lt.mpr; have hh := hx i; constructor <;> linarith
  · have hh := abs_lt.mp (hx i); constructor <;> linarith

theorem closure_openVoxel (p : Lattice 3) : closure (openVoxel p) = voxel p := by
  rw [← interior_voxel, closure_interior_voxel]

theorem openVoxel_voxel_disjoint {p q : Lattice 3} (hne : p ≠ q) :
    Disjoint (openVoxel p) (voxel q) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  apply hne
  funext i
  have hh := abs_lt.mp (hx i)
  have hh' := abs_le.mp (hy i)
  have hl : (-1:ℝ) < (p i:ℝ)-(q i:ℝ) := by linarith
  have hu : (p i:ℝ)-(q i:ℝ) < 1 := by linarith
  have hl' : (-1:ℤ) < p i-q i := by exact_mod_cast hl
  have hu' : p i-q i < (1:ℤ) := by exact_mod_cast hu
  omega

theorem solid_disjoint_interior {F G : Finset (Lattice 3)} (hd : Disjoint F G) :
    Disjoint (solid F) (interior (solid G)) := by
  apply Set.disjoint_left.mpr
  rintro x ⟨p,hp,hx⟩ hxG
  have hd' : Disjoint (interior (solid G)) (openVoxel p) := by
    apply Set.disjoint_left.mpr
    intro y hyG hyp
    obtain ⟨q,hq,hyq⟩ := interior_subset hyG
    have hne : p ≠ q := by intro he; exact Finset.disjoint_left.mp hd hp (he.symm ▸ hq)
    exact Set.disjoint_left.mp (openVoxel_voxel_disjoint hne) hyp hyq
  have hd'' := hd'.closure_right isOpen_interior
  rw [closure_openVoxel] at hd''
  exact Set.disjoint_left.mp hd'' hxG hx

end
end TranslationTiling.Rotations.Euclidean
