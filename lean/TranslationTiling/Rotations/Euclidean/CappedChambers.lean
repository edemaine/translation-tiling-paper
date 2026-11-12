import TranslationTiling.Rotations.Euclidean.LocalChambers

namespace TranslationTiling.Rotations.Euclidean

noncomputable section
open Set SixKeys

def chamberAbove (i : Face) (h : ℝ) : Set EPoint :=
  interior (solid (localChamber i)) ∩ {x | h < x 0}

theorem isOpen_chamberAbove (i : Face) (h : ℝ) : IsOpen (chamberAbove i h) :=
  isOpen_interior.inter (isOpen_lt continuous_const (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) 0))

theorem local_middle_section (i : Face) {x : EPoint}
    (hx : x ∈ interior (solid (localChamber i)))
    (h0 : (3:ℝ)/2 < x 0 ∧ x 0 < 5/2) :
    |x 1| < (1:ℝ)/2 ∧ |x 2| < (1:ℝ)/2 := by
  let V : Set EPoint := interior (solid (localChamber i)) ∩ {y | (3:ℝ)/2 < y 0 ∧ y 0 < 5/2}
  have hV : IsOpen V := isOpen_interior.inter
    ((isOpen_lt continuous_const (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) 0)).inter
      (isOpen_lt (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) 0) continuous_const))
  have hsub : V ⊆ voxel (![2,0,0] : Lattice 3) := by
    rintro y ⟨hy,hy0⟩
    change (3:ℝ)/2 < y 0 ∧ y 0 < 5/2 at hy0
    have ht := local_neck_section i (interior_subset hy) (by linarith : y 0 < (9:ℝ)/2)
    intro j
    fin_cases j
    · change |y 0-2| ≤ (1:ℝ)/2
      apply abs_le.mpr
      constructor <;> linarith
    · simpa using ht.1
    · simpa using ht.2
  have hi := hV.subset_interior_iff.mpr hsub (show x ∈ V from ⟨hx,h0⟩)
  rw [interior_voxel] at hi
  exact ⟨by simpa using hi 1,by simpa using hi 2⟩

/-- Cutting through the middle of the neck creates no new exit except its
open square section. -/
theorem capped_frontier (i : Face) (h : ℝ) (hh : (3:ℝ)/2 < h ∧ h < 5/2)
    (V : Set EPoint)
    (cap : ∀ x ∈ interior (solid (localChamber i)), x 0 = h → x ∈ V) :
    frontier (chamberAbove i h) ⊆ solid (localBody i) ∪ V := by
  intro x hx
  have hclosed : closure {y : EPoint | h < y 0} ⊆ {y | h ≤ y 0} :=
    closure_minimal (fun y hy => (show h < y 0 from hy).le)
      (isClosed_le continuous_const (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) 0))
  have hge : h ≤ x 0 := hclosed
    (closure_mono (show chamberAbove i h ⊆ {y | h < y 0} from fun _ hy => hy.2) hx.1)
  have from_frontier (hxC : x ∈ frontier (solid (localChamber i))) :
      x ∈ solid (localBody i) := by
    rcases local_frontier i hxC with hxB | hxG
    · exact hxB
    · have hg := abs_le.mp (hxG 0)
      simp only [Pi.zero_apply, Int.cast_zero, sub_zero] at hg
      linarith
  rcases frontier_inter_subset _ _ hx with hc | hc
  · exact Or.inl (from_frontier (frontier_interior_subset hc.1))
  · have hxC : x ∈ solid (localChamber i) := by
      have hs := closure_mono (interior_subset : interior (solid (localChamber i)) ⊆ _) hc.1
      rwa [(isClosed_solid _).closure_eq] at hs
    have he : x 0 = h := by
      have ht := (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) 0).frontier_preimage_subset (Ioi h) hc.2
      simpa only [frontier_Ioi, mem_preimage, mem_singleton_iff] using ht
    by_cases hi : x ∈ interior (solid (localChamber i))
    · exact Or.inr (cap x hi he)
    · exact Or.inl (from_frontier ⟨subset_closure hxC,hi⟩)

theorem chamber_diameter (i : Face) {x y : EPoint}
    (hx : x ∈ solid (localChamber i)) (hy : y ∈ solid (localChamber i)) : dist x y < 39 := by
  have xb := local_chamber_bounds i hx
  have yb := local_chamber_bounds i hy
  have hd : (dimensions i).1 ≤ 5 ∧ (dimensions i).2.1 ≤ 15 ∧ (dimensions i).2.2 ≤ 15 := by
    fin_cases i <;> decide
  have d0 : ((dimensions i).1 : ℝ) ≤ 5 := by exact_mod_cast hd.1
  have d1 : ((dimensions i).2.1 : ℝ) ≤ 15 := by exact_mod_cast hd.2.1
  have d2 : ((dimensions i).2.2 : ℝ) ≤ 15 := by exact_mod_cast hd.2.2
  have bound (j : Fin 3) : (x j-y j)^2 ≤ 225 := by
    have hl : -15 ≤ x j-y j := by fin_cases j <;> dsimp <;> linarith
    have hu : x j-y j ≤ 15 := by fin_cases j <;> dsimp <;> linarith
    nlinarith [mul_nonneg (by linarith : 0 ≤ 15-(x j-y j)) (by linarith : 0 ≤ 15+(x j-y j))]
  have he := EuclideanSpace.real_norm_sq_eq (x-y)
  simp only [Fin.sum_univ_three, PiLp.sub_apply] at he
  rw [dist_eq_norm]
  nlinarith [bound 0,bound 1,bound 2,norm_nonneg (x-y)]

end
end TranslationTiling.Rotations.Euclidean
