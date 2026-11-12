import TranslationTiling.Rotations.General.Real.LocalChambers
import TranslationTiling.Rotations.General.Real.NeckPosition

namespace TranslationTiling.Rotations.General.Real
noncomputable section
open Set
variable {d : ℕ} [NeZero d]

def chamberAbove (f : Face d) (h : ℝ) : Set (EPoint d) :=
  interior (solid (localChamber f)) ∩ {x | h < x 0}

theorem isOpen_chamberAbove (f : Face d) (h : ℝ) : IsOpen (chamberAbove f h) :=
  isOpen_interior.inter (isOpen_lt continuous_const (PiLp.continuous_apply 2 (fun _ : Fin d => ℝ) 0))

theorem local_middle_section (f : Face d) {x : EPoint d}
    (hx : x ∈ interior (solid (localChamber f)))
    (h0 : (neckCenter d : ℝ)-(1 : ℝ)/2 < x 0 ∧ x 0 < (neckCenter d : ℝ)+(1 : ℝ)/2) :
    ∀ j : Fin d, j ≠ 0 → |x j| < (1 : ℝ)/2 := by
  let V : Set (EPoint d) := interior (solid (localChamber f)) ∩
    {y | (neckCenter d : ℝ)-(1 : ℝ)/2 < y 0 ∧ y 0 < (neckCenter d : ℝ)+(1 : ℝ)/2}
  have hV : IsOpen V := isOpen_interior.inter
    ((isOpen_lt continuous_const (PiLp.continuous_apply 2 (fun _ : Fin d => ℝ) 0)).inter
      (isOpen_lt (PiLp.continuous_apply 2 (fun _ : Fin d => ℝ) 0) continuous_const))
  have hsub : V ⊆ voxel (Pi.single 0 (neckCenter d : ℤ)) := by
    rintro y ⟨hy,hy0⟩
    have hneck : y 0 < (neckLength d : ℝ)-(1 : ℝ)/2 := by
      have hh := hy0.2
      simp only [neckLength,neckCenter,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] at hh ⊢
      linarith [Nat.cast_nonneg (α := ℝ) d]
    have ht := local_neck_section f (interior_subset hy) hneck
    intro j
    by_cases hj : j=0
    · subst j
      simp only [Pi.single_eq_same,Int.cast_natCast]
      rw [abs_le]
      constructor <;> linarith [hy0.1,hy0.2]
    · simpa [Pi.single_eq_of_ne hj] using ht j hj
  have hi := hV.subset_interior_iff.mpr hsub (show x ∈ V from ⟨hx,h0⟩)
  rw [interior_voxel] at hi
  intro j hj
  simpa [Pi.single_eq_of_ne hj] using hi j

/-- Cutting an interior cross-section introduces just its open cap as a new exit. -/
theorem capped_frontier (f : Face d) (h : ℝ) (hh : (1 : ℝ)/2 < h)
    (V : Set (EPoint d))
    (cap : ∀ x ∈ interior (solid (localChamber f)), x 0=h → x ∈ V) :
    frontier (chamberAbove f h) ⊆ solid (localBody f) ∪ V := by
  intro x hx
  have hclosed : closure {y : EPoint d | h < y 0} ⊆ {y | h ≤ y 0} :=
    closure_minimal (fun _ hy => (show h < _ from hy).le)
      (isClosed_le continuous_const (PiLp.continuous_apply 2 (fun _ : Fin d => ℝ) 0))
  have hge : h ≤ x 0 := hclosed
    (closure_mono (show chamberAbove f h ⊆ {y | h < y 0} from fun _ hy => hy.2) hx.1)
  have from_frontier (hxC : x ∈ frontier (solid (localChamber f))) : x ∈ solid (localBody f) := by
    rcases local_frontier f hxC with hxB | hxG
    · exact hxB
    · have hg := abs_le.mp (hxG 0)
      simp only [Pi.zero_apply,Int.cast_zero,sub_zero] at hg
      linarith
  rcases frontier_inter_subset _ _ hx with hc | hc
  · exact Or.inl (from_frontier (frontier_interior_subset hc.1))
  · have hxC : x ∈ solid (localChamber f) := by
      have hs := closure_mono (interior_subset : interior (solid (localChamber f)) ⊆ _) hc.1
      rwa [(isClosed_solid _).closure_eq] at hs
    have he : x 0=h := by
      have ht := (PiLp.continuous_apply 2 (fun _ : Fin d => ℝ) 0).frontier_preimage_subset (Ioi h) hc.2
      simpa only [frontier_Ioi,mem_preimage,mem_singleton_iff] using ht
    by_cases hi : x ∈ interior (solid (localChamber f))
    · exact Or.inr (cap x hi he)
    · exact Or.inl (from_frontier ⟨subset_closure hxC,hi⟩)

end
end TranslationTiling.Rotations.General.Real
