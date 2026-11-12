import TranslationTiling.Rotations.General.Real.CapForcing
import TranslationTiling.Rotations.General.Real.ChamberContents
import TranslationTiling.Rotations.General.Real.Monopoly

namespace TranslationTiling.Rotations.General.Real
noncomputable section
open Set MeasureTheory
variable {d : ℕ} [NeZero d]

/-- A tile covering the neck's middle acquires a grid orientation and a fully
integral translation, before any grid assumption on the covering family. -/
theorem integral_chamber_blocker (hd : 3 ≤ d) {ι : Type*} (M : ι → RigidMotion d)
    (cover : AECover (fun j => Placed gadget (M j))) (host : ι) (f : Face d)
    (hhost : Placed gadget (M host)=solid (localGadget f)) :
    ∃ (j : ι) (a : Motion d) (h : ℝ), j ≠ host ∧ M j=embedMotion a ∧
      ((neckCenter d : ℝ)-1/4 < h ∧ h < (neckCenter d : ℝ)+1/4) ∧
      chamberAbove f h ⊆ Placed gadget (M j) ∧
      (Pi.single 0 (neckCenter d : ℤ) : Lattice d) ∈ a.apply '' (gadget : Finset (Lattice d)) := by
  let lower : Fin d → ℝ := fun k => if k=0 then (neckCenter d : ℝ)-1/4 else -1/2
  let upper : Fin d → ℝ := fun k => if k=0 then (neckCenter d : ℝ)+1/4 else 1/2
  let W := openBox lower upper
  have hW : W.Nonempty := by
    refine ⟨EuclideanSpace.single 0 (neckCenter d : ℝ),?_⟩
    intro k
    by_cases hk : k=0 <;> simp [W,lower,upper,PiLp.single_apply,hk] <;> norm_num
  have hF : gadget.Nonempty := ⟨0,body_subset_gadget (zero_body (by omega : 2 ≤ d))⟩
  obtain ⟨x,hxW,j,p,hp,u,hu,he⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    ((isOpen_openBox _ _).measure_ne_zero volume hW)
    (ae_restrict_of_ae (cover.ae_open_voxel hF M))
  have h0 : (neckCenter d : ℝ)-1/4 < (M j).apply u 0 ∧ (M j).apply u 0 < (neckCenter d : ℝ)+1/4 := by
    have hh := hxW 0
    simpa [W,lower,upper,← he] using hh
  have ht (k : Fin d) (hk : k ≠ 0) : |(M j).apply u k| < (1 : ℝ)/2 := by
    have hh := hxW k
    simp only [lower,upper,ite_eq_right hk] at hh
    rw [abs_lt]
    rw [← he] at hh
    constructor <;> linarith
  have hmid : (Pi.single 0 (neckCenter d : ℤ) : Lattice d) ∈ localChamber f := by
    rw [mem_localChamber]
    right
    refine ⟨?_,?_,?_⟩
    · simp only [Pi.single_eq_same]
      unfold neckCenter
      omega
    · simp only [Pi.single_eq_same]
      unfold neckCenter neckLength
      omega
    · intro k hk; simp [Pi.single_eq_of_ne hk]
  have hxC : x ∈ interior (solid (localChamber f)) := by
    apply openVoxel_subset_interior hmid
    intro k
    by_cases hk : k=0
    · subst k
      rw [← he]
      simp only [Pi.single_eq_same,Int.cast_natCast]
      rw [abs_lt]
      constructor <;> linarith [h0.1,h0.2]
    · simpa [he,Pi.single_eq_of_ne hk] using ht k hk
  have jne : j ≠ host := by
    intro hj
    have hxhost : x ∈ solid (localGadget f) := by
      rw [← hhost,← hj,← he]
      exact ⟨u,⟨p,hp,openVoxel_subset_voxel p hu⟩,rfl⟩
    exact Set.disjoint_left.mp (solid_disjoint_interior (localGadget_chamber_disjoint f)) hxhost hxC
  have packing : Disjoint (Placed gadget (M j)) (interior (solid (localBody f))) := by
    have hh := (cover.interior_solid_disjoint (Ne.symm jne)).symm
    rw [hhost] at hh
    apply hh.mono_right
    apply interior_mono
    rintro y ⟨q,hq,hy⟩
    exact ⟨q,localBody_subset_localGadget f hq,hy⟩
  obtain ⟨r,hr,hcent,hphase⟩ := neck_copy_alignment hp (M j) f hu h0 ht packing
  let h := (M j).apply u 0
  have filled : chamberAbove f h ⊆ Placed gadget (M j) := by
    apply chamber_monopoly hF (gadget_connected hd) M cover host j _ (isOpen_chamberAbove f h)
    · rw [hhost]
      exact chamberAbove_avoids_host f h
    · apply (capped_frontier f h (by
        have hh := h0.1
        dsimp [h]
        simp only [neckCenter,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] at hh
        linarith [Nat.cast_nonneg (α := ℝ) d]) _ (blocker_cap hp (M j) r hr hu f h0 hcent)).trans
      apply union_subset_union_left
      rintro y ⟨q,hq,hy⟩
      rw [hhost]
      exact ⟨q,localBody_subset_localGadget f hq,hy⟩
    · exact fun k => copy_escapes_chamber hd f h (M k)
  have far : farChamberPoint f ∈ Placed gadget (M j) :=
    (isClosed_placed gadget (M j)).closure_subset_iff.mpr filled
      (farPoint_closure_above f h (by dsimp [h]; linarith [h0.2]))
  obtain ⟨a,ha⟩ := phase_of_end_contact (M j) r hr f hphase far packing
  have hpCenter : a.apply p=(Pi.single 0 (neckCenter d : ℤ) : Lattice d) := by
    have hc (k : Fin d) (hk : k ≠ 0) : (a.apply p) k=0 := by
      have hh := hcent k hk
      rw [ha,embedMotion_castPoint] at hh
      simp only [castPoint_apply] at hh
      exact_mod_cast hh
    have hd0 := hu (r.axes 0)
    rw [← grid_voxel_difference (M j) r hr p u 0,ha,embedMotion_castPoint] at hd0
    have hb := abs_lt.mp hd0
    rw [← ha] at hb
    simp only [castPoint_apply] at hb
    have hl : (neckCenter d : ℝ)-1 < ((a.apply p) 0 : ℝ) := by linarith [h0.1,h0.2]
    have hu' : ((a.apply p) 0 : ℝ) < (neckCenter d : ℝ)+1 := by linarith [h0.1,h0.2]
    have hl' : (neckCenter d : ℤ)-1 < (a.apply p) 0 := by exact_mod_cast hl
    have hu'' : (a.apply p) 0 < (neckCenter d : ℤ)+1 := by exact_mod_cast hu'
    ext k
    by_cases hk : k=0
    · subst k; simp only [Pi.single_eq_same]; omega
    · simp [hc k hk,Pi.single_eq_of_ne hk]
  exact ⟨j,a,h,jne,ha,h0,filled,p,hp,hpCenter⟩

end
end TranslationTiling.Rotations.General.Real
