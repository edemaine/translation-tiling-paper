import TranslationTiling.Rotations.Euclidean.CapForcing
import TranslationTiling.Rotations.Euclidean.ChamberContents

namespace TranslationTiling.Rotations.Euclidean

noncomputable section
open Set SixKeys MeasureTheory

/-- Before any grid assumption, a tile covering the middle of a key neck is
forced to have both a signed grid orientation and an integral translation. -/
theorem integral_chamber_blocker {ι : Type*} (M : ι → RigidMotion)
    (cover : AECover (fun j => Placed gadget (M j))) (host : ι) (i : Face)
    (hhost : Placed gadget (M host)=solid (localGadget i)) :
    ∃ (j : ι) (a : Motion) (h : ℝ), j ≠ host ∧ M j=embedMotion a ∧
      ((7:ℝ)/4<h ∧ h<9/4) ∧ chamberAbove i h ⊆ Placed gadget (M j) ∧
      (![2,0,0] : Lattice 3) ∈ a.apply '' (gadget : Set (Lattice 3)) := by
  let W := openBox (![((7:ℝ)/4),-1/2,-1/2]) (![((9:ℝ)/4),1/2,1/2])
  have hW : W.Nonempty := by
    refine ⟨WithLp.toLp 2 (![2,0,0]),?_⟩
    intro k; fin_cases k <;> norm_num [W]
  have hF : gadget.Nonempty := ⟨0,body_subset_gadget zero_body⟩
  obtain ⟨x,hxW,j,p,hp,u,hu,he⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    ((isOpen_openBox _ _).measure_ne_zero volume hW)
    (ae_restrict_of_ae (cover.ae_open_voxel hF M))
  have h0 : (7:ℝ)/4<(M j).apply u 0 ∧ (M j).apply u 0<9/4 := by
    have hh := hxW 0
    simpa [W,← he] using hh
  have h1 : |(M j).apply u 1|<(1:ℝ)/2 := by
    apply abs_lt.mpr
    have hh := hxW 1
    simp [W,← he] at hh
    constructor <;> linarith
  have h2 : |(M j).apply u 2|<(1:ℝ)/2 := by
    apply abs_lt.mpr
    have hh := hxW 2
    simp [W,← he] at hh
    constructor <;> linarith
  have hxC : x ∈ interior (solid (localChamber i)) := by
    have hmid : (![2,0,0] : Lattice 3) ∈ localChamber i := by
      rw [mem_localChamber]; left; norm_num [NeckBox]
    apply openVoxel_subset_interior hmid
    intro k
    fin_cases k
    · have hh := h0; rw [he] at hh
      change |x 0-2|<(1:ℝ)/2
      apply abs_lt.mpr; constructor <;> linarith
    · simpa [he] using h1
    · simpa [he] using h2
  have jne : j ≠ host := by
    intro hj
    have hxhost : x ∈ solid (localGadget i) := by
      rw [← hhost,← hj,← he]
      exact ⟨u,⟨p,hp,openVoxel_subset_voxel p hu⟩,rfl⟩
    exact Set.disjoint_left.mp (solid_disjoint_interior (localGadget_chamber_disjoint i)) hxhost hxC
  have packing : Disjoint (Placed gadget (M j)) (interior (solid (localBody i))) := by
    have hd := (cover.interior_solid_disjoint (Ne.symm jne)).symm
    rw [hhost] at hd
    apply hd.mono_right
    apply interior_mono
    rintro y ⟨q,hq,hy⟩
    exact ⟨q,localBody_subset_localGadget i hq,hy⟩
  obtain ⟨r,hr,hc1,hc2,ht1,ht2⟩ := neck_copy_alignment hp (M j) i hu h0 h1 h2 packing
  let h := (M j).apply u 0
  have filled : chamberAbove i h ⊆ Placed gadget (M j) := by
    apply chamber_monopoly hF gadget_connected M cover host j _ (isOpen_chamberAbove i h)
    · rw [hhost]
      exact chamberAbove_avoids_host i h
    · apply (capped_frontier i h ⟨by dsimp [h]; linarith,by dsimp [h]; linarith⟩ _
        (blocker_cap hp (M j) r hr hu i h0 hc1 hc2)).trans
      apply union_subset_union_left
      rintro y ⟨q,hq,hy⟩
      rw [hhost]
      exact ⟨q,localBody_subset_localGadget i hq,hy⟩
    · exact fun k => copy_escapes_chamber i h (M k)
  have far : farChamberPoint i ∈ Placed gadget (M j) :=
    (isClosed_placed gadget (M j)).closure_subset_iff.mpr filled
      (farPoint_closure_above i h (by dsimp [h]; linarith))
  obtain ⟨a,ha⟩ := phase_of_end_contact (M j) r hr i ht1 ht2 far packing
  have hp2 : a.apply p=(![2,0,0] : Lattice 3) := by
    have hc1' : (a.apply p) 1=0 := by
      rw [ha,embedMotion_castPoint] at hc1
      simp only [castPoint_apply] at hc1
      exact_mod_cast hc1
    have hc2' : (a.apply p) 2=0 := by
      rw [ha,embedMotion_castPoint] at hc2
      simp only [castPoint_apply] at hc2
      exact_mod_cast hc2
    have hd := hu (r.axes 0)
    rw [← grid_voxel_difference (M j) r hr p u 0,ha,embedMotion_castPoint] at hd
    have hd' := abs_lt.mp hd
    rw [← ha] at hd'
    simp only [castPoint_apply] at hd'
    have hl : (1:ℝ)<((a.apply p) 0:ℝ) := by linarith
    have hu' : ((a.apply p) 0:ℝ)<3 := by linarith
    have hlZ : (1:ℤ)<(a.apply p) 0 := by exact_mod_cast hl
    have huZ : (a.apply p) 0<(3:ℤ) := by exact_mod_cast hu'
    ext k
    fin_cases k <;> simp_all <;> omega
  exact ⟨j,a,h,jne,ha,h0,filled,p,hp,hp2⟩

end
end TranslationTiling.Rotations.Euclidean
