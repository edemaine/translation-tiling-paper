import TranslationTiling.Rotations.General.Real.LocalIntegrality
import TranslationTiling.Rotations.General.Real.GridSampling

namespace TranslationTiling.Rotations.General.Real
noncomputable section
open Set
variable {d : ℕ} [NeZero d]

theorem local_chamber_axial {f : Face d} {p : Lattice d} (hp : p ∈ localChamber f)
    (hl : p 0 < neckLength d) : p=Pi.single 0 (p 0) := by
  rcases (mem_localChamber f p).mp hp with hb | hs
  · have hn := (hb 0).1
    simp only [keyLo,ite_true] at hn
    omega
  · ext j
    by_cases hj : j=0
    · subst j; simp
    · simp [hs.2.2 j hj,Pi.single_eq_of_ne hj]

theorem local_chamber_positive {f : Face d} {p : Lattice d} (hp : p ∈ localChamber f) : 1 ≤ p 0 := by
  rcases (mem_localChamber f p).mp hp with hb | hs
  · have hn := (hb 0).1
    simp only [keyLo,ite_true] at hn
    unfold neckLength at hn
    omega
  · exact hs.1

/-- An integral blocking copy fills the entire chamber, including the arbitrarily
long neck prefix. For each prefix voxel its suffix has that voxel as sole exit. -/
theorem integral_fills_chamber (hd : 3 ≤ d) {ι : Type*} (M : ι → RigidMotion d)
    (cover : AECover (fun j => Placed gadget (M j))) (host : ι) (f : Face d)
    (hhost : Placed gadget (M host)=solid (localGadget f)) :
    ∃ (j : ι) (a : Motion d), j ≠ host ∧ M j=embedMotion a ∧
      (localChamber f : Set (Lattice d)) ⊆ a.apply '' (gadget : Finset (Lattice d)) ∧
      Disjoint (a.apply '' (gadget : Finset (Lattice d))) (localBody f : Set (Lattice d)) := by
  obtain ⟨j,a,h,jne,ha,hh,filled,neck⟩ := integral_chamber_blocker hd M cover host f hhost
  let S := a.apply '' (gadget : Finset (Lattice d))
  have packing : Disjoint (Placed gadget (embedMotion a)) (interior (solid (localBody f))) := by
    rw [← ha]
    have ht := (cover.interior_solid_disjoint (Ne.symm jne)).symm
    rw [hhost] at ht
    apply ht.mono_right
    apply interior_mono
    rintro y ⟨q,hq,hy⟩
    exact ⟨q,localBody_subset_localGadget f hq,hy⟩
  have avoids : Disjoint S (localBody f : Set (Lattice d)) := grid_footprint_avoids_body a _ _ packing
  have escape : ∃ y ∈ S, y ∉ (localChamber f : Set (Lattice d)) := by
    apply escape_of_card (localChamber f).finite_toSet
    rw [Set.ncard_coe_finset,localChamber_card (by omega : 2 ≤ d),
      Set.ncard_image_of_injective _ a.injective,Set.ncard_coe_finset]
    have hb := body_large hd
    have hg := Finset.card_le_card (body_subset_gadget (d := d))
    omega
  have neckPrefix (n : ℤ) (hn : 1 ≤ n) (hnc : n < (neckCenter d : ℤ)) :
      (Pi.single 0 n : Lattice d) ∈ S := by
    let K : Set (Lattice d) := {q | q ∈ localChamber f ∧ n < q 0}
    have midK : (Pi.single 0 (neckCenter d : ℤ) : Lattice d) ∈ K := by
      refine ⟨?_,by simpa⟩
      rw [mem_localChamber]
      right
      refine ⟨?_,?_,?_⟩
      · simp [neckCenter]; omega
      · simp only [Pi.single_eq_same]; unfold neckCenter neckLength; omega
      · intro k hk; simp [Pi.single_eq_of_ne hk]
    apply uses_gate midK neck (a.connected (gadget_connected hd))
      (by obtain ⟨y,hy,he⟩ := escape; exact ⟨y,hy,fun hk => he hk.1⟩)
    intro q hq r hr hqr
    rcases local_chamber_boundary f hq.1 hqr with hrl | hr0 | hrB
    · by_cases hnr : n < r 0
      · exact Or.inl ⟨hrl,hnr⟩
      · right
        have hdelta := abs_le.mp (adjacent_coordinate hqr 0)
        have hrn : r 0=n := by have := hq.2; omega
        have hrneck : r 0 < neckLength d := by rw [hrn]; unfold neckCenter neckLength at *; omega
        rw [local_chamber_axial hrl hrneck,hrn]
    · have hdelta := abs_le.mp (adjacent_coordinate hqr 0)
      rw [hr0] at hdelta
      simp only [Pi.zero_apply] at hdelta
      have := hq.2
      omega
    · exact (Set.disjoint_left.mp avoids hr hrB).elim
  refine ⟨j,a,jne,ha,fun p hp => ?_,avoids⟩
  by_cases hlo : p 0 ≤ (neckCenter d : ℤ)
  · have hp0 := local_chamber_positive hp
    have hpn : p 0 < neckLength d := by unfold neckCenter neckLength at *; omega
    have he := local_chamber_axial hp hpn
    by_cases heq : p 0=(neckCenter d : ℤ)
    · rw [he,heq]
      exact neck
    · rw [he]
      exact neckPrefix (p 0) hp0 (by omega)
  · apply (castPoint_mem_placed a gadget p).mp
    rw [← ha]
    apply filled
    exact chamber_center_above f h (by linarith [hh.2]) p hp (by omega)

end
end TranslationTiling.Rotations.General.Real
