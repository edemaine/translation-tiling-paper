import TranslationTiling.Rotations.General.Real.GridEmbedding
import TranslationTiling.Rotations.General.Real.VoxelPacking
import TranslationTiling.Rotations.General.ChamberGeometry

namespace TranslationTiling.Rotations.General.Real
noncomputable section
open Set
variable {d : ℕ} [NeZero d]

def localChamber (f : Face d) : Finset (Lattice d) := (fullKeyFinset f).erase 0

def localBody (f : Face d) : Finset (Lattice d) := body.image (frameMotion f).inverse.apply

theorem mem_localChamber (f : Face d) (p : Lattice d) : p ∈ localChamber f ↔ p ∈ Key f := by
  rw [localChamber,Finset.mem_erase]
  have hm : p ∈ fullKeyFinset f ↔ p ∈ Key f ∨ p=0 := by
    rw [← Finset.mem_coe,fullKeyFinset_set]
    rfl
  rw [hm]
  constructor
  · rintro ⟨hp,hk | hz⟩
    · exact hk
    · exact (hp hz).elim
  · intro hp
    exact ⟨by intro he; exact zero_not_key f (he ▸ hp),Or.inl hp⟩

theorem localChamber_set (f : Face d) : (localChamber f : Set (Lattice d)) = Key f := by
  ext p; exact mem_localChamber f p

theorem local_chamber_boundary (f : Face d) {p q : Lattice d}
    (hp : p ∈ localChamber f) (hpq : FaceAdjacent p q) :
    q ∈ localChamber f ∨ q=0 ∨ q ∈ localBody f := by
  have hp' : (frameMotion f).apply p ∈ chamber f :=
    ⟨p,(mem_localChamber f p).mp hp,rfl⟩
  rcases chamber_boundary f hp' ((frameMotion f).adjacent hpq) with hq | hq | hq
  · left
    obtain ⟨u,hu,he⟩ := hq
    have he' := (frameMotion f).injective he
    exact (mem_localChamber f q).mpr (he' ▸ hu)
  · right; left
    apply (frameMotion f).injective
    simpa only [frame_zero] using hq
  · right; right
    exact Finset.mem_image.mpr ⟨_,hq,Motion.inverse_apply_apply _ _⟩

theorem local_frontier (f : Face d) :
    frontier (solid (localChamber f)) ⊆ solid (localBody f) ∪ voxel 0 :=
  frontier_single_entrance _ _ _ (fun _ hp _ hpq => local_chamber_boundary f hp hpq)

theorem localChamber_card (hd : 2 ≤ d) (f : Face d) :
    (localChamber f).card = boxVolume d+neckLength d-1 := by
  have h := key_card hd f
  rw [← localChamber_set,Set.ncard_coe_finset] at h
  exact h

theorem local_chamber_bounds (f : Face d) {x : EPoint d} (hx : x ∈ solid (localChamber f)) :
    (1 : ℝ)/2 ≤ x 0 ∧ ∀ j : Fin d, -(1 : ℝ)/2 ≤ x j ∧ x j ≤ (margin d : ℝ)-(1 : ℝ)/2 := by
  obtain ⟨p,hp,hx⟩ := hx
  have hk := (mem_localChamber f p).mp hp
  have hp0 : 1 ≤ p 0 := by
    rcases hk with hb | hs
    · have h := (hb 0).1
      simp only [keyLo,ite_true] at h
      unfold neckLength at h
      omega
    · exact hs.1
  have hb0 : (1 : ℝ) ≤ (p 0 : ℝ) := by exact_mod_cast hp0
  have hx0 := abs_le.mp (hx 0)
  refine ⟨by linarith,fun j => ?_⟩
  have hpf : p ∈ fullKeyFinset f := by
    rw [← Finset.mem_coe,fullKeyFinset_set]
    exact Or.inl ((mem_localChamber f p).mp hp)
  have hb := fullKey_bounds f hpf j
  have hbl : (0 : ℝ) ≤ (p j : ℝ) := by exact_mod_cast hb.1
  have hbu : (p j : ℝ) ≤ (margin d : ℝ)-1 := by exact_mod_cast (show p j ≤ (margin d : ℤ)-1 by omega)
  have hxj := abs_le.mp (hx j)
  constructor <;> linarith

theorem local_neck_section (f : Face d) {x : EPoint d} (hx : x ∈ solid (localChamber f))
    (h0 : x 0 < (neckLength d : ℝ)-(1 : ℝ)/2) :
    ∀ j : Fin d, j ≠ 0 → |x j| ≤ (1 : ℝ)/2 := by
  obtain ⟨p,hp,hx⟩ := hx
  rcases (mem_localChamber f p).mp hp with hb | hs
  · have hp0 := (hb 0).1
    simp only [keyLo,ite_true] at hp0
    have hp0' : (neckLength d : ℝ) ≤ (p 0 : ℝ) := by exact_mod_cast hp0
    have hx0 := abs_le.mp (hx 0)
    linarith
  · intro j hj
    simpa only [hs.2.2 j hj,Int.cast_zero,sub_zero] using hx j

end
end TranslationTiling.Rotations.General.Real
