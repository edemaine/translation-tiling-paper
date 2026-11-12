import TranslationTiling.Rotations.Euclidean.NeckWalls
import TranslationTiling.Rotations.Euclidean.VoxelPacking
import TranslationTiling.Rotations.KeyConnectivity

namespace TranslationTiling.Rotations.Euclidean

noncomputable section
open Set SixKeys

def localChamber (i : Face) := (chamber i).image (frameMotion i).inverse.apply
def localBody (i : Face) := body.image (frameMotion i).inverse.apply

theorem mem_localChamber (i : Face) (p : Lattice 3) :
    p ∈ localChamber i ↔ p ∈ NeckBox 1 (dimensions i).1 (dimensions i).2.1 (dimensions i).2.2 := by
  constructor
  · rintro hp
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hp
    have hy' : y ∈ (frameMotion i).apply ''
        NeckBox 1 (dimensions i).1 (dimensions i).2.1 (dimensions i).2.2 := by
      rw [frame_chamber]; exact hy
    obtain ⟨z,hz,rfl⟩ := hy'
    simpa using hz
  · intro hp
    apply Finset.mem_image.mpr
    refine ⟨(frameMotion i).apply p, ?_, Motion.inverse_apply_apply _ _⟩
    have hh : (frameMotion i).apply p ∈ (frameMotion i).apply ''
        NeckBox 1 (dimensions i).1 (dimensions i).2.1 (dimensions i).2.2 := ⟨p,hp,rfl⟩
    rwa [frame_chamber] at hh

theorem local_chamber_boundary (i : Face) {p q : Lattice 3}
    (hp : p ∈ localChamber i) (hpq : FaceAdjacent p q) :
    q ∈ localChamber i ∨ q = 0 ∨ q ∈ localBody i := by
  have hp' : (frameMotion i).apply p ∈ chamber i := by
    obtain ⟨p',hp',he⟩ := Finset.mem_image.mp hp
    rw [← he, Motion.apply_inverse_apply]
    exact hp'
  rcases chamber_boundary i hp' ((frameMotion i).adjacent hpq) with hq | hq | hq
  · left
    exact Finset.mem_image.mpr ⟨_,hq,Motion.inverse_apply_apply _ _⟩
  · right; left
    apply (frameMotion i).injective
    simpa only [frame_zero] using hq
  · right; right
    exact Finset.mem_image.mpr ⟨_,hq,Motion.inverse_apply_apply _ _⟩

theorem local_frontier (i : Face) :
    frontier (solid (localChamber i)) ⊆ solid (localBody i) ∪ voxel 0 :=
  frontier_single_entrance _ _ _ (fun p hp q hpq => local_chamber_boundary i hp hpq)

theorem local_chamber_bounds (i : Face) {x : EPoint} (hx : x ∈ solid (localChamber i)) :
    (1:ℝ)/2 ≤ x 0 ∧ x 0 ≤ (dimensions i).1+(9:ℝ)/2 ∧
    -(1:ℝ)/2 ≤ x 1 ∧ x 1 ≤ (dimensions i).2.1-(1:ℝ)/2 ∧
    -(1:ℝ)/2 ≤ x 2 ∧ x 2 ≤ (dimensions i).2.2-(1:ℝ)/2 := by
  obtain ⟨p,hp,hx⟩ := hx
  have hp' := (mem_localChamber i p).mp hp
  have hpos := dimensions_pos i
  have h0 := abs_le.mp (hx 0)
  have h1 := abs_le.mp (hx 1)
  have h2 := abs_le.mp (hx 2)
  rcases hp' with hs | hb
  · have hp1 : (p 1:ℝ)=0 := by exact_mod_cast hs.2.2.1
    have hp2 : (p 2:ℝ)=0 := by exact_mod_cast hs.2.2.2
    have hp0l : (1:ℝ) ≤ (p 0:ℝ) := by exact_mod_cast hs.1
    have hp0u : (p 0:ℝ) ≤ 4 := by exact_mod_cast hs.2.1
    have hd : (1:ℝ) ≤ (dimensions i).1 := by exact_mod_cast hpos.1
    have ha : (1:ℝ) ≤ (dimensions i).2.1 := by exact_mod_cast hpos.2.1
    have hb : (1:ℝ) ≤ (dimensions i).2.2 := by exact_mod_cast hpos.2.2
    exact ⟨by linarith,by linarith,by linarith,by linarith,by linarith,by linarith⟩
  · have hl0 : (5:ℝ) ≤ (p 0:ℝ) := by exact_mod_cast hb.1
    have hu0 : (p 0:ℝ) ≤ 4+(dimensions i).1 := by exact_mod_cast (by omega : p 0 ≤ 4+(dimensions i).1)
    have hl1 : (0:ℝ) ≤ (p 1:ℝ) := by exact_mod_cast hb.2.2.1
    have hu1 : (p 1:ℝ) ≤ (dimensions i).2.1-1 := by exact_mod_cast (by omega : p 1 ≤ (dimensions i).2.1-1)
    have hl2 : (0:ℝ) ≤ (p 2:ℝ) := by exact_mod_cast hb.2.2.2.2.1
    have hu2 : (p 2:ℝ) ≤ (dimensions i).2.2-1 := by exact_mod_cast (by omega : p 2 ≤ (dimensions i).2.2-1)
    exact ⟨by linarith,by linarith,by linarith,by linarith,by linarith,by linarith⟩

theorem local_neck_section (i : Face) {x : EPoint} (hx : x ∈ solid (localChamber i))
    (h0 : x 0 < (9:ℝ)/2) : |x 1| ≤ (1:ℝ)/2 ∧ |x 2| ≤ (1:ℝ)/2 := by
  obtain ⟨p,hp,hx⟩ := hx
  rcases (mem_localChamber i p).mp hp with hs | hb
  · simpa only [hs.2.2.1, hs.2.2.2, Int.cast_zero, sub_zero] using And.intro (hx 1) (hx 2)
  · have hp0 : (5:ℝ) ≤ (p 0:ℝ) := by exact_mod_cast hb.1
    have hh := abs_le.mp (hx 0)
    linarith

end
end TranslationTiling.Rotations.Euclidean
