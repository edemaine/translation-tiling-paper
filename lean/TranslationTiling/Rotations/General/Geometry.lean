import TranslationTiling.Rotations.General.Gadget
import Mathlib.Tactic.Linarith

namespace TranslationTiling.Rotations.General
variable {d : ℕ} [NeZero d]

theorem margin_pos : 0 < margin d := by
  unfold margin neckLength
  omega

theorem margin_five_lt_cubeSide : 5*margin d < cubeSide d := by
  have hp := margin_pos (d := d)
  unfold cubeSide
  nlinarith

theorem fullKey_bounds (f : Face d) {x : Lattice d} (hx : x ∈ fullKeyFinset f) (j : Fin d) :
    0 ≤ x j ∧ x j + 1 < (margin d : ℤ) := by
  have hm := boxSide_lt_max f j
  have hl := boxSide_two_le f j
  have hn : 0 < neckLength d := by unfold neckLength; omega
  have hp : 1 < margin d := by unfold margin; omega
  rw [← Finset.mem_coe,fullKeyFinset_set] at hx
  rcases hx with (hb | hs) | hz
  · have hj := hb j
    dsimp [KeyBox,Box] at hb
    dsimp [keyHi,keyLo] at hj
    unfold margin
    split_ifs at hj <;> omega
  · by_cases hj : j = 0
    · subst j
      unfold margin
      have := hs.1
      have := hs.2.1
      omega
    · rw [hs.2.2 j hj]
      exact ⟨le_rfl,by omega⟩
  · have he : x = 0 := hz
    subst x
    simp only [Pi.zero_apply]
    exact ⟨le_rfl,by omega⟩

theorem frame_normal_apply (f : Face d) (x : Lattice d) :
    (frameMotion f).apply x (faceAxis f) =
      if negative f then x 0 else (cubeSide d : ℤ)-1-x 0 := by
  simp [frameMotion,Motion.apply,Orientation.linear_apply,frameOrientation,Orientation.sign,gate]
  cases h : negative f <;> simp [h] <;> ring

theorem frame_tangent_apply (f : Face d) (x : Lattice d) (j : Fin d) (hj : j ≠ faceAxis f) :
    (frameMotion f).apply x j =
      3*(margin d : ℤ) + (if negative f then 0 else 1) + x ((frameOrientation f).axes j) := by
  simp [frameMotion,Motion.apply,Orientation.linear_apply,frameOrientation,Orientation.sign,gate,hj]

/-- A recess lies near its own face and centrally in every other coordinate. -/
def RecessBounds (f : Face d) (x : Lattice d) : Prop :=
  (if negative f then 0 ≤ x (faceAxis f) ∧ x (faceAxis f) < (margin d : ℤ)
   else (cubeSide d : ℤ)-(margin d : ℤ) < x (faceAxis f) ∧ x (faceAxis f) < cubeSide d) ∧
  ∀ j, j ≠ faceAxis f → 3*(margin d : ℤ) ≤ x j ∧ x j ≤ 4*(margin d : ℤ)

theorem recess_bounds (f : Face d) {x : Lattice d} (hx : x ∈ recess f) : RecessBounds f x := by
  obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
  constructor
  · rw [frame_normal_apply]
    have hb := fullKey_bounds f hy 0
    cases hn : negative f <;> simp only [hn,Bool.false_eq_true,ite_false,ite_true]
    all_goals omega
  · intro j hj
    rw [frame_tangent_apply f y j hj]
    have hb := fullKey_bounds f hy ((frameOrientation f).axes j)
    cases hn : negative f <;> simp only [hn,Bool.false_eq_true,ite_false,ite_true]
    all_goals omega

theorem recess_subset_cell (f : Face d) : recess f ⊆ cell (cubeSide d) := by
  intro x hx
  have hb := recess_bounds f hx
  have hL := margin_five_lt_cubeSide (d := d)
  have hp := margin_pos (d := d)
  apply (mem_boxFinset _ _ _).mpr
  intro j
  by_cases hj : j = faceAxis f
  · subst j
    have hn := hb.1
    cases h : negative f <;> simp only [h,Bool.false_eq_true,ite_false,ite_true] at hn
    all_goals dsimp; omega
  · have ht := hb.2 j hj
    dsimp
    omega

theorem face_ext {f g : Face d} (ha : faceAxis f = faceAxis g) (hn : negative f = negative g) : f = g := by
  have hav := congrArg Fin.val ha
  dsimp [faceAxis] at hav
  by_cases hf : f.val % 2 = 0 <;> by_cases hg : g.val % 2 = 0
  all_goals simp [negative,hf,hg] at hn
  all_goals apply Fin.ext; omega

/-- Chambers at different faces occupy disjoint sets of voxels. -/
theorem recesses_disjoint {f g : Face d} (hfg : f ≠ g) : Disjoint (recess f) (recess g) := by
  apply Finset.disjoint_left.mpr
  intro x hf hg
  have hbf := recess_bounds f hf
  have hbg := recess_bounds g hg
  have hL := margin_five_lt_cubeSide (d := d)
  have hp := margin_pos (d := d)
  by_cases ha : faceAxis f = faceAxis g
  · have hn : negative f ≠ negative g := fun he => hfg (face_ext ha he)
    have hfn := hbf.1
    have hgn := hbg.1
    rw [← ha] at hgn
    cases h1 : negative f <;> cases h2 : negative g
    all_goals simp [h1,h2] at hfn hgn hn
    all_goals omega
  · have hfn := hbf.1
    have hgt := hbg.2 (faceAxis f) ha
    cases h1 : negative f <;> simp only [h1,Bool.false_eq_true,ite_false,ite_true] at hfn
    all_goals omega

end TranslationTiling.Rotations.General
