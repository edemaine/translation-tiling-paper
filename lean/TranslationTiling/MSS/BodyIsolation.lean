import TranslationTiling.MSS.FrameIsolation
import Mathlib.Tactic.Ring

/-! The singleton component in the punctured main cube is its first marker. -/

namespace TranslationTiling.MSS

noncomputable section
open scoped Classical

-- Keep elaboration from enumerating the 201³-point box.
attribute [local irreducible] box

def holes (j : ℕ) : Finset (Lattice 3) := removed ∪ (frame j).image (marker j + ·)
def body (j : ℕ) : Finset (Lattice 3) := box 100 \ holes j

theorem body_subset_component (Q j : ℕ) {v : Lattice 3} (hv : v ∈ body j) :
    v ∈ component Q j := by
  obtain ⟨hb, hh⟩ := Finset.mem_sdiff.mp hv
  have hn : v ∉ removed ∧ v ∉ (frame j).image (marker j + ·) := by
    simpa only [holes, Finset.mem_union, not_or] using hh
  exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr
    ⟨Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hb, hn.1⟩), hn.2⟩)

theorem mem_holes_witness (j : ℕ) (hj : 0 < j) (hj5 : j ≤ 5)
    {v : Lattice 3} (hv : v ∈ holes j) :
    ∃ r : ℕ, 0 < r ∧ r ≤ 5 ∧ v - marker r ∈ frame r ∧
      ∀ z : Lattice 3, z - marker r ∈ frame r → z ∈ holes j := by
  rcases Finset.mem_union.mp hv with hv | hv
  · obtain ⟨i, hi, hv⟩ := Finset.mem_biUnion.mp hv
    obtain ⟨u, hu, he⟩ := Finset.mem_image.mp hv
    refine ⟨i.val + 1, by omega, by have := i.isLt; omega, ?_, ?_⟩
    · rw [← he]
      simpa only [add_sub_cancel_left] using hu
    · intro z hz
      apply Finset.mem_union_left
      apply Finset.mem_biUnion.mpr
      refine ⟨i, hi, Finset.mem_image.mpr ⟨z - marker (i.val + 1), hz, ?_⟩⟩
      exact add_sub_cancel _ _
  · obtain ⟨u, hu, he⟩ := Finset.mem_image.mp hv
    refine ⟨j, hj, hj5, ?_, ?_⟩
    · rw [← he]
      simpa only [add_sub_cancel_left] using hu
    · intro z hz
      exact Finset.mem_union_right _ (Finset.mem_image.mpr
        ⟨z - marker j, hz, add_sub_cancel _ _⟩)

theorem holes_second_coordinate (j : ℕ) (hj : 0 < j) (hj5 : j ≤ 5)
    {v : Lattice 3} (hv : v ∈ holes j) : -5 ≤ v 1 ∧ v 1 ≤ 5 := by
  obtain ⟨r, hr, hr5, hv, _⟩ := mem_holes_witness j hj hj5 hv
  have hh := (mem_frame_iff r hr _).mp hv |>.1 (1 : Fin 3)
  simp only [Pi.sub_apply, marker, if_neg (by decide : (1 : Fin 3) ≠ 0), sub_zero] at hh
  omega

set_option maxHeartbeats 200000 in
theorem body_isolated_point (j : ℕ) (hj : 0 < j) (hj5 : j ≤ 5)
    (v : Lattice 3) (hv : v ∈ body j)
    (hplus : Function.update v (1 : Fin 3) (v 1 + 1) ∉ body j)
    (hminus : Function.update v (1 : Fin 3) (v 1 - 1) ∉ body j) :
    v = marker 1 := by
  obtain ⟨hbox, hholes⟩ := Finset.mem_sdiff.mp hv
  have hb := (mem_box_iff _ _).mp hbox
  have update_box (y : ℤ) (hy : -100 ≤ y ∧ y ≤ 100) :
      Function.update v (1 : Fin 3) y ∈ box 100 := by
    exact (mem_box_iff 100 (Function.update v (1 : Fin 3) y)).mpr (by
      intro i
      by_cases hi : i = 1
      · subst i; simpa only [Function.update_self, Nat.cast_ofNat] using hy
      · simpa only [Function.update_of_ne hi] using hb i)
  have in_holes (z : Lattice 3) (hz : z ∈ box 100) (hn : z ∉ body j) : z ∈ holes j := by
    by_contra hh
    exact hn (Finset.mem_sdiff.mpr ⟨hz, hh⟩)
  have hb1 := hb 1
  have htop : v 1 ≠ 100 := by
    intro he
    have hz := in_holes _ (update_box (v 1 - 1) (by omega)) hminus
    have hh := holes_second_coordinate j hj hj5 hz
    simp only [Function.update_self] at hh
    omega
  have hbottom : v 1 ≠ -100 := by
    intro he
    have hz := in_holes _ (update_box (v 1 + 1) (by omega)) hplus
    have hh := holes_second_coordinate j hj hj5 hz
    simp only [Function.update_self] at hh
    omega
  have hpbox := update_box (v 1 + 1) (by omega)
  have hmbox := update_box (v 1 - 1) (by omega)
  obtain ⟨rp, hrp, hrp5, hfp, hsub⟩ := mem_holes_witness j hj hj5 (in_holes _ hpbox hplus)
  obtain ⟨rm, hrm, hrm5, hfm, _⟩ := mem_holes_witness j hj hj5 (in_holes _ hmbox hminus)
  have hp0 := ((mem_frame_iff rp hrp _).mp hfp).1 (0 : Fin 3)
  have hm0 := ((mem_frame_iff rm hrm _).mp hfm).1 (0 : Fin 3)
  simp only [Pi.sub_apply, Function.update_of_ne (by decide : (0 : Fin 3) ≠ 1),
    marker] at hp0 hm0
  push_cast at hp0 hm0
  have he : rm = rp := by omega
  subst rm
  let x := v - marker rp
  have hupdate (t : ℤ) :
      Function.update v (1 : Fin 3) (v 1 + t) - marker rp =
        Function.update x (1 : Fin 3) (x 1 + t) := by
    funext i
    by_cases hi : i = 1
    · subst i
      simp only [Pi.sub_apply, Function.update_self, x]
      ring
    · simp only [Pi.sub_apply, Function.update_of_ne hi, x]
  have hfp' : Function.update x (1 : Fin 3) (x 1 + 1) ∈ frame rp := by
    rwa [hupdate 1] at hfp
  have hfm' : Function.update x (1 : Fin 3) (x 1 - 1) ∈ frame rp := by
    have he' := hupdate (-1)
    simp only [← sub_eq_add_neg] at he'
    rwa [he'] at hfm
  have hxn : x ∉ frame rp := fun hx => hholes (hsub v hx)
  obtain ⟨hr1, hx0⟩ := opposite_neighbors_in_frame rp hrp x hfp' hfm' hxn
  have hv0 : v = marker rp := sub_eq_zero.mp hx0
  simpa only [hr1] using hv0

end
end TranslationTiling.MSS
