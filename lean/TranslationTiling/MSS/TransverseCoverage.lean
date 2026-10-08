import TranslationTiling.MSS.FirstPeriod
import Mathlib.Data.Fintype.Card

/-! The projections of the main cubes cover the transverse plane. -/

namespace TranslationTiling.MSS

noncomputable section
open scoped Classical
attribute [local irreducible] box

def transverseBox (c : Lattice 3) (y z : ℤ) : Prop :=
  -100 ≤ y - c 1 ∧ y - c 1 ≤ 100 ∧ -100 ≤ z - c 2 ∧ z - c 2 ≤ 100

def rowPoint (y z x : ℤ) : Lattice 3 :=
  fun i => if i = 0 then x else if i = 1 then y else z

def detachedShift (Q : ℕ) (t : Fin 3) : Lattice 3 :=
  if t = 0 then scale • Pi.single 1 1 else
  if t = 1 then scale • Pi.single 2 1 else scale • kernelStep Q

def detachedBounds (Q : ℕ) (t : Fin 3) (v : Lattice 3) : Prop :=
  (22 + 11 * (t.val : ℤ) ≤ v 0 ∧ v 0 ≤ 22 + 11 * (t.val : ℤ) + 21) ∧
  (-5 ≤ v 1 - detachedShift Q t 1 ∧ v 1 - detachedShift Q t 1 ≤ 5) ∧
  (-5 ≤ v 2 - detachedShift Q t 2 ∧ v 2 - detachedShift Q t 2 ≤ 5)

theorem vertex_without_transverse_box (Q : ℕ) (a : Placement Q C₁ C₂)
    (y z x : ℤ) (ha : a.position = rowPoint y z x)
    (hn : ¬ transverseBox a.center y z) : ∃ t : Fin 3, detachedBounds Q t a.vertex := by
  have he1 : a.center 1 + a.vertex 1 = y := congrFun ha 1
  have he2 : a.center 2 + a.vertex 2 = z := congrFun ha 2
  rcases Finset.mem_union.mp a.vertex_mem with hv | hv
  · rcases Finset.mem_union.mp (Finset.mem_sdiff.mp hv).1 with hv | hv
    · have hh := (mem_box_iff 100 _).mp (Finset.mem_sdiff.mp hv).1
      have h1 := hh 1
      have h2 := hh 2
      exact (hn (by unfold transverseBox; omega)).elim
    · obtain ⟨i, _, hv⟩ := Finset.mem_biUnion.mp hv
      obtain ⟨u, hu, he⟩ := Finset.mem_image.mp hv
      have hh := ((mem_frame_iff (i.val + 1) (by omega) _).mp hu).1
      have h0 := hh 0
      have h1 := hh 1
      have h2 := hh 2
      fin_cases i
      · change scale • Pi.single (0 : Fin 3) 1 + marker 1 + u = a.vertex at he
        have hy : a.vertex 1 = u 1 := by
          rw [← he]
          simp only [Pi.add_apply, Pi.smul_apply,
            Pi.single_eq_of_ne (by decide : (1 : Fin 3) ≠ 0), marker,
            if_neg (by decide : (1 : Fin 3) ≠ 0), smul_eq_mul, mul_zero, zero_add]
        have hz : a.vertex 2 = u 2 := by
          rw [← he]
          simp only [Pi.add_apply, Pi.smul_apply,
            Pi.single_eq_of_ne (by decide : (2 : Fin 3) ≠ 0), marker,
            if_neg (by decide : (2 : Fin 3) ≠ 0), smul_eq_mul, mul_zero, zero_add]
        exact (hn (by unfold transverseBox; omega)).elim
      · change scale • Pi.single (1 : Fin 3) 1 + marker 2 + u = a.vertex at he
        refine ⟨0, ?_⟩
        rw [← he]
        norm_num [detachedBounds, detachedShift, marker, Pi.single_apply]
        norm_num at h0 h1 h2
        omega
      · change scale • Pi.single (2 : Fin 3) 1 + marker 3 + u = a.vertex at he
        refine ⟨1, ?_⟩
        rw [← he]
        norm_num [detachedBounds, detachedShift, marker, Pi.single_apply]
        norm_num at h0 h1 h2
        omega
  · obtain ⟨u, hu, he⟩ := Finset.mem_image.mp hv
    have hh := ((mem_frame_iff a.radius a.radius_pos _).mp hu).1
    have h0 := hh 0
    have h1 := hh 1
    have h2 := hh 2
    have hr : a.radius = 4 ∨ a.radius = 5 := by cases a <;> simp [Placement.radius]
    refine ⟨2, ?_⟩
    rw [← he]
    simp only [detachedBounds]
    have hs0 : (scale • kernelStep Q) 0 = 0 := by
      simp only [Pi.smul_apply, kernelStep, if_neg (by decide : (0 : Fin 3) ≠ 2),
        smul_eq_mul, mul_zero]
    have hs1 : (scale • kernelStep Q) 1 = 0 := by
      simp only [Pi.smul_apply, kernelStep, if_neg (by decide : (1 : Fin 3) ≠ 2),
        smul_eq_mul, mul_zero]
    have hds1 : detachedShift Q 2 1 = (scale • kernelStep Q) 1 := by
      simp only [detachedShift, if_neg (by decide : (2 : Fin 3) ≠ 0),
        if_neg (by decide : (2 : Fin 3) ≠ 1)]
    have hds2 : detachedShift Q 2 2 = (scale • kernelStep Q) 2 := by
      simp only [detachedShift, if_neg (by decide : (2 : Fin 3) ≠ 0),
        if_neg (by decide : (2 : Fin 3) ≠ 1)]
    simp only [Pi.add_apply, hs0, hs1, hds1, hds2, marker]
    norm_num
    push_cast
    omega

theorem mixed_transverse_cover {Q C₁ C₂} (h : MixedTiling Q C₁ C₂) (y z : ℤ) :
    ∃ c ∈ C₁ ∪ C₂, transverseBox c y z := by
  by_contra hn
  have hn' : ∀ c ∈ C₁ ∪ C₂, ¬ transverseBox c y z := by
    intro c hc ht; exact hn ⟨c, hc, ht⟩
  have cover (i : Fin 4) : ∃ a : Placement Q C₁ C₂, ∃ t : Fin 3,
      a.position = rowPoint y z (50 * (i.val : ℤ)) ∧ detachedBounds Q t a.vertex := by
    obtain ⟨a, ha⟩ := (mixed_placement_bijective h).2 (rowPoint y z (50 * (i.val : ℤ)))
    obtain ⟨t, ht⟩ := vertex_without_transverse_box Q a y z _ ha (hn' _ a.center_mem)
    exact ⟨a, t, ha, ht⟩
  choose a t hpos hbounds using cover
  have hinj : Function.Injective t := by
    intro i j hij
    have hi := hbounds i
    have hj := hbounds j
    simp only [detachedBounds] at hi hj
    rw [← hij] at hj
    have he (k : Fin 3) : (a j).center k - (a i).center k =
        rowPoint y z (50 * (j.val : ℤ)) k - rowPoint y z (50 * (i.val : ℤ)) k +
        (a i).vertex k - (a j).vertex k := by
      have hei := congrFun (hpos i) k
      have hej := congrFun (hpos j) k
      change (a i).center k + (a i).vertex k = _ at hei
      change (a j).center k + (a j).vertex k = _ at hej
      omega
    have hnear1 : -200 ≤ (a j).center 1 - (a i).center 1 ∧
        (a j).center 1 - (a i).center 1 ≤ 200 := by
      have hh := he 1
      have hbi := hi.2.1
      have hbj := hj.2.1
      change (a j).center 1 - (a i).center 1 = y - y +
        (a i).vertex 1 - (a j).vertex 1 at hh
      omega
    have hnear2 : -200 ≤ (a j).center 2 - (a i).center 2 ∧
        (a j).center 2 - (a i).center 2 ≤ 200 := by
      have hh := he 2
      have hbi := hi.2.2
      have hbj := hj.2.2
      change (a j).center 2 - (a i).center 2 = z - z +
        (a i).vertex 2 - (a j).vertex 2 at hh
      omega
    obtain ⟨_, _, k, hk⟩ := mixed_centers_near h (a i).center_mem (a j).center_mem
      hnear1 hnear2
    have he0 := he 0
    have hbi := hi.1
    have hbj := hj.1
    have hdiff : -21 ≤ (a i).vertex 0 - (a j).vertex 0 ∧
        (a i).vertex 0 - (a j).vertex 0 ≤ 21 := by omega
    change (a j).center 0 - (a i).center 0 = 50 * (j.val : ℤ) - 50 * (i.val : ℤ) +
      (a i).vertex 0 - (a j).vertex 0 at he0
    have hi4 := i.isLt
    have hj4 := j.isLt
    have hkzero : k = 0 := by omega
    rw [hkzero, mul_zero] at hk
    apply Fin.ext
    omega
  have hh := Fintype.card_le_of_injective t hinj
  norm_num at hh

end
end TranslationTiling.MSS
