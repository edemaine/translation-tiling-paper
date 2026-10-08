import TranslationTiling.MSS.RayPacking

/-! Coverage closes the forced rays in the negative direction as well. -/

namespace TranslationTiling.MSS

noncomputable section
open scoped Classical
attribute [local irreducible] box

theorem mixed_no_left_center {Q C₁ C₂} (h : MixedTiling Q C₁ C₂)
    {c d : Lattice 3} (hc : c ∈ C₁ ∪ C₂) (hd : d ∈ C₁ ∪ C₂)
    (hn : c - scale • Pi.single 0 1 ∉ C₁ ∪ C₂)
    (hy : d 1 = c 1) (hz : d 2 = c 2) (hx : d 0 < c 0) : False := by
  obtain ⟨_, _, t, ht⟩ := mixed_centers_near h hc hd (by rw [hy]; omega) (by rw [hz]; omega)
  have htneg : t ≤ -1 := by omega
  have hnat : ((-t - 1).toNat : ℤ) = -t - 1 := by omega
  have hh := mixed_first_forward_iterate h hd (-t - 1).toNat
  have he : d + (201 * ((-t - 1).toNat : ℤ)) • Pi.single 0 1 =
      c - scale • Pi.single 0 1 := by
    ext i
    fin_cases i
    · change d 0 + 201 * ((-t - 1).toNat : ℤ) * 1 = c 0 - 201 * 1
      rw [hnat]; omega
    · change d 1 + 201 * ((-t - 1).toNat : ℤ) * 0 = c 1 - 201 * 0
      omega
    · change d 2 + 201 * ((-t - 1).toNat : ℤ) * 0 = c 2 - 201 * 0
      omega
  exact hn (he ▸ hh)

def cornerPoint (c : Lattice 3) (x : ℤ) : Lattice 3 :=
  fun i => if i = 0 then c 0 + x else c i + 100

theorem mixed_corner_kernel {Q C₁ C₂} (h : MixedTiling Q C₁ C₂)
    {c : Lattice 3} (hc : c ∈ C₁ ∪ C₂)
    (hn : c - scale • Pi.single 0 1 ∉ C₁ ∪ C₂)
    (x : ℤ) (hx : x < -100) (a : Placement Q C₁ C₂)
    (ha : a.position = cornerPoint c x) :
    ∃ u ∈ frame a.radius, a.vertex = scale • kernelStep Q + marker a.radius + u := by
  have he (i : Fin 3) : a.center i + a.vertex i = cornerPoint c x i := congrFun ha i
  rcases Finset.mem_union.mp a.vertex_mem with hv | hv
  · rcases Finset.mem_union.mp (Finset.mem_sdiff.mp hv).1 with hv | hv
    · have hb := (mem_box_iff 100 _).mp (Finset.mem_sdiff.mp hv).1
      have hy := hb 1
      have hz := hb 2
      have he1 := he 1
      have he2 := he 2
      simp only [cornerPoint, if_neg (by decide : (1 : Fin 3) ≠ 0)] at he1
      simp only [cornerPoint, if_neg (by decide : (2 : Fin 3) ≠ 0)] at he2
      obtain ⟨hyc, hzc, _⟩ := mixed_centers_near h hc a.center_mem (by omega) (by omega)
      have he0 := he 0
      have hb0 := hb 0
      change a.center 0 + a.vertex 0 = c 0 + x at he0
      have hlt : a.center 0 < c 0 := by omega
      exact (mixed_no_left_center h hc a.center_mem hn hyc hzc hlt).elim
    · obtain ⟨i, _, hv⟩ := Finset.mem_biUnion.mp hv
      obtain ⟨u, hu, huvertex⟩ := Finset.mem_image.mp hv
      have hub := ((mem_frame_iff (i.val + 1) (by omega) _).mp hu).1
      have hu1 := hub 1
      have hu2 := hub 2
      have he1 := he 1
      have he2 := he 2
      rw [← huvertex] at he1 he2
      simp only [cornerPoint, if_neg (by decide : (1 : Fin 3) ≠ 0),
        Pi.add_apply, Pi.smul_apply, smul_eq_mul, marker] at he1
      simp only [cornerPoint, if_neg (by decide : (2 : Fin 3) ≠ 0),
        Pi.add_apply, Pi.smul_apply, smul_eq_mul, marker] at he2
      have hi3 := i.isLt
      have hnear1 : -200 ≤ a.center 1 - c 1 ∧ a.center 1 - c 1 ≤ 200 := by
        by_cases hi : i = 1
        · subst i; simp only [Pi.single_eq_same] at he1; norm_num at he1; omega
        · simp only [Pi.single_eq_of_ne (Ne.symm hi)] at he1; norm_num at he1; omega
      have hnear2 : -200 ≤ a.center 2 - c 2 ∧ a.center 2 - c 2 ≤ 200 := by
        by_cases hi : i = 2
        · subst i; simp only [Pi.single_eq_same] at he2; norm_num at he2; omega
        · simp only [Pi.single_eq_of_ne (Ne.symm hi)] at he2; norm_num at he2; omega
      obtain ⟨hcy, _, _⟩ := mixed_centers_near h hc a.center_mem hnear1 hnear2
      rw [hcy] at he1
      by_cases hi : i = 1
      · subst i; simp only [Pi.single_eq_same] at he1; norm_num at he1; omega
      · simp only [Pi.single_eq_of_ne (Ne.symm hi)] at he1; norm_num at he1; omega
  · obtain ⟨u, hu, he⟩ := Finset.mem_image.mp hv
    exact ⟨u, hu, he.symm⟩

theorem mixed_first_backward {Q C₁ C₂} (h : MixedTiling Q C₁ C₂)
    {c : Lattice 3} (hc : c ∈ C₁ ∪ C₂) : c - scale • Pi.single 0 1 ∈ C₁ ∪ C₂ := by
  by_contra hn
  have hb := mixed_placement_bijective h
  obtain ⟨a, ha⟩ := hb.2 (cornerPoint c (-301))
  obtain ⟨b, hbpos⟩ := hb.2 (cornerPoint c (-201))
  obtain ⟨u, hu, huv⟩ := mixed_corner_kernel h hc hn (-301) (by omega) a ha
  obtain ⟨v, hv, hvv⟩ := mixed_corner_kernel h hc hn (-201) (by omega) b hbpos
  have hau := ((mem_frame_iff a.radius a.radius_pos _).mp hu).1
  have hbv := ((mem_frame_iff b.radius b.radius_pos _).mp hv).1
  have hra : a.radius = 4 ∨ a.radius = 5 := by cases a <;> simp [Placement.radius]
  have hrb : b.radius = 4 ∨ b.radius = 5 := by cases b <;> simp [Placement.radius]
  have he (i : Fin 3) : b.center i - a.center i =
      cornerPoint c (-201) i - cornerPoint c (-301) i + a.vertex i - b.vertex i := by
    have he1 := congrFun ha i
    have he2 := congrFun hbpos i
    change a.center i + a.vertex i = _ at he1
    change b.center i + b.vertex i = _ at he2
    omega
  have near (i : Fin 3) (hi : i ≠ 0) :
      -200 ≤ b.center i - a.center i ∧ b.center i - a.center i ≤ 200 := by
    have hh := he i
    have haui := hau i
    have hbvi := hbv i
    rw [huv, hvv] at hh
    simp only [cornerPoint, if_neg hi, Pi.add_apply, marker] at hh
    omega
  obtain ⟨_, _, k, hk⟩ := mixed_centers_near h a.center_mem b.center_mem
    (near 1 (by decide)) (near 2 (by decide))
  have he0 := he 0
  have hau0 := hau 0
  have hbv0 := hbv 0
  rw [huv, hvv] at he0
  simp only [cornerPoint, if_pos rfl, Pi.add_apply, Pi.smul_apply, kernelStep,
    if_neg (by decide : (0 : Fin 3) ≠ 2), smul_eq_mul, mul_zero, zero_add, marker] at he0
  push_cast at he0
  omega

theorem mixed_first_period {Q C₁ C₂} (h : MixedTiling Q C₁ C₂) :
    Period (C₁ ∪ C₂) (scale • Pi.single 0 1) := by
  intro c
  constructor
  · intro hc
    have hh := mixed_first_backward h hc
    simpa only [add_sub_cancel_right] using hh
  · exact mixed_first_forward h

end
end TranslationTiling.MSS
