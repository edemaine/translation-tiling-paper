import TranslationTiling.MSS.FirstBump

/-! Forward rays of centers force separation of their transverse coordinates. -/

namespace TranslationTiling.MSS

noncomputable section
open scoped Classical
attribute [local irreducible] box

theorem mixed_first_forward_iterate {Q C₁ C₂} (h : MixedTiling Q C₁ C₂)
    {c : Lattice 3} (hc : c ∈ C₁ ∪ C₂) (n : ℕ) :
    c + (201 * (n : ℤ)) • Pi.single 0 1 ∈ C₁ ∪ C₂ := by
  induction n with
  | zero => simpa using hc
  | succ n ih =>
    have hh := mixed_first_forward h ih
    convert hh using 1
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Nat.cast_add, Nat.cast_one, scale]
    ring

theorem mixed_centers_disjoint {Q C₁ C₂} (h : MixedTiling Q C₁ C₂) : Disjoint C₁ C₂ := by
  apply Set.disjoint_left.mpr
  intro c hc hd
  let a : Placement Q C₁ C₂ := .inl (⟨c, hc⟩, ⟨0, zero_mem_component Q 4 (by omega)⟩)
  let b : Placement Q C₁ C₂ := .inr (⟨c, hd⟩, ⟨0, zero_mem_component Q 5 (by omega)⟩)
  have he : a.position = b.position := rfl
  have hh := (mixed_placement_bijective h).1 he
  dsimp [a, b] at hh
  cases hh

theorem mixed_centers_near {Q C₁ C₂} (h : MixedTiling Q C₁ C₂)
    {c d : Lattice 3} (hc : c ∈ C₁ ∪ C₂) (hd : d ∈ C₁ ∪ C₂)
    (hy : -200 ≤ d 1 - c 1 ∧ d 1 - c 1 ≤ 200)
    (hz : -200 ≤ d 2 - c 2 ∧ d 2 - c 2 ≤ 200) :
    d 1 = c 1 ∧ d 2 = c 2 ∧ 201 ∣ d 0 - c 0 := by
  let t : ℤ := (d 0 - c 0 + 100) / 201
  let delta : ℤ := (d 0 - c 0 + 100) % 201 - 100
  have hdelta : -100 ≤ delta ∧ delta ≤ 100 := by
    have hl := Int.emod_nonneg (d 0 - c 0 + 100) (by omega : (201 : ℤ) ≠ 0)
    have hu := Int.emod_lt_of_pos (d 0 - c 0 + 100) (by omega : (0 : ℤ) < 201)
    dsimp [delta]; omega
  have hdiv : d 0 - c 0 = 201 * t + delta := by
    have hh := Int.emod_add_mul_ediv (d 0 - c 0 + 100) 201
    dsimp [t, delta]; omega
  let c' := c + (201 * (t.toNat : ℤ)) • Pi.single 0 1
  let d' := d + (201 * ((-t).toNat : ℤ)) • Pi.single 0 1
  have hc' : c' ∈ C₁ ∪ C₂ := mixed_first_forward_iterate h hc t.toNat
  have hd' : d' ∈ C₁ ∪ C₂ := mixed_first_forward_iterate h hd (-t).toNat
  have hdx : d' 0 - c' 0 = delta := by
    dsimp [c', d']
    simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
    omega
  have hcy (i : Fin 3) (hi : i ≠ 0) : c' i = c i := by
    simp only [c', Pi.add_apply, Pi.smul_apply, Pi.single_eq_of_ne hi,
      smul_eq_mul, mul_zero, add_zero]
  have hdy (i : Fin 3) (hi : i ≠ 0) : d' i = d i := by
    simp only [d', Pi.add_apply, Pi.smul_apply, Pi.single_eq_of_ne hi,
      smul_eq_mul, mul_zero, add_zero]
  have hbnd (i : Fin 3) : -200 ≤ d' i - c' i ∧ d' i - c' i ≤ 200 := by
    fin_cases i
    · change -200 ≤ d' 0 - c' 0 ∧ d' 0 - c' 0 ≤ 200
      omega
    · change -200 ≤ d' 1 - c' 1 ∧ d' 1 - c' 1 ≤ 200
      simpa only [hcy 1 (by decide), hdy 1 (by decide)] using hy
    · change -200 ≤ d' 2 - c' 2 ∧ d' 2 - c' 2 ≤ 200
      simpa only [hcy 2 (by decide), hdy 2 (by decide)] using hz
  let v : Lattice 3 := fun i => max (c' i) (d' i) - 100
  have hvc : v - c' ∈ box 100 := by
    apply (mem_box_iff 100 _).mpr
    intro i
    have hh := hbnd i
    simp only [Pi.sub_apply, v, max_def]
    split_ifs <;> omega
  have hvd : v - d' ∈ box 100 := by
    apply (mem_box_iff 100 _).mpr
    intro i
    have hh := hbnd i
    simp only [Pi.sub_apply, v, max_def]
    split_ifs <;> omega
  have hxc : (v - c') 0 ≤ 0 := by
    simp only [Pi.sub_apply, v, max_def]
    split_ifs <;> omega
  have hxd : (v - d') 0 ≤ 0 := by
    simp only [Pi.sub_apply, v, max_def]
    split_ifs <;> omega
  have make (e : Lattice 3) (he : e ∈ C₁ ∪ C₂) (hv : v - e ∈ box 100)
      (hx : (v - e) 0 ≤ 0) :
      ∃ a : Placement Q C₁ C₂, a.center = e ∧ a.position = v := by
    have pos : e + (v - e) = v := add_sub_cancel _ _
    rcases he with he | he
    · refine ⟨.inl (⟨e, he⟩, ⟨v - e, negative_box_mem_component Q 4 (by omega) hv hx⟩),
        rfl, pos⟩
    · refine ⟨.inr (⟨e, he⟩, ⟨v - e, negative_box_mem_component Q 5 (by omega) hv hx⟩),
        rfl, pos⟩
  obtain ⟨a, hac, hap⟩ := make c' hc' hvc hxc
  obtain ⟨b, hbc, hbp⟩ := make d' hd' hvd hxd
  have hab := (mixed_placement_bijective h).1 (hap.trans hbp.symm)
  have he : c' = d' := hac.symm.trans ((congrArg Placement.center hab).trans hbc)
  have he1 := congrFun he 1
  have he2 := congrFun he 2
  have he0 := congrFun he 0
  refine ⟨?_, ?_, t, ?_⟩
  · simpa only [hcy 1 (by decide), hdy 1 (by decide)] using he1.symm
  · simpa only [hcy 2 (by decide), hdy 2 (by decide)] using he2.symm
  · have hzdelta : delta = 0 := by omega
    rw [hzdelta, add_zero] at hdiv
    exact hdiv

end
end TranslationTiling.MSS
