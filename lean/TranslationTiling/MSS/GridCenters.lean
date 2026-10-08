import TranslationTiling.MSS.CommonForcing

/-! The common frames force every center onto one full cubic grid. -/

namespace TranslationTiling.MSS

noncomputable section
open scoped Classical

theorem mixed_coordinate_forward {Q C₁ C₂} (h : MixedTiling Q C₁ C₂)
    {c : Lattice 3} (hc : c ∈ C₁ ∪ C₂) (i : Fin 3) :
    c + scale • Pi.single i 1 ∈ C₁ ∪ C₂ := by
  by_cases hi : i = 0
  · subst i; exact mixed_first_forward h hc
  · exact mixed_common_forward h hc i hi

theorem mixed_coordinate_forward_iterate {Q C₁ C₂} (h : MixedTiling Q C₁ C₂)
    {c : Lattice 3} (hc : c ∈ C₁ ∪ C₂) (i : Fin 3) (n : ℕ) :
    c + (201 * (n : ℤ)) • Pi.single i 1 ∈ C₁ ∪ C₂ := by
  induction n with
  | zero => simpa using hc
  | succ n ih =>
    have hh := mixed_coordinate_forward h ih i
    convert hh using 1
    ext j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Nat.cast_add, Nat.cast_one, scale]
    ring

theorem mixed_balance_axis {Q C₁ C₂} (h : MixedTiling Q C₁ C₂)
    {c d : Lattice 3} (hc : c ∈ C₁ ∪ C₂) (hd : d ∈ C₁ ∪ C₂) (i : Fin 3) :
    ∃ c' d' : Lattice 3, c' ∈ C₁ ∪ C₂ ∧ d' ∈ C₁ ∪ C₂ ∧
      (∀ j, j ≠ i → c' j = c j ∧ d' j = d j) ∧
      (-100 ≤ d' i - c' i ∧ d' i - c' i ≤ 100) ∧
      201 ∣ (d i - c i) - (d' i - c' i) := by
  let t : ℤ := (d i - c i + 100) / 201
  let c' := c + (201 * (t.toNat : ℤ)) • Pi.single i 1
  let d' := d + (201 * ((-t).toNat : ℤ)) • Pi.single i 1
  have hdiff : d' i - c' i = (d i - c i + 100) % 201 - 100 := by
    have hh := Int.emod_add_mul_ediv (d i - c i + 100) 201
    dsimp only [c', d']
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_eq_same, mul_one]
    dsimp [t]; omega
  refine ⟨c', d', mixed_coordinate_forward_iterate h hc i t.toNat,
    mixed_coordinate_forward_iterate h hd i (-t).toNat, ?_, ?_, ?_⟩
  · intro j hj
    simp only [c', d', Pi.add_apply, Pi.smul_apply, Pi.single_eq_of_ne hj,
      smul_eq_mul, mul_zero, add_zero, and_self]
  · have hl := Int.emod_nonneg (d i - c i + 100) (by omega : (201 : ℤ) ≠ 0)
    have hu := Int.emod_lt_of_pos (d i - c i + 100) (by omega : (0 : ℤ) < 201)
    omega
  · refine ⟨t, ?_⟩
    have hh := Int.emod_add_mul_ediv (d i - c i + 100) 201
    dsimp [t]; omega

theorem mixed_centers_congruent {Q C₁ C₂} (h : MixedTiling Q C₁ C₂)
    {c d : Lattice 3} (hc : c ∈ C₁ ∪ C₂) (hd : d ∈ C₁ ∪ C₂) :
    ∀ i, 201 ∣ d i - c i := by
  obtain ⟨c', d', hc', hd', hkeep1, hbound1, hdiv1⟩ := mixed_balance_axis h hc hd 1
  obtain ⟨c'', d'', hc'', hd'', hkeep2, hbound2, hdiv2⟩ := mixed_balance_axis h hc' hd' 2
  have hnear1 : -200 ≤ d'' 1 - c'' 1 ∧ d'' 1 - c'' 1 ≤ 200 := by
    obtain ⟨hec, hed⟩ := hkeep2 1 (by decide)
    rw [hec, hed]; omega
  obtain ⟨he1, he2, hdiv0⟩ := mixed_centers_near h hc'' hd'' hnear1 (by omega)
  have hx : 201 ∣ d 0 - c 0 := by
    obtain ⟨hec1, hed1⟩ := hkeep1 0 (by decide)
    obtain ⟨hec2, hed2⟩ := hkeep2 0 (by decide)
    simpa only [hec2, hed2, hec1, hed1] using hdiv0
  have hy : 201 ∣ d 1 - c 1 := by
    obtain ⟨hec, hed⟩ := hkeep2 1 (by decide)
    have hzero : d' 1 - c' 1 = 0 := by rw [← hec, ← hed, he1]; omega
    simpa only [hzero, sub_zero] using hdiv1
  have hz : 201 ∣ d 2 - c 2 := by
    obtain ⟨hec, hed⟩ := hkeep1 2 (by decide)
    simpa only [he2, sub_self, sub_zero, hec, hed] using hdiv2
  intro i
  fin_cases i
  · exact hx
  · exact hy
  · exact hz

theorem mixed_grid_centers {Q C₁ C₂} (h : MixedTiling Q C₁ C₂)
    (h0 : 0 ∈ C₁ ∪ C₂) : C₁ ∪ C₂ = Set.range (fun x : Lattice 3 => scale • x) := by
  have divs (c : Lattice 3) (hc : c ∈ C₁ ∪ C₂) : ∀ i, 201 ∣ c i := by
    simpa only [Pi.zero_apply, sub_zero] using mixed_centers_congruent h h0 hc
  apply Set.Subset.antisymm
  · intro c hc
    refine ⟨(fun i => c i / 201), ?_⟩
    ext i
    change 201 * (c i / 201) = c i
    have hh := Int.emod_add_mul_ediv (c i) 201
    have he := Int.emod_eq_zero_of_dvd (divs c hc i)
    omega
  · rintro _ ⟨w, rfl⟩
    obtain ⟨c, hc, hbox⟩ := mixed_transverse_cover h (201 * w 1) (201 * w 2)
    obtain ⟨kx, hx⟩ := divs c hc 0
    obtain ⟨ky, hy⟩ := divs c hc 1
    obtain ⟨kz, hz⟩ := divs c hc 2
    have hcy : c 1 = 201 * w 1 := by
      have hh : -100 ≤ 201 * w 1 - c 1 ∧ 201 * w 1 - c 1 ≤ 100 := ⟨hbox.1, hbox.2.1⟩
      omega
    have hcz : c 2 = 201 * w 2 := by
      have hh : -100 ≤ 201 * w 2 - c 2 ∧ 201 * w 2 - c 2 ≤ 100 :=
        ⟨hbox.2.2.1, hbox.2.2.2⟩
      omega
    have hh := mixed_first_shift h hc (w 0 - kx)
    have he : c + (201 * (w 0 - kx)) • Pi.single 0 1 = scale • w := by
      ext i
      fin_cases i
      · change c 0 + 201 * (w 0 - kx) * 1 = 201 * w 0
        omega
      · change c 1 + 201 * (w 0 - kx) * 0 = 201 * w 1
        omega
      · change c 2 + 201 * (w 0 - kx) * 0 = 201 * w 2
        omega
    rw [he] at hh
    exact hh

end
end TranslationTiling.MSS
