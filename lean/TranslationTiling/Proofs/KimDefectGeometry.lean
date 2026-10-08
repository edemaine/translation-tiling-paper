import TranslationTiling.Proofs.KimDefects

/-! A dent has a full transverse rim, and a 3-block loses at most one point. -/

namespace TranslationTiling.Kim

noncomputable section
open scoped Classical

theorem dentAt_mem (m : ℕ) (i : Fin 3) : dentAt m i ∈ dents m := by
  simp only [dents, List.mem_cons, List.not_mem_nil, or_false]
  fin_cases i
  · apply Or.inl; ext j; fin_cases j <;> norm_num [dentAt]
  · apply Or.inr ∘ Or.inl; ext j; fin_cases j <;> norm_num [dentAt]
  · apply Or.inr ∘ Or.inr; ext j; fin_cases j <;> norm_num [dentAt]

theorem dents_close_unique (m : ℕ) {u v : Lattice 3}
    (hu : u ∈ dents m) (hv : v ∈ dents m)
    (hnear : ∀ i, -2 ≤ v i - u i ∧ v i - u i ≤ 2) : u = v := by
  obtain ⟨i, rfl⟩ := dents_eq_dentAt m hu
  obtain ⟨j, rfl⟩ := dents_eq_dentAt m hv
  have hij : i = j := by
    by_contra hne
    have hneval : i.val ≠ j.val := fun h => hne (Fin.ext h)
    have hh := hnear i
    simp only [dentAt, if_pos rfl, if_neg hneval, ite_true] at hh
    have hs : (6 : ℤ) ≤ scale m := by unfold scale; omega
    omega
  rw [hij]

theorem rawShell_missing_close_unique (l : ℕ) (hl : 0 < l) {u v : Lattice 3}
    (hu : u ∈ rawShell l) (hv : v ∈ rawShell l)
    (hun : u ∉ shell l) (hvn : v ∉ shell l)
    (hnear : ∀ i, -2 ≤ v i - u i ∧ v i - u i ≤ 2) : u = v := by
  obtain ⟨d, hd, hu'⟩ := rawShell_missing_is_dent l hl hu hun
  obtain ⟨e, he, hv'⟩ := rawShell_missing_is_dent l hl hv hvn
  have heq := dents_close_unique (boundary l).length hd he (by
    intro i
    have hh := hnear i
    rw [hu', hv'] at hh
    simp only [Pi.add_apply] at hh
    omega)
  rw [hu', hv', heq]

theorem dent_mem_rawShell (l : ℕ) (hl : 0 < l) (i : Fin 3) :
    firstSlot l hl + dentAt (boundary l).length i ∈ rawShell l :=
  (mem_rawShell_iff _ _).mpr ⟨0, boundary_length_pos l hl, _,
    dent_mem_rawPiece (dentAt_mem _ i), rfl⟩

theorem dent_not_mem_shell (l : ℕ) (hl : 0 < l) (i : Fin 3) :
    firstSlot l hl + dentAt (boundary l).length i ∉ shell l := by
  intro hd
  have hb := bump_mem_shell l hl (bumpAt_mem i)
  have hr : residue (scale (boundary l).length)
      (firstSlot l hl + dentAt (boundary l).length i) =
      residue (scale (boundary l).length) (firstSlot l hl + bumpAt i) := by
    have he : dentAt (boundary l).length i =
        (scale (boundary l).length : ℤ) • Pi.single i 1 + bumpAt i := by
      rw [dentAt_eq]; abel
    rw [he]
    simp only [firstSlot, residue_scale_add]
  have heq := add_left_cancel (shell_residue_injective hd hb hr)
  have heqi := congrFun heq i
  simp only [dentAt, bumpAt, if_pos rfl, ite_true] at heqi
  have hs := scale_pos (boundary l).length
  omega

theorem dent_block_offset (l : ℕ) (hl : 0 < l) (i : Fin 3)
    {q c : Lattice 3} (hc : c ∈ cube 3)
    (he : firstSlot l hl + dentAt (boundary l).length i = 3 • q + c) :
    c = defectOffset i := by
  obtain ⟨origin, horigin⟩ := firstSlot_three l hl
  ext j
  have hh := congrFun he j
  rw [horigin] at hh
  simp only [Pi.add_apply, Pi.smul_apply, nsmul_eq_mul, Nat.cast_ofNat] at hh
  have hcb := (mem_cube_iff 3 _).mp hc j
  by_cases hj : j.val = i.val
  · simp only [dentAt, defectOffset, if_pos hj, scale] at hh ⊢
    push_cast at hh
    omega
  · simp only [dentAt, defectOffset, if_neg hj] at hh ⊢
    omega

theorem coordinate_step_cube {c : Lattice 3} (hc : c ∈ cube 3) (j : Fin 3)
    (e : ℤ) (he : e = 1 ∨ e = -1) (hce : 0 ≤ c j + e ∧ c j + e < 3) :
    c + Pi.single j e ∈ cube 3 := by
  apply (mem_cube_iff 3 _).mpr
  intro k
  by_cases hk : k = j
  · subst k; simpa only [Pi.add_apply, Pi.single_eq_same, Nat.cast_ofNat] using hce
  · simpa only [Pi.add_apply, Pi.single_eq_of_ne hk, add_zero] using (mem_cube_iff 3 _).mp hc k

theorem dent_transverse_neighbor (l : ℕ) (hl : 0 < l) (i j : Fin 3) (hji : j ≠ i)
    (e : ℤ) (he : e = 1 ∨ e = -1) :
    firstSlot l hl + dentAt (boundary l).length i + Pi.single j e ∈ shell l := by
  let p : Lattice 3 := firstSlot l hl + dentAt (boundary l).length i
  have hpraw := dent_mem_rawShell l hl i
  obtain ⟨q, c, hc, hp, hblock⟩ := rawShell_three_block l hpraw
  have hcoff := dent_block_offset l hl i hc hp
  have hcj : c j = 1 := by
    rw [hcoff]
    exact if_neg (fun h => hji (Fin.ext h))
  have hc' : c + Pi.single j e ∈ cube 3 :=
    coordinate_step_cube hc j e he (by rw [hcj]; rcases he with rfl | rfl <;> omega)
  have hraw : p + Pi.single j e ∈ rawShell l := by
    have hh := hblock _ hc'
    convert hh using 1 <;> dsimp [p] <;> rw [hp] <;> abel
  by_contra hn
  have hnear : ∀ k : Fin 3, -2 ≤ (p + Pi.single j e : Lattice 3) k - p k ∧
      (p + Pi.single j e : Lattice 3) k - p k ≤ 2 := by
    intro k
    simp only [Pi.add_apply, Pi.single_apply]
    split_ifs <;> rcases he with rfl | rfl <;> omega
  have heq := rawShell_missing_close_unique l hl hpraw hraw
    (dent_not_mem_shell l hl i) hn hnear
  have hh := congrFun heq j
  change p j = (p + Pi.single j e : Lattice 3) j at hh
  simp only [Pi.add_apply, Pi.single_eq_same] at hh
  rcases he with rfl | rfl <;> omega

theorem first_block_mem_shell (l : ℕ) (hl : 0 < l) {c : Lattice 3} (hc : c ∈ cube 3) :
    firstSlot l hl + c ∈ shell l := by
  have hq : (0 : Lattice 3) ∈ cube ((boundary l).length + 2) := by
    apply (mem_cube_iff _ _).mpr
    intro i; simp only [Pi.zero_apply]; omega
  have hcolor : color (boundary l).length 0 = 1 := by norm_num [color]
  have hnd : c ∉ dents (boundary l).length := by
    intro hd
    obtain ⟨i, hi⟩ := dents_eq_dentAt _ hd
    have hci := (mem_cube_iff 3 _).mp hc i
    rw [hi] at hci
    simp only [dentAt, if_pos rfl, ite_true] at hci
    have hs : (6 : ℤ) ≤ scale (boundary l).length := by unfold scale; omega
    omega
  have hp : c ∈ piece (boundary l).length 1 := by
    simpa only [smul_zero, zero_add] using mem_piece_of_block hq hcolor hc
      (by simpa only [smul_zero, zero_add] using hnd)
  exact (mem_shell_iff _ _).mpr ⟨0, boundary_length_pos l hl, c, hp, rfl⟩

end
end TranslationTiling.Kim
