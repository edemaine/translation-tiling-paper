import TranslationTiling.Proofs.KimDefectGeometry

/-! The transverse dent rim forces a bump of the matching orientation. -/

namespace TranslationTiling.Kim

noncomputable section
open scoped Classical

theorem exactTiling_centers_eq {A F : Set (Lattice 3)} (h : ExactTiling A F)
    {a b u v : Lattice 3} (ha : a ∈ A) (hb : b ∈ A) (hu : u ∈ F) (hv : v ∈ F)
    (he : a + u = b + v) : a = b := by
  have hh := h.1 (a₁ := (⟨a, ha⟩, ⟨u, hu⟩)) (a₂ := (⟨b, hb⟩, ⟨v, hv⟩)) he
  exact congrArg (fun p => p.1.val) hh

theorem raw_block_cannot_cover_dent (l : ℕ) (hl : 0 < l) {A : Set (Lattice 3)}
    (hA : ExactTiling A {v | v ∈ shell l}) {a b v : Lattice 3}
    (ha : a ∈ A) (hb : b ∈ A) (hne : b ≠ a) (i : Fin 3)
    (hv : v ∈ rawShell l)
    (he : b + v = a + (firstSlot l hl + dentAt (boundary l).length i)) : False := by
  obtain ⟨j, k, hji, hki, hjk⟩ :
      ∃ j k : Fin 3, j ≠ i ∧ k ≠ i ∧ j ≠ k := by
    fin_cases i
    · exact ⟨1, 2, by decide, by decide, by decide⟩
    · exact ⟨0, 2, by decide, by decide, by decide⟩
    · exact ⟨0, 1, by decide, by decide, by decide⟩
  obtain ⟨q, c, hc, hvc, hblock⟩ := rawShell_three_block l hv
  let e : Fin 3 → ℤ := fun r => if c r ≤ 1 then 1 else -1
  have hes (r : Fin 3) : e r = 1 ∨ e r = -1 := by
    dsimp [e]; split_ifs
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hstep (r : Fin 3) : c + Pi.single r (e r) ∈ cube 3 := by
    apply coordinate_step_cube hc r (e r)
    have hcr := (mem_cube_iff 3 _).mp hc r
    dsimp [e]; split_ifs <;> omega
  have hraw (r : Fin 3) : v + Pi.single r (e r) ∈ rawShell l := by
    have hh := hblock _ (hstep r)
    rw [hvc]
    convert hh using 1
    abel
  have missing (r : Fin 3) (hri : r ≠ i) : v + Pi.single r (e r) ∉ shell l := by
    intro hv'
    have hp := dent_transverse_neighbor l hl i r hri (e r) (hes r)
    apply hne
    apply exactTiling_centers_eq hA hb ha hv' hp
    calc
      b + (v + Pi.single r (e r)) = (b + v) + Pi.single r (e r) := by abel
      _ = a + (firstSlot l hl + dentAt (boundary l).length i + Pi.single r (e r)) := by
        rw [he]; abel
  have hclose : ∀ r : Fin 3,
      -2 ≤ (v + Pi.single k (e k) : Lattice 3) r - (v + Pi.single j (e j) : Lattice 3) r ∧
      (v + Pi.single k (e k) : Lattice 3) r - (v + Pi.single j (e j) : Lattice 3) r ≤ 2 := by
    intro r
    have hej := hes j
    have hek := hes k
    simp only [Pi.add_apply, Pi.single_apply]
    split_ifs <;> omega
  have heq := rawShell_missing_close_unique l hl (hraw j) (hraw k)
    (missing j hji) (missing k hki) hclose
  have hh := congrFun heq j
  simp only [Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hjk] at hh
  have hej := hes j
  omega

theorem shell_forward_step (l : ℕ) (hl : 0 < l) {A : Set (Lattice 3)}
    (hA : ExactTiling A {v | v ∈ shell l}) {a : Lattice 3} (ha : a ∈ A) (i : Fin 3) :
    a + (scale (boundary l).length : ℤ) • Pi.single i 1 ∈ A := by
  let p := firstSlot l hl + dentAt (boundary l).length i
  obtain ⟨⟨b, v⟩, he⟩ := hA.2 (a + p)
  have hne : b.val ≠ a := by
    intro hb
    have hev : v.val = p := by
      change b.val + v.val = a + p at he
      rw [hb] at he
      exact add_left_cancel he
    have hh := v.property
    rw [hev] at hh
    exact dent_not_mem_shell l hl i hh
  rcases mem_shell_raw_or_bump l hl v.property with hv | hv
  · exact (raw_block_cannot_cover_dent l hl hA ha b.property hne i hv he).elim
  · obtain ⟨u, hu, hv⟩ := hv
    obtain ⟨j, huj⟩ := bumps_eq_bumpAt hu
    have hji : j = i := by
      by_contra hji
      let c := bumpAt j + Pi.single j 1
      have hc : c ∈ cube 3 := by
        apply (mem_cube_iff 3 _).mpr
        intro r
        by_cases hr : r = j
        · subst r
          simp only [c, Pi.add_apply, bumpAt, ite_true, Pi.single_eq_same]
          omega
        · have hrv : r.val ≠ j.val := fun h => hr (Fin.ext h)
          simp only [c, Pi.add_apply, bumpAt, if_neg hrv, Pi.single_eq_of_ne hr]
          omega
      have hbpoint := first_block_mem_shell l hl hc
      have hapoint := dent_transverse_neighbor l hl i j hji 1 (Or.inl rfl)
      apply hne
      apply exactTiling_centers_eq hA b.property ha hbpoint hapoint
      have he' := he
      change b.val + v.val = a + p at he'
      rw [hv, huj] at he'
      dsimp [c, p]
      calc
        _ = (b.val + (firstSlot l hl + bumpAt j)) + Pi.single j 1 := by abel
        _ = a + (firstSlot l hl + dentAt (boundary l).length i + Pi.single j 1) := by
          rw [he']; dsimp [p]; abel
    have hb : b.val = a + (scale (boundary l).length : ℤ) • Pi.single i 1 := by
      change b.val + v.val = a + p at he
      rw [hv, huj, hji] at he
      dsimp [p] at he
      rw [dentAt_eq] at he
      have he' : b.val + (firstSlot l hl + bumpAt i) =
          (a + (scale (boundary l).length : ℤ) • Pi.single i 1) +
            (firstSlot l hl + bumpAt i) := by
        convert he using 1
        abel
      exact add_right_cancel he'
    exact hb ▸ b.property

end
end TranslationTiling.Kim
