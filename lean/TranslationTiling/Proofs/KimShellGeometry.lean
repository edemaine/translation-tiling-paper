import TranslationTiling.Proofs.KimResidues

/-! Contacts between distinct grid translates of Kim's shell. -/

namespace TranslationTiling.Kim


theorem boundary_difference {l : ℕ} {u v : Lattice 3}
    (hu : u ∈ cube l) (hv : v ∈ cube l) (hne : u ≠ v) :
    ∃ x ∈ boundary l, ∃ y ∈ boundary l, u + x = v + y ∧ x ≠ y := by
  have hu' := (mem_cube_iff _ _).mp hu
  have hv' := (mem_cube_iff _ _).mp hv
  have hu0 := hu' 0; have hu1 := hu' 1; have hu2 := hu' 2
  have hv0 := hv' 0; have hv1 := hv' 1; have hv2 := hv' 2
  let x : Lattice 3 := ![if u 0 ≤ v 0 then (l : ℤ) - 1 else 0,
    if u 1 ≤ v 1 then v 1 - u 1 else (l : ℤ) - 1 + (v 1 - u 1),
    max (v 2 - u 2) 0]
  let y : Lattice 3 := x - (v - u)
  have hxc : x ∈ cube l := by
    apply (mem_cube_iff _ _).mpr
    intro k
    fin_cases k <;> simp [x] <;> (try split_ifs) <;> omega
  have hyc : y ∈ cube l := by
    apply (mem_cube_iff _ _).mpr
    intro k
    fin_cases k <;> simp [x, y] <;> (try split_ifs) <;> omega
  have hxb : x ∈ boundary l := by
    apply List.mem_filter.mpr
    refine ⟨hxc, ?_⟩
    simp only [decide_eq_true_eq]
    refine ⟨0, ?_⟩
    simp only [x, Matrix.cons_val_zero]
    split_ifs <;> omega
  have hyb : y ∈ boundary l := by
    apply List.mem_filter.mpr
    refine ⟨hyc, ?_⟩
    simp only [decide_eq_true_eq]
    refine ⟨1, ?_⟩
    simp [x, y]
    split_ifs <;> omega
  have hsum : u + x = v + y := by dsimp [y]; abel
  refine ⟨x, hxb, y, hyb, hsum, ?_⟩
  intro hxy
  rw [hxy] at hsum
  exact hne (add_right_cancel hsum)

theorem adjacent_add_left (t : Lattice 3) {a b : Lattice 3} (h : FaceAdjacent a b) :
    FaceAdjacent (t + a) (t + b) := by
  obtain ⟨k, hk⟩ := h
  refine ⟨k, ?_⟩
  rcases hk with hk | hk
  · exact Or.inl (by rw [hk, add_assoc])
  · exact Or.inr (by rw [hk, add_assoc])

theorem shell_contacts (l : ℕ) {u v : Lattice 3}
    (hu : u ∈ cube l) (hv : v ∈ cube l) (hne : u ≠ v) :
    ∃ a ∈ shell l, ∃ b ∈ shell l,
      FaceAdjacent ((scale (boundary l).length : ℤ) • u + a)
        ((scale (boundary l).length : ℤ) • v + b) := by
  obtain ⟨x, hx, y, hy, hsum, _⟩ := boundary_difference hu hv hne
  obtain ⟨i, hi, hix⟩ := List.mem_iff_getElem.mp hx
  obtain ⟨j, hj, hjy⟩ := List.mem_iff_getElem.mp hy
  obtain ⟨q, hq, r, hr, hcontact⟩ := pieces_adjacent (boundary l).length (i + 1) (j + 1)
    (by omega) (by omega) (by omega) (by omega)
  let a := (scale (boundary l).length : ℤ) • (boundary l)[i] + q
  let b := (scale (boundary l).length : ℤ) • (boundary l)[j] + r
  refine ⟨a, (mem_shell_iff _ _).mpr ⟨i, hi, q, hq, rfl⟩,
    b, (mem_shell_iff _ _).mpr ⟨j, hj, r, hr, rfl⟩, ?_⟩
  have hea : (scale (boundary l).length : ℤ) • u + a =
      (scale (boundary l).length : ℤ) • (u + x) + q := by
    dsimp [a]
    rw [hix, smul_add]
    abel
  have heb : (scale (boundary l).length : ℤ) • v + b =
      (scale (boundary l).length : ℤ) • (v + y) + r := by
    dsimp [b]
    rw [hjy, smul_add]
    abel
  rw [hea, heb, hsum]
  exact adjacent_add_left _ hcontact

/-- The geometric coverage and contact fields of the shell input are proved. -/
theorem shell_geometry (l : ℕ) (hl : 0 < l) :
    ExactTiling (gridCoset (scale (boundary l).length) 0) {x | x ∈ shell l} ∧
    (∀ u ∈ cube l, ∀ v ∈ cube l, u ≠ v →
      Disjoint {x | ∃ a ∈ shell l, x = (scale (boundary l).length : ℤ) • u + a}
        {x | ∃ b ∈ shell l, x = (scale (boundary l).length : ℤ) • v + b} ∧
      ∃ a ∈ shell l, ∃ b ∈ shell l,
        FaceAdjacent ((scale (boundary l).length : ℤ) • u + a)
          ((scale (boundary l).length : ℤ) • v + b)) := by
  refine ⟨shell_exactTiling l hl, ?_⟩
  intro u hu v hv hne
  exact ⟨shell_translates_disjoint l hne, shell_contacts l hu hv hne⟩

/-- To finish the Kim input, only shell connectivity and arbitrary-tiling coset
rigidity remain. Coverage and contacts are no longer proof obligations. -/
theorem rigidity_of_connected_cosets
    (connected : ∀ l : ℕ, 3 ≤ l → FaceConnected (shell l))
    (cosets : ∀ l : ℕ, 3 ≤ l → ∀ A : Set (Lattice 3),
      ExactTiling A {x | x ∈ shell l} →
        ∃ t, A = gridCoset (scale (boundary l).length) t) : Rigidity := by
  intro l hl
  obtain ⟨hfund, hcontacts⟩ := shell_geometry l (by omega)
  exact ⟨connected l hl, hfund, hcontacts, cosets l hl⟩

end TranslationTiling.Kim
