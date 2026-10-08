import TranslationTiling.Proofs.KimResidues
import Mathlib.Tactic.Ring

/-! The shell before its six unit modifications consists of aligned 3-blocks. -/

namespace TranslationTiling.Kim

noncomputable section
open scoped Classical

def rawShell (l : ℕ) : Tile 3 :=
  let X := boundary l
  X.zipIdx |>.flatMap fun p =>
    (rawPiece X.length (p.2 + 1)).map fun q => (scale X.length : ℤ) • p.1 + q

theorem mem_rawShell_iff (l : ℕ) (v : Lattice 3) : v ∈ rawShell l ↔
    ∃ (i : ℕ) (hi : i < (boundary l).length), ∃ q ∈ rawPiece (boundary l).length (i + 1),
      v = (scale (boundary l).length : ℤ) • (boundary l)[i] + q := by
  simp only [rawShell, List.mem_flatMap]
  rw [List.exists_mem_zipIdx']
  simp only [List.mem_map]
  exact exists_congr fun i => exists_congr fun hi =>
    exists_congr fun q => and_congr_right fun _ => eq_comm

def firstSlot (l : ℕ) (hl : 0 < l) : Lattice 3 :=
  (scale (boundary l).length : ℤ) • (boundary l)[0]'(boundary_length_pos l hl)

theorem firstSlot_three (l : ℕ) (hl : 0 < l) : ∃ q : Lattice 3, firstSlot l hl = 3 • q := by
  refine ⟨((boundary l).length + 2 : ℤ) • (boundary l)[0]'(boundary_length_pos l hl), ?_⟩
  ext i
  simp only [firstSlot, Pi.smul_apply, smul_eq_mul, scale]
  push_cast
  ring

theorem bump_mem_shell (l : ℕ) (hl : 0 < l) {u : Lattice 3} (hu : u ∈ bumps) :
    firstSlot l hl + u ∈ shell l := by
  apply (mem_shell_iff _ _).mpr
  refine ⟨0, boundary_length_pos l hl, u, ?_, rfl⟩
  rw [piece_eq, if_pos rfl]
  exact List.mem_append_right _ hu

theorem mem_shell_raw_or_bump (l : ℕ) (hl : 0 < l) {v : Lattice 3} (hv : v ∈ shell l) :
    v ∈ rawShell l ∨ ∃ u ∈ bumps, v = firstSlot l hl + u := by
  obtain ⟨i, hi, q, hq, he⟩ := (mem_shell_iff _ _).mp hv
  rcases mem_piece_cases hq with hq | hq
  · exact Or.inl ((mem_rawShell_iff _ _).mpr ⟨i, hi, q, hq.1, he⟩)
  · have hi0 : i = 0 := by omega
    subst i
    exact Or.inr ⟨q, hq.2, he⟩

theorem rawShell_bump_not_mem (l : ℕ) (hl : 0 < l) {u : Lattice 3} (hu : u ∈ bumps) :
    firstSlot l hl + u ∉ rawShell l := by
  intro hv
  obtain ⟨i, hi, q, hq, he⟩ := (mem_rawShell_iff _ _).mp hv
  have hres := congrArg (residue (scale (boundary l).length)) he
  have hres' : residue (scale (boundary l).length) u = q := by
    simpa only [firstSlot, residue_scale_add, residue_eq_self (rawPiece_mem_cube hq)] using hres
  have hu1 : residue (scale (boundary l).length) u ∈ rawPiece (boundary l).length 1 :=
    dent_mem_rawPiece (bump_residue_mem_dents hu)
  rw [hres'] at hu1
  have hi1 := rawPiece_color_unique hq hu1
  have hi0 : i = 0 := by omega
  subst i
  have heq : u = q := add_left_cancel he
  have hcube := (mem_cube_iff _ _).mp (rawPiece_mem_cube hq)
  rw [← heq] at hcube
  simp only [bumps, List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl
  · have hh := (hcube 0).1; change 0 ≤ (-1 : ℤ) at hh; omega
  · have hh := (hcube 1).1; change 0 ≤ (-1 : ℤ) at hh; omega
  · have hh := (hcube 2).1; change 0 ≤ (-1 : ℤ) at hh; omega

theorem rawShell_missing_is_dent (l : ℕ) (hl : 0 < l) {v : Lattice 3}
    (hv : v ∈ rawShell l) (hn : v ∉ shell l) :
    ∃ u ∈ dents (boundary l).length, v = firstSlot l hl + u := by
  obtain ⟨i, hi, u, hu, he⟩ := (mem_rawShell_iff _ _).mp hv
  by_cases hd : u ∈ dents (boundary l).length
  · have hi1 := rawPiece_color_unique hu (dent_mem_rawPiece hd)
    have hi0 : i = 0 := by omega
    subst i
    exact ⟨u, hd, he⟩
  · have hp : u ∈ piece (boundary l).length (i + 1) := by
      rw [piece_eq]
      split_ifs
      · exact List.mem_append_left _ (List.mem_filter.mpr ⟨hu, by simpa using hd⟩)
      · exact hu
    exact (hn ((mem_shell_iff _ _).mpr ⟨i, hi, u, hp, he⟩)).elim

theorem rawShell_three_block (l : ℕ) {v : Lattice 3} (hv : v ∈ rawShell l) :
    ∃ q c : Lattice 3, c ∈ cube 3 ∧ v = 3 • q + c ∧
      ∀ d ∈ cube 3, 3 • q + d ∈ rawShell l := by
  obtain ⟨i, hi, u, hu, he⟩ := (mem_rawShell_iff _ _).mp hv
  obtain ⟨r, hr, hcolor, c, hc, hur⟩ := (mem_rawPiece _ _ _).mp hu
  let slot : Lattice 3 := ((boundary l).length + 2 : ℤ) • (boundary l)[i]
  have hslot : (scale (boundary l).length : ℤ) • (boundary l)[i] = 3 • slot := by
    ext j
    simp only [slot, Pi.smul_apply, smul_eq_mul, scale]
    push_cast
    ring
  refine ⟨slot + r, c, hc, ?_, ?_⟩
  · rw [he, hur, hslot, smul_add]
    abel
  · intro d hd
    apply (mem_rawShell_iff _ _).mpr
    refine ⟨i, hi, 3 • r + d, (mem_rawPiece _ _ _).mpr ⟨r, hr, hcolor, d, hd, rfl⟩, ?_⟩
    rw [hslot, smul_add]
    abel

end
end TranslationTiling.Kim
