import TranslationTiling.Rotations.General.Boxes

/-! Moving each voxel of a fundamental cube by an arbitrary period vector
preserves the fundamental-domain property. This avoids a separate volume
calculation for each chamber or key. -/
namespace TranslationTiling.Rotations.General
variable {d : ℕ}

def cell (L : ℕ) : Finset (Lattice d) := boxFinset 0 (fun _ => (L : ℤ)-1)

def scale (L : ℕ) (x : Lattice d) : Lattice d := (L : ℤ) • x

def relocate (L : ℕ) (home : Lattice d → Lattice d) (q : Lattice d) : Lattice d :=
  q + scale L (home q)

def periodicCell (L : ℕ) (home : Lattice d → Lattice d) : Finset (Lattice d) :=
  (cell L).image (relocate L home)

theorem cell_bounds {L : ℕ} {q : Lattice d} (hq : q ∈ cell L) (i : Fin d) :
    0 ≤ q i ∧ q i < L := by
  have hi := (mem_boxFinset _ _ _).mp hq i
  simpa only [Pi.zero_apply] using (show 0 ≤ q i ∧ q i < (L : ℤ) by dsimp at hi; omega)

theorem cell_card (L : ℕ) : (cell L : Finset (Lattice d)).card = L^d := by
  simp [cell,boxFinset,Fintype.card_piFinset,Int.card_Icc]

theorem relocate_mod {L : ℕ} (home : Lattice d → Lattice d) {q : Lattice d}
    (hq : q ∈ cell L) (i : Fin d) : relocate L home q i % L = q i := by
  change (q i + (L : ℤ) * home q i) % L = q i
  rw [Int.add_mul_emod_self_left]
  exact Int.emod_eq_of_lt (cell_bounds hq i).1 (cell_bounds hq i).2

theorem periodicCell_card (L : ℕ) (home : Lattice d → Lattice d) :
    (periodicCell L home).card = L^d := by
  rw [periodicCell,Finset.card_image_iff.mpr,cell_card]
  intro q hq r hr he
  ext i
  have hi := congrArg (fun x : Lattice d => x i % L) he
  simpa only [relocate_mod home hq,relocate_mod home hr] using hi

/-- Unique lattice translates of the relocated cell cover every lattice point. -/
theorem periodicCell_exact (L : ℕ) (hL : 0 < L) (home : Lattice d → Lattice d) :
    ∀ x : Lattice d, ∃! z : Lattice d, x ∈ (scale L z + ·) '' (periodicCell L home : Set (Lattice d)) := by
  intro x
  let q : Lattice d := fun i => x i % L
  let z : Lattice d := fun i => x i / L - home q i
  have hq : q ∈ cell L := by
    apply (mem_boxFinset _ _ _).mpr
    intro i
    have hl := Int.emod_nonneg (x i) (by omega : (L : ℤ) ≠ 0)
    have hu := Int.emod_lt_of_pos (x i) (by omega : (0 : ℤ) < L)
    dsimp [q]
    exact ⟨hl,by omega⟩
  have he : scale L z + relocate L home q = x := by
    ext i
    have hi := Int.emod_add_mul_ediv (x i) L
    change (L : ℤ) * (x i / L - home q i) + (x i % L + (L : ℤ) * home q i) = x i
    nlinarith only [hi]
  refine ⟨z,⟨relocate L home q,Finset.mem_image.mpr ⟨q,hq,rfl⟩,he⟩,?_⟩
  rintro w ⟨p,hp,hw⟩
  obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hp
  have hrq : r = q := by
    ext i
    have hi := congrArg (fun t : Lattice d => t i % L) hw
    change ((L : ℤ) * w i + relocate L home r i) % L = x i % L at hi
    rw [add_comm,Int.add_mul_emod_self_left,relocate_mod home hr] at hi
    exact hi
  subst r
  have hz := hw.trans he.symm
  ext i
  have hi := congrFun hz i
  change (L : ℤ) * w i + relocate L home q i = (L : ℤ) * z i + relocate L home q i at hi
  exact mul_left_cancel₀ (by omega : (L : ℤ) ≠ 0) (add_right_cancel hi)

end TranslationTiling.Rotations.General
