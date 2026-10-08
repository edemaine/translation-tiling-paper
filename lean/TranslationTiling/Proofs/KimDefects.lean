import TranslationTiling.Proofs.KimBlocks

/-! Coordinate descriptions of the shell's three bumps and three dents. -/

namespace TranslationTiling.Kim

noncomputable section
open scoped Classical

def bumpAt (i : Fin 3) : Lattice 3 := fun j => if j.val = i.val then -1 else 1
def defectOffset (i : Fin 3) : Lattice 3 := fun j => if j.val = i.val then 2 else 1
def dentAt (m : ℕ) (i : Fin 3) : Lattice 3 :=
  fun j => if j.val = i.val then (scale m : ℤ) - 1 else 1

theorem bumpAt_mem (i : Fin 3) : bumpAt i ∈ bumps := by
  simp only [bumps, List.mem_cons, List.not_mem_nil, or_false]
  fin_cases i
  · apply Or.inl; ext j; fin_cases j <;> norm_num [bumpAt]
  · apply Or.inr ∘ Or.inl; ext j; fin_cases j <;> norm_num [bumpAt]
  · apply Or.inr ∘ Or.inr; ext j; fin_cases j <;> norm_num [bumpAt]

theorem dents_eq_dentAt (m : ℕ) {u : Lattice 3} (hu : u ∈ dents m) :
    ∃ i : Fin 3, u = dentAt m i := by
  simp only [dents, List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl
  · refine ⟨0, ?_⟩; ext j; fin_cases j <;> norm_num [dentAt]
  · refine ⟨1, ?_⟩; ext j; fin_cases j <;> norm_num [dentAt]
  · refine ⟨2, ?_⟩; ext j; fin_cases j <;> norm_num [dentAt]

theorem dentAt_eq (m : ℕ) (i : Fin 3) :
    dentAt m i = bumpAt i + (scale m : ℤ) • Pi.single i 1 := by
  ext j
  by_cases hj : j = i
  · subst j
    simp only [dentAt, bumpAt, ite_true, Pi.add_apply, Pi.smul_apply,
      Pi.single_eq_same, smul_eq_mul, mul_one]
    omega
  · have hjv : j.val ≠ i.val := fun h => hj (Fin.ext h)
    simp only [dentAt, bumpAt, if_neg hjv, Pi.add_apply, Pi.smul_apply,
      Pi.single_eq_of_ne hj, smul_eq_mul, mul_zero, add_zero]

theorem bump_coordinate (u : Lattice 3) (hu : u ∈ bumps) (i : Fin 3) :
    u i = -1 ∨ u i = 1 := by
  simp only [bumps, List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl <;> fin_cases i <;> norm_num

end
end TranslationTiling.Kim
