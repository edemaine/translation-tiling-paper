import TranslationTiling.MSS.FrameGeometry

/-! A check on the one-point local forcing argument in MSS Lemma 2.1.
This does not refute the global rigidity theorem. It shows that covering the
neighboring cube center while avoiding the original copy does not alone force
the intended neighbor. A proof of rigidity must use the remaining coverage. -/

namespace TranslationTiling.MSS

open scoped Classical

theorem bump_corner_mem : (![214, 1, 1] : Lattice 3) ∈ baseShape := by
  apply Finset.mem_union_right
  apply Finset.mem_biUnion.mpr
  refine ⟨0, Finset.mem_univ _, Finset.mem_image.mpr ?_⟩
  refine ⟨![1, 1, 1], ?_, ?_⟩
  · apply (mem_frame_iff 1 (by decide) _).mpr
    refine ⟨?_, 0, Or.inr rfl⟩
    intro k; fin_cases k <;> simp
  · funext k; fin_cases k <;> simp [marker, scale]

/-- Two copies can be disjoint even when the second covers `201 e₂` at a bump
rather than at its cube center. Thus that local condition is insufficient. -/
theorem unintended_neighbor :
    Disjoint {x | x ∈ baseShape}
      {x | ∃ u ∈ baseShape, x = (![-214, -1, 200] : Lattice 3) + u} ∧
    (∃ u ∈ baseShape, (scale : ℤ) • Pi.single (2 : Fin 3) 1 =
      (![-214, -1, 200] : Lattice 3) + u) ∧
    (![-214, -1, 200] : Lattice 3) ≠ (scale : ℤ) • Pi.single (2 : Fin 3) 1 := by
  refine ⟨?_, ⟨![214, 1, 1], bump_corner_mem, ?_⟩, ?_⟩
  · apply Set.disjoint_left.mpr
    rintro x hx ⟨u, hu, rfl⟩
    obtain ⟨i, hi⟩ := baseShape_bounds _ hx
    obtain ⟨j, hj⟩ := baseShape_bounds _ hu
    have hi0 := hi 0; have hi1 := hi 1; have hi2 := hi 2
    have hj0 := hj 0; have hj1 := hj 1; have hj2 := hj 2
    fin_cases i <;> fin_cases j <;>
      simp [bodyCenter, bodyRadius] at hi0 hi1 hi2 hj0 hj1 hj2 <;> omega
  · funext k; fin_cases k <;> simp [scale]
  · intro he
    have := congrFun he 0
    change (-214 : ℤ) = 201 * (Pi.single (2 : Fin 3) 1 : Lattice 3) 0 at this
    have hz : (Pi.single (2 : Fin 3) 1 : Lattice 3) 0 = 0 :=
      Pi.single_eq_of_ne (by decide : (0 : Fin 3) ≠ 2) 1
    rw [hz] at this
    norm_num [scale] at this

end TranslationTiling.MSS
