import TranslationTiling.External.Geometry
import Mathlib.Data.Nat.Factorial.Basic

namespace TranslationTiling

/-- A finite-index period subgroup contains a whole rectangular grid.
This supplies periods suitable for a finite torus search. -/
theorem FullyPeriodic.grid {d : ℕ} {A : Set (Lattice d)} (h : FullyPeriodic A) :
    ∃ m : ℕ, 0 < m ∧ ∀ v : Lattice d, Period A (m • v) := by
  obtain ⟨P, hP, hp⟩ := h
  refine ⟨P.index.factorial, Nat.factorial_pos _, ?_⟩
  intro v
  apply hp
  exact P.nsmul_mem_of_index_ne_zero_of_dvd hP.index_ne_zero v
    (fun n hn hle => Nat.dvd_factorial hn hle)

theorem planar_grid_of_periodicity (h : PlanarPeriodicity) {F : Tile 2} (hF : Tiles F) :
    ∃ A : Set (Lattice 2), ExactTiling A {f | f ∈ F} ∧
      ∃ m : ℕ, 0 < m ∧ ∀ v : Lattice 2, Period A (m • v) := by
  obtain ⟨A, ha, hp⟩ := h F hF
  exact ⟨A, ha, hp.grid⟩

end TranslationTiling
