import TranslationTiling.Rotations.Motions
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring

namespace TranslationTiling.Rotations

open scoped BigOperators

/-- An integral central moment; multiplying by the cardinality avoids division. -/
def moment (F : Finset (Lattice 3)) (i : Fin 3) (k : ℕ) : ℤ :=
  ∑ x ∈ F, ((F.card : ℤ) * x i - ∑ y ∈ F, y i) ^ k

/-- Translation cancels from central moments, and signed axis permutations
only permute the coordinates and multiply an odd moment by the sign. -/
theorem moment_motion (m : Motion) (F : Finset (Lattice 3)) (i : Fin 3) (k : ℕ) :
    moment (F.image m.apply) i k = m.orientation.sign i ^ k *
      moment F (m.orientation.axes i) k := by
  have hinj : ∀ x ∈ F, ∀ y ∈ F, m.apply x = m.apply y → x = y :=
    fun _ _ _ _ he => m.injective he
  have sum_coord : (∑ y ∈ F, m.apply y i) =
      (F.card : ℤ) * m.offset i + m.orientation.sign i *
        (∑ y ∈ F, y (m.orientation.axes i)) := by
    simp [Motion.apply, Finset.sum_add_distrib, ← Finset.mul_sum]
  unfold moment
  rw [Finset.card_image_of_injective F m.injective, Finset.sum_image hinj,
    Finset.sum_image hinj, sum_coord]
  calc
    _ = ∑ x ∈ F, m.orientation.sign i ^ k *
        ((F.card : ℤ) * x (m.orientation.axes i) -
          ∑ y ∈ F, y (m.orientation.axes i)) ^ k := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [← mul_pow]
      congr 1
      simp only [Motion.apply, Pi.add_apply, Orientation.linear_apply]
      ring
    _ = _ := (Finset.mul_sum ..).symm

end TranslationTiling.Rotations
