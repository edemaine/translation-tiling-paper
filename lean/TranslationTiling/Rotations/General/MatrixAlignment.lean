import TranslationTiling.Rotations.General.Motions
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

namespace TranslationTiling.Rotations.General
open scoped BigOperators

abbrev RealMatrix (d : ℕ) := Matrix (Fin d) (Fin d) ℝ

def OrthonormalRows {d : ℕ} (R : RealMatrix d) : Prop :=
  ∀ i j, ∑ k, R i k * R j k = if i = j then 1 else 0

def UnitRow {d : ℕ} (v : Fin d → ℝ) : Prop :=
  ∃ j, |v j| = 1 ∧ ∀ k, k ≠ j → v k = 0

/-- Equality of the one- and two-norm bounds forces a coordinate unit vector. -/
theorem unitRow_of_norm {d : ℕ} (v : Fin d → ℝ)
    (hnorm : ∑ i, v i ^ 2 = 1) (hwidth : ∑ i, |v i| ≤ 1) : UnitRow v := by
  have hab (i : Fin d) : |v i| ≤ 1 :=
    (Finset.single_le_sum (fun j _ => abs_nonneg (v j)) (Finset.mem_univ i)).trans hwidth
  have hnonneg (i : Fin d) : 0 ≤ |v i| - v i ^ 2 := by
    have := abs_nonneg (v i)
    nlinarith [sq_abs (v i),hab i]
  have hsum : ∑ i, (|v i| - v i ^ 2) = 0 := by
    rw [Finset.sum_sub_distrib,hnorm]
    have hn : 0 ≤ ∑ i, (|v i| - v i ^ 2) := Finset.sum_nonneg (fun i _ => hnonneg i)
    rw [Finset.sum_sub_distrib,hnorm] at hn
    linarith
  have heach (i : Fin d) : |v i| - v i ^ 2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hnonneg i)).mp hsum i (Finset.mem_univ i)
  have hex : ∃ j, v j ≠ 0 := by
    by_contra! hz
    simp only [hz,zero_pow (by decide : 2 ≠ 0),Finset.sum_const_zero] at hnorm
    norm_num at hnorm
  obtain ⟨j,hj⟩ := hex
  have hu : |v j| = 1 := by
    have hp := abs_pos.mpr hj
    have he := heach j
    nlinarith [sq_abs (v j)]
  refine ⟨j,hu,fun k hk => ?_⟩
  have hp : |v j| + |v k| ≤ ∑ i, |v i| := by
    have h := Finset.sum_le_sum_of_subset_of_nonneg
      (show ({j,k} : Finset (Fin d)) ⊆ Finset.univ from Finset.subset_univ _)
      (fun i _ _ => abs_nonneg (v i))
    simpa only [Finset.sum_pair (Ne.symm hk)] using h
  have hz : |v k| = 0 := by linarith [abs_nonneg (v k)]
  exact abs_eq_zero.mp hz

theorem column_norm {d : ℕ} {R : RealMatrix d} (hR : OrthonormalRows R) (j : Fin d) :
    ∑ i, R i j ^ 2 = 1 := by
  have hr : R * R.transpose = 1 := by
    ext i k
    simpa only [Matrix.mul_apply,Matrix.transpose_apply,Matrix.one_apply] using hR i k
  have hc : R.transpose * R = 1 := (mul_eq_one_comm).mp hr
  have h := congrArg (fun M : RealMatrix d => M j j) hc
  simpa only [Matrix.mul_apply,Matrix.transpose_apply,Matrix.one_apply,ite_true,pow_two] using h

theorem orthogonal_unit_distinct {d : ℕ} {R : RealMatrix d} (hR : OrthonormalRows R)
    {i j a b : Fin d} (hij : i ≠ j)
    (hi : |R i a| = 1 ∧ ∀ k, k ≠ a → R i k = 0)
    (hj : |R j b| = 1 ∧ ∀ k, k ≠ b → R j k = 0) : a ≠ b := by
  intro he
  subst b
  have hdot := hR i j
  rw [if_neg hij,Finset.sum_eq_single a] at hdot
  · have hni : R i a ≠ 0 := by intro h; simp [h] at hi
    have hnj : R j a ≠ 0 := by intro h; simp [h] at hj
    exact (mul_ne_zero hni hnj) hdot
  · intro k _ hka; simp [hi.2 k hka]
  · simp

/-- Once all transverse rows are coordinate vectors, the axial row is too. -/
theorem remaining_unit {d : ℕ} {R : RealMatrix d} (hR : OrthonormalRows R) (a : Fin d)
    (hu : ∀ i, i ≠ a → UnitRow (R i)) : UnitRow (R a) := by
  have hnorm : ∑ j, R a j ^ 2 = 1 := by
    simpa only [ite_true,pow_two] using hR a a
  have hab (j : Fin d) : |R a j| = 0 ∨ |R a j| = 1 := by
    by_cases hj : R a j = 0
    · exact Or.inl (by simp [hj])
    · right
      have ho (i : Fin d) (hi : i ≠ a) : R i j = 0 := by
        obtain ⟨k,hk⟩ := hu i hi
        by_cases he : j = k
        · subst k
          have hcol := column_norm hR j
          have hp : R a j ^ 2 + R i j ^ 2 ≤ ∑ k, R k j ^ 2 := by
            have h := Finset.sum_le_sum_of_subset_of_nonneg
              (show ({a,i} : Finset (Fin d)) ⊆ Finset.univ from Finset.subset_univ _)
              (fun k _ _ => sq_nonneg (R k j))
            simpa only [Finset.sum_pair (Ne.symm hi)] using h
          have hs : R i j ^ 2 = 1 := by nlinarith [sq_abs (R i j),hk.1]
          have hz : R a j = 0 := by nlinarith [sq_nonneg (R a j)]
          exact False.elim (hj hz)
        · exact hk.2 j he
      have hc := column_norm hR j
      rw [Finset.sum_eq_single a] at hc
      · have hn := abs_nonneg (R a j)
        nlinarith [sq_abs (R a j)]
      · intro i _ hi; simp [ho i hi]
      · simp
  have hsum : ∑ j, |R a j| = 1 := by
    have he (j : Fin d) : |R a j| = R a j ^ 2 := by
      rcases hab j with h | h <;> nlinarith [sq_abs (R a j)]
    simpa only [he] using hnorm
  exact unitRow_of_norm _ hnorm hsum.le

/-- Matrix of a signed coordinate permutation, allowing either determinant sign. -/
def gridMatrix {d : ℕ} (r : Orientation d) : RealMatrix d := fun i j =>
  if j = r.axes i then (r.sign i : ℝ) else 0

/-- A unit-width constraint in every transverse direction forces grid alignment. -/
theorem matrix_alignment {d : ℕ} {R : RealMatrix d} (hR : OrthonormalRows R)
    (a : Fin d) (hw : ∀ i, i ≠ a → ∑ j, |R i j| ≤ 1) :
    ∃ r : Orientation d, R = gridMatrix r := by
  have norm (i : Fin d) : ∑ j, R i j ^ 2 = 1 := by
    simpa only [pow_two,ite_true] using hR i i
  have hu (i : Fin d) (hi : i ≠ a) : UnitRow (R i) :=
    unitRow_of_norm _ (norm i) (hw i hi)
  have allUnit (i : Fin d) : UnitRow (R i) := by
    by_cases hi : i = a
    · subst i; exact remaining_unit hR a hu
    · exact hu i hi
  choose p hp using allUnit
  have pinj : Function.Injective p := by
    intro i j he
    by_contra hne
    exact orthogonal_unit_distinct hR hne (hp i) (hp j) he
  let e : Equiv.Perm (Fin d) := Equiv.ofBijective p ⟨pinj,Finite.surjective_of_injective pinj⟩
  have e_apply (i : Fin d) : e i = p i := rfl
  let r : Orientation d := ⟨e,fun i => decide (R i (p i) < 0)⟩
  refine ⟨r,?_⟩
  ext i j
  by_cases hj : j = p i
  · subst j
    have hh := (hp i).1
    simp only [gridMatrix,r,e_apply,if_pos rfl,Orientation.sign]
    by_cases hn : R i (p i) < 0
    · simp [hn]
      rw [abs_of_neg hn] at hh
      linarith
    · simp [hn]
      rw [abs_of_nonneg (by linarith)] at hh
      exact hh
  · simp only [gridMatrix,r,e_apply,if_neg hj]
    exact (hp i).2 j hj

end TranslationTiling.Rotations.General
