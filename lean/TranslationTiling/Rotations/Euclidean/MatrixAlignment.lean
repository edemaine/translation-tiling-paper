import TranslationTiling.Rotations.Motions
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace TranslationTiling.Rotations.Euclidean

abbrev Matrix3 := Fin 3 → Fin 3 → ℝ

def OrthonormalRows (R : Matrix3) : Prop :=
  ∀ i j, ∑ k, R i k * R j k = if i = j then 1 else 0

def UnitRow (v : Fin 3 → ℝ) : Prop :=
  ∃ j, |v j| = 1 ∧ ∀ k, k ≠ j → v k = 0

/-- Equality between the one- and two-norms characterizes a coordinate unit vector. -/
theorem unitRow_of_norm (v : Fin 3 → ℝ)
    (hnorm : ∑ i, v i ^ 2 = 1) (hwidth : ∑ i, |v i| ≤ 1) : UnitRow v := by
  simp only [Fin.sum_univ_three] at hnorm hwidth
  have h0 := abs_nonneg (v 0)
  have h1 := abs_nonneg (v 1)
  have h2 := abs_nonneg (v 2)
  have sq0 := sq_abs (v 0)
  have sq1 := sq_abs (v 1)
  have sq2 := sq_abs (v 2)
  have hs : (|v 0| + |v 1| + |v 2|) ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg (show 0 ≤ 1 - (|v 0| + |v 1| + |v 2|) by linarith)
      (show 0 ≤ 1 + (|v 0| + |v 1| + |v 2|) by positivity)]
  have m01 := mul_nonneg h0 h1
  have m02 := mul_nonneg h0 h2
  have m12 := mul_nonneg h1 h2
  have z01 : |v 0| * |v 1| = 0 := by nlinarith
  have z02 : |v 0| * |v 2| = 0 := by nlinarith
  have z12 : |v 1| * |v 2| = 0 := by nlinarith
  by_cases hz0 : v 0 = 0
  · by_cases hz1 : v 1 = 0
    · refine ⟨2, ?_, ?_⟩
      · simp [hz0, hz1] at hnorm
        rcases hnorm with h | h <;> simp [h]
      · intro k hk
        fin_cases k <;> simp_all
    · have hz2 : v 2 = 0 := by
        rcases mul_eq_zero.mp z12 with h | h
        · exact (hz1 (abs_eq_zero.mp h)).elim
        · exact abs_eq_zero.mp h
      refine ⟨1, ?_, ?_⟩
      · simp [hz0, hz2] at hnorm
        rcases hnorm with h | h <;> simp [h]
      · intro k hk
        fin_cases k <;> simp_all
  · have hz1 : v 1 = 0 := by
      rcases mul_eq_zero.mp z01 with h | h
      · exact (hz0 (abs_eq_zero.mp h)).elim
      · exact abs_eq_zero.mp h
    have hz2 : v 2 = 0 := by
      rcases mul_eq_zero.mp z02 with h | h
      · exact (hz0 (abs_eq_zero.mp h)).elim
      · exact abs_eq_zero.mp h
    refine ⟨0, ?_, ?_⟩
    · simp [hz1, hz2] at hnorm
      rcases hnorm with h | h <;> simp [h]
    · intro k hk
      fin_cases k <;> simp_all

theorem orthogonal_unit_distinct {R : Matrix3} (hR : OrthonormalRows R)
    {i j a b : Fin 3} (hij : i ≠ j)
    (hi : |R i a| = 1 ∧ ∀ k, k ≠ a → R i k = 0)
    (hj : |R j b| = 1 ∧ ∀ k, k ≠ b → R j k = 0) : a ≠ b := by
  intro he
  subst b
  have hdot := hR i j
  rw [if_neg hij, Finset.sum_eq_single a] at hdot
  · have hni : R i a ≠ 0 := by intro h; simp [h] at hi
    have hnj : R j a ≠ 0 := by intro h; simp [h] at hj
    exact (mul_ne_zero hni hnj) hdot
  · intro k _ hka; simp [hi.2 k hka]
  · simp

theorem third_unit {R : Matrix3} (hR : OrthonormalRows R)
    (h1 : UnitRow (R 1)) (h2 : UnitRow (R 2)) : UnitRow (R 0) := by
  obtain ⟨a, ha⟩ := h1
  obtain ⟨b, hb⟩ := h2
  have hab := orthogonal_unit_distinct hR (by decide : (1 : Fin 3) ≠ 2) ha hb
  have zero_at (i j : Fin 3) (hij : i ≠ j) (k : Fin 3)
      (hk : |R j k| = 1 ∧ ∀ l, l ≠ k → R j l = 0) : R i k = 0 := by
    have hh := hR i j
    rw [if_neg hij, Finset.sum_eq_single k] at hh
    · have hn : R j k ≠ 0 := by intro h; simp [h] at hk
      exact (mul_eq_zero.mp hh).resolve_right hn
    · intro l _ hl; simp [hk.2 l hl]
    · simp
  have h0a := zero_at 0 1 (by decide) a ha
  have h0b := zero_at 0 2 (by decide) b hb
  obtain ⟨c, hca, hcb⟩ : ∃ c : Fin 3, c ≠ a ∧ c ≠ b := by
    fin_cases a <;> fin_cases b <;> dsimp at hab <;> simp_all
    all_goals decide
  have cover (k : Fin 3) : k = a ∨ k = b ∨ k = c := by
    fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases k <;> simp_all
  have off (k : Fin 3) (hk : k ≠ c) : R 0 k = 0 := by
    rcases cover k with rfl | rfl | h
    · exact h0a
    · exact h0b
    · exact (hk h).elim
  have norm0 := hR 0 0
  rw [if_pos rfl, Finset.sum_eq_single c] at norm0
  · refine ⟨c, ?_, off⟩
    have hh : R 0 c ^ 2 = 1 := by nlinarith
    have hs := sq_abs (R 0 c)
    have hn := abs_nonneg (R 0 c)
    nlinarith
  · intro k _ hk; simp [off k hk]
  · simp

def gridMatrix (r : Orientation) : Matrix3 := fun i j =>
  if j = r.axes i then (r.sign i : ℝ) else 0

/-- Two transverse unit-width constraints force a full signed coordinate permutation. -/
theorem matrix_alignment {R : Matrix3} (hR : OrthonormalRows R)
    (h1 : ∑ j, |R 1 j| ≤ 1) (h2 : ∑ j, |R 2 j| ≤ 1) :
    ∃ r : Orientation, R = gridMatrix r := by
  have norm (i : Fin 3) : ∑ j, R i j ^ 2 = 1 := by
    simpa only [pow_two, ite_true] using hR i i
  have u1 := unitRow_of_norm (R 1) (norm 1) h1
  have u2 := unitRow_of_norm (R 2) (norm 2) h2
  have allUnit (i : Fin 3) : UnitRow (R i) := by
    fin_cases i
    · exact third_unit hR u1 u2
    · exact u1
    · exact u2
  choose p hp using allUnit
  have pinj : Function.Injective p := by
    intro i j he
    by_contra hne
    exact orthogonal_unit_distinct hR hne (hp i) (hp j) he
  let e : Equiv.Perm (Fin 3) := Equiv.ofBijective p ⟨pinj, Finite.surjective_of_injective pinj⟩
  have e_apply (i : Fin 3) : e i = p i := rfl
  let r : Orientation := ⟨e, fun i => decide (R i (p i) < 0)⟩
  refine ⟨r, ?_⟩
  ext i j
  by_cases hj : j = p i
  · subst j
    have hu := (hp i).1
    simp only [gridMatrix, r, e_apply, if_pos rfl, Orientation.sign]
    by_cases hn : R i (p i) < 0
    · simp [hn]
      rw [abs_of_neg hn] at hu
      linarith
    · simp [hn]
      rw [abs_of_nonneg (by linarith)] at hu
      exact hu
  · simp only [gridMatrix, r, e_apply, if_neg hj]
    exact (hp i).2 j hj

end TranslationTiling.Rotations.Euclidean
