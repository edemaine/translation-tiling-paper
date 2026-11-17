import TranslationTiling.SudokuArithmetic.WordAffineAlgebra
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

namespace TranslationTiling.Sudoku.ArithmeticRule
open scoped Classical
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
section Field
variable {K : Type*} [Field K]

theorem one_good_of_seven_affines (x : Fin 8→K) (hx : Function.Injective x)
    (a b : Fin 7→K) (hab : ∀ k, a k≠0 ∨ b k≠0) :
    ∃ i, ∀ k, a k*x i+b k≠0 := by
  let bad := Finset.univ.biUnion fun k : Fin 7 => Finset.univ.filter (fun i => a k*x i+b k=0)
  have hb : bad.card≤7 := by
    have h : bad.card≤(Finset.univ : Finset (Fin 7)).card*1 := by
      apply Finset.card_biUnion_le_card_mul
      exact fun k _ => affine_roots_card_le_one _ _ (fun _ _ _ _ h => hx h) _ _ (hab k)
    simpa using h
  have hc := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ bad)
  have hgood : 0<(Finset.univ \ bad).card := by
    simp only [Finset.card_univ,Fintype.card_fin] at hc
    omega
  obtain ⟨i,hi⟩ := Finset.card_pos.mp hgood
  exact ⟨i,by simpa [bad] using hi⟩

theorem three_point_alternatives (h2 : (2:K)≠0) (l0 l1 l2 u v h : K)
    (hlinear : l2-2*l1+l0=0) (hnz : l0≠0 ∨ l1≠0)
    (ha : l0≠0 → l0=u) (hb : l1≠0 → l1=v) (hc : l2≠0 → l2=h)
    (hf : 2*v-u≠0) : h=2*v-u ∨ h=2*v ∨ h=-u := by
  by_cases h0 : l0=0
  · have h1 : l1≠0 := hnz.resolve_left (not_not.mpr h0)
    have he : l2=2*l1 := by linear_combination hlinear-h0
    have h2' : l2≠0 := by rw [he]; exact mul_ne_zero h2 h1
    right; left
    linear_combination (hb h1)*2-(hc h2')+hlinear-h0
  by_cases h1 : l1=0
  · have he : l2=-l0 := by linear_combination hlinear+2*h1
    have h2' : l2≠0 := by rw [he]; exact neg_ne_zero.mpr h0
    right; right
    linear_combination -(ha h0)-(hc h2')+hlinear+2*h1
  have h2' : l2≠0 := by
    intro hz
    apply hf
    linear_combination (ha h0)-2*(hb h1)-hlinear+hz
  left
  linear_combination -(ha h0)+2*(hb h1)-(hc h2')+hlinear

theorem five_point_coefficients (h2 : (2:K)≠0) (U0 V0 U1 V1 T : K)
    (h0 : T=2*(2*U1+V1)-V0)
    (h1 : T=2*(3*U1+V1)-(2*U0+V0)) :
    U0=U1 ∧ T=4*U0+2*V1-V0 := by
  have hu : 2*(U0-U1)=0 := by linear_combination h1-h0
  have he := sub_eq_zero.mp ((mul_eq_zero.mp hu).resolve_left h2)
  exact ⟨he,by rw [he]; linear_combination h0⟩

def RowCandidate {K : Type*} [Ring K] (A D0 D1 U V s : K) : Prop :=
  (U=A ∧ V=2*D1-D0) ∨
  (U=2*A ∧ V=2*D1-2*A*s) ∨
  (U=-A ∧ V=2*A*s-D0)

theorem intersect_row_candidates (h2 : (2:K)≠0) (h3 : (3:K)≠0)
    (A D0 D1 U V : K) (hA : A≠0)
    (h1 : RowCandidate A D0 D1 U V 1) (h2' : RowCandidate A D0 D1 U V 2) :
    U=A ∧ V=2*D1-D0 := by
  rcases h1 with h | h | h
  · exact h
  · rcases h2' with hh | hh | hh
    · exact hh
    · exfalso
      have hz : 2*A=0 := by linear_combination hh.2-h.2
      exact (mul_ne_zero h2 hA) hz
    · exfalso
      have hz : 3*A=0 := by linear_combination hh.1-h.1
      exact (mul_ne_zero h3 hA) hz
  · rcases h2' with hh | hh | hh
    · exact hh
    · exfalso
      have hz : 3*A=0 := by linear_combination h.1-hh.1
      exact (mul_ne_zero h3 hA) hz
    · exfalso
      have hz : 2*A=0 := by linear_combination h.2-hh.2
      exact (mul_ne_zero h2 hA) hz

end Field
end
end TranslationTiling.Sudoku.ArithmeticRule
