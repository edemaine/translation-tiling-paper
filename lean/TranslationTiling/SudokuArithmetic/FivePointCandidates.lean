import TranslationTiling.SudokuArithmetic.FivePointAlgebra

namespace TranslationTiling.Sudoku.ArithmeticRule
open scoped Classical
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
section Field
variable {K : Type*} [Field K]

theorem row_candidate_of_values (x : Fin 8→K) (hx : Function.Injective x)
    (A D0 D1 U V s : K)
    (h0 : A≠0 ∨ D0≠0) (h1 : A≠0 ∨ D1≠0) (h2 : A≠0 ∨ 2*D1-D0≠0)
    (hH : U≠0 ∨ V≠0)
    (hv : ∀ i, A*(x i-2*s)+D0≠0 → A*(x i-s)+D1≠0 →
      A*x i+(2*D1-D0)≠0 → U*x i+V≠0 →
      U*x i+V=A*x i+(2*D1-D0) ∨
      U*x i+V=2*(A*(x i-s)+D1) ∨ U*x i+V=-(A*(x i-2*s)+D0)) :
    RowCandidate A D0 D1 U V s := by
  by_contra hn
  have hd0 : U-A≠0 ∨ V-(2*D1-D0)≠0 := by
    by_contra hh
    push_neg at hh
    exact hn (Or.inl ⟨sub_eq_zero.mp hh.1,sub_eq_zero.mp hh.2⟩)
  have hd1 : U-2*A≠0 ∨ V-(2*D1-2*A*s)≠0 := by
    by_contra hh
    push_neg at hh
    exact hn (Or.inr (Or.inl ⟨sub_eq_zero.mp hh.1,sub_eq_zero.mp hh.2⟩))
  have hd2 : U+A≠0 ∨ V-(2*A*s-D0)≠0 := by
    by_contra hh
    push_neg at hh
    apply hn
    right; right
    exact ⟨by linear_combination hh.1,sub_eq_zero.mp hh.2⟩
  let a : Fin 7→K := ![A,A,A,U,U-A,U-2*A,U+A]
  let b : Fin 7→K := ![D0-2*A*s,D1-A*s,2*D1-D0,V,
    V-(2*D1-D0),V-(2*D1-2*A*s),V-(2*A*s-D0)]
  have shifted (D t : K) (h : A≠0 ∨ D≠0) : A≠0 ∨ D-A*t≠0 := by
    by_cases hA : A=0
    · right; simpa [hA] using h.resolve_left (not_not.mpr hA)
    · exact Or.inl hA
  have hab : ∀ k, a k≠0 ∨ b k≠0 := by
    intro k
    fin_cases k
    · simpa [a,b,mul_assoc,mul_comm,mul_left_comm] using shifted D0 (2*s) h0
    · simpa [a,b] using shifted D1 s h1
    · simpa [a,b] using h2
    · simpa [a,b] using hH
    · simpa [a,b] using hd0
    · simpa [a,b] using hd1
    · simpa [a,b] using hd2
  obtain ⟨i,hi⟩ := one_good_of_seven_affines x hx a b hab
  have h0' : A*(x i-2*s)+D0≠0 := by
    convert hi 0 using 1 <;> dsimp [a,b] <;> ring
  have h1' : A*(x i-s)+D1≠0 := by
    convert hi 1 using 1 <;> dsimp [a,b] <;> ring
  have h2' : A*x i+(2*D1-D0)≠0 := by simpa [a,b] using hi 2
  have hH' : U*x i+V≠0 := by simpa [a,b] using hi 3
  rcases hv i h0' h1' h2' hH' with he | he | he
  · apply hi 4
    dsimp [a,b]
    linear_combination he
  · apply hi 5
    dsimp [a,b]
    linear_combination he
  · apply hi 6
    dsimp [a,b]
    linear_combination he

end Field
end
end TranslationTiling.Sudoku.ArithmeticRule
