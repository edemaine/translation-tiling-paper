import TranslationTiling.SudokuArithmetic.WordAffineAlgebra

namespace TranslationTiling.Sudoku.NinePatch
open ArithmeticRule

/-- Four distinct columns and four distinct rows identify a nonzero affine
form, even though observations at its zero set impose no condition. -/
theorem overlap_unique {K : Type*} [Field K]
    (x y : Fin 4 → K) (hx : Function.Injective x) (hy : Function.Injective y)
    (A B C A' B' C' : K)
    (hn : A≠0 ∨ B≠0 ∨ C≠0) (hn' : A'≠0 ∨ B'≠0 ∨ C'≠0)
    (h : ∀ i j, A*x i+B*y j+C≠0 → A'*x i+B'*y j+C'≠0 →
      A*x i+B*y j+C=A'*x i+B'*y j+C') :
    A=A' ∧ B=B' ∧ C=C' := by
  classical
  let b := if A=0 then B else 0
  let c := if A=0 then C else 1
  let b' := if A'=0 then B' else 0
  let c' := if A'=0 then C' else 1
  have hn0 : b≠0 ∨ c≠0 := by
    by_cases ha : A=0
    · simpa [b,c,ha] using hn.resolve_left (not_not.mpr ha)
    · simp [b,c,ha]
  have hn1 : b'≠0 ∨ c'≠0 := by
    by_cases ha : A'=0
    · simpa [b',c',ha] using hn'.resolve_left (not_not.mpr ha)
    · simp [b',c',ha]
  obtain ⟨j,k,hjk,hj,hj',hk,hk'⟩ :=
    two_common_nonzero_of_four y hy b c b' c' hn0 hn1
  have row (t : Fin 4) (ht : b*y t+c≠0) (ht' : b'*y t+c'≠0) :
      A=A' ∧ B*y t+C=B'*y t+C' := by
    have ha : A≠0 ∨ B*y t+C≠0 := by
      by_cases hz : A=0
      · right; simpa [b,c,hz] using ht
      · exact Or.inl hz
    have ha' : A'≠0 ∨ B'*y t+C'≠0 := by
      by_cases hz : A'=0
      · right; simpa [b',c',hz] using ht'
      · exact Or.inl hz
    obtain ⟨i,l,hil,hi,hi',hl,hl'⟩ :=
      two_common_nonzero_of_four x hx A (B*y t+C) A' (B'*y t+C') ha ha'
    apply affine_coefficients_eq_of_two (fun he => hil (hx he))
    · simpa only [add_assoc] using h i t (by simpa only [add_assoc] using hi)
        (by simpa only [add_assoc] using hi')
    · simpa only [add_assoc] using h l t (by simpa only [add_assoc] using hl)
        (by simpa only [add_assoc] using hl')
  have rj := row j hj hj'
  have rk := row k hk hk'
  exact ⟨rj.1, affine_coefficients_eq_of_two (fun he => hjk (hy he)) rj.2 rk.2⟩

/-- Affine explanations on every seven-row translate glue to one global
explanation. The coefficients here use global row coordinates. -/
theorem glue_patches {K : Type*} [Field K]
    (x : Fin 9 → K) (y : Int → K)
    (hx : Function.Injective (fun i : Fin 4 => x ⟨i.val, by omega⟩))
    (hy : ∀ t : Int, Function.Injective (fun j : Fin 4 => y (t+j.val)))
    (W : Fin 9 → Int → K)
    (hpatch : ∀ t : Int, ∃ abc : K × K × K,
      (abc.1≠0 ∨ abc.2.1≠0 ∨ abc.2.2≠0) ∧
      ∀ n m, t≤m → m<t+7 → abc.1*x n+abc.2.1*y m+abc.2.2≠0 →
        W n m=abc.1*x n+abc.2.1*y m+abc.2.2) :
    ∃ abc : K × K × K, (abc.1≠0 ∨ abc.2.1≠0 ∨ abc.2.2≠0) ∧
      ∀ n m, abc.1*x n+abc.2.1*y m+abc.2.2≠0 →
        W n m=abc.1*x n+abc.2.1*y m+abc.2.2 := by
  classical
  choose c hc using hpatch
  have adjacent (t : Int) : c (t+1)=c t := by
    have he := overlap_unique _ _ hx (hy (t+1))
      (c (t+1)).1 (c (t+1)).2.1 (c (t+1)).2.2
      (c t).1 (c t).2.1 (c t).2.2 (hc (t+1)).1 (hc t).1 (by
        intro i j hi hj
        let n : Fin 9 := ⟨i.val, by omega⟩
        let m : Int := t+1+j.val
        have hjlt := j.isLt
        exact ((hc (t+1)).2 n m (by dsimp [m]; omega) (by dsimp [m]; omega) hi).symm.trans
          ((hc t).2 n m (by dsimp [m]; omega) (by dsimp [m]; omega) hj))
    exact Prod.ext he.1 (Prod.ext he.2.1 he.2.2)
  have constant (t : Int) : c t=c 0 := by
    induction t using Int.induction_on with
    | zero => rfl
    | succ i ih => exact (adjacent i).trans ih
    | pred i ih =>
      have h := adjacent (-(i:Int)-1)
      simp only [sub_add_cancel] at h
      simpa only [show -(i:Int)-1 = -((i+1:Nat):Int) by omega] using h.symm.trans ih
  refine ⟨c 0, (hc 0).1, ?_⟩
  intro n m hm
  have h := (hc m).2 n m (le_refl _) (by omega)
  rw [constant m] at h
  exact h hm

end TranslationTiling.Sudoku.NinePatch
