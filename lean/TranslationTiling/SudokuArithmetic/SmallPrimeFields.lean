import TranslationTiling.SudokuArithmetic.FivePointAlgebra
namespace TranslationTiling.Sudoku.ArithmeticRule.SmallPrime
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option synthInstance.maxSize 10000
set_option maxSynthPendingDepth 10000

def ThirdTest (p : Nat) : Prop :=
  ∀ A D0 D1 U V : ZMod p,
    (A ≠ 0 ∨ D0 ≠ 0) → (A ≠ 0 ∨ D1 ≠ 0) →
    (A ≠ 0 ∨ 2*D1-D0 ≠ 0) → (U ≠ 0 ∨ V ≠ 0) →
    (U≠0 ∨ ∃ x : ZMod p, U*x+V=A*x+2*D1-D0 ∧ A*x+2*D1-D0 ≠ 0) →
    (∀ s : ZMod p, s=-2 ∨ s=-1 ∨ s=1 ∨ s=2 → ∀ x : ZMod p,
      A*(x-2*s)+D0 ≠ 0 → A*(x-s)+D1 ≠ 0 → A*x+2*D1-D0 ≠ 0 → U*x+V ≠ 0 →
      U*x+V=A*x+2*D1-D0 ∨ U*x+V=2*(A*(x-s)+D1) ∨ U*x+V=-(A*(x-2*s)+D0)) →
    U=A ∧ V=2*D1-D0

theorem thirdTest5 : ThirdTest 5 := by
  unfold ThirdTest
  decide +kernel

theorem thirdTest7 : ThirdTest 7 := by
  unfold ThirdTest
  decide +kernel

def MidTest (p : Nat) (t : Nat) : Prop :=
  ∀ a b c : Fin p,
    let A : ZMod p := a.val
    let B : ZMod p := b.val
    let C : ZMod p := c.val
    ∀ U V : ZMod p,
    (∀ j : Fin 3, A≠0 ∨ B*(2*j.val:ZMod p)+C≠0) →
    (A≠0 ∨ B*(t:ZMod p)+C≠0) → (U≠0 ∨ V≠0) →
    (∀ z : ZMod p, z=1 ∨ z=-1 → ∀ x : ZMod p,
      ∃ a b : ZMod p, (a≠0 ∨ b≠0) ∧
        (∀ j : Fin 3, let y : ZMod p := 2*j.val;
          let n := x+z*y;
          a*n+b≠0 → A*n+B*y+C≠0 → a*n+b=A*n+B*y+C) ∧
        (let n := x+z*(t:ZMod p);
          a*n+b≠0 → U*n+V≠0 → a*n+b=U*n+V)) →
    U=A ∧ V=B*(t:ZMod p)+C


/-- The only possible target values after three affine line observations. -/
def MidAlternative (p t : Nat) (a b H : ZMod p) : Prop :=
  let f := a*t+b
  H=0 ∨ f=0 ∨ H=f ∨
    (b=0 ∧ (H=2*f-4*a ∨ H=-f+4*a)) ∨
    (2*a+b=0 ∧ (2*H=f+2*a ∨ 2*H=f-2*a)) ∨
    (4*a+b=0 ∧ (H=-f-4*a ∨ H=2*f+4*a))
def MidAlternativeTest (p t : Nat) : Prop :=
  ∀ a b c d H : ZMod p, (c≠0 ∨ d≠0) →
    (∀ j : Fin 3, c*(2*j.val)+d≠0 → a*(2*j.val)+b≠0 → c*(2*j.val)+d=a*(2*j.val)+b) →
    (c*t+d≠0 → H≠0 → c*t+d=H) → MidAlternative p t a b H

def FastMidTest (p t : Nat) : Prop :=
  ∀ a b c : Fin p,
    let A : ZMod p := a.val
    let B : ZMod p := b.val
    let C : ZMod p := c.val
    ∀ U V : ZMod p,
      (∀ j : Fin 3, A≠0 ∨ B*(2*j.val)+C≠0) →
      (A≠0 ∨ B*t+C≠0) → (U≠0 ∨ V≠0) →
      (∀ z : ZMod p, z=1 ∨ z=-1 → ∀ x : ZMod p,
        MidAlternative p t (A*z+B) (A*x+C) (U*(x+z*t)+V)) →
      U=A ∧ V=B*t+C

theorem midAlternative5_1 : MidAlternativeTest 5 1 := by
  unfold MidAlternativeTest MidAlternative
  decide +kernel

theorem fastMid5_1 : FastMidTest 5 1 := by
  unfold FastMidTest
  intro a b c
  fin_cases a <;> fin_cases b <;> fin_cases c <;> simp only <;> unfold MidAlternative <;> decide +kernel

theorem midAlternative5_3 : MidAlternativeTest 5 3 := by
  unfold MidAlternativeTest MidAlternative
  decide +kernel

theorem fastMid5_3 : FastMidTest 5 3 := by
  unfold FastMidTest
  intro a b c
  fin_cases a <;> fin_cases b <;> fin_cases c <;> simp only <;> unfold MidAlternative <;> decide +kernel

theorem midAlternative7_1 : MidAlternativeTest 7 1 := by
  unfold MidAlternativeTest MidAlternative
  decide +kernel

theorem fastMid7_1 : FastMidTest 7 1 := by
  unfold FastMidTest
  intro a b c
  fin_cases a <;> fin_cases b <;> fin_cases c <;> simp only <;> unfold MidAlternative <;> decide +kernel

theorem midAlternative7_3 : MidAlternativeTest 7 3 := by
  unfold MidAlternativeTest MidAlternative
  decide +kernel

theorem fastMid7_3 : FastMidTest 7 3 := by
  unfold FastMidTest
  intro a b c
  fin_cases a <;> fin_cases b <;> fin_cases c <;> simp only <;> unfold MidAlternative <;> decide +kernel

theorem midTest_of_fast {p t : Nat} [Fact p.Prime]
    (ha : MidAlternativeTest p t) (hf : FastMidTest p t) : MidTest p t := by
  intro aa bb cc
  dsimp only
  intro U V hknown htarget hH hlines
  apply hf aa bb cc U V hknown htarget hH
  intro z hz x
  obtain ⟨a,b,hnz,hrows,hrowt⟩ := hlines z hz x
  have hznz : z≠0 := by rcases hz with rfl|rfl <;> simp
  have hnz' : a*z≠0 ∨ a*x+b≠0 := by
    by_cases haz : a=0
    · right
      simpa [haz] using hnz.resolve_left (not_not.mpr haz)
    · exact Or.inl (mul_ne_zero haz hznz)
  apply ha _ _ (a*z) (a*x+b) _ hnz'
  · intro j
    have he1 : (a*z)*(2*j.val)+(a*x+b)=a*(x+z*(2*j.val))+b := by ring
    have he2 : ((aa.val:ZMod p)*z+bb.val)*(2*j.val)+((aa.val:ZMod p)*x+cc.val)=
        (aa.val:ZMod p)*(x+z*(2*j.val))+(bb.val:ZMod p)*(2*j.val)+cc.val := by ring
    rw [he1,he2]
    exact hrows j
  · have he : (a*z)*t+(a*x+b)=a*(x+z*t)+b := by ring
    rw [he]
    exact hrowt

theorem midTest5_1 : MidTest 5 1 := by
  letI : Fact (Nat.Prime 5) := ⟨by decide⟩
  exact midTest_of_fast midAlternative5_1 fastMid5_1

theorem midTest5_3 : MidTest 5 3 := by
  letI : Fact (Nat.Prime 5) := ⟨by decide⟩
  exact midTest_of_fast midAlternative5_3 fastMid5_3

theorem midTest7_1 : MidTest 7 1 := by
  letI : Fact (Nat.Prime 7) := ⟨by decide⟩
  exact midTest_of_fast midAlternative7_1 fastMid7_1

theorem midTest7_3 : MidTest 7 3 := by
  letI : Fact (Nat.Prime 7) := ⟨by decide⟩
  exact midTest_of_fast midAlternative7_3 fastMid7_3
end TranslationTiling.Sudoku.ArithmeticRule.SmallPrime
