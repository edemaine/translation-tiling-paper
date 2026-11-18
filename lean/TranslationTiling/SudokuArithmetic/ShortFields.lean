import TranslationTiling.SudokuArithmetic.ShortWordRule
import TranslationTiling.SudokuArithmetic.SmallPrimeFields

namespace TranslationTiling.Sudoku.ShortRule.Seed
open ArithmeticRule.SmallPrime
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option synthInstance.maxSize 1000000
set_option maxSynthPendingDepth 100000

def step (i : Fin 4) : ℤ := if i.val=0 then -2 else if i.val=1 then -1 else if i.val=2 then 1 else 2
def sign (i : Fin 2) : ℤ := if i.val=0 then -1 else 1

def ThirdTest (p : ℕ) : Prop :=
  ∀ A D0 D1 U V : ZMod p,
    (A≠0 ∨ D0≠0) → (A≠0 ∨ D1≠0) → (A≠0 ∨ 2*D1-D0≠0) → (U≠0 ∨ V≠0) →
    (U≠0 ∨ ∃ n : Fin (wordWidth p), U*n.val+V=A*n.val+2*D1-D0 ∧ A*n.val+2*D1-D0≠0) →
    (∀ i : Fin 4, ∀ n : Fin (wordWidth p),
      0≤(n.val:ℤ)-2*step i → (n.val:ℤ)-2*step i<wordWidth p →
      0≤(n.val:ℤ)-step i → (n.val:ℤ)-step i<wordWidth p →
      A*((n.val:ℤ)-2*step i)+D0≠0 → A*((n.val:ℤ)-step i)+D1≠0 →
      A*n.val+2*D1-D0≠0 → U*n.val+V≠0 →
      U*n.val+V=A*n.val+2*D1-D0 ∨ U*n.val+V=2*(A*((n.val:ℤ)-step i)+D1) ∨
      U*n.val+V=-(A*((n.val:ℤ)-2*step i)+D0)) → U=A ∧ V=2*D1-D0

theorem third5 : ThirdTest 5 := by
  unfold ThirdTest
  decide +kernel

theorem third7 : ThirdTest 7 := by
  unfold ThirdTest
  decide +kernel

def MidTest (p t : ℕ) : Prop :=
  ∀ A B C U V : ZMod p,
    (∀ j : Fin 3, A≠0 ∨ B*(2*j.val)+C≠0) →
    (A≠0 ∨ B*t+C≠0) → (U≠0 ∨ V≠0) →
    (∀ z : Fin 2, ∀ x : Fin (wordWidth p),
      (∀ j : Fin 3, 0≤(x.val:ℤ)+sign z*(2*j.val) ∧ (x.val:ℤ)+sign z*(2*j.val)<wordWidth p) →
      0≤(x.val:ℤ)+sign z*t → (x.val:ℤ)+sign z*t<wordWidth p →
      ∃ a b : ZMod p, (a≠0 ∨ b≠0) ∧
        (∀ j : Fin 3, let y : ZMod p := 2*j.val;
          let n := (x.val:ZMod p)+(sign z:ZMod p)*y;
          a*n+b≠0 → A*n+B*y+C≠0 → a*n+b=A*n+B*y+C) ∧
        (let n := (x.val:ZMod p)+(sign z:ZMod p)*t;
          a*n+b≠0 → U*n+V≠0 → a*n+b=U*n+V)) → U=A ∧ V=B*t+C

def FastMidTest (p t : ℕ) : Prop :=
  ∀ A B C U V : ZMod p,
    (∀ j : Fin 3, A≠0 ∨ B*(2*j.val)+C≠0) →
    (A≠0 ∨ B*t+C≠0) → (U≠0 ∨ V≠0) →
    (∀ z : Fin 2, ∀ x : Fin (wordWidth p),
      (∀ j : Fin 3, 0≤(x.val:ℤ)+sign z*(2*j.val) ∧ (x.val:ℤ)+sign z*(2*j.val)<wordWidth p) →
      0≤(x.val:ℤ)+sign z*t → (x.val:ℤ)+sign z*t<wordWidth p →
      MidAlternative p t (A*(sign z:ZMod p)+B) (A*x.val+C)
        (U*((x.val:ZMod p)+(sign z:ZMod p)*t)+V)) → U=A ∧ V=B*t+C

theorem fastMid5_1 : FastMidTest 5 1 := by
  unfold FastMidTest MidAlternative
  decide +kernel

theorem fastMid5_3 : FastMidTest 5 3 := by
  unfold FastMidTest MidAlternative
  decide +kernel

theorem fastMid7_1 : FastMidTest 7 1 := by
  unfold FastMidTest MidAlternative
  decide +kernel

theorem fastMid7_3 : FastMidTest 7 3 := by
  unfold FastMidTest MidAlternative
  decide +kernel

theorem midTest_of_fast {p t : ℕ} [Fact p.Prime]
    (ha : MidAlternativeTest p t) (hf : FastMidTest p t) : MidTest p t := by
  intro A B C U V hknown htarget hH hlines
  apply hf A B C U V hknown htarget hH
  intro z x hxs hxt0 hxtN
  obtain ⟨a,b,hnz,hrows,hrowt⟩ := hlines z x hxs hxt0 hxtN
  have hznz : (sign z:ZMod p)≠0 := by fin_cases z <;> simp [sign]
  have hnz' : a*(sign z:ZMod p)≠0 ∨ a*x.val+b≠0 := by
    by_cases haz : a=0
    · right; simpa [haz] using hnz.resolve_left (not_not.mpr haz)
    · exact Or.inl (mul_ne_zero haz hznz)
  apply ha _ _ (a*(sign z:ZMod p)) (a*x.val+b) _ hnz'
  · intro j
    have he1 : (a*(sign z:ZMod p))*(2*j.val)+(a*x.val+b)=a*(x.val+(sign z:ZMod p)*(2*j.val))+b := by ring
    have he2 : (A*(sign z:ZMod p)+B)*(2*j.val)+(A*x.val+C)=A*(x.val+(sign z:ZMod p)*(2*j.val))+B*(2*j.val)+C := by ring
    rw [he1,he2]
    exact hrows j
  · have he : (a*(sign z:ZMod p))*t+(a*x.val+b)=a*(x.val+(sign z:ZMod p)*t)+b := by ring
    rw [he]
    exact hrowt

theorem mid5_1 : MidTest 5 1 := by
  letI : Fact (Nat.Prime 5) := ⟨by decide⟩
  exact midTest_of_fast midAlternative5_1 fastMid5_1

theorem mid5_3 : MidTest 5 3 := by
  letI : Fact (Nat.Prime 5) := ⟨by decide⟩
  exact midTest_of_fast midAlternative5_3 fastMid5_3

theorem mid7_1 : MidTest 7 1 := by
  letI : Fact (Nat.Prime 7) := ⟨by decide⟩
  exact midTest_of_fast midAlternative7_1 fastMid7_1

theorem mid7_3 : MidTest 7 3 := by
  letI : Fact (Nat.Prime 7) := ⟨by decide⟩
  exact midTest_of_fast midAlternative7_3 fastMid7_3

end TranslationTiling.Sudoku.ShortRule.Seed
