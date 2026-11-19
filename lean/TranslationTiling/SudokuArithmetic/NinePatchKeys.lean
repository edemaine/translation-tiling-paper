import TranslationTiling.SudokuArithmetic.NinePatchFormula
import Mathlib.Tactic

namespace TranslationTiling.Sudoku.NinePatch

private theorem pack_inj {q a b c d : Nat} (hb : b < q) (hd : d < q)
    (h : a*q+b=c*q+d) : a=c ∧ b=d := by
  have hm := congrArg (fun k => k%q) h
  simp only [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt hd] at hm
  have he : a*q=c*q := by omega
  exact ⟨Nat.eq_of_mul_eq_mul_right (by omega) he, hm⟩

theorem cell_inj {p n y z n' y' z' : Nat} (hy : y<7) (hy' : y'<7)
    (hz : z<p) (hz' : z'<p) (h : cell p n y z=cell p n' y' z') :
    n=n' ∧ y=y' ∧ z=z' := by
  have he : (n*7+y)*p+z=(n'*7+y')*p+z' := by
    simpa only [cell, Nat.add_mul, Nat.add_assoc] using h
  obtain ⟨ha,hz⟩ := pack_inj hz hz' he
  obtain ⟨hn,hy⟩ := pack_inj hy hy' ha
  exact ⟨hn,hy,hz⟩

theorem mem_forms {p a b : Nat} : (a,b)∈forms p ↔ a<p ∧ b<p ∧ (a≠0 ∨ b≠0) := by
  simp [forms,List.mem_flatMap,List.mem_map,Prod.mk.injEq]

theorem form_bounds {p a b : Nat} (h : (a,b)∈forms p) :
    0<a*p+b ∧ a*p+b<p*p := by
  obtain ⟨ha,hb,hab⟩ := mem_forms.mp h
  constructor
  · rcases hab with h|h
    · have := Nat.mul_pos (by omega : 0<a) (by omega : 0<p)
      omega
    · omega
  · nlinarith

theorem coeff_inj {p i a b i' a' b' : Nat}
    (h : (a,b)∈forms p) (h' : (a',b')∈forms p)
    (he : coeff p i a b=coeff p i' a' b') :
    i=i' ∧ a=a' ∧ b=b' := by
  have hb := form_bounds h
  have hb' := form_bounds h'
  have hle : a*p+b-1<p*p-1 := by omega
  have hle' : a'*p+b'-1<p*p-1 := by omega
  have he' : i*(p*p-1)+(a*p+b-1)=i'*(p*p-1)+(a'*p+b'-1) := by
    simpa only [coeff,Nat.add_assoc,Nat.add_left_cancel_iff] using he
  obtain ⟨hi,hab⟩ := pack_inj hle hle' he'
  have heab : a*p+b=a'*p+b' := by omega
  obtain ⟨ha,hb⟩ := pack_inj (mem_forms.mp h).2.1 (mem_forms.mp h').2.1 heab
  exact ⟨hi,ha,hb⟩

theorem cell_lt {p n y z : Nat} (hn : n<9) (hy : y<7) (hz : z<p) :
    cell p n y z<9*7*p := by
  have : n*7+y<9*7 := by omega
  unfold cell
  nlinarith

theorem coeff_ge (p i a b : Nat) : 9*7*p≤coeff p i a b := by
  unfold coeff
  omega

end TranslationTiling.Sudoku.NinePatch
