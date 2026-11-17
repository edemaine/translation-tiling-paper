import TranslationTiling.SudokuArithmetic.WordAffine
import Mathlib.Logic.Equiv.Fin.Basic
import Std.Tactic.BVDecide.LRAT.Checker

namespace TranslationTiling.Sudoku.ArithmeticRule.SmallPrime
open scoped Classical
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

def width (p : ℕ) := 2*p+2
def extent (p : ℕ) := 13+8*width p
abbrev Cell (p : ℕ) := Fin (width p) × Fin 13 × Fin p
abbrev Line (p : ℕ) := Fin 9 × Fin (extent p)
abbrev Coeff (p : ℕ) := Fin 9 × Fin (extent p) × Fin p × Fin p
abbrev Bad (p : ℕ) := Fin 9 × Fin (extent p) × Fin (width p)
abbrev Atom (p : ℕ) := Cell p ⊕ (Coeff p ⊕ Bad p)
abbrev Clause (p : ℕ) := List (Atom p × Bool)

def cellEquiv (p : ℕ) : Cell p ≃ Fin (width p*(13*p)) :=
  (Equiv.prodCongr (Equiv.refl _) finProdFinEquiv).trans finProdFinEquiv
def coeffEquiv (p : ℕ) : Coeff p ≃ Fin (9*(extent p*(p*p))) :=
  (Equiv.prodCongr (Equiv.refl _)
    ((Equiv.prodCongr (Equiv.refl _) finProdFinEquiv).trans finProdFinEquiv)).trans finProdFinEquiv
def badEquiv (p : ℕ) : Bad p ≃ Fin (9*(extent p*width p)) :=
  (Equiv.prodCongr (Equiv.refl _) finProdFinEquiv).trans finProdFinEquiv
def atomEquiv (p : ℕ) :
    Atom p ≃ Fin (width p*(13*p)+(9*(extent p*(p*p))+9*(extent p*width p))) :=
  (Equiv.sumCongr (cellEquiv p)
    ((Equiv.sumCongr (coeffEquiv p) (badEquiv p)).trans finSumFinEquiv)).trans finSumFinEquiv
def key {p : ℕ} (a : Atom p) : ℕ := (atomEquiv p a).val

def direction {p : ℕ} (l : Line p) : ℤ := (l.1.val:ℤ)-4
def intercept {p : ℕ} (l : Line p) : ℤ := (l.2.val:ℤ)-4*width p
def height {p : ℕ} (l : Line p) (n : Fin (width p)) : ℤ :=
  direction l*n.val+intercept l

def cell {p : ℕ} (n : Fin (width p)) (y : Fin 13) (v : Fin p) : Atom p := .inl (n,y,v)
def coeff {p : ℕ} (l : Line p) (a b : Fin p) : Atom p := .inr (.inl (l.1,l.2,a,b))
def bad {p : ℕ} (l : Line p) (n : Fin (width p)) : Atom p := .inr (.inr (l.1,l.2,n))
def forms (p : ℕ) : List (Fin p×Fin p) :=
  ((List.finRange p).flatMap fun a => (List.finRange p).map fun b => (a,b)).filter
    fun ab => ab.1.val≠0 ∨ ab.2.val≠0
def lines (p : ℕ) : List (Line p) :=
  (List.finRange 9).flatMap fun d => (List.finRange (extent p)).map fun e => (d,e)
def value {p : ℕ} (ab : Fin p×Fin p) (n : Fin (width p)) : ℕ :=
  (ab.1.val*n.val+ab.2.val)%p

def cellChoices (p : ℕ) : List (Clause p) :=
  (List.finRange (width p)).flatMap fun n => (List.finRange 13).map fun y =>
    ((List.finRange p).filter fun v => v.val≠0).map fun v => (cell n y v,true)
def cellUnique (p : ℕ) : List (Clause p) :=
  (List.finRange (width p)).flatMap fun n => (List.finRange 13).flatMap fun y =>
    (List.finRange p).flatMap fun u => ((List.finRange p).filter fun v => u.val<v.val).map
      fun v => [(cell n y u,false),(cell n y v,false)]
def lineChoices (p : ℕ) : List (Clause p) :=
  (lines p).map fun l => (forms p).map fun ab => (coeff l ab.1 ab.2,true)

def consistency (p : ℕ) : List (Clause p) :=
  (lines p).flatMap fun l => (List.finRange (width p)).flatMap fun n =>
    if hy : 0≤height l n ∧ height l n<13 then
      ((forms p).filter fun ab => value ab n≠0).map fun ab =>
        [(coeff l ab.1 ab.2,false),
          (cell n ⟨(height l n).toNat,by omega⟩ ⟨value ab n,by
            exact Nat.mod_lt _ (by have := ab.1.isLt; omega)⟩,true)]
    else []
def badLinks (p : ℕ) : List (Clause p) :=
  (lines p).flatMap fun l => (List.finRange (width p)).flatMap fun n =>
    if 0≤height l n ∧ height l n<13 then
      ((forms p).filter fun ab => value ab n≠0).map fun ab =>
        [(bad l n,false),(coeff l ab.1 ab.2,false)]
    else []

def pattern (h : ℕ) : List (ℤ×ℕ×ℕ) :=
  [(0,0,0),(0,2,0),(0,2,h),(0,3,h),
   (h/2,0,0),(h/2,2,h),(h/2,4,2*h),
   (h,2,0),(h,3,h),(h,4,2*h)]
def seedClause (p r q h : ℕ) : Clause p :=
  (pattern h).map fun ⟨d,i,j⟩ =>
    let x := r+i
    let e := (q+j:ℤ)-d*x
    let l : Line p := (⟨(d+4).toNat%(9),Nat.mod_lt _ (by decide)⟩,
      ⟨(e+4*width p).toNat%(extent p),Nat.mod_lt _ (by unfold extent; omega)⟩)
    (bad l ⟨x%(width p),Nat.mod_lt _ (by unfold width; omega)⟩,true)
def seedFailures (p : ℕ) : List (Clause p) :=
  [2,4].flatMap fun h => (List.range (width p-4)).flatMap fun r =>
    (List.range (13-2*h)).map fun q => seedClause p r q h

def clauses (p : ℕ) : List (Clause p) :=
  cellChoices p ++ cellUnique p ++ lineChoices p ++ consistency p ++ badLinks p ++ seedFailures p

def formula (p : ℕ) : Std.Sat.CNF ℕ :=
  ⟨((clauses p).map fun c => Std.Sat.CNF.Clause.ofLiterals (c.map fun ab => (key ab.1,ab.2))).toArray⟩

end TranslationTiling.Sudoku.ArithmeticRule.SmallPrime
