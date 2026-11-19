import Mathlib.Tactic.Sat.FromLRAT
import Mathlib.Data.List.FinRange

/-! Finite affine tests on the nine retained arithmetic columns. -/
namespace TranslationTiling.Sudoku.NinePatch
open Mathlib.Tactic

def position (p n : Nat) : Nat :=
  if n < 5 then n else if n < 8 then p + (n-5) else 2*p

def forms (p : Nat) : List (Nat × Nat) :=
  (List.range p).flatMap fun a => ((List.range p).map fun b => (a,b)).filter
    fun ab => ab.1 != 0 || ab.2 != 0

def entries (p : Nat) (l : Int × Int) : List (Nat × Nat) :=
  (List.range 9).filterMap fun n =>
    let y := l.1 * (position p n : Int) + l.2
    if 0 ≤ y ∧ y < 7 then some (n,y.toNat) else none

def lines (p : Nat) : List (Int × Int) :=
  ((List.range 13).flatMap fun d => (List.range (7+12*(2*p))).map fun e =>
    ((d:Int)-6, (e:Int)-6*(2*p))).filter fun l => 2 ≤ (entries p l).length

def cell (p n y v : Nat) : Nat := n*7*p+y*p+v

def coeff (p l a b : Nat) : Nat := 9*7*p+l*(p*p-1)+(a*p+b-1)

def value (p : Nat) (ab : Nat × Nat) (n : Nat) := (ab.1 * position p n + ab.2)%p

def triples (p : Nat) : List (Nat × Nat × Nat) :=
  (List.range p).flatMap fun a => (List.range p).flatMap fun b =>
    ((List.range p).map fun c => (a,b,c)).filter fun abc =>
      abc.1 != 0 || abc.2.1 != 0 || abc.2.2 != 0

def affineValue (p : Nat) (abc : Nat × Nat × Nat) (n y : Nat) :=
  (abc.1 * position p n + abc.2.1*y + abc.2.2)%p

def cellChoices (p : Nat) : Sat.Fmla :=
  (List.range 9).flatMap fun n => (List.range 7).flatMap fun y =>
    [(List.range (p-1)).map fun v => .pos (cell p n y (v+1))] ++
    (List.range p).flatMap fun u =>
      ((List.range p).filter fun v => u<v).map fun v =>
        [.neg (cell p n y u), .neg (cell p n y v)]

def normalization (p : Nat) : Sat.Fmla := [[.pos (cell p 0 0 1)]]

def lineClauses (p : Nat) : Sat.Fmla :=
  ((lines p).zipIdx).flatMap fun (l,i) =>
    [(forms p).map fun (a,b) => .pos (coeff p i a b)] ++
    (forms p).flatMap fun (a,b) =>
      ((entries p l).filter fun (n,_) => value p (a,b) n != 0).map fun (n,y) =>
        [.neg (coeff p i a b), .pos (cell p n y (value p (a,b) n))]

def exclusions (p : Nat) : Sat.Fmla :=
  (triples p).map fun abc =>
    (List.range 9).flatMap fun n =>
      ((List.range 7).filter fun y => affineValue p abc n y != 0).map fun y =>
        .neg (cell p n y (affineValue p abc n y))

def formula (p : Nat) : Sat.Fmla :=
  cellChoices p ++ normalization p ++ lineClauses p ++ exclusions p

end TranslationTiling.Sudoku.NinePatch
