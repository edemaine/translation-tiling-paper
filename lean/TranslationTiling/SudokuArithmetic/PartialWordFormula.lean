import TranslationTiling.SudokuArithmetic.NinePatchCertificate
import TranslationTiling.SudokuArithmetic.NineArithmetic
import TranslationTiling.Proofs.WordResidues

namespace TranslationTiling.Sudoku.PartialWord
open Mathlib.Tactic
open NineArithmetic (Column position)

abbrev Pattern := List (ℕ × ℕ)

def coordinates (r : ℕ) (digit : ℕ → ℕ) : Pattern :=
  (List.range 9).filterMap fun i =>
    if digit i = 0 then none else some (i, digit i)

def decode (r code : ℕ) : Pattern := coordinates r fun i => code / r^i % r

def predicted (r a b i : ℕ) : ℕ :=
  let z := (a : ℤ) * (NinePatch.position r i : ℤ) + b
  if (lowValuation r z).isSome then (lowDigit r z).val else 0

def residues (r : ℕ) : List (ℕ × ℕ) :=
  (List.range (r^2)).flatMap fun a =>
    ((List.range (r^2)).filter fun b => a % r != 0 || b % r != 0).map fun b => (a,b)

def legal (r : ℕ) : List Pattern :=
  ((residues r).map fun (a,b) => coordinates r (predicted r a b)).eraseDups

def clashes (p q : Pattern) : Bool :=
  p.any fun (i,v) => q.any fun (j,w) => i == j && v != w

def cell (r i v : ℕ) : ℕ := i * (r-1) + (v-1)

def digits (r : ℕ) := (List.range (r-1)).map (· + 1)

def choices (r : ℕ) : Sat.Fmla :=
  (List.range 9).flatMap fun i =>
    [(digits r).map fun v => .pos (cell r i v)] ++
    (digits r).flatMap fun v => ((digits r).filter (v < ·)).map fun w =>
      [.neg (cell r i v), .neg (cell r i w)]

def exclusion (r : ℕ) (p : Pattern) : Sat.Clause :=
  p.map fun (i,v) => .neg (cell r i v)

def formula (r : ℕ) (cover : List Pattern) : Sat.Fmla :=
  choices r ++ (cover ++ legal r).map (exclusion r)

end TranslationTiling.Sudoku.PartialWord
