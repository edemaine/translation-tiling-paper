import TranslationTiling.Proofs.Basic
import Mathlib.Data.Finset.Pi
import Mathlib.Data.Int.Interval
import Mathlib.GroupTheory.Index

/-! Explicit hypotheses for MSS Lemma 2.1 and Bhattacharya's planar periodicity.
Neither an algorithmic reduction nor the paper's main conclusion is assumed. -/

namespace TranslationTiling

noncomputable section
open scoped Classical

def Period {G : Type*} [AddCommGroup G] (A : Set G) (v : G) : Prop :=
  ∀ x, x + v ∈ A ↔ x ∈ A

def FullyPeriodic {G : Type*} [AddCommGroup G] (A : Set G) : Prop :=
  ∃ P : AddSubgroup G, P.FiniteIndex ∧ ∀ v ∈ P, Period A v

/-- Bhattacharya, arXiv:1602.05738v1: existence of a full-rank periodic complement. -/
def PlanarPeriodicity : Prop :=
  ∀ F : Tile 2, Tiles F →
    ∃ A : Set (Lattice 2), ExactTiling A {f | f ∈ F} ∧ FullyPeriodic A

namespace MSS

abbrev scale : ℤ := 201

def box (k : ℕ) : Finset (Lattice 3) := Fintype.piFinset (fun _ : Fin 3 => Finset.Icc (-(k : ℤ)) (k : ℤ))
def frame (k : ℕ) : Finset (Lattice 3) := box k \ box (k - 1)
def marker (j : ℕ) : Lattice 3 := fun i => if i = 0 then 12 * j else 0
def kernelStep (Q : ℕ) : Lattice 3 := fun i => if i = 2 then Q else 0

def removed : Finset (Lattice 3) :=
  Finset.univ.biUnion fun j : Fin 3 => (frame (j.val + 1)).image (marker (j.val + 1) + ·)

def bumps : Finset (Lattice 3) :=
  Finset.univ.biUnion fun j : Fin 3 =>
    (frame (j.val + 1)).image (fun x => scale • Pi.single j 1 + marker (j.val + 1) + x)

def baseShape : Finset (Lattice 3) := (box 100 \ removed) ∪ bumps

def component (Q j : ℕ) : Finset (Lattice 3) :=
  (baseShape \ (frame j).image (marker j + ·)) ∪
    (frame j).image (fun x => scale • kernelStep Q + marker j + x)

/-- Mixed coverage retains the component type in each representation. -/
def MixedTiling (Q : ℕ) (C₁ C₂ : Set (Lattice 3)) : Prop :=
  Function.Bijective (Sum.elim
    (fun z : C₁ × ↥(component Q 4) => z.1.val + z.2.val)
    (fun z : C₂ × ↥(component Q 5) => z.1.val + z.2.val))

/-- MSS, arXiv:2211.07140v1, Lemma 2.1(c), specialized to the paper's shapes. -/
def Rigidity : Prop :=
  ∀ Q : ℕ, 0 < Q → ∀ C₁ C₂ : Set (Lattice 3), 0 ∈ C₁ ∪ C₂ →
    (MixedTiling Q C₁ C₂ ↔
      Disjoint C₁ C₂ ∧ C₁ ∪ C₂ = Set.range (fun x : Lattice 3 => scale • x) ∧
      Period C₁ (scale • kernelStep Q) ∧ Period C₂ (scale • kernelStep Q))

end MSS
end
end TranslationTiling
