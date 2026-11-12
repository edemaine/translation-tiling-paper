import TranslationTiling.EuclideanMembership.Rounding
import LeanWang.CoRE

/-!
# Co-RE membership for computable compact polynomial constraint systems

This theorem combines finite integer search, explicit rounding bounds, and
compactness. It needs no real quantifier elimination or real-number oracle.
-/
namespace TranslationTiling.EuclideanMembership

open Compiler.Effective

/-- One assignment satisfies every constraint with zero error. -/
def Satisfiable (c : ℕ → Formula) : Prop :=
  ∃ x : Assignment, ∀ n, Holds (c n) 0 (coordinates x)

def initialConstraints (c : ℕ → Formula) (k : ℕ) : List Formula := (List.range (k+1)).map c

/-- Every exact solution survives finite search; passing every finite test
produces an exact solution by compactness. -/
theorem satisfiable_iff_tests (c : ℕ → Formula) :
    Satisfiable c ↔ ∀ k, finiteTest (initialConstraints c k) k := by
  constructor
  · rintro ⟨x,hx⟩ k
    apply finiteTest_of_solution _ k x
    rintro f hf
    obtain ⟨n,hn,rfl⟩ := List.mem_map.mp hf
    exact hx n
  · intro h
    apply (satisfiable_iff_approximate c).mpr
    intro k
    obtain ⟨x,hx⟩ := finiteTest_solution (h k)
    refine ⟨x,fun n hn => hx (c n) ?_⟩
    exact List.mem_map.mpr ⟨n,List.mem_range.mpr (by omega),rfl⟩

/-- Uniform effective compactness: satisfiability is co-RE whenever the
integer polynomial constraints are generated primitive recursively. -/
theorem satisfiable_coRE {α : Type*} [Primcodable α]
    (c : α → ℕ → Formula) (hc : Primrec₂ c) :
    LeanWang.CoREPred (fun a => Satisfiable (c a)) := by
  have hp : Primrec (fun q : α × ℕ => initialConstraints (c q.1) q.2) := by
    unfold initialConstraints
    apply mapList (g := fun (q : α × ℕ) n => c q.1 n) (by fun_prop)
    exact hc.comp (Primrec.fst.comp Primrec.fst) Primrec.snd
  have ht : PrimrecPred (fun q : α × ℕ => finiteTest (initialConstraints (c q.1) q.2) q.2) :=
    finiteTest_primrec.comp (hp.pair Primrec.snd)
  exact (LeanWang.REPred.exists_nat ht.not.computablePred).of_eq fun a => by
    simpa only [not_forall] using (not_congr (satisfiable_iff_tests (c a))).symm

end TranslationTiling.EuclideanMembership
