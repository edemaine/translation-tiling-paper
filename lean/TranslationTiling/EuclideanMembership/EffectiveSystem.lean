import TranslationTiling.EuclideanMembership.EffectiveGeometry
import TranslationTiling.EuclideanMembership.SourceModel
import TranslationTiling.Proofs.FiniteConnectivity

namespace TranslationTiling.EuclideanMembership
open Compiler.Effective
noncomputable section
variable {d : ℕ}

@[fun_prop] theorem sumValue {α β γ σ : Type*} [Primcodable α] [Primcodable β]
    [Primcodable γ] [Primcodable σ] {s : α → β ⊕ γ} {g : α → β → σ} {h : α → γ → σ}
    (hs : Primrec s) (hg : Primrec (fun q : α × β => g q.1 q.2))
    (hh : Primrec (fun q : α × γ => h q.1 q.2)) :
    Primrec (fun a => Sum.elim (g a) (h a) (s a)) :=
  Primrec.sumCasesOn hs hg.to₂ hh.to₂

@[fun_prop] theorem optionMapValue {α β γ : Type*} [Primcodable α] [Primcodable β]
    [Primcodable γ] {s : α → Option β} {g : α → β → γ}
    (hs : Primrec s) (hg : Primrec (fun q : α × β => g q.1 q.2)) :
    Primrec (fun a => (s a).map (g a)) := Primrec.option_map hs hg.to₂

@[fun_prop] theorem optionGetDValue {α β : Type*} [Primcodable α] [Primcodable β]
    {s : α → Option β} {g : α → β} (hs : Primrec s) (hg : Primrec g) :
    Primrec (fun a => (s a).getD (g a)) := Primrec.option_getD.comp hs hg

theorem constraint_primrec (ar af : Bool) :
    Primrec (fun q : Tile d × ConstraintIndex d => constraint q.1 ar af q.2) := by
  classical
  unfold constraint
  fun_prop

@[fun_prop] theorem constraintValue {α : Type*} [Primcodable α] (ar af : Bool)
    {p : α → Tile d} {i : α → ConstraintIndex d} (hp : Primrec p) (hi : Primrec i) :
    Primrec (fun a => constraint (p a) ar af (i a)) :=
  (constraint_primrec ar af).comp (hp.pair hi)

theorem constraints_primrec (ar af : Bool) :
    Primrec₂ (fun (P : Tile d) n => constraints P ar af n) := by
  unfold Primrec₂ constraints
  fun_prop

/-- Euclidean tilability is co-RE for every choice of the two motion flags.
The proof enumerates finite integer tests for a compact system of polynomial
constraints; it makes no restriction on the real translations or angles. -/
theorem motionTiles_coRE [NeZero d] (ar af : Bool) :
    LeanWang.CoREPred (fun P : Tile d => MotionTiles P ar af) := by
  have hc := satisfiable_coRE (fun (P : Tile d) n => constraints P ar af n)
    (constraints_primrec ar af)
  unfold LeanWang.CoREPred at hc ⊢
  apply hc.of_eq
  intro P
  exact not_congr ((satisfiable_iff_model P ar af).trans (motionTiles_iff_model P ar af).symm)

/-- The same membership bound holds with facet-connectedness required. -/
theorem connectedMotionTiles_coRE [NeZero d] (ar af : Bool) :
    LeanWang.CoREPred (fun P : Tile d => FaceConnected P ∧ MotionTiles P ar af) := by
  have hp : Primrec (fun q : Tile d × ℕ =>
      initialConstraints (constraints q.1 ar af) q.2) := by
    unfold initialConstraints
    apply mapList (g := fun (q : Tile d × ℕ) (n : ℕ) => constraints q.1 ar af n)
      (by fun_prop)
    exact (constraints_primrec ar af).comp (by fun_prop) (by fun_prop)
  have ht : PrimrecPred (fun q : Tile d × ℕ =>
      finiteTest (initialConstraints (constraints q.1 ar af) q.2) q.2) :=
    finiteTest_primrec.comp (hp.pair Primrec.snd)
  have hbad := (((finiteConnectedTest_primrec d).comp Primrec.fst).not.or ht.not).computablePred
  have hRE := LeanWang.REPred.exists_nat
    (p := fun (P : Tile d) n => ¬ finiteConnectedTest P ∨
      ¬ finiteTest (initialConstraints (constraints P ar af) n) n) hbad
  apply hRE.of_eq
  intro P
  have hi : MotionTiles P ar af ↔ ∀ k, finiteTest (initialConstraints (constraints P ar af) k) k :=
    (motionTiles_iff_model P ar af).trans
      ((satisfiable_iff_model P ar af).symm.trans (satisfiable_iff_tests _))
  simp only [hi,finiteConnectedTest_iff,not_and_or,not_forall,exists_or,exists_const]

end
end TranslationTiling.EuclideanMembership
