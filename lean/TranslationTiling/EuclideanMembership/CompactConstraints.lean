import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
# Compact systems of closed polynomial constraints

A countable family of finite disjunctions of polynomial inequalities on a
countable product of unit intervals is satisfiable exactly when every finite
prefix is satisfiable with arbitrarily small error. This is the topological
part of the finite rational approximation test used for Euclidean tilings.
-/

namespace TranslationTiling.EuclideanMembership

noncomputable section

abbrev Polynomial := List (ℤ × List ℕ)
abbrev Formula := List (List Polynomial)
abbrev Assignment := ℕ → Set.Icc (-1 : ℝ) 1

def monomial (v : List ℕ) (x : ℕ → ℝ) : ℝ := (v.map x).prod

def evaluate (p : Polynomial) (x : ℕ → ℝ) : ℝ :=
  (p.map fun t => (t.1 : ℝ) * monomial t.2 x).sum

/-- A finite disjunction of finite conjunctions of weak inequalities. -/
def Holds (f : Formula) (e : ℝ) (x : ℕ → ℝ) : Prop :=
  ∃ c ∈ f, ∀ p ∈ c, evaluate p x ≤ e

def coordinates (x : Assignment) : ℕ → ℝ := fun i => x i

private theorem continuous_monomial (v : List ℕ) : Continuous (monomial v) := by
  induction v with
  | nil => change Continuous (fun _ : ℕ → ℝ => (1 : ℝ)); exact continuous_const
  | cons i v ih =>
    change Continuous (fun x : ℕ → ℝ => x i * monomial v x)
    exact (continuous_apply i).mul ih

private theorem continuous_evaluate (p : Polynomial) : Continuous (evaluate p) := by
  induction p with
  | nil => change Continuous (fun _ : ℕ → ℝ => (0 : ℝ)); exact continuous_const
  | cons t p ih =>
    change Continuous (fun x : ℕ → ℝ => (t.1 : ℝ) * monomial t.2 x + evaluate p x)
    exact (continuous_const.mul (continuous_monomial t.2)).add ih

private theorem continuous_coordinates : Continuous coordinates := by
  exact continuous_pi fun i => (continuous_apply i).subtype_val

theorem holds_closed (f : Formula) (e : ℝ) :
    IsClosed {x : Assignment | Holds f e (coordinates x)} := by
  classical
  have he : {x : Assignment | Holds f e (coordinates x)} =
      ⋃ c ∈ (f.toFinset : Finset (List Polynomial)),
        ⋂ p ∈ (c.toFinset : Finset Polynomial), {x | evaluate p (coordinates x) ≤ e} := by
    ext x
    simp [Holds]
  rw [he]
  apply isClosed_biUnion_finset
  intro c hc
  exact isClosed_iInter fun p => isClosed_iInter fun _ =>
    isClosed_le ((continuous_evaluate p).comp continuous_coordinates) continuous_const

private theorem holds_error_closed (f : Formula) (x : ℕ → ℝ) :
    IsClosed {e : ℝ | Holds f e x} := by
  classical
  have he : {e : ℝ | Holds f e x} =
      ⋃ c ∈ (f.toFinset : Finset (List Polynomial)),
        ⋂ p ∈ (c.toFinset : Finset Polynomial), {e | evaluate p x ≤ e} := by
    ext e
    simp [Holds]
  rw [he]
  exact isClosed_biUnion_finset fun c _ =>
    isClosed_iInter fun p => isClosed_iInter fun _ => isClosed_le continuous_const continuous_id

theorem holds_mono {f : Formula} {a b : ℝ} {x : ℕ → ℝ}
    (hab : a ≤ b) (h : Holds f a x) : Holds f b x := by
  obtain ⟨c,hc,hp⟩ := h
  exact ⟨c,hc,fun p hp' => (hp p hp').trans hab⟩

/-- The tolerance for the `k`th finite approximation. -/
def error (k : ℕ) : ℝ := 1 / ((k : ℝ) + 1)

theorem error_pos (k : ℕ) : 0 < error k := by unfold error; positivity

theorem error_antitone : Antitone error := by
  intro a b hab
  unfold error
  exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hab 1)

private theorem error_tendsto : Filter.Tendsto error Filter.atTop (nhds 0) := by
  change Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) Filter.atTop (nhds 0)
  exact tendsto_one_div_add_atTop_nhds_zero_nat

/-- Compactness converts approximate solutions of every finite prefix into one
exact solution of the entire system. -/
theorem satisfiable_iff_approximate (c : ℕ → Formula) :
    (∃ x : Assignment, ∀ n, Holds (c n) 0 (coordinates x)) ↔
      ∀ k, ∃ x : Assignment, ∀ n ≤ k, Holds (c n) (error k) (coordinates x) := by
  classical
  constructor
  · rintro ⟨x,hx⟩ k
    exact ⟨x,fun n _ => holds_mono (error_pos k).le (hx n)⟩
  · intro h
    let C (p : ℕ × ℕ) : Set Assignment :=
      {x | Holds (c p.1) (error p.2) (coordinates x)}
    have hc (p : ℕ × ℕ) : IsClosed (C p) := holds_closed _ _
    have hf (s : Finset (ℕ × ℕ)) : (⋂ p ∈ s, C p).Nonempty := by
      let m := s.sup fun p => max p.1 p.2
      obtain ⟨x,hx⟩ := h m
      refine ⟨x,?_⟩
      simp only [Set.mem_iInter]
      intro p hp
      have hm : max p.1 p.2 ≤ m := Finset.le_sup (f := fun p : ℕ × ℕ => max p.1 p.2) hp
      exact holds_mono (error_antitone ((le_max_right _ _).trans hm))
        (hx p.1 ((le_max_left _ _).trans hm))
    obtain ⟨x,hx⟩ := (isCompact_univ : IsCompact (Set.univ : Set Assignment)).inter_iInter_nonempty
      C hc (by simpa using hf)
    refine ⟨x,fun n => ?_⟩
    apply (holds_error_closed (c n) (coordinates x)).mem_of_tendsto error_tendsto
    exact Filter.Eventually.of_forall fun k => Set.mem_iInter.mp hx.2 (n,k)

end

end TranslationTiling.EuclideanMembership
