import Mathlib.Tactic.Sat.FromLRAT
import TranslationTiling.SudokuArithmetic.ShortSeedModel
namespace TranslationTiling.Sudoku.ShortRule.Seed
open Mathlib.Tactic

def satLiteral (z : Atom p × Bool) : Sat.Literal :=
  if z.2 then .pos (key z.1) else .neg (key z.1)
def satFormula (p : Nat) : Sat.Fmla := (clauses p).map fun c => c.map satLiteral

theorem satClause_of_holds {p : Nat} [Fact p.Prime] (m : Atom p → Bool) (c : Clause p) (h : Holds m c) :
    Sat.Valuation.satisfies (fun n => assignment m n=true) (c.map satLiteral) := by
  induction c with
  | nil => simp [Holds] at h
  | cons a c ih =>
    intro ha
    obtain ⟨z,hz,hzv⟩ := h
    rcases List.mem_cons.mp hz with rfl|hz
    · cases z with | mk a b =>
        cases b <;> simp [Sat.Valuation.neg,Sat.Literal.negate,satLiteral,assignment_key,hzv] at ha hzv
    · exact ih ⟨z,hz,hzv⟩

theorem satFormula_of_holds {p : Nat} [Fact p.Prime] (m : Atom p → Bool) (hm : ∀ c∈clauses p, Holds m c) :
    Sat.Valuation.satisfies_fmla (fun n => assignment m n=true) (satFormula p) := by
  constructor
  intro c hc
  change c∈(clauses p).map (fun c => c.map satLiteral) at hc
  rcases List.mem_map.mp hc with ⟨d,hd,he⟩
  subst c
  exact satClause_of_holds m d (hm d hd)


noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

theorem exists_clean_seed_sat {p : Nat} [Fact p.Prime] {W : WordArray p}
    (hW : LineRule p W) (hu : Sat.Fmla.proof (satFormula p) []) :
    ∃ h∈[2,4], ∃ r∈List.range (width p-4), ∃ q∈List.range (13-2*h),
      ∀ z∈seedClause p r q h, model hW z.1=false := by
  by_contra hn
  apply hu (fun n => assignment (model hW) n=true)
  apply satFormula_of_holds
  intro c hc
  simp only [clauses,List.mem_append] at hc
  rcases hc with hc|hc
  · exact baseClauses_hold hW c (by simpa only [List.mem_append] using hc)
  · simp only [seedFailures,List.mem_flatMap,List.mem_map] at hc
    obtain ⟨h,hh,r,hr,q,hq,rfl⟩ := hc
    have hf : ¬∀ z∈seedClause p r q h, model hW z.1=false := by
      intro hz
      exact hn ⟨h,hh,r,hr,q,hq,hz⟩
    push Not at hf
    obtain ⟨z,hz,hv⟩ := hf
    refine ⟨z,hz,?_⟩
    have hb : z.2=true := by
      simp only [seedClause,List.mem_map] at hz
      obtain ⟨a,_,rfl⟩ := hz
      rfl
    rw [hb]
    exact Bool.eq_true_of_not_eq_false hv
end
end TranslationTiling.Sudoku.ShortRule.Seed
