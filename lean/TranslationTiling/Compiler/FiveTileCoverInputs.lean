import TranslationTiling.Compiler.FiveTileSymmetry

/-! Checked clauses covering all rectangular horizontal matching relations. -/
namespace TranslationTiling.Compiler.FiveTile
open Mathlib.Tactic
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

inductive CoverInput where
  | rectangular (a b c d : Letter)
  | rowbit (b : Letter)
  | exclude (e : Orbit)

def CoverInput.clause (r : Fin 32) : CoverInput → Sat.Clause
  | .rectangular a b c d => [.neg (vVar a c),.neg (vVar b c),.neg (vVar a d),.pos (vVar b d)]
  | .rowbit b => [if r.val.testBit b.val then .pos (vVar 0 b) else .neg (vVar 0 b)]
  | .exclude e => (List.range 25).map fun i => if e.mask.testBit i then .neg i else .pos i

def CoverInput.valid : CoverInput → Bool
  | .rectangular _ _ _ _ => true
  | .rowbit _ => true
  | .exclude e => e.valid

def coverAssignment (H : ℕ) : Sat.Valuation := assignment 0 (edge H) (fun _ _ => 0)

theorem coverAssignment_var (H : ℕ) (a b : Letter) :
    coverAssignment H (vVar a b) ↔ edge H a b=true := assignment_vVar _ _ _ _ _

private theorem satisfies_iff (v : Sat.Valuation) (c : List Sat.Literal) :
    v.satisfies c ↔ ∃ l∈c, ¬v.neg l := by
  classical
  induction c with
  | nil => simp [Sat.Valuation.satisfies]
  | cons l c ih =>
    simp only [Sat.Valuation.satisfies,ih,List.mem_cons]
    by_cases h : v.neg l <;> simp_all

theorem CoverInput.satisfied (cs : Fin 676 → CheckedCase)
    (hcs : ∀ i, (cs i).mask=caseMask i)
    {H : ℕ} {V : Matrix} {W : ℕ → ℕ → Letter} (r : Fin 32)
    (hrH : Rectangular (edge H)) (hrV : Rectangular V) (hp : Patch H V W)
    (hrow : ∀ b, edge H 0 b=r.val.testBit b.val)
    (hn : ¬Plane H V) (i : CoverInput) (hi : i.valid=true) :
    (coverAssignment H).satisfies (i.clause r) := by
  classical
  cases i with
  | rectangular a b c d =>
    simp only [CoverInput.clause,Sat.Valuation.satisfies,Sat.Valuation.neg]
    intro hac hbc had hbd
    apply hbd
    apply (coverAssignment_var H b d).mpr
    rw [←hrH a b c d ((coverAssignment_var H a c).mp hac) ((coverAssignment_var H b c).mp hbc)]
    exact (coverAssignment_var H a d).mp had
  | rowbit b =>
    cases hb : r.val.testBit b.val with
    | false =>
      simp only [CoverInput.clause,hb,Bool.false_eq_true,ite_false,Sat.Valuation.satisfies,Sat.Valuation.neg]
      intro he
      have hf := (coverAssignment_var H 0 b).mp he
      rw [hrow,hb] at hf
      cases hf
    | true =>
      simp only [CoverInput.clause,hb,ite_true,Sat.Valuation.satisfies,Sat.Valuation.neg]
      intro he
      exact he ((coverAssignment_var H 0 b).mpr (by rw [hrow,hb]))
  | exclude e =>
    by_contra hs
    have hm : ∀ a b, edge H a b=edge e.mask a b := by
      intro a b
      by_contra he
      apply hs
      apply satisfies_iff _ _ |>.mpr
      let k := vVar a b
      refine ⟨if e.mask.testBit k then .neg k else .pos k,?_,?_⟩
      · apply List.mem_map.mpr
        refine ⟨k,List.mem_range.mpr ?_,rfl⟩
        have := a.isLt; have := b.isLt; dsimp [k,vVar]; omega
      · change ¬(coverAssignment H).neg (if edge e.mask a b then .neg (vVar a b) else .pos (vVar a b))
        cases h0 : edge e.mask a b with
        | false =>
          simp only [h0,Bool.false_eq_true,ite_false,Sat.Valuation.neg,not_not]
          apply (coverAssignment_var H a b).mpr
          cases h1 : edge H a b <;> simp_all
        | true =>
          simp only [h0,ite_true,Sat.Valuation.neg]
          intro hh
          have hh := (coverAssignment_var H a b).mp hh
          exact he (by rw [hh,h0])
    exact hn (e.complete hi cs hcs H V W hrV hp hm)

theorem plane_of_cover_inputs (cs : Fin 676 → CheckedCase) (hcs : ∀ i, (cs i).mask=caseMask i)
    (r : Fin 32) (inputs : List CoverInput) (hi : (inputs.all CoverInput.valid)=true)
    (hc : Sat.Fmla.proof (inputs.map (CoverInput.clause r)) [])
    (H : ℕ) (V : Matrix) (W : ℕ → ℕ → Letter)
    (hrH : Rectangular (edge H)) (hrV : Rectangular V) (hp : Patch H V W)
    (hrow : ∀ b, edge H 0 b=r.val.testBit b.val) : Plane H V := by
  classical
  by_contra hn
  apply hc (coverAssignment H)
  constructor
  intro c hcm
  obtain ⟨i,him,rfl⟩ := List.mem_map.mp hcm
  exact i.satisfied cs hcs r hrH hrV hp hrow hn (List.all_eq_true.mp hi i him)

structure CheckedCover where
  row : Fin 32
  complete : ∀ (cs : Fin 676 → CheckedCase), (∀ i, (cs i).mask=caseMask i) →
    ∀ (H : ℕ) (V : Matrix) (W : ℕ → ℕ → Letter),
    Rectangular (edge H) → Rectangular V → Patch H V W →
    (∀ b, edge H 0 b=row.val.testBit b.val) → Plane H V

end TranslationTiling.Compiler.FiveTile
