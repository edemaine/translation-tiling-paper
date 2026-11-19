import TranslationTiling.Compiler.FiveTilePattern
import Mathlib.Tactic.Sat.FromLRAT

/-! Checked input clauses for the split five-symbol classification. -/
namespace TranslationTiling.Compiler.FiveTile
open Mathlib.Tactic
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def Plane (H : ℕ) (V : Matrix) : Prop :=
  ∃ a : ℤ×ℤ → Letter, ∀ z, edge H (a z) (a (z.1+1,z.2))=true ∧ V (a z) (a (z.1,z.2+1))=true

def Rectangular (V : Matrix) : Prop :=
  ∀ a b c d, V a c=true → V b c=true → V a d=V b d

def maskLE (A B : ℕ) : Bool :=
  (List.range 25).all fun i => !A.testBit i || B.testBit i

theorem maskLE_sound {A B : ℕ} (h : maskLE A B=true) : MaskLe A B := by
  intro a b hab
  have hi : 5*a.val+b.val<25 := by have := a.isLt; have := b.isLt; omega
  have hh := List.all_eq_true.mp h (5*a.val+b.val) (List.mem_range.mpr hi)
  change A.testBit (5*a.val+b.val)=true at hab
  change B.testBit (5*a.val+b.val)=true
  simpa only [hab,Bool.not_true,Bool.false_or] using hh

inductive Input where
  | rectangular (a b c d : Letter)
  | choice (x y : ℕ)
  | distinct (x y : ℕ) (a b : Letter)
  | horizontal (x y : ℕ) (a b : Letter)
  | vertical (x y : ℕ) (a b : Letter)
  | exclude (H V : ℕ) (p : Pattern)

def vVar (a b : Letter) : ℕ := 5*a.val+b.val
def cVar (w x y : ℕ) (a : Letter) : ℕ := 25+5*(w*y+x)+a.val

def Input.clause (w : ℕ) : Input → Sat.Clause
  | .rectangular a b c d => [.neg (vVar a c),.neg (vVar b c),.neg (vVar a d),.pos (vVar b d)]
  | .choice x y => (List.finRange 5).map fun a => .pos (cVar w x y a)
  | .distinct x y a b => [.neg (cVar w x y a),.neg (cVar w x y b)]
  | .horizontal x y a b => [.neg (cVar w x y a),.neg (cVar w (x+1) y b)]
  | .vertical x y a b => [.neg (cVar w x y a),.neg (cVar w x (y+1) b),.pos (vVar a b)]
  | .exclude _ V _ => ((List.range 25).filter fun i => V.testBit i).map fun i => .neg i

def Input.valid (H w h : ℕ) : Input → Bool
  | .rectangular _ _ _ _ => true
  | .choice x y => decide (x<w ∧ y<h)
  | .distinct x y a b => decide (x<w ∧ y<h ∧ a≠b)
  | .horizontal x y a b => decide (x+1<w ∧ y<h) && !edge H a b
  | .vertical x y _ _ => decide (x<w ∧ y+1<h)
  | .exclude A B p => p.valid A B && maskLE A H

def assignment (w : ℕ) (V : Matrix) (W : ℕ → ℕ → Letter) : Sat.Valuation := fun k =>
  if k<25 then V ⟨k/5%5,Nat.mod_lt _ (by decide)⟩ ⟨k%5,Nat.mod_lt _ (by decide)⟩=true
  else (W ((k-25)/5%w) ((k-25)/5/w)).val=(k-25)%5

theorem assignment_vVar (w : ℕ) (V : Matrix) (W : ℕ → ℕ → Letter) (a b : Letter) :
    assignment w V W (vVar a b) ↔ V a b=true := by
  have ha := a.isLt; have hb := b.isLt
  have hi : vVar a b<25 := by dsimp [vVar]; omega
  have h1 : (5*a.val+b.val)/5%5=a.val := by omega
  have h2 : (5*a.val+b.val)%5=b.val := by omega
  unfold assignment
  rw [if_pos hi]
  simp only [vVar,h1,h2,Fin.eta]

theorem assignment_cVar (w : ℕ) (V : Matrix) (W : ℕ → ℕ → Letter)
    (x y : ℕ) (a : Letter) (hx : x<w) :
    assignment w V W (cVar w x y a) ↔ W x y=a := by
  have ha := a.isLt
  have hi : ¬cVar w x y a<25 := by dsimp [cVar]; omega
  have h1 : (5*(w*y+x)+a.val)/5=w*y+x := by omega
  have h2 : (5*(w*y+x)+a.val)%5=a.val := by omega
  have h3 : (w*y+x)%w=x := by simp [Nat.add_mod,Nat.mod_eq_of_lt hx]
  have h4 : (w*y+x)/w=y := by rw [Nat.mul_add_div (by omega : 0<w)]; simp [Nat.div_eq_of_lt hx]
  unfold assignment
  rw [if_neg hi]
  have hs : 25+5*(w*y+x)+a.val-25=5*(w*y+x)+a.val := by omega
  simp only [cVar,hs,h1,h2,h3,h4,Fin.ext_iff]

private theorem satisfies_iff (v : Sat.Valuation) (c : List Sat.Literal) :
    v.satisfies c ↔ ∃ l∈c, ¬v.neg l := by
  classical
  induction c with
  | nil => simp [Sat.Valuation.satisfies]
  | cons l c ih =>
    simp only [Sat.Valuation.satisfies,ih,List.mem_cons]
    by_cases h : v.neg l <;> simp_all

end TranslationTiling.Compiler.FiveTile

namespace TranslationTiling.Compiler.FiveTile
open Mathlib.Tactic

theorem Input.satisfied {H w h : ℕ} (V : Matrix) (W : ℕ → ℕ → Letter)
    (hr : Rectangular V)
    (hh : ∀ x y, x+1<w → y<h → edge H (W x y) (W (x+1) y)=true)
    (hv : ∀ x y, x<w → y+1<h → V (W x y) (W x (y+1))=true)
    (hn : ¬Plane H V) (i : Input) (hi : i.valid H w h=true) :
    (assignment w V W).satisfies (i.clause w) := by
  classical
  cases i with
  | rectangular a b c d =>
    simp only [Input.clause,Sat.Valuation.satisfies,Sat.Valuation.neg]
    intro hac hbc had hbd
    apply hbd
    apply (assignment_vVar w V W b d).mpr
    rw [←hr a b c d ((assignment_vVar w V W a c).mp hac) ((assignment_vVar w V W b c).mp hbc)]
    exact (assignment_vVar w V W a d).mp had
  | choice x y =>
    have hb := of_decide_eq_true hi
    apply satisfies_iff _ _ |>.mpr
    refine ⟨.pos (cVar w x y (W x y)),?_,?_⟩
    · exact List.mem_map.mpr ⟨W x y,by simp,rfl⟩
    · simpa only [Sat.Valuation.neg,not_not] using (assignment_cVar w V W x y (W x y) hb.1).mpr rfl
  | distinct x y a b =>
    have hb := of_decide_eq_true hi
    simp only [Input.clause,Sat.Valuation.satisfies,Sat.Valuation.neg]
    intro ha hb'
    exact hb.2.2 (((assignment_cVar w V W x y a hb.1).mp ha).symm.trans
      ((assignment_cVar w V W x y b hb.1).mp hb'))
  | horizontal x y a b =>
    have hi' := Bool.and_eq_true_iff.mp hi
    have hb := of_decide_eq_true hi'.1
    simp only [Input.clause,Sat.Valuation.satisfies,Sat.Valuation.neg]
    intro ha hb'
    have ha := (assignment_cVar w V W x y a (by omega)).mp ha
    have hb' := (assignment_cVar w V W (x+1) y b hb.1).mp hb'
    have he := hh x y hb.1 hb.2
    rw [ha,hb'] at he
    have hf := hi'.2
    simp [he] at hf
  | vertical x y a b =>
    have hb := of_decide_eq_true hi
    simp only [Input.clause,Sat.Valuation.satisfies,Sat.Valuation.neg]
    intro ha hb' hc
    apply hc
    apply (assignment_vVar w V W a b).mpr
    have ha := (assignment_cVar w V W x y a hb.1).mp ha
    have hb' := (assignment_cVar w V W x (y+1) b hb.1).mp hb'
    simpa only [ha,hb'] using hv x y hb.1 hb.2
  | exclude A B p =>
    have hi' := Bool.and_eq_true_iff.mp hi
    by_contra hs
    have hB : ∀ a b, edge B a b=true → V a b=true := by
      intro a b hab
      apply (assignment_vVar w V W a b).mp
      by_contra hn'
      apply hs
      apply satisfies_iff _ _ |>.mpr
      refine ⟨.neg (vVar a b),?_,?_⟩
      · apply List.mem_map.mpr
        refine ⟨vVar a b,List.mem_filter.mpr ⟨List.mem_range.mpr ?_,hab⟩,rfl⟩
        have := a.isLt; have := b.isLt; dsimp [vVar]; omega
      · exact hn'
    obtain ⟨g,hg⟩ := p.plane hi'.1
    apply hn
    exact ⟨g,fun z => ⟨maskLE_sound hi'.2 _ _ (hg z).1,hB _ _ (hg z).2⟩⟩

end TranslationTiling.Compiler.FiveTile

namespace TranslationTiling.Compiler.FiveTile
open Mathlib.Tactic

def Patch (H : ℕ) (V : Matrix) (W : ℕ → ℕ → Letter) : Prop :=
  (∀ x y, x+1<11 → y<11 → edge H (W x y) (W (x+1) y)=true) ∧
  (∀ x y, x<11 → y+1<11 → V (W x y) (W x (y+1))=true)

theorem plane_of_inputs {H w h : ℕ} (inputs : List Input)
    (hi : (inputs.all (Input.valid H w h))=true)
    (hc : Sat.Fmla.proof (inputs.map (Input.clause w)) [])
    (hw : w≤11) (hh : h≤11)
    (V : Matrix) (W : ℕ → ℕ → Letter) (hr : Rectangular V) (hp : Patch H V W) :
    Plane H V := by
  classical
  by_contra hn
  apply hc (assignment w V W)
  constructor
  intro c hcm
  obtain ⟨i,him,rfl⟩ := List.mem_map.mp hcm
  apply i.satisfied (H:=H) (w:=w) (h:=h) V W hr
  · intro x y hx hy
    exact hp.1 x y (by omega) (by omega)
  · intro x y hx hy
    exact hp.2 x y (by omega) (by omega)
  · exact hn
  · exact List.all_eq_true.mp hi i him

structure CheckedCase where
  mask : ℕ
  complete : ∀ (V : Matrix) (W : ℕ → ℕ → Letter), Rectangular V → Patch mask V W → Plane mask V

end TranslationTiling.Compiler.FiveTile
