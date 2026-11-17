import TranslationTiling.SudokuArithmetic.SmallPrimeSAT
namespace TranslationTiling.Sudoku.ArithmeticRule.SmallPrime
open Mathlib.Tactic
open scoped Classical
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

def lineCode (p : Nat) (d e : Int) : Line p :=
  (⟨(d+4).toNat%9,Nat.mod_lt _ (by decide)⟩,
   ⟨(e+4*width p).toNat%extent p,Nat.mod_lt _ (by unfold extent; omega)⟩)

theorem lineCode_correct (p : Nat) (d e : Int)
    (hd : -4≤d ∧ d≤4) (he : -4*(width p:Int)≤e ∧ e<13+4*(width p:Int)) :
    direction (lineCode p d e)=d ∧ intercept (lineCode p d e)=e := by
  have hd0 : 0≤d+4 := by omega
  have hd9 : (d+4).toNat<9 := by omega
  have he0 : 0≤e+4*width p := by omega
  have heE : (e+4*width p).toNat<extent p := by unfold extent; omega
  simp only [lineCode,direction,intercept,Nat.mod_eq_of_lt hd9,Nat.mod_eq_of_lt heE,
    Int.toNat_of_nonneg hd0,Int.toNat_of_nonneg he0]
  constructor <;> omega

theorem pattern_bounds (h : Nat) (hh : h=2 ∨ h=4) (d : Int) (i j : Nat)
    (hm : (d,i,j)∈pattern h) : 0≤d ∧ d≤4 ∧ i≤4 ∧ j≤2*h := by
  rcases hh with rfl|rfl <;> simp [pattern] at hm <;>
    rcases hm with h|h|h|h|h|h|h|h|h|h <;> obtain ⟨rfl,rfl,rfl⟩ := h <;> norm_num

theorem clean_seed_coordinates {p : Nat} [Fact p.Prime] {W : WordArray p}
    (hW : LineRule p W) (hu : Sat.Fmla.proof (satFormula p) []) :
    ∃ h : Nat, (h=2 ∨ h=4) ∧ ∃ r q : Int, 0≤r ∧ r+4<(wordWidth p:Nat) ∧
      ∀ d : Int, ∀ i j : Nat, (d,i,j)∈pattern h →
        (chooseLine hW d (q+j-d*(r+i))).a*((r+i:Int):ZMod p)+
          (chooseLine hW d (q+j-d*(r+i))).b≠0 := by
  obtain ⟨h,hh,r,hr,q,hq,hclean⟩ := exists_clean_seed_sat hW hu
  have hh' : h=2 ∨ h=4 := by simpa using hh
  refine ⟨h,hh',r,q,by omega,by have := List.mem_range.mp hr; dsimp [width,wordWidth] at *; omega,?_⟩
  intro d i j hm
  have hm' : (d,i,j)∈pattern h := by simpa using hm
  have hb := pattern_bounds h hh' d i j hm'
  have hr' := List.mem_range.mp hr
  have hq' := List.mem_range.mp hq
  let x := r+i
  let e : Int := (q+j:Int)-d*x
  have hx : x<width p := by dsimp [x]; omega
  have hy : q+j<13 := by rcases hh' with rfl|rfl <;> omega
  have hxn : (0:Int)≤x := by omega
  have hde := lineCode_correct p d e ⟨by omega,hb.2.1⟩ (by dsimp [e]; constructor <;> nlinarith [Nat.zero_le i,Nat.zero_le r])
  have hz := hclean ((bad (lineCode p d e) ⟨x%width p,Nat.mod_lt _ (by unfold width; omega)⟩),true) (by
    apply List.mem_map.mpr
    exact ⟨(d,i,j),hm',rfl⟩)
  change decide ((chooseLine hW (direction (lineCode p d e)) (intercept (lineCode p d e))).a*((x%width p:Nat):ZMod p)+(chooseLine hW (direction (lineCode p d e)) (intercept (lineCode p d e))).b=0)=false at hz
  rw [decide_eq_false_iff_not,hde.1,hde.2,Nat.mod_eq_of_lt hx] at hz
  simpa [e,x,Int.cast_add] using hz
end
end TranslationTiling.Sudoku.ArithmeticRule.SmallPrime
