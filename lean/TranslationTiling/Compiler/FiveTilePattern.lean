import Mathlib.Data.ZMod.Basic
import Mathlib.Data.List.FinRange

/-! Finite periodic witnesses for five named Wang symbols. -/
namespace TranslationTiling.Compiler.FiveTile
open scoped Classical
abbrev Letter := Fin 5
abbrev Matrix := Letter → Letter → Bool

def digit (code i : ℕ) : Letter := ⟨code/5^i%5,Nat.mod_lt _ (by decide)⟩
def edge (mask : ℕ) (a b : Letter) : Bool := mask.testBit (5*a.val+b.val)

structure Pattern where
  width : ℕ
  height : ℕ
  code : ℕ

def Pattern.valid (p : Pattern) (H V : ℕ) : Bool :=
  decide (0<p.width ∧ 0<p.height) &&
  (List.range p.height).all fun y => (List.range p.width).all fun x =>
    edge H (digit p.code (x+p.width*y))
      (digit p.code ((x+1)%p.width+p.width*y)) &&
    edge V (digit p.code (x+p.width*y))
      (digit p.code (x+p.width*((y+1)%p.height)))

def Pattern.at (p : Pattern) (x : ZMod p.width) (y : ZMod p.height) : Letter :=
  digit p.code (@ZMod.val p.width x+p.width*@ZMod.val p.height y)

theorem Pattern.edges (p : Pattern) {H V : ℕ} (hc : p.valid H V=true)
    [NeZero p.width] [NeZero p.height] (x : ZMod p.width) (y : ZMod p.height) :
    edge H (p.at x y) (p.at (x+1) y)=true ∧
    edge V (p.at x y) (p.at x (y+1))=true := by
  have hh := List.all_eq_true.mp (List.all_eq_true.mp (show _ from (Bool.and_eq_true_iff.mp hc).2)
    (@ZMod.val p.height y) (List.mem_range.mpr (ZMod.val_lt y)))
    (@ZMod.val p.width x) (List.mem_range.mpr (ZMod.val_lt x))
  simpa only [Pattern.at,ZMod.val_add,ZMod.val_one_eq_one_mod,
    Nat.add_mod,Nat.mod_mod,Bool.and_eq_true] using hh

theorem Pattern.plane (p : Pattern) {H V : ℕ} (hc : p.valid H V=true) :
    ∃ a : ℤ×ℤ → Letter, ∀ z,
      edge H (a z) (a (z.1+1,z.2))=true ∧
      edge V (a z) (a (z.1,z.2+1))=true := by
  have hp := of_decide_eq_true (Bool.and_eq_true_iff.mp hc).1
  letI : NeZero p.width := ⟨by omega⟩
  letI : NeZero p.height := ⟨by omega⟩
  refine ⟨fun z => p.at (z.1 : ZMod p.width) (z.2 : ZMod p.height),fun z => ?_⟩
  simpa only [Int.cast_add,Int.cast_one] using p.edges hc (z.1 : ZMod p.width) (z.2 : ZMod p.height)

end TranslationTiling.Compiler.FiveTile

namespace TranslationTiling.Compiler.FiveTile

def MaskLe (A B : ℕ) : Prop := ∀ a b, edge A a b=true → edge B a b=true

theorem Pattern.valid_mono (p : Pattern) {H V H' V' : ℕ}
    (hp : p.valid H V=true) (hH : MaskLe H H') (hV : MaskLe V V') :
    p.valid H' V'=true := by
  have hp' := Bool.and_eq_true_iff.mp hp
  apply Bool.and_eq_true_iff.mpr
  refine ⟨hp'.1, List.all_eq_true.mpr fun y hy => ?_⟩
  apply List.all_eq_true.mpr
  intro x hx
  have hc := Bool.and_eq_true_iff.mp (List.all_eq_true.mp (List.all_eq_true.mp hp'.2 y hy) x hx)
  exact Bool.and_eq_true_iff.mpr ⟨hH _ _ hc.1,hV _ _ hc.2⟩

end TranslationTiling.Compiler.FiveTile
