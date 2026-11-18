import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Linarith

/-! Mixed-radix indices with explicit bounds and inverse arithmetic. -/
namespace TranslationTiling.CompactIndex

def pack (b u x : ℕ) : ℕ := b*u+x

theorem pack_injective {b u v x y : ℕ} (hb : 0<b) (hx : x<b) (hy : y<b)
    (h : pack b u x=pack b v y) : u=v ∧ x=y := by
  have hu := congrArg (fun n => n/b) h
  simp only [pack,Nat.mul_add_div hb,Nat.div_eq_of_lt hx,Nat.div_eq_of_lt hy,Nat.add_zero] at hu
  refine ⟨hu,?_⟩
  unfold pack at h
  rw [hu] at h
  exact Nat.add_left_cancel h

theorem pack_lt {b u x c : ℕ} (hu : u<c) (hx : x<b) : pack b u x<b*c := by
  have hm := Nat.mul_le_mul_left b (Nat.succ_le_of_lt hu)
  unfold pack
  nlinarith

end TranslationTiling.CompactIndex
