import Mathlib.Data.List.Nodup
import Mathlib.Data.Nat.Bitwise

namespace TranslationTiling.FiniteCompiler

/-- A bit records each number already encountered. -/
def distinctCheck (seen : ℕ) : List ℕ → Bool
  | [] => true
  | p::ps => !seen.testBit p && distinctCheck (seen ||| (1 <<< p)) ps

theorem distinctCheck_sound {seen : ℕ} {ps : List ℕ} (h : distinctCheck seen ps=true) :
    ps.Nodup ∧ ∀ p∈ps, seen.testBit p=false := by
  induction ps generalizing seen with
  | nil => simp
  | cons p ps ih =>
    have h' := Bool.and_eq_true_iff.mp h
    obtain ⟨hnd,hs⟩ := ih h'.2
    have hnot : p∉ps := by
      intro hp
      have hh := hs p hp
      rw [Nat.testBit_or, Nat.shiftLeft_eq, one_mul, Nat.testBit_two_pow_self, Bool.or_true] at hh
      contradiction
    refine ⟨List.nodup_cons.mpr ⟨hnot,hnd⟩,?_⟩
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · simpa using h'.1
    · have hh := hs q hq
      rw [Nat.testBit_or] at hh
      exact (Bool.or_eq_false_iff.mp hh).1

end TranslationTiling.FiniteCompiler
