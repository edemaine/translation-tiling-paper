import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Tactic

namespace TranslationTiling.Compiler.Size

/-- A polynomial bound with coefficient one, valid for every base at least two.
Allowing a larger exponent absorbs all fixed coefficients. -/
def PowerBound (f : ℕ → ℕ) : Prop := ∃ d : ℕ, ∀ b, 2 ≤ b → f b ≤ b ^ d

/-- The degree is retained so that numerical constants can be extracted. -/
def PowerBoundAt (d : ℕ) (f : ℕ → ℕ) : Prop := ∀ b, 2 ≤ b → f b ≤ b ^ d

namespace PowerBoundAt

theorem id : PowerBoundAt 1 (fun b => b) := fun _ _ => by simp

theorem const (c : ℕ) : PowerBoundAt c (fun _ => c) := fun b hb =>
  (Nat.lt_two_pow_self (n := c)).le.trans (Nat.pow_le_pow_left hb c)

theorem mono {d e : ℕ} {f : ℕ → ℕ} (h : PowerBoundAt d f) (hde : d ≤ e) :
    PowerBoundAt e f := fun b hb => (h b hb).trans (Nat.pow_le_pow_right (by omega) hde)

theorem const_le {c d : ℕ} (h : c ≤ d) : PowerBoundAt d (fun _ => c) := (const c).mono h

theorem add {d e : ℕ} {f g : ℕ → ℕ} (hf : PowerBoundAt d f) (hg : PowerBoundAt e g) :
    PowerBoundAt (d + e + 1) (fun b => f b + g b) := by
  intro b hb
  have h1 : 1 ≤ b := by omega
  have hfd := (hf b hb).trans (Nat.pow_le_pow_right h1 (show d ≤ d + e by omega))
  have hge := (hg b hb).trans (Nat.pow_le_pow_right h1 (show e ≤ d + e by omega))
  rw [pow_succ]
  nlinarith

theorem mul {d e : ℕ} {f g : ℕ → ℕ} (hf : PowerBoundAt d f) (hg : PowerBoundAt e g) :
    PowerBoundAt (d + e) (fun b => f b * g b) := by
  intro b hb
  simpa only [pow_add] using Nat.mul_le_mul (hf b hb) (hg b hb)

theorem pow {d : ℕ} {f : ℕ → ℕ} (hf : PowerBoundAt d f) (k : ℕ) :
    PowerBoundAt (d * k) (fun b => f b ^ k) := by
  intro b hb
  simpa only [pow_mul] using Nat.pow_le_pow_left (hf b hb) k

end PowerBoundAt

namespace PowerBound

theorem id : PowerBound (fun b => b) := ⟨1, fun _ _ => by simp⟩

theorem const (c : ℕ) : PowerBound (fun _ => c) := by
  refine ⟨c, fun b hb => ?_⟩
  exact (Nat.lt_two_pow_self (n := c)).le.trans (Nat.pow_le_pow_left hb c)

theorem add {f g : ℕ → ℕ} (hf : PowerBound f) (hg : PowerBound g) :
    PowerBound (fun b => f b + g b) := by
  obtain ⟨d, hd⟩ := hf
  obtain ⟨e, he⟩ := hg
  refine ⟨d + e + 1, fun b hb => ?_⟩
  have h1 : 1 ≤ b := by omega
  have hfd := (hd b hb).trans (Nat.pow_le_pow_right h1 (show d ≤ d + e by omega))
  have hge := (he b hb).trans (Nat.pow_le_pow_right h1 (show e ≤ d + e by omega))
  rw [pow_succ]
  nlinarith

theorem mul {f g : ℕ → ℕ} (hf : PowerBound f) (hg : PowerBound g) :
    PowerBound (fun b => f b * g b) := by
  obtain ⟨d, hd⟩ := hf
  obtain ⟨e, he⟩ := hg
  refine ⟨d + e, fun b hb => ?_⟩
  simpa only [pow_add] using Nat.mul_le_mul (hd b hb) (he b hb)

theorem pow {f : ℕ → ℕ} (hf : PowerBound f) (k : ℕ) :
    PowerBound (fun b => f b ^ k) := by
  obtain ⟨d, hd⟩ := hf
  refine ⟨d * k, fun b hb => ?_⟩
  simpa only [pow_mul] using Nat.pow_le_pow_left (hd b hb) k

end PowerBound

end TranslationTiling.Compiler.Size
