/- Adapted from openai/math, OAI/Geometry/PeriodicTiling, commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a. Apache 2.0; see
third_party/openai-math.LICENSE. Namespace and imports changed for Lean 4.31. -/
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Linarith

namespace TranslationTiling.Activation
universe uα
open scoped BigOperators

def MixedDifferenceZero {a b : ℕ} (Q : ZMod a × ZMod b → ℤ) : Prop :=
  ∀ x y, Q (x, y) - Q (x - 1, y) - Q (x, y - 1) + Q (x - 1, y - 1) = 0

private theorem zmod_eq_zero_of_pred_invariant {n : ℕ} [NeZero n] {α : Type uα}
    (f : ZMod n → α) (hf : ∀ x, f x = f (x - 1)) (x : ZMod n) : f x = f 0 := by
  have hnat : ∀ m : ℕ, f (m : ZMod n) = f 0 := by
    intro m
    induction m with
    | zero => simp only [Nat.cast_zero]
    | succ m ih =>
        calc
          f ((m + 1 : ℕ) : ZMod n) = f (m : ZMod n) := by
            simpa only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right] using
              hf ((m : ZMod n) + 1)
          _ = f 0 := ih
  simpa only [ZMod.natCast_zmod_val] using hnat x.val

theorem mixedDifference_rectangle {a b : ℕ} [NeZero a] [NeZero b]
    (Q : ZMod a × ZMod b → ℤ) (hmixed : MixedDifferenceZero Q)
    (x x₀ : ZMod a) (y : ZMod b) :
    Q (x, y) - Q (x₀, y) = Q (x, 0) - Q (x₀, 0) := by
  have hfirst (z : ZMod a) :
      Q (z, y) - Q (z - 1, y) = Q (z, 0) - Q (z - 1, 0) := by
    apply zmod_eq_zero_of_pred_invariant
      (fun w : ZMod b => Q (z, w) - Q (z - 1, w))
    intro w
    have h := hmixed z w
    linarith only [h]
  have hrow (z : ZMod a) :
      Q (z, y) - Q (z, 0) = Q (0, y) - Q (0, 0) := by
    apply zmod_eq_zero_of_pred_invariant
      (fun w : ZMod a => Q (w, y) - Q (w, 0))
    intro w
    have h := hfirst w
    linarith only [h]
  linarith only [hrow x, hrow x₀]

theorem histogram_separable {a b : ℕ} [NeZero a] [NeZero b]
    (Q : ZMod a × ZMod b → ℕ)
    (hmixed : MixedDifferenceZero (fun z => (Q z : ℤ))) :
    ∃ u : ZMod a → ℕ, ∃ v : ZMod b → ℕ, ∀ x y, Q (x, y) = u x + v y := by
  classical
  obtain ⟨x₀, _hx₀, hmin⟩ := Finset.exists_min_image
    (Finset.univ : Finset (ZMod a)) (fun x => Q (x, 0)) Finset.univ_nonempty
  let u : ZMod a → ℕ := fun x => Q (x, 0) - Q (x₀, 0)
  let v : ZMod b → ℕ := fun y => Q (x₀, y)
  refine ⟨u, v, ?_⟩
  intro x y
  have hle : Q (x₀, 0) ≤ Q (x, 0) := hmin x (Finset.mem_univ x)
  have hrectangle := mixedDifference_rectangle
    (fun z => (Q z : ℤ)) hmixed x x₀ y
  dsimp [u, v]
  omega

theorem histogram_mass_eq {a b : ℕ} [NeZero a] [NeZero b]
    (Q : ZMod a × ZMod b → ℕ) (u : ZMod a → ℕ) (v : ZMod b → ℕ)
    (hsep : ∀ x y, Q (x, y) = u x + v y) :
    (∑ z, Q z) = b * (∑ x, u x) + a * (∑ y, v y) := by
  calc
    (∑ z, Q z) = ∑ x : ZMod a, ∑ y : ZMod b, (u x + v y) := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y _
      exact hsep x y
    _ = b * (∑ x, u x) + a * (∑ y, v y) := by
      simp [Finset.sum_add_distrib, ← Finset.mul_sum]

theorem histogram_mass_dvd {a b D : ℕ} [NeZero a] [NeZero b]
    (Q : ZMod a × ZMod b → ℕ)
    (hmixed : MixedDifferenceZero (fun z => (Q z : ℤ)))
    (hmass : (∑ z, Q z) = D) (hlarge : D < b) : a ∣ D := by
  obtain ⟨u, v, hsep⟩ := histogram_separable Q hmixed
  have htotal : D = b * (∑ x, u x) + a * (∑ y, v y) := by
    rw [← hmass]
    exact histogram_mass_eq Q u v hsep
  have hu : (∑ x, u x) = 0 := by
    by_contra hne
    have hone : 1 ≤ ∑ x, u x := Nat.one_le_iff_ne_zero.mpr hne
    have hmul : b ≤ b * (∑ x, u x) := by
      simpa only [Nat.mul_one] using Nat.mul_le_mul_left b hone
    omega
  refine ⟨∑ y, v y, ?_⟩
  simpa only [hu, Nat.mul_zero, Nat.zero_add] using htotal

end TranslationTiling.Activation
