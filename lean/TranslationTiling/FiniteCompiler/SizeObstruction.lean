import TranslationTiling.FiniteCompiler.GraphTests
import TranslationTiling.FiniteCompiler.Parameters
import Mathlib.Data.Finset.Max
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Order.Interval.Finset.Nat

/-!
# A size obstruction for the current finite-channel encoding

The useful-output moduli are distinct primes. Their product already forces a
factorial lower bound on the graph-kernel tile, independently of the digit
moduli and of all later geometric steps. This is an obstruction for this
encoding, not a lower bound for arbitrary Wang-to-polycube reductions.
-/

namespace TranslationTiling.FiniteCompiler

open scoped BigOperators

private theorem factorial_succ_card_le_prod_of_two_le (s : Finset ℕ)
    (hs : ∀ x ∈ s, 2 ≤ x) : (s.card + 1).factorial ≤ ∏ x ∈ s, x := by
  classical
  induction s using Finset.strongInductionOn with | _ s ih
  rcases s.eq_empty_or_nonempty with rfl | hne
  · simp
  let m := s.max' hne
  have hm : m ∈ s := s.max'_mem hne
  have hsub : s ⊆ Finset.Icc 2 m := by
    intro x hx
    exact Finset.mem_Icc.mpr ⟨hs x hx, Finset.le_max' s x hx⟩
  have hcard : s.card + 1 ≤ m := by
    have hc := Finset.card_le_card hsub
    have hm2 := hs m hm
    simp only [Nat.card_Icc] at hc
    omega
  have herase := ih (s.erase m) (Finset.erase_ssubset hm)
    (fun x hx => hs x (Finset.mem_of_mem_erase hx))
  have hc := Finset.card_erase_add_one hm
  calc
    (s.card + 1).factorial = (s.card + 1) * ((s.erase m).card + 1).factorial := by
      rw [hc, Nat.factorial_succ]
    _ ≤ m * ∏ x ∈ s.erase m, x := Nat.mul_le_mul hcard herase
    _ = ∏ x ∈ s, x := Finset.mul_prod_erase s id hm

/-- Distinct integers at least two have product at least the successor
factorial of the size of their index type. -/
theorem factorial_succ_card_le_prod_of_injective {ι : Type*} [Fintype ι]
    (f : ι → ℕ) (hf : Function.Injective f) (hf2 : ∀ i, 2 ≤ f i) :
    (Fintype.card ι + 1).factorial ≤ ∏ i, f i := by
  classical
  have h := factorial_succ_card_le_prod_of_two_le
    (Finset.univ.image f) (by
      intro x hx
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
      exact hf2 i)
  simpa only [Finset.card_image_of_injective _ hf, Finset.card_univ,
    Finset.prod_image hf.injOn] using h

noncomputable section

variable {T : System} (E : EncodingParameters T)

/-- The product of the current encoding's useful-output primes has factorial
growth in the number of channels. -/
theorem factorial_usefulPrimeProduct_le :
    (2 * channelCount T + 1).factorial ≤ ∏ i : Channel T, E.a i * E.b i := by
  let f : Channel T ⊕ Channel T → ℕ := Sum.elim E.a E.b
  have hf : Function.Injective f := by
    intro i j hij
    cases i with
    | inl i =>
      cases j with
      | inl j => exact congrArg Sum.inl (Sum.inl.inj (E.prime_injective hij))
      | inr j => cases E.prime_injective hij
    | inr i =>
      cases j with
      | inl j => cases E.prime_injective hij
      | inr j =>
        exact congrArg Sum.inr (Sum.inl.inj (Sum.inr.inj (E.prime_injective hij)))
  have h := factorial_succ_card_le_prod_of_injective f hf (by
    intro i
    cases i with
    | inl i => exact E.a_two_le i
    | inr i => exact E.b_two_le i)
  have hc : Fintype.card (Channel T ⊕ Channel T) = 2 * channelCount T := by
    rw [Fintype.card_sum, channel_card]
    omega
  rw [hc] at h
  simpa only [Fintype.prod_sum_type, f, Sum.elim_inl, Sum.elim_inr,
    Finset.prod_mul_distrib] using h

/-- The full useful-output space embeds into the graph-kernel tile. -/
theorem useful_card_le_kernelTile_card :
    Fintype.card (Useful E) ≤ (kernelTile E).card := by
  classical
  let f : Useful E → ↥(kernelTile E) := fun e =>
    ⟨(0, 0, fun i => (0, e i)), by
      rw [mem_kernelTile]
      exact Prod.ext rfl (funext fun i => map_zero (low E i))⟩
  have hf : Function.Injective f := by
    intro e e' h
    exact funext fun i => congrArg (fun v : ↥(kernelTile E) => ((v : Ambient E).2.2 i).2) h
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hf

/-- The current finite-channel construction already has factorial size before
stacking or geometric assembly. -/
theorem factorial_le_kernelTile_card :
    (2 * channelCount T + 1).factorial ≤ (kernelTile E).card := by
  apply (factorial_usefulPrimeProduct_le E).trans
  have h := useful_card_le_kernelTile_card E
  simpa only [Useful, Fintype.card_pi, P, Fintype.card_prod, ZMod.card] using h

end

end TranslationTiling.FiniteCompiler
