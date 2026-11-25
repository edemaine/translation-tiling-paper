import TranslationTiling.FiniteCompiler.SlotShiftMultiplicity

namespace TranslationTiling.FiniteCompiler.SlotShift

open scoped Classical BigOperators

noncomputable section

variable {d : ℕ} [NeZero d] {m : ZMod d → ℕ} [∀ j, NeZero (m j)]

private def countAt {K : Type*} [Fintype K] {a : ℕ} (c : K → ZMod a) (t : ZMod a) : ℤ :=
  ∑ k, if c k = t then 1 else 0

private theorem exists_difference {K : Type*} [Fintype K] {a : ℕ} [NeZero a]
    (c : K → ZMod a) (h : ¬ a ∣ Fintype.card K) :
    ∃ t, countAt c t - countAt c (t-1) ≠ 0 := by
  by_contra! hn
  have hadj (t : ZMod a) : countAt c t = countAt c (t-1) := sub_eq_zero.mp (hn t)
  have hconst (t : ZMod a) : countAt c t = countAt c 0 := by
    have hiter (v : ℕ) : countAt c (v : ZMod a) = countAt c 0 := by
      induction v with
      | zero => simp
      | succ v ih => rw [hadj (↑(v+1)),Nat.cast_add,Nat.cast_one,add_sub_cancel_right,ih]
    simpa only [ZMod.natCast_zmod_val] using hiter t.val
  have hmass : (∑ t, countAt c t) = Fintype.card K := by
    unfold countAt
    rw [Finset.sum_comm]
    simp
  simp_rw [hconst] at hmass
  rw [Finset.sum_const,Finset.card_univ,ZMod.card,nsmul_eq_mul] at hmass
  exact h (by exact_mod_cast (show (a : ℤ) ∣ (Fintype.card K : ℤ) from ⟨_,hmass.symm⟩))

omit [∀ j, NeZero (m j)] in
private theorem prod_indicator (x y : Shift m) :
    (∏ j, (if x j = y j then 1 else 0 : ℤ)) = (if x = y then 1 else 0) := by
  by_cases h : x = y
  · subst y
    simp
  · have hn : ∃ j, x j ≠ y j := by
      by_contra! hn
      exact h (funext hn)
    obtain ⟨j,hj⟩ := hn
    exact (Finset.prod_eq_zero (Finset.mem_univ j) (ite_eq_right hj)).trans (ite_eq_right h).symm

omit [∀ j, NeZero (m j)] in
private theorem sum_bit_correction (x y : Shift m) :
    (∑ u : Bits d, parity u * (if x + bitPoint u = y then 1 else 0 : ℤ)) =
      ∏ j, ((if x j = y j then 1 else 0 : ℤ) - if x j = y j - 1 then 1 else 0) := by
  rw [show (∏ j, ((if x j = y j then 1 else 0 : ℤ) - if x j = y j - 1 then 1 else 0)) =
    ∏ j, ∑ b : Bool, bitSign b * (if x j + (if b then 1 else 0) = y j then 1 else 0 : ℤ) from ?_]
  · rw [Fintype.prod_sum]
    apply Finset.sum_congr rfl
    intro u _
    simp only [parity,Finset.prod_mul_distrib]
    rw [← prod_indicator (x+bitPoint u) y]
    rfl
  · congr 1
    funext j
    have he : x j = y j - 1 ↔ x j + 1 = y j := eq_sub_iff_add_eq
    simp only [he]
    simp [bitSign,neg_ite,sub_eq_add_neg,add_comm]

/-- Uniform coverage is impossible if each observed output depends on
its own independent input and its modulus does not divide the size of
that input. Constant outputs are represented by singleton inputs. -/
theorem independent_inputs_not_bijective (hm : ∀ j, 1 < m j)
    {K : ZMod d → Type*} [∀ j, Fintype (K j)]
    (hdiv : ∀ j, ¬ m j ∣ Fintype.card (K j)) (c : ∀ j, K j → ZMod (m j))
    (high : (∀ j, K j) × Shift m → (∀ j, K j)) :
    ¬ Function.Bijective (fun v => ((fun j => c j (v.1 j)) + shift v.2, high v)) := by
  intro hb
  choose t ht using fun j => exists_difference (c j) (hdiv j)
  let a : Shift m := t
  let out (v : (∀ j, K j) × Shift m) := ((fun j => c j (v.1 j)) + shift v.2, high v)
  have hcount := sum_firstCoordinate_of_bijective out hb a
  have hc : (∑ v : (∀ j, K j) × Shift m, if (out v).1 = a then (1 : ℤ) else 0) =
      Fintype.card (∀ j, K j) := by exact_mod_cast hcount
  have hraw (x : Shift m) : (∑ z : Shift m, if x + z = a then (1 : ℤ) else 0) = 1 := by
    simp_rw [show ∀ z : Shift m, x + z = a ↔ z = a - x by
      intro z; rw [eq_sub_iff_add_eq,add_comm]]
    simp
  let difference (j : ZMod d) (k : K j) : ℤ :=
    (if c j k = a j then 1 else 0) - if c j k = a j-1 then 1 else 0
  have hrow (k : ∀ j, K j) :
      (∑ z : Shift m, if (out (k,z)).1 = a then (1 : ℤ) else 0) =
        1 + ∏ j, difference j (k j) := by
    change (∑ z : Shift m, (fun y => if (fun j => c j (k j)) + y = a then (1 : ℤ) else 0)
      (shift z)) = _
    have h := sum_shift hm (fun y => if (fun j => c j (k j)) + y = a then (1 : ℤ) else 0)
    rw [h, hraw, sum_bit_correction]
  rw [Fintype.sum_prod_type] at hc
  simp_rw [hrow] at hc
  rw [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one] at hc
  have hz : (∑ k : ∀ j, K j, ∏ j, difference j (k j)) = 0 := by omega
  rw [← Fintype.prod_sum] at hz
  have he (j : ZMod d) : (∑ k, difference j k) = countAt (c j) (t j) - countAt (c j) (t j-1) :=
    by unfold difference countAt a; rw [Finset.sum_sub_distrib]
  simp_rw [he] at hz
  exact (Finset.prod_ne_zero_iff.mpr (fun j _ => ht j)) hz

end

end TranslationTiling.FiniteCompiler.SlotShift
