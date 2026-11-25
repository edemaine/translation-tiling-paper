import TranslationTiling.FiniteCompiler.SlotShift
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace TranslationTiling.FiniteCompiler.SlotShift

open scoped Classical BigOperators

noncomputable section

variable {d : ℕ} [NeZero d]

def bitSign (b : Bool) : ℤ := if b then -1 else 1

def parity (z : Bits d) : ℤ := ∏ j, bitSign (z j)

private theorem bitSign_xor (a b : Bool) : bitSign (xor a b) = bitSign a * bitSign b := by
  cases a <;> cases b <;> decide

private theorem bitSign_mul_self (b : Bool) : bitSign b * bitSign b = 1 := by
  cases b <;> decide

private theorem bitSign_injective : Function.Injective bitSign := by
  intro a b h
  cases a <;> cases b <;> simp_all [bitSign]

private theorem parity_mul_self (z : Bits d) : parity z * parity z = 1 := by
  rw [parity,← Finset.prod_mul_distrib]
  simp only [bitSign_mul_self,Finset.prod_const_one]

theorem parity_changeBits (z : Bits d) : parity (changeBits z) = 1 := by
  unfold parity changeBits
  simp only [bitSign_xor,Finset.prod_mul_distrib]
  change parity z * (∏ j, bitSign (z ((Equiv.addRight 1) j))) = 1
  have h := Equiv.prod_comp (Equiv.addRight (1 : ZMod d)) (fun j => bitSign (z j))
  rw [h]
  exact parity_mul_self z

private theorem eq_of_parity_eq {a b : Bits d} (i : ZMod d)
    (h : ∀ j ≠ i, a j = b j) (hp : parity a = parity b) : a = b := by
  have he : ∏ j ∈ Finset.univ.erase i, bitSign (a j) =
      ∏ j ∈ Finset.univ.erase i, bitSign (b j) :=
    Finset.prod_congr rfl (fun j hj => congrArg bitSign (h j (Finset.ne_of_mem_erase hj)))
  have hn : (∏ j ∈ Finset.univ.erase i, bitSign (b j)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (by intro j _; cases b j <;> simp [bitSign])
  unfold parity at hp
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i),
    ← Finset.prod_erase_mul _ _ (Finset.mem_univ i),he] at hp
  funext j
  by_cases hj : j = i
  · subst j
    exact bitSign_injective (mul_left_cancel₀ hn hp)
  · exact h j hj

/-- Every even-parity output has two preimages, distinguished by any
one chosen input bit. Odd-parity outputs have empty fibres. -/
def changeBitsFibre (v : Bits d) (hv : parity v = 1) :
    {z : Bits d // changeBits z = v} ≃ Bool where
  toFun z := z.val 0
  invFun b := by
    let R := Equiv.ofBijective (restoreBits ({0} : Set (ZMod d)))
      (restoreBits_bijective (Set.singleton_nonempty 0))
    let z := R.symm (Function.update v 0 b)
    have hz : restoreBits ({0} : Set (ZMod d)) z = Function.update v 0 b :=
      R.apply_symm_apply _
    refine ⟨z,eq_of_parity_eq 0 (fun j hj => ?_) ((parity_changeBits z).trans hv.symm)⟩
    simpa [restoreBits,hj] using congrFun hz j
  left_inv z := by
    apply Subtype.ext
    apply (restoreBits_bijective (Set.singleton_nonempty (0 : ZMod d))).1
    let R := Equiv.ofBijective (restoreBits ({0} : Set (ZMod d)))
      (restoreBits_bijective (Set.singleton_nonempty 0))
    change R (R.symm (Function.update v 0 (z.val 0))) = restoreBits {0} z.val
    rw [R.apply_symm_apply]
    funext i
    by_cases hi : i = 0
    · subst i
      simp [restoreBits]
    · simp [restoreBits,hi,z.property]
  right_inv b := by
    let R := Equiv.ofBijective (restoreBits ({0} : Set (ZMod d)))
      (restoreBits_bijective (Set.singleton_nonempty 0))
    change R.symm (Function.update v 0 b) 0 = b
    have h := congrFun (R.apply_symm_apply (Function.update v 0 b)) 0
    change restoreBits ({0} : Set (ZMod d)) _ 0 = _ at h
    simpa [restoreBits] using h

private theorem sum_changeBits (f : Bits d → ℤ) :
    (∑ z, f (changeBits z)) = ∑ z, (1 + parity z) * f z := by
  classical
  rw [← (Equiv.sigmaFiberEquiv changeBits).sum_comp (fun z => f (changeBits z)),
    Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro z _
  simp only [Equiv.sigmaFiberEquiv, Equiv.coe_fn_mk]
  by_cases hz : parity z = 1
  · have hc := Fintype.card_congr (changeBitsFibre z hz)
    have hterm (y : {x : Bits d // changeBits x = z}) : f (changeBits y.val) = f z :=
      congrArg f y.property
    simp_rw [hterm]
    simp [Finset.sum_const, hc, hz]
  · have hneg := (mul_self_eq_one_iff.mp (parity_mul_self z)).resolve_left hz
    have hf : IsEmpty {x : Bits d // changeBits x = z} :=
      ⟨fun x => hz (x.property ▸ parity_changeBits x.val)⟩
    simp [hneg]

variable {m : ZMod d → ℕ} [∀ j, NeZero (m j)]

/-- Relative to the uniform shift list, the multiplicity correction is
the alternating sum of the binary corners. -/
theorem sum_shift (hm : ∀ j, 1 < m j) (f : Shift m → ℤ) :
    (∑ z, f (shift z)) = (∑ z, f z) + ∑ z : Bits d, parity z * f (bitPoint z) := by
  classical
  let isBit (z : Shift m) := ∃ w : Bits d, bitPoint w = z
  let e : Bits d ≃ {z : Shift m // isBit z} :=
    Equiv.ofBijective (fun w => ⟨bitPoint w, w,rfl⟩)
      ⟨fun _ _ h => (bitPoint_injective hm) (congrArg Subtype.val h),
        fun ⟨_, w,hw⟩ => ⟨w, Subtype.ext hw⟩⟩
  rw [← Fintype.sum_subtype_add_sum_subtype isBit (fun z => f (shift z)),
    ← Fintype.sum_subtype_add_sum_subtype isBit f]
  have hOutside (z : {z : Shift m // ¬ isBit z}) : shift z.val = z.val :=
    dite_eq_right z.property
  simp_rw [hOutside,← e.sum_comp (fun z => f (shift z.val)),
    ← e.sum_comp (fun z => f z.val)]
  change (∑ w : Bits d, f (shift (bitPoint w))) + _ =
    (∑ w : Bits d, f (bitPoint w)) + _ + _
  simp_rw [shift_bitPoint hm]
  have h := sum_changeBits (fun w => f (bitPoint w))
  rw [h]
  simp_rw [add_mul,one_mul,Finset.sum_add_distrib]
  abel

end

end TranslationTiling.FiniteCompiler.SlotShift
