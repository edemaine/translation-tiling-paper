import TranslationTiling.FiniteCompiler.Effective.AxisSlotLayout

namespace TranslationTiling.FiniteCompiler.Packed

open SharedCoordinates
open scoped Classical BigOperators

noncomputable section

namespace AxisParameters

variable {k m : ℕ} (s : AxisParameters k m)

private def owner : AxisPrime k m → AxisAddedRow k m
  | .inl (i,_) => .inl i
  | .inr f => .inr f

private def factors : AxisAddedRow k m → List (AxisPrime k m)
  | .inl i => [.inl (i,.inl false),.inl (i,.inl true),.inl (i,.inl false),.inl (i,.inl true)] ++
    List.ofFn (fun j : Fin 3 => .inl (i,.inr j))
  | .inr i => [.inr i]

private theorem owner_of_mem (i : AxisAddedRow k m) {t : AxisPrime k m} (ht : t ∈ factors i) :
    owner t = i := by
  rcases i with i | i
  · simp only [factors,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,List.mem_ofFn] at ht
    rcases ht with (rfl | rfl | rfl | rfl) | ⟨_,rfl⟩ <;> rfl
  · have he : t = Sum.inr i := by simpa [factors] using ht
    subst t
    rfl

private theorem modulus_eq (i : AxisAddedRow k m) :
    rowModulus s.layout (.inr i) = ((factors i).map s.prime).prod := by
  rcases i with i | i
  · simp only [factors,List.map_append,List.prod_append,List.map_cons,List.prod_cons,
      List.map_ofFn,List.prod_ofFn]
    change s.low i ^ 2 * 1 * _ = _
    simp only [low,lowAxis,layout,marker,Function.comp_apply,List.map_nil,List.prod_nil]
    ring
  · simp [factors,rowModulus,layout,fallback]

private theorem pairwise_added :
    Pairwise fun i j : AxisAddedRow k m =>
      (rowModulus s.layout (.inr i)).Coprime (rowModulus s.layout (.inr j)) := by
  intro i j hij
  rw [modulus_eq s i,modulus_eq s j]
  apply Nat.coprime_list_prod_left_iff.mpr
  intro p hp
  apply Nat.coprime_list_prod_right_iff.mpr
  intro q hq
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hp
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hq
  apply (Nat.coprime_primes (s.prime_isPrime a) (s.prime_isPrime b)).mpr
  intro h
  have he := s.prime_injective h
  exact hij ((owner_of_mem i ha).symm.trans (he ▸ owner_of_mem j hb))

private theorem arithmetic_coprime :
    (order (fourValueLayout 0)).Coprime (∏ i : AxisAddedRow k m, rowModulus s.layout (.inr i)) := by
  apply Nat.coprime_fintype_prod_right_iff.mpr
  intro i
  rw [modulus_eq]
  apply Nat.coprime_list_prod_right_iff.mpr
  intro q hq
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp hq
  exact (s.coprime_arithmetic j).symm

private theorem internal_coprime (i : AxisAddedRow k m) :
    ((s.layout.lowSize (.inr i))^2 * s.layout.firstSize (.inr i)).Coprime
      (s.layout.secondSize (.inr i)) := by
  rcases i with i | i
  · change (s.low i ^ 2 * 1).Coprime (∏ j, s.marker i j)
    rw [mul_one]
    apply Nat.coprime_fintype_prod_right_iff.mpr
    intro j
    apply Nat.Coprime.pow_left
    unfold low
    apply Nat.Coprime.mul_left
    · exact s.prime_coprime (by intro h; cases h)
    · exact s.prime_coprime (by intro h; cases h)
  · change (1^2 * 1 : ℕ).Coprime (s.fallback i)
    simp

/-- Appending the slot rows preserves the arithmetic-frame projection. -/
def splitFactor : Factor s.layout ≃+* Factor (fourValueLayout 0) ×
    (∀ i : AxisAddedRow k m, Private s.layout (.inr i)) where
  toFun v := ((v.1,fun i => v.2 (.inl i)),fun i => v.2 (.inr i))
  invFun v := (v.1.1,fun
    | .inl i => v.1.2 i
    | .inr i => v.2 i)
  left_inv v := Prod.ext rfl (funext fun i => by cases i <;> rfl)
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

theorem order_split : order s.layout =
    order (fourValueLayout 0) * (∏ i : AxisAddedRow k m, rowModulus s.layout (.inr i)) := by
  rw [order,order,Fintype.prod_sum_type,← mul_assoc]
  rfl

/-- A cap on the added primes and the fixed arithmetic primes bounds
all primes of the layout, including the repeated low factors. -/
theorem primeBound {P : ℕ} (h₀ : SlotParameters.slotBasePrimeCap ≤ P)
    (h : ∀ i, s.prime i ≤ P) : Effective.PrimeBound (order s.layout) P := by
  intro q _
  by_cases hq : q.Prime
  · right
    by_cases hd : q ∣ order s.layout
    · right
      rw [s.order_split] at hd
      rcases hq.dvd_mul.mp hd with hd | hd
      · have hle := Nat.le_of_dvd (fourValueOrder_pos 0) hd
        have hbase := SlotParameters.slotBasePrimeBound q (List.mem_range.mpr (by omega))
        exact ((hbase.resolve_left (not_not.mpr hq)).resolve_left (not_not.mpr hd)).trans h₀
      · obtain ⟨i,_,hi⟩ := (hq.prime.dvd_finsetProd_iff _).mp hd
        rw [s.modulus_eq] at hi
        by_contra! hlt
        have he : q.Coprime ((factors i).map s.prime).prod := by
          apply Nat.coprime_list_prod_right_iff.mpr
          intro p hp
          obtain ⟨j,_,rfl⟩ := List.mem_map.mp hp
          exact hq.coprime_iff_not_dvd.mpr
            (Nat.not_dvd_of_pos_of_lt (s.prime_isPrime j).pos ((h j).trans_lt hlt))
        exact (hq.coprime_iff_not_dvd.mp he) hi
    · exact Or.inl hd
  · exact Or.inl hq

/-- The entire finite factor is cyclic. -/
def crt : ZMod (order s.layout) ≃+* Factor s.layout := by
  rw [order_split]
  exact (ZMod.chineseRemainder (arithmetic_coprime s)).trans
    (((fourValueLayoutCRT 0).prodCongr
      ((ZMod.prodEquivPi _ (pairwise_added s)).trans
        (RingEquiv.piCongrRight fun i => privateCRT s.layout (.inr i)
          (by change Nat.Coprime _ 1; simp) (internal_coprime s i)))).trans (splitFactor s).symm)

end AxisParameters

end

end TranslationTiling.FiniteCompiler.Packed
