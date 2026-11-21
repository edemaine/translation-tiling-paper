import TranslationTiling.FiniteCompiler.PackedLayout

namespace TranslationTiling.FiniteCompiler.Packed

open scoped BigOperators

noncomputable section

theorem origin_val (p : Profile) (j : Fin p.width) :
    (p.origin j).val =
      if j.val < 18 then j.val else if j.val < 18+p.radices.length then 18 else 19 := by
  unfold Profile.origin
  split_ifs <;> rfl

theorem wangFibre_iff (p : Profile) (j : Fin p.width) (t : Fin 2) :
    p.origin j = ⟨18+t.val, by have := t.isLt; omega⟩ ↔
      18+t.val*p.radices.length ≤ j.val ∧ j.val < 18+(t.val+1)*p.radices.length := by
  have hj := j.isLt
  unfold Profile.width at hj
  rw [Fin.ext_iff, origin_val]
  fin_cases t <;> simp only [Fin.val_zero, Fin.val_one, zero_mul, zero_add, one_mul, Nat.reduceAdd]
  all_goals split_ifs <;> omega

/-- A Wang column is replaced by one column for each digit. -/
def wangFibre (p : Profile) (t : Fin 2) :
    Fin p.radices.length ≃ p.Fibre ⟨18+t.val, by have := t.isLt; omega⟩ := by
  let f : Fin p.radices.length → p.Fibre ⟨18+t.val, by have := t.isLt; omega⟩ :=
    fun j =>
      let v := 18 + t.val*p.radices.length + j.val
      have hv := j.isLt
      have ht : t.val*p.radices.length ≤ p.radices.length := by
        exact (Nat.mul_le_mul_right _ (by have := t.isLt; omega : t.val ≤ 1)).trans_eq (one_mul _)
      ⟨⟨v, by dsimp [v, Profile.width]; omega⟩, (wangFibre_iff p _ t).mpr
        ⟨by dsimp [v]; omega, by dsimp [v]; rw [Nat.add_mul]; omega⟩⟩
  apply Equiv.ofBijective f
  constructor
  · intro j k h
    have he := congrArg (fun v => v.val.val) h
    apply Fin.ext
    dsimp [f] at he
    omega
  · intro j
    obtain ⟨hlo,hhi⟩ := (wangFibre_iff p j.val t).mp j.property
    rw [Nat.add_mul, one_mul] at hhi
    refine ⟨⟨j.val.val-(18+t.val*p.radices.length), by omega⟩, ?_⟩
    apply Subtype.ext
    apply Fin.ext
    dsimp [f]
    omega

theorem arity_original (d : ℕ) (i : Fin 20) :
    PairSmall.arity d i = if i.val < 9 then 4 else if i.val < 18 then 6 else d := by
  fin_cases i <;> rfl

private theorem arithmetic_slope (i : Fin 20) (hi : i.val < 18) :
    PairSmall.slope i =
      (([0,1,2,3,4,5,6,7,10,0,1,2,3,4,7,8,9,14] : List ℕ).getD i.val 0 : ℤ) := by
  fin_cases i <;> first | rfl | contradiction | omega

theorem packedTernary_layout (p : Profile) {k : ℕ} (hk : 0 < k)
    (hr : p.radices = List.replicate k 3) : Layout p := by
  have hlen : p.radices.length = k := by rw [hr, List.length_replicate]
  have hprod : p.radices.prod = 3^k := by rw [hr, List.prod_replicate]
  have hw : p.width = 18+2*k := by rw [Profile.width, hlen]
  have harity (j : Fin p.width) : p.arity j.val =
      if j.val < 9 then 4 else if j.val < 18 then 6 else 3 := by
    have hj := j.isLt
    unfold Profile.arity
    split_ifs with h9 h18 hwidth
    · rfl
    · rfl
    · rw [List.getD_eq_getElem _ _ (Nat.mod_lt _ (by omega : 0 < p.radices.length))]
      simp [hr]
  have hcover : Function.Surjective p.origin := by
    intro i
    by_cases h : i.val < 18
    · refine ⟨⟨i.val, by omega⟩, Fin.ext ?_⟩
      simp only [origin_val, Fin.val_mk, if_pos h]
    · let t : Fin 2 := ⟨i.val-18, by have := i.isLt; omega⟩
      have he : (⟨18+t.val, by have := t.isLt; omega⟩ : Fin 20) = i := Fin.ext (by dsimp [t]; omega)
      obtain ⟨j,hj⟩ := wangFibre p t ⟨0, by omega⟩
      exact ⟨j,hj.trans he⟩
  refine ⟨hcover, ?_, ?_, ?_⟩
  · intro j
    rw [harity]
    split_ifs <;> decide
  · intro i
    by_cases hi : i.val < 18
    · letI : Unique (p.Fibre i) :=
        ⟨⟨⟨i.val, by omega⟩, Fin.ext (by simp [origin_val, hi])⟩,
          fun a => p.arithmetic_unique i hi a _⟩
      rw [Fintype.prod_unique]
      rw [harity, arity_original]
      change (if i.val < 9 then 4 else if i.val < 18 then 6 else 3) = _
      simp only [if_pos hi]
    · let t : Fin 2 := ⟨i.val-18, by have := i.isLt; omega⟩
      have he : (⟨18+t.val, by have := t.isLt; omega⟩ : Fin 20) = i := Fin.ext (by dsimp [t]; omega)
      have hcard : Fintype.card (p.Fibre i) = k := by
        rw [← he, ← Fintype.card_congr (wangFibre p t), Fintype.card_fin, hlen]
      have hall (j : p.Fibre i) : p.arity j.val.val = 3 := by
        have hj : 18 ≤ j.val.val := by
          have ho := congrArg Fin.val j.property
          rw [origin_val] at ho
          split_ifs at ho <;> omega
        rw [harity]
        simp [show ¬ j.val.val < 9 by omega, show ¬ j.val.val < 18 by omega]
      simp only [hall, Finset.prod_const, Finset.card_univ, hcard, arity_original,
        if_neg hi, if_neg (show ¬ i.val < 9 by omega), hprod]
  · intro j
    have ho := origin_val p j
    unfold Profile.slope
    split_ifs with hj hs
    · rw [arithmetic_slope _ (by rw [ho, if_pos hj]; exact hj), ho, if_pos hj]
    · have he : p.origin j = 18 := Fin.ext (by rw [ho, if_neg hj, if_pos hs]; decide)
      rw [he]
      rfl
    · have he : p.origin j = 19 := Fin.ext (by rw [ho, if_neg hj, if_neg hs]; decide)
      rw [he]
      rfl


/-- The guarded board with two groups of ternary Wang-label digits. -/
def ternaryLayoutProfile (k : ℕ) : Profile := ⟨List.replicate k 3, [], []⟩

@[simp] theorem ternaryLayout_width (k : ℕ) :
    (ternaryLayoutProfile k).width = 18 + 2*k := by
  simp [ternaryLayoutProfile, Profile.width]

theorem ternaryLayout_arity {k i : ℕ} (hk : 0 < k)
    (hi : i < (ternaryLayoutProfile k).width) :
    (ternaryLayoutProfile k).arity i = if i < 9 then 4 else if i < 18 then 6 else 3 := by
  unfold Profile.arity
  split_ifs
  · rfl
  · rfl
  · simp only [ternaryLayoutProfile, List.length_replicate]
    rw [List.getD_eq_getElem _ _ (by simpa using Nat.mod_lt (i-18) hk)]
    simp

end
end TranslationTiling.FiniteCompiler.Packed
