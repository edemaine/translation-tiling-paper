import TranslationTiling.FiniteCompiler.Effective.SlotWordBridge
import TranslationTiling.FiniteCompiler.Effective.MixedInput

namespace TranslationTiling.FiniteCompiler.Packed

open Compiler.Effective FiniteCompiler.Effective

private theorem factorial_primrec : Primrec Nat.factorial := by
  have hf : Primrec (fun _ : Unit => (1 : ℕ)) := Primrec.const _
  have hs := Primrec.to₂ (show Primrec (fun p : Unit × (ℕ × ℕ) => (p.2.1+1)*p.2.2) by fun_prop)
  have hr := (Primrec.nat_rec hf hs).comp (Primrec.const ())
    (Primrec.id : Primrec (id : ℕ → ℕ))
  apply hr.of_eq
  intro n
  induction n with
  | zero => rfl
  | succ n ih => change (n+1)*_ = _; rw [Nat.factorial_succ,← ih]; rfl

theorem choose_primrec : Primrec (fun z : ℕ × ℕ => Nat.choose z.1 z.2) := by
  let f := fun z : ℕ × ℕ =>
    if z.2 ≤ z.1 then z.1.factorial / (z.2.factorial * (z.1-z.2).factorial) else 0
  have hf : Primrec f := by
    unfold f
    have ha := factorial_primrec.comp (Primrec.fst : Primrec (Prod.fst : ℕ × ℕ → ℕ))
    have hb := factorial_primrec.comp (Primrec.snd : Primrec (Prod.snd : ℕ × ℕ → ℕ))
    have hc := factorial_primrec.comp (show Primrec (fun z : ℕ × ℕ => z.1-z.2) by fun_prop)
    fun_prop
  apply hf.of_eq
  intro z
  by_cases h : z.2 ≤ z.1
  · rw [Nat.choose_eq_factorial_div_factorial h]
    simp [f,h]
  · simp [f,h,Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge h)]

theorem clog_primrec : Primrec (fun z : ℕ × ℕ => Nat.clog z.1 z.2) := by
  have hbound : Primrec.PrimrecBounded (fun z : ℕ × ℕ => Nat.clog z.1 z.2) := by
    refine ⟨fun z => z.2, Primrec.snd, ?_⟩
    intro z
    change Nat.clog z.1 z.2 ≤ z.2
    by_cases hb : 1 < z.1
    · apply (Nat.clog_le_iff_le_pow hb).mpr
      have h (n : ℕ) : n+1 ≤ 2^n := by
        induction n with
        | zero => decide
        | succ n ih => rw [pow_succ]; omega
      exact (Nat.le_add_right z.2 1).trans ((h z.2).trans (Nat.pow_le_pow_left hb _))
    · simp [Nat.clog_of_left_le_one (Nat.le_of_not_gt hb)]
  apply Primrec.of_graph hbound
  have h : PrimrecPred (fun z : (ℕ × ℕ) × ℕ =>
      (z.1.1 ≤ 1 ∧ z.2 = 0) ∨
      (1 < z.1.1 ∧ z.1.2 ≤ z.1.1^z.2 ∧ (z.2 = 0 ∨ z.1.1^(z.2-1) < z.1.2))) := by
    fun_prop
  apply h.of_eq
  rintro ⟨⟨b,n⟩,k⟩
  by_cases hb : 1 < b
  · simp only [hb,Nat.not_le_of_gt hb,false_and,false_or,true_and]
    constructor
    · rintro ⟨hle,hk⟩
      apply le_antisymm
      · exact (Nat.clog_le_iff_le_pow hb).mpr hle
      · rcases hk with rfl | hk
        · exact Nat.zero_le _
        · have hlt := (Nat.lt_clog_iff_pow_lt hb).mpr hk
          omega
    · intro he
      subst k
      refine ⟨Nat.le_pow_clog hb _,?_⟩
      by_cases hn : Nat.clog b n = 0
      · exact Or.inl hn
      · exact Or.inr (Nat.pow_lt_of_lt_clog (by omega))
  · simp [hb,Nat.le_of_not_gt hb,Nat.clog_of_left_le_one (Nat.le_of_not_gt hb),eq_comm]

theorem slotLengthParameter_primrec : Primrec slotLengthParameter := by
  unfold slotLengthParameter
  have hl := natLog_primrec 2 (by decide)
  have hh := hl.comp hl
  fun_prop

theorem slotRadix_primrec : Primrec (fun z : ℕ × ℕ => slotRadix z.1 z.2) := by
  unfold slotRadix
  have h := choose_primrec
  fun_prop

theorem slotPackedDigits_primrec : Primrec (fun z : ℕ × ℕ => slotPackedDigits z.1 z.2) := by
  unfold slotPackedDigits
  have h : Primrec (fun z : ℕ × ℕ => (4*z.2,3*z.2)) := by fun_prop
  have hr := slotRadix_primrec.comp h
  have hc := clog_primrec.comp (hr.pair Primrec.fst)
  fun_prop

end TranslationTiling.FiniteCompiler.Packed
