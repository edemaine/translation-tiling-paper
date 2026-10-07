import Mathlib.Data.ZMod.Basic
import TranslationTiling.Compiler.EffectiveArithmetic

namespace TranslationTiling.Compiler.Effective

/-- A finite list of modulus/residue pairs. -/
abbrev CongruenceList := List (ℕ × ℕ)

def Congruences (cs : CongruenceList) (n : ℕ) : Prop :=
  ∀ c ∈ cs, n % c.1 = c.2 % c.1

instance (cs : CongruenceList) (n : ℕ) : Decidable (Congruences cs n) := by
  unfold Congruences
  infer_instance

theorem congruences_primrec : PrimrecPred (fun z : CongruenceList × ℕ =>
    Congruences z.1 z.2) := by unfold Congruences; fun_prop

/-- Bounded Chinese-remainder search. Its specification supplies uniqueness;
the executable search itself needs only natural numbers. -/
def residueSearch (M : ℕ) (cs : CongruenceList) : ℕ :=
  ((List.range M).filter fun n => decide (Congruences cs n)).headD 0

theorem residueSearch_primrec : Primrec (fun z : ℕ × CongruenceList =>
    residueSearch z.1 z.2) := by
  unfold residueSearch
  have hf : Primrec (fun z : ℕ × CongruenceList =>
      (List.range z.1).filter fun n => decide (Congruences z.2 n)) := by
    apply filterList (by fun_prop)
    exact congruences_primrec.comp ((Primrec.snd.comp Primrec.fst).pair Primrec.snd)
  simpa only [List.headD_eq_head?_getD] using
    Primrec.option_getD.comp (Primrec.list_head?.comp hf) (Primrec.const 0)

theorem residueSearch_eq {M x : ℕ} {cs : CongruenceList} (hx : x < M)
    (hc : Congruences cs x) (hu : ∀ n, n < M → Congruences cs n → n = x) :
    residueSearch M cs = x := by
  let xs := (List.range M).filter fun n => decide (Congruences cs n)
  have hxmem : x ∈ xs := List.mem_filter.mpr ⟨List.mem_range.mpr hx, by simpa⟩
  have hh : xs.headD 0 ∈ xs := by
    cases hs : xs with
    | nil => simp only [hs, List.not_mem_nil] at hxmem
    | cons a as => simp
  obtain ⟨hr, hp⟩ := List.mem_filter.mp hh
  exact hu _ (List.mem_range.mp hr) (of_decide_eq_true hp)

theorem residueSearch_of_equiv {M : ℕ} [NeZero M] {R : Type*}
    (e : ZMod M ≃ R) (v : R) (cs : CongruenceList)
    (hspec : ∀ n, Congruences cs n ↔ e (n : ZMod M) = v) :
    residueSearch M cs = (e.symm v).val := by
  apply residueSearch_eq (ZMod.val_lt _)
  · apply (hspec _).mpr
    rw [ZMod.natCast_zmod_val, e.apply_symm_apply]
  · intro n hn hc
    have he : (n : ZMod M) = e.symm v :=
      e.injective ((hspec n).mp hc |>.trans (e.apply_symm_apply v).symm)
    have hv := congrArg ZMod.val he
    simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt hn] using hv

/-- Canonical residue of a difference, including negative differences. -/
def differenceResidue (M a b : ℕ) : ℕ :=
  (((a : ℤ) - (b : ℤ)) % (M : ℤ)).toNat

theorem differenceResidue_primrec :
    Primrec (fun z : ℕ × ℕ × ℕ => differenceResidue z.1 z.2.1 z.2.2) := by
  unfold differenceResidue
  fun_prop

theorem differenceResidue_eq (M a b : ℕ) [NeZero M] :
    differenceResidue M a b = ((a : ZMod M) - (b : ZMod M)).val := by
  have h := ZMod.val_intCast (n := M) ((a : ℤ) - (b : ℤ))
  simp only [Int.cast_sub, Int.cast_natCast] at h
  simpa only [differenceResidue, Int.toNat_natCast] using (congrArg Int.toNat h).symm

end TranslationTiling.Compiler.Effective
