import TranslationTiling.FiniteCompiler.SlotShift
import TranslationTiling.Compiler.EffectiveResidues

namespace TranslationTiling.FiniteCompiler.SlotShift

variable {d : ℕ} [NeZero d] {m : ZMod d → ℕ}

/-- The shift acts on binary vectors by a cyclic XOR and fixes every
other vector. This test only examines the residue representatives. -/
def evaluate (z : Shift m) : Shift m := fun j =>
  if (List.finRange d).all (fun i => decide ((z (i.val : ZMod d)).val ≤ 1)) then
    if xor ((z j).val == 1) ((z (j+1)).val == 1) then 1 else 0
  else z j

theorem evaluate_eq_shift (hm : ∀ j, 1 < m j) (z : Shift m) : evaluate z = shift z := by
  have (j : ZMod d) : NeZero (m j) := ⟨by have := hm j; omega⟩
  have (j : ZMod d) : Fact (1 < m j) := ⟨hm j⟩
  let bits : Bits d := fun j => (z j).val == 1
  have hbin : (List.finRange d).all (fun i => decide ((z (i.val : ZMod d)).val ≤ 1)) = true ↔
      ∃ w : Bits d, bitPoint w = z := by
    rw [List.all_eq_true]
    constructor
    · intro h
      refine ⟨bits,funext fun j => ?_⟩
      have hj := h ⟨j.val,ZMod.val_lt j⟩ (List.mem_finRange _)
      change decide ((z (j.val : ZMod d)).val ≤ 1) = true at hj
      rw [ZMod.natCast_zmod_val] at hj
      simp only [decide_eq_true_eq] at hj
      apply ZMod.val_injective (m j)
      unfold bitPoint bits
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hj with hz | ho
      · simp [hz]
      · simp [ho,ZMod.val_one]
    · rintro ⟨w,rfl⟩ i _
      simp only [bitPoint]
      split <;> simp [ZMod.val_one]
  funext j
  unfold evaluate
  split
  · rename_i h
    obtain ⟨w,hw⟩ := hbin.mp h
    rw [← hw,shift_bitPoint hm]
    have hbit (i : ZMod d) : ((bitPoint (m := m) w i).val == 1) = w i := by
      cases hwi : w i <;> simp [bitPoint,hwi,ZMod.val_one]
    rw [hbit,hbit]
    rfl
  · rename_i h
    rw [shift,dite_eq_right (mt hbin.mpr h)]

end TranslationTiling.FiniteCompiler.SlotShift

namespace TranslationTiling.FiniteCompiler

open Compiler.Effective

/-- The search selects the common residue and the quotient records the
batch index, keeping displacements for different indices distinct. -/
def evaluatedSlotOffset (modulus : ℕ) (cs : CongruenceList) (index : ℕ) (slope : ℤ) : Plane :=
  let a : ℤ := (residueSearch modulus cs + modulus*index : ℕ)
  (a,-slope*a)

theorem evaluatedSlotOffset_primrec :
    Primrec (fun z : (ℕ × CongruenceList) × ℕ × ℤ =>
      evaluatedSlotOffset z.1.1 z.1.2 z.2.1 z.2.2) := by
  unfold evaluatedSlotOffset
  have : Primrec (fun z : (ℕ × CongruenceList) × ℕ × ℤ => residueSearch z.1.1 z.1.2) :=
    residueSearch_primrec.comp Primrec.fst
  fun_prop

end TranslationTiling.FiniteCompiler
