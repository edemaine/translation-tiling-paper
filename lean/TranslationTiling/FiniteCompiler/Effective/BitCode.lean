import TranslationTiling.Compiler.BitChannels
import TranslationTiling.Compiler.EffectiveAlphabet
import Mathlib.Data.Nat.Bitwise

namespace TranslationTiling.FiniteCompiler.Effective

open Compiler.Effective
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

@[fun_prop] theorem natPower {α : Type*} [Primcodable α] {f g : α → ℕ}
    (hf : Primrec f) (hg : Primrec g) : Primrec (fun a => f a ^ g a) :=
  (Primrec₂.unpaired'.mp Nat.Primrec.pow).comp hf hg

theorem shiftedLog_primrec : Primrec (fun n : ℕ => Nat.log 2 (n + 2)) := by
  apply Primrec.of_graph (f := fun n : ℕ => Nat.log 2 (n + 2))
    ⟨fun n => n + 2, by fun_prop, fun n => Nat.log_le_self 2 (n + 2)⟩
  have h : PrimrecPred (fun z : ℕ × ℕ => 2 ^ z.2 ≤ z.1 + 2 ∧ z.1 + 2 < 2 ^ (z.2 + 1)) := by
    fun_prop
  exact h.of_eq (fun z => (Nat.log_eq_iff (Or.inr ⟨by decide,by omega⟩)).symm)

@[fun_prop] theorem testBit_primrec : Primrec (fun z : ℕ × ℕ => z.1.testBit z.2) := by
  have h : Primrec (fun z : ℕ × ℕ => decide (z.1 / 2 ^ z.2 % 2 ≠ 0)) := by fun_prop
  apply h.of_eq
  intro z
  simp only [Nat.testBit, Nat.one_and_eq_mod_two, Nat.shiftRight_eq_div_pow]
  rfl

def bitWidth (T : LeanWang.TileSet) : ℕ := Nat.log 2 (T.length + 2) + 1

theorem bitWidth_primrec : Primrec bitWidth :=
  natAdd (shiftedLog_primrec.comp Primrec.list_length) (Primrec.const 1)

def bitCode (T : LeanWang.TileSet) (t : LeanWang.TileIn T) : Fin (bitWidth T) → Bool :=
  fun j => (T.idxOf t.val).testBit j.val

theorem bitCode_injective (T : LeanWang.TileSet) : Function.Injective (bitCode T) := by
  intro a b hab
  apply Subtype.ext
  apply (List.idxOf_inj a.property).mp
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < bitWidth T
  · exact congrFun hab ⟨j,hj⟩
  · have hpow : 2 ^ bitWidth T ≤ 2 ^ j := Nat.pow_le_pow_right (by decide) (by omega)
    have ha : T.idxOf a.val < 2 ^ bitWidth T :=
      (List.idxOf_lt_length_of_mem a.property).trans
        ((by omega : T.length < T.length + 2).trans
          (Nat.lt_pow_succ_log_self (by decide) _))
    have hb : T.idxOf b.val < 2 ^ bitWidth T :=
      (List.idxOf_lt_length_of_mem b.property).trans
        ((by omega : T.length < T.length + 2).trans
          (Nat.lt_pow_succ_log_self (by decide) _))
    rw [Nat.testBit_eq_false_of_lt (ha.trans_le hpow), Nat.testBit_eq_false_of_lt (hb.trans_le hpow)]

theorem indexedBit_primrec : Primrec (fun z : LeanWang.TileSet × LeanWang.WangTile × ℕ =>
    (z.1.idxOf z.2.1).testBit z.2.2) := by
  have hi : Primrec (fun z : LeanWang.TileSet × LeanWang.WangTile × ℕ => z.1.idxOf z.2.1) :=
    Primrec.list_idxOf.comp (Primrec.fst.comp Primrec.snd) Primrec.fst
  exact testBit_primrec.comp (hi.pair (Primrec.snd.comp Primrec.snd))

end TranslationTiling.FiniteCompiler.Effective
