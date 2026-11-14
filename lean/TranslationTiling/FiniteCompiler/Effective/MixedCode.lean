import TranslationTiling.FiniteCompiler.TaggedSystem
import TranslationTiling.FiniteCompiler.Effective.TernaryInput

namespace TranslationTiling.FiniteCompiler.Effective
open Compiler.Effective
open scoped Classical
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

/-- Enough positions for a binary tile index or a ternary decorated index. -/
def mixedPayloadWidth (n : ℕ) : ℕ :=
  max (Nat.log 2 n + 1) (Nat.log 3 (Sudoku.p * Sudoku.q * n) + 1)
def mixedWidth (n : ℕ) : ℕ := mixedPayloadWidth n + 2

def mixedIndex (T : LeanWang.TileSet) (s : Sudoku.Symbol T) : ℕ :=
  arithmeticIndex s * T.length + T.idxOf s.2.2.val

theorem arithmeticIndex_lt_pq {T : LeanWang.TileSet} (s : Sudoku.Symbol T) :
    arithmeticIndex s < Sudoku.p * Sudoku.q := by
  have ha := ZMod.val_lt s.1.val
  have hb := ZMod.val_lt s.2.1.val
  unfold arithmeticIndex
  norm_num [Sudoku.p,Sudoku.q] at *
  omega

theorem mixedIndex_lt (T : LeanWang.TileSet) (s : Sudoku.Symbol T) :
    mixedIndex T s < Sudoku.p * Sudoku.q * T.length := by
  have hi := List.idxOf_lt_length_of_mem s.2.2.property
  have ha := arithmeticIndex_lt_pq s
  unfold mixedIndex
  nlinarith

theorem mixedIndex_injective (T : LeanWang.TileSet) : Function.Injective (mixedIndex T) := by
  intro s u h
  have hi := List.idxOf_lt_length_of_mem s.2.2.property
  have hj := List.idxOf_lt_length_of_mem u.2.2.property
  have har : arithmeticIndex s = arithmeticIndex u := by
    have he := congrArg (fun z => z / T.length) h
    simpa only [mixedIndex,Nat.mul_comm (arithmeticIndex s) T.length,
      Nat.mul_comm (arithmeticIndex u) T.length,Nat.mul_add_div (show 0 < T.length by omega),
      Nat.div_eq_of_lt hi,Nat.div_eq_of_lt hj,Nat.add_zero] using he
  have ht : s.2.2 = u.2.2 := by
    apply Subtype.ext
    apply (List.idxOf_inj s.2.2.property).mp
    have he := congrArg (fun z => z % T.length) h
    simpa [mixedIndex,Nat.add_mod,Nat.mod_eq_of_lt hi,Nat.mod_eq_of_lt hj] using he
  have hb := ZMod.val_lt s.2.1.val
  have hb' := ZMod.val_lt u.2.1.val
  have haeq : s.1.val.val = u.1.val.val := by
    unfold arithmeticIndex at har
    norm_num [Sudoku.q] at har hb hb'
    omega
  have hbeq : s.2.1.val.val = u.2.1.val.val := by
    unfold arithmeticIndex at har
    rw [haeq] at har
    omega
  exact Prod.ext (Units.ext (ZMod.val_injective _ haeq))
    (Prod.ext (Units.ext (ZMod.val_injective _ hbeq)) ht)

/-- Equality of a bounded integer's digits determines the integer. -/
theorem eq_of_digits {b m a c : ℕ} (hb : 0 < b) (ha : a < b ^ m) (hc : c < b ^ m)
    (h : ∀ j < m, a / b ^ j % b = c / b ^ j % b) : a = c := by
  induction m generalizing a c with
  | zero => simp only [pow_zero] at ha hc; omega
  | succ m ih =>
    have had : a / b < b ^ m := (Nat.div_lt_iff_lt_mul hb).mpr (by simpa [pow_succ] using ha)
    have hcd : c / b < b ^ m := (Nat.div_lt_iff_lt_mul hb).mpr (by simpa [pow_succ] using hc)
    have hd : a / b = c / b := ih had hcd (by
      intro j hj
      have he := h (j+1) (by omega)
      simpa only [Nat.div_div_eq_div_mul,pow_succ',Nat.mul_comm b] using he)
    have hm := h 0 (by omega)
    simp only [pow_zero,Nat.div_one] at hm
    calc
      a = a % b + b * (a / b) := (Nat.mod_add_div a b).symm
      _ = c % b + b * (c / b) := by rw [hm,hd]
      _ = c := Nat.mod_add_div c b

def mixedPrefix (c : Fin 3) (k : Fin 2) : Fin 3 :=
  if c = 2 then ⟨k.val,by omega⟩ else c

theorem mixedPrefix_injective (c d : Fin 3)
    (h0 : mixedPrefix c 0 = mixedPrefix d 0) (h1 : mixedPrefix c 1 = mixedPrefix d 1) : c = d := by
  fin_cases c <;> fin_cases d <;> simp_all [mixedPrefix]

def mixedWord (T : LeanWang.TileSet) (s : Sudoku.Symbol T) (k : Fin (mixedWidth T.length)) : Fin 3 :=
  if h : k.val < 2 then mixedPrefix (TernarySystem.tag s) ⟨k.val,h⟩
  else if TernarySystem.tag s = 2 then
    ⟨mixedIndex T s / 3 ^ (k.val-2) % 3,Nat.mod_lt _ (by decide)⟩
  else if (T.idxOf s.2.2.val).testBit (k.val-2) then 2 else TernarySystem.tag s

theorem mixedWord_seed (T : LeanWang.TileSet) (t : Fin 2) (s : Sudoku.Symbol T) :
    (∀ k, mixedWord T s k = TernarySystem.seedTag t ∨ mixedWord T s k = 2) ↔
      Compiler.SeedSet t s := by
  rw [← TernarySystem.tag_seed]
  constructor
  · intro h
    have h0 := h ⟨0,by unfold mixedWidth; omega⟩
    have h1 := h ⟨1,by unfold mixedWidth; omega⟩
    generalize he : TernarySystem.tag s = c at *
    fin_cases c <;> fin_cases t <;> simp_all [mixedWord,mixedPrefix,TernarySystem.seedTag]
  · intro h k
    unfold mixedWord
    rw [h]
    fin_cases t <;> simp only [TernarySystem.seedTag]
    all_goals split_ifs <;> simp_all [mixedPrefix,TernarySystem.seedTag]

theorem mixedWord_injective (T : LeanWang.TileSet) : Function.Injective (mixedWord T) := by
  intro s u h
  have htag : TernarySystem.tag s = TernarySystem.tag u := by
    apply mixedPrefix_injective
    · simpa [mixedWord] using congrFun h ⟨0,by unfold mixedWidth; omega⟩
    · simpa [mixedWord] using congrFun h ⟨1,by unfold mixedWidth; omega⟩
  have h2 : T.length < 2 ^ mixedPayloadWidth T.length :=
    (Nat.lt_pow_succ_log_self (by decide : 1 < 2) _).trans_le
      (Nat.pow_le_pow_right (by decide) (le_max_left _ _))
  by_cases hc : TernarySystem.tag s = 2
  · apply mixedIndex_injective T
    have h3 : Sudoku.p * Sudoku.q * T.length < 3 ^ mixedPayloadWidth T.length :=
      (Nat.lt_pow_succ_log_self (by decide : 1 < 3) _).trans_le
        (Nat.pow_le_pow_right (by decide) (le_max_right _ _))
    apply eq_of_digits (by decide : 0 < 3) ((mixedIndex_lt T s).trans h3)
      ((mixedIndex_lt T u).trans h3)
    intro j hj
    have he := congrArg Fin.val (congrFun h ⟨j+2,by unfold mixedWidth; omega⟩)
    simpa [mixedWord,hc,← htag,show ¬ j+2<2 by omega] using he
  · have ht : s.2.2 = u.2.2 := by
      apply Subtype.ext
      apply (List.idxOf_inj s.2.2.property).mp
      apply Nat.eq_of_testBit_eq
      intro j
      by_cases hj : j < mixedPayloadWidth T.length
      · have he := congrArg (fun z : Fin 3 => z = 2)
          (congrFun h ⟨j+2,by unfold mixedWidth; omega⟩)
        have hu : TernarySystem.tag u ≠ 2 := by simpa [← htag] using hc
        simp only [mixedWord,show ¬ j+2<2 by omega,↓reduceDIte,Nat.add_sub_cancel,hc,hu,↓reduceIte] at he
        cases hs : (T.idxOf s.2.2.val).testBit j <;>
          cases ht : (T.idxOf u.2.2.val).testBit j <;> simp_all
      · have hp : 2 ^ mixedPayloadWidth T.length ≤ 2 ^ j := Nat.pow_le_pow_right (by decide) (by omega)
        rw [Nat.testBit_eq_false_of_lt ((List.idxOf_lt_length_of_mem s.2.2.property).trans (h2.trans_le hp)),
          Nat.testBit_eq_false_of_lt ((List.idxOf_lt_length_of_mem u.2.2.property).trans (h2.trans_le hp))]
    have hs : ∃ t, Compiler.SeedSet t s ∧ Compiler.SeedSet t u := by
      generalize he : TernarySystem.tag s = c at *
      fin_cases c
      · exact ⟨0,(TernarySystem.tag_seed 0 s).mp he,(TernarySystem.tag_seed 0 u).mp htag.symm⟩
      · exact ⟨1,(TernarySystem.tag_seed 1 s).mp he,(TernarySystem.tag_seed 1 u).mp htag.symm⟩
      · exact (hc rfl).elim
    obtain ⟨t,hs,hu⟩ := hs
    exact Prod.ext (Units.ext (hs.1.trans hu.1.symm)) (Prod.ext (Units.ext (hs.2.trans hu.2.symm)) ht)

def mixedCode (T : LeanWang.TileSet) : TaggedSystem.Code T (mixedWidth T.length) :=
  ⟨by unfold mixedWidth; omega,mixedWord T,mixedWord_injective T,mixedWord_seed T⟩
def mixedSystem (T : LeanWang.TileSet) : System := TaggedSystem.system (mixedCode T)

end
end TranslationTiling.FiniteCompiler.Effective
