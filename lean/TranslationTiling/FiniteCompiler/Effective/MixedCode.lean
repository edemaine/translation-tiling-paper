import TranslationTiling.FiniteCompiler.TaggedSystem
import TranslationTiling.FiniteCompiler.Effective.PackedWords

namespace TranslationTiling.FiniteCompiler.Effective
open Compiler.Effective
open scoped Classical
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

/-- Enough words in each seed class, without dedicated prefix positions. -/
def mixedPayloadWidth (n : ℕ) : ℕ :=
  max (Nat.log 2 n + 1) (Nat.log 3 (2 * Sudoku.p * Sudoku.q * n) + 1)
def mixedWidth (n : ℕ) : ℕ := mixedPayloadWidth n

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

theorem mixedWidth_pos (n : ℕ) : 0 < mixedWidth n := by
  unfold mixedWidth mixedPayloadWidth
  omega

theorem mixedWidth_four {n : ℕ} (hn : 0<n) : 4 ≤ mixedWidth n := by
  have hp : 3^3 ≤ 2*Sudoku.p*Sudoku.q*n := by
    have h := Nat.mul_le_mul_left (2*Sudoku.p*Sudoku.q) hn
    norm_num [Sudoku.p,Sudoku.q] at *
    omega
  have hl := Nat.le_log_of_pow_le (by decide : 1<3) hp
  unfold mixedWidth mixedPayloadWidth
  omega

private theorem binary_quarter_ternary {m : ℕ} (hm : 4≤m) : 4*2^m≤3^m := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hm
  induction k with
  | zero => norm_num
  | succ k ih =>
    rw [show 4+(k+1)=(4+k)+1 by omega,pow_succ,pow_succ]
    omega

theorem mixedClass_capacity {n : ℕ} (hn : 0<n) :
    n ≤ (packedCandidates (mixedWidth n) 0).length ∧
    n ≤ (packedCandidates (mixedWidth n) 1).length ∧
    Sudoku.p*Sudoku.q*n ≤ (packedCandidates (mixedWidth n) 2).length := by
  have h2 : n < 2 ^ mixedWidth n :=
    (Nat.lt_pow_succ_log_self (by decide : 1<2) _).trans_le
      (Nat.pow_le_pow_right (by decide) (le_max_left _ _))
  have h3 : 2*Sudoku.p*Sudoku.q*n < 3 ^ mixedWidth n :=
    (Nat.lt_pow_succ_log_self (by decide : 1<3) _).trans_le
      (Nat.pow_le_pow_right (by decide) (le_max_right _ _))
  have hm := binary_quarter_ternary (show 4≤mixedWidth n by have := mixedWidth_four hn; omega)
  have hc := wordClassSet_card (mixedWidth n)
  simp only [← packedCandidates_length] at hc
  constructor
  · omega
  constructor
  · omega
  · nlinarith

/-- Within a seed class only the tile index is needed. -/
def mixedSourceIndex (T : LeanWang.TileSet) (s : Sudoku.Symbol T) : ℕ :=
  if TernarySystem.tag s=2 then mixedIndex T s else T.idxOf s.2.2.val

theorem mixedSourceIndex_lt (T : LeanWang.TileSet) (s : Sudoku.Symbol T) :
    mixedSourceIndex T s < (packedCandidates (mixedWidth T.length) (TernarySystem.tag s).val).length := by
  have hi := List.idxOf_lt_length_of_mem s.2.2.property
  have hc := mixedClass_capacity (show 0<T.length by omega)
  unfold mixedSourceIndex
  generalize he : TernarySystem.tag s = c at *
  fin_cases c
  · simpa using hi.trans_le hc.1
  · simpa using hi.trans_le hc.2.1
  · simpa using (mixedIndex_lt T s).trans_le hc.2.2

def mixedWord (T : LeanWang.TileSet) (s : Sudoku.Symbol T) (k : Fin (mixedWidth T.length)) : Fin 3 :=
  ⟨packedDigit (mixedWidth T.length) (TernarySystem.tag s).val (mixedSourceIndex T s) k.val,
    Nat.mod_lt _ (by decide)⟩

theorem mixedWord_class (T : LeanWang.TileSet) (s : Sudoku.Symbol T) :
    wordClass (mixedWord T s) = (TernarySystem.tag s).val := by
  obtain ⟨ha,hc⟩ := packedSelect_mem (mixedSourceIndex_lt T s)
  let a : Fin (3^mixedWidth T.length) := ⟨_,ha⟩
  have he : mixedWord T s = finFunctionFinEquiv.symm a := by
    funext k
    rfl
  rw [he,← packedClass_equiv,Equiv.apply_symm_apply]
  exact hc

theorem mixedWord_seed (T : LeanWang.TileSet) (t : Fin 2) (s : Sudoku.Symbol T) :
    (∀ k, mixedWord T s k = TernarySystem.seedTag t ∨ mixedWord T s k = 2) ↔
      Compiler.SeedSet t s := by
  rw [wordClass_seed _ (by rw [mixedWord_class]; exact (TernarySystem.tag s).isLt),mixedWord_class,
    ← TernarySystem.tag_seed]
  constructor
  · intro h; exact Fin.ext h
  · intro h; exact congrArg Fin.val h

theorem mixedWord_injective (T : LeanWang.TileSet) : Function.Injective (mixedWord T) := by
  intro s u h
  have htag : TernarySystem.tag s = TernarySystem.tag u := by
    apply Fin.ext
    rw [← mixedWord_class,← mixedWord_class,h]
  have ha := packedSelect_mem (mixedSourceIndex_lt T s)
  have hb := packedSelect_mem (mixedSourceIndex_lt T u)
  have he : packedSelect (mixedWidth T.length) (TernarySystem.tag s).val (mixedSourceIndex T s) =
      packedSelect (mixedWidth T.length) (TernarySystem.tag u).val (mixedSourceIndex T u) := by
    apply eq_of_digits (by decide : 0<3) ha.1 hb.1
    intro k hk
    exact congrArg Fin.val (congrFun h ⟨k,hk⟩)
  have hi : mixedSourceIndex T s = mixedSourceIndex T u := by
    apply packedSelect_injective (mixedSourceIndex_lt T s)
    · simpa [htag] using mixedSourceIndex_lt T u
    · simpa [htag] using he
  by_cases hc : TernarySystem.tag s = 2
  · apply mixedIndex_injective T
    simpa [mixedSourceIndex,hc,← htag] using hi
  · have ht : s.2.2 = u.2.2 := by
      apply Subtype.ext
      apply (List.idxOf_inj s.2.2.property).mp
      simpa [mixedSourceIndex,hc,← htag] using hi
    have hs : ∃ t, Compiler.SeedSet t s ∧ Compiler.SeedSet t u := by
      generalize htagS : TernarySystem.tag s = c at *
      fin_cases c
      · exact ⟨0,(TernarySystem.tag_seed 0 s).mp htagS,(TernarySystem.tag_seed 0 u).mp htag.symm⟩
      · exact ⟨1,(TernarySystem.tag_seed 1 s).mp htagS,(TernarySystem.tag_seed 1 u).mp htag.symm⟩
      · exact (hc rfl).elim
    obtain ⟨t,hs,hu⟩ := hs
    exact Prod.ext (Units.ext (hs.1.trans hu.1.symm)) (Prod.ext (Units.ext (hs.2.trans hu.2.symm)) ht)

def mixedCode (T : LeanWang.TileSet) : TaggedSystem.Code T (mixedWidth T.length) :=
  ⟨mixedWidth_pos _,mixedWord T,mixedWord_injective T,mixedWord_seed T⟩
def mixedSystem (T : LeanWang.TileSet) : System := TaggedSystem.system (mixedCode T)

end
end TranslationTiling.FiniteCompiler.Effective
