import TranslationTiling.FiniteCompiler.Effective.AxisSlotDeck
import TranslationTiling.FiniteCompiler.Effective.SlotVolumeBound

namespace TranslationTiling.FiniteCompiler.Packed.AxisParameters

open PairSmall GuardedCompiler Effective
open scoped Classical BigOperators
noncomputable section

local instance slotDeckCountFrame : SeedFrame := compactSeedFrame
set_option maxRecDepth 8000

variable {k m w : ℕ} {T : LeanWang.TileSet} (c : Code T ((axisRadix m w)^k))
local instance slotDeckCountAlphabet : AlphabetFamily (system c) := GuardedCompiler.alphabet c
variable (s : AxisParameters k m)

def axisDeckCap (k m D : ℕ) :=
  2530 + arithmeticBaseline.length + 20*(2*k*m+8*m) +
    (6*k*m+4*m)*(21+2*k*m+8*m+k) + 2*k*2^m + 72*D^2

private theorem row_card : Fintype.card (AxisRow k m) = 20+2*k*m+8*m := by
  simp only [AxisRow,WangSlot,AxisFallback,Fintype.card_sum,Fintype.card_prod,
    Fintype.card_fin,Fintype.card_bool,FourValueRow,fourValueRows_length]
  ring

private theorem patterns_length (D : ℕ) (a : Code T D) :
    (patterns a).length ≤ 2313+72*D^2 := by
  have hs : Sudoku.PartialWord.codes5.length + Sudoku.PartialWord.codes7.length = 2313 :=
    by decide +kernel
  have hq : Fintype.card (QueryIndex D) = 72*D^2 := by
    simp only [QueryIndex,Fintype.card_prod,Fintype.card_fin]
    rw [Fintype.card_congr pEquiv,Fintype.card_congr qEquiv]
    simp only [Fintype.card_fin]
    ring
  unfold patterns
  simp only [List.length_append,List.length_map,Finset.length_toList,hs]
  exact Nat.add_le_add_left ((Finset.card_filter_le _ _).trans_eq
    (Finset.card_univ.trans hq)) _

theorem slotDeck_length (hwm : w ≤ m) :
    (s.slotDeck c hwm).length ≤ axisDeckCap k m ((axisRadix m w)^k) := by
  let r := Fintype.card (AxisRow k m)
  have hmarker : s.markerDeck.length ≤ (6*k*m)*(1+r) := by
    unfold markerDeck
    rw [List.length_flatMap]
    calc
      _ ≤ ((Finset.univ : Finset (WangSlot k m × Fin 3)).toList.map fun _ => 1+r).sum := by
        apply listSumMap_le
        rintro ⟨i,j⟩ _
        simp only [markerTests,List.length_cons,List.length_map,Finset.length_toList]
        have h : ((Finset.univ : Finset (AxisRow k m)).erase (wangRow i)).card ≤ r :=
          Finset.card_erase_le.trans_eq Finset.card_univ
        omega
      _ = _ := by simp [r,WangSlot,Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc]
  have hfallback : s.fallbackDeck.length ≤ (4*m)*(1+r) := by
    unfold fallbackDeck
    rw [List.length_flatMap]
    calc
      _ ≤ ((Finset.univ : Finset (Bool × Fin m × Bool)).toList.map fun _ => 1+r).sum := by
        apply listSumMap_le
        rintro ⟨g,i,a⟩ _
        simp only [fallbackTests,List.length_cons,List.length_map,List.length_append,
          List.length_finRange,Finset.length_toList]
        let J := (Finset.univ : Finset (AxisRow k m)).filter (· ∈ controls g i)
        have hJ : J.card = k := by
          let e : Fin k ↪ AxisRow k m :=
            ⟨fun d => wangRow (g,d,i),fun _ _ h =>
              congrArg (fun r : WangSlot k m => r.2.1) (Sum.inl.inj (Sum.inr.inj h))⟩
          have he : J = Finset.univ.map e := by ext j; simp [J,controls,Finset.mem_map]; rfl
          rw [he,Finset.card_map,Finset.card_univ,Fintype.card_fin]
        have hp := Finset.card_filter_add_card_filter_not
          (s := (Finset.univ : Finset (AxisRow k m))) (· ∈ controls g i)
        change J.card + _ = _ at hp
        rw [hJ,Finset.card_univ] at hp
        omega
      _ = _ := by simp [r,Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc]
  have ha : (s.activationDeck hwm).length ≤ 2*k*2^m := by
    have hc : Fintype.card {S : Finset (Fin m) // S.card = m+1-w} ≤ 2^m :=
      (Fintype.card_le_of_injective Subtype.val Subtype.val_injective).trans_eq
        (by rw [Fintype.card_finset,Fintype.card_fin])
    unfold activationDeck
    rw [List.length_flatMap]
    simp only [List.length_map,Finset.length_toList,Finset.card_univ]
    let a := Fintype.card {S : Finset (Fin m) // S.card = m+1-w}
    change (((Finset.univ : Finset (Bool × Fin k)).toList).map
      (Function.const _ a)).sum ≤ 2*k*2^m
    rw [List.map_const,List.sum_replicate,Finset.length_toList,Finset.card_univ,
      Fintype.card_prod,Fintype.card_bool,Fintype.card_fin,nsmul_eq_mul]
    exact Nat.mul_le_mul_left _ hc
  have hseed : (s.seedDeck c).length ≤ 216 := by
    have h : ∀ i : Fin 18, PairSmall.arity ((axisRadix m w)^k) (arithmeticColumn i) ≤ 6 := by
      intro i
      rw [← arithmetic_arity]
      exact (by decide +kernel : ∀ i : Fin 18,
        (rowDigits (fourValueRows 0) (arithmeticRow i)).length ≤ 6) i
    have hs : Fintype.card (Σ i : Fin 18, Letter (system c) (arithmeticColumn i)) ≤ 108 := by
      rw [Fintype.card_sigma]
      simp only [Fintype.card_fin]
      calc
        _ ≤ ∑ _ : Fin 18, 6 := Finset.sum_le_sum fun i _ => h i
        _ = _ := by decide
    unfold seedDeck
    simp only [List.length_map,Finset.length_toList]
    apply (Finset.card_filter_le _ _).trans
    rw [Finset.card_univ,Fintype.card_sigma]
    calc
      _ ≤ ∑ _ : Fin 2, 108 := Finset.sum_le_sum fun _ _ => hs
      _ = _ := by decide
  have hg : (s.guardDeck c).length ≤ 2313+72*((axisRadix m w)^k)^2 := by
    unfold guardDeck
    simpa [guardDeck] using patterns_length _ c
  have hanchor : s.anchorTests.length = 20*(2*k*m+8*m) := by
    simp only [anchorTests,List.length_map,Finset.length_toList,Finset.card_univ,Fintype.card_prod,
      Fintype.card_sum,Fintype.card_bool,Fintype.card_fin,FourValueRow,fourValueRows_length,
      AxisAddedRow,WangSlot,AxisFallback]
    ring
  have hcombine : s.markerDeck.length+s.fallbackDeck.length ≤ (6*k*m+4*m)*(21+2*k*m+8*m) := by
    apply (Nat.add_le_add hmarker hfallback).trans
    rw [← Nat.add_mul,show r = 20+2*k*m+8*m from row_card]
    apply le_of_eq
    ring
  have hh := hcombine.trans (Nat.mul_le_mul_left (6*k*m+4*m)
    (Nat.le_add_right (21+2*k*m+8*m) k))
  simp only [slotDeck,List.length_cons,List.length_append,hanchor,arithmeticTiles,List.length_map]
  unfold axisDeckCap
  omega

end
end TranslationTiling.FiniteCompiler.Packed.AxisParameters
