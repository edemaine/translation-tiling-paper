import TranslationTiling.FiniteCompiler.PackedTailParameters
import TranslationTiling.FiniteCompiler.Effective.GuardedNumericalCorrect
import TranslationTiling.FiniteCompiler.Effective.MixedInput

namespace TranslationTiling.FiniteCompiler.Packed

open Compiler.Size Compiler.Effective
open Effective
open scoped BigOperators Classical

noncomputable section

local instance packedParameterDataFrame : SeedFrame := compactSeedFrame

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def rawArity (i : ℕ) : ℕ := if i < 9 then 4 else if i < 18 then 6 else 3

def tailRows (k : ℕ) : GuardedRows :=
  ((List.range (18+2*k)).map fun i =>
    (tailPair k (2*i), tailPair k (2*i+1), (List.range (rawArity i)).map (tailDigit k i))) ++
  [(2,1229,[1231]), (3,773,[797])]

def tailSlopes (k : ℕ) : List ℕ :=
  (List.range (18+2*k)).map (ternaryLayoutProfile k).slope

@[fun_prop] theorem guardedTrits_primrec : Primrec guardedTrits := by
  unfold guardedTrits
  have h := (natLog_primrec 3 (by decide)).comp (show Primrec (fun n : ℕ => n-1) by fun_prop)
  fun_prop

@[fun_prop] theorem guardedPrimeCap_primrec : Primrec guardedPrimeCap := by
  unfold guardedPrimeCap
  have h := natLog_primrec 2 (by decide)
  fun_prop

@[fun_prop] theorem guardedPairCap_primrec : Primrec guardedPairCap := by
  unfold guardedPairCap guardedPairRanks
  fun_prop

@[fun_prop] theorem guardedDigitStart_primrec : Primrec guardedDigitStart := by
  unfold guardedDigitStart
  simp only [pow_two]
  fun_prop

@[fun_prop] theorem guardedDigitCap_primrec : Primrec guardedDigitCap := by
  unfold guardedDigitCap guardedDigitRanks
  fun_prop

theorem pairPool_primrec : Primrec pairPool := by
  unfold pairPool
  have hr : Primrec (fun k => List.range (guardedPairCap k + 1)) := by fun_prop
  have he : PrimrecPred (fun z : ℕ × ℕ => z.2 ∉ reservedPrimes) := by
    unfold reservedPrimes
    simp only [List.mem_cons,List.not_mem_nil,or_false]
    fun_prop
  exact filterList hr ((nat_prime_primrec.comp Primrec.snd).and he)

theorem digitPool_primrec : Primrec digitPool := by
  unfold digitPool
  have hr : Primrec (fun k => List.range (guardedDigitCap k + 1)) := by fun_prop
  have he : PrimrecPred (fun z : ℕ × ℕ => guardedDigitStart z.1 < z.2) := by fun_prop
  exact filterList hr ((nat_prime_primrec.comp Primrec.snd).and he)

@[fun_prop] theorem tailPair_primrec :
    Primrec (fun z : ℕ × ℕ => tailPair z.1 z.2) := by
  unfold tailPair
  have h := pairPool_primrec.comp (Primrec.fst : Primrec (Prod.fst : ℕ × ℕ → ℕ))
  fun_prop

@[fun_prop] theorem tailDigit_primrec :
    Primrec (fun z : ℕ × ℕ × ℕ => tailDigit z.1 z.2.1 z.2.2) := by
  unfold tailDigit digitRank
  have h := digitPool_primrec.comp (Primrec.fst : Primrec (Prod.fst : ℕ × ℕ × ℕ → ℕ))
  fun_prop

@[fun_prop] theorem tailRows_primrec : Primrec tailRows := by
  unfold tailRows rawArity
  fun_prop

@[fun_prop] theorem tailSlopes_primrec : Primrec tailSlopes := by
  unfold tailSlopes
  have hr : Primrec (fun k : ℕ => List.range (18+2*k)) := by fun_prop
  apply mapList hr
  unfold Profile.slope ternaryLayoutProfile
  simp only [List.length_replicate]
  fun_prop

variable {T : System} [AlphabetFamily T] {k : ℕ} (hk : 20 ≤ k)
  (hw : T.width = (ternaryLayoutProfile k).width)
  (ha : ∀ n : Column T, AlphabetFamily.size (T:=T) n = (ternaryLayoutProfile k).arity n.val)

include hw in
private theorem tailRows_inl (i : Column T) :
    (tailRows k).getD i.val (0,0,[]) =
      (tailPair k (2*i.val),tailPair k (2*i.val+1),
        (List.range (rawArity i.val)).map (tailDigit k i.val)) := by
  have hi := i.isLt
  have hwidth := hw.trans (ternaryLayout_width k)
  have hi' : i.val < 18+2*k := hi.trans_le hwidth.le
  simp [tailRows,List.getD_eq_getElem?_getD,List.getElem?_append_left,hi']

include hw in
private theorem tailRows_seed (t : Fin 2) :
    (tailRows k).getD (T.width+t.val) (0,0,[]) =
      (tailSeedA t,tailSeedB t,[tailSeedDigit t]) := by
  have hh : T.width = 18+2*k := hw.trans (ternaryLayout_width _)
  fin_cases t <;> simp [tailRows,List.getD_eq_getElem?_getD,List.getElem?_append_right,hh,
    tailSeedA,tailSeedB,tailSeedDigit]

theorem tailRowsMatch : GuardedRowsMatch (tailEncoding hk hw ha) (tailRows k) := by
  refine ⟨by simp [tailRows,hw,ternaryLayout_width], ?_, ?_, ?_, ?_⟩
  · intro i
    rcases i with i|t
    · simp only [rowA,channelNumber_inl,tailRows_inl hw]
      rfl
    · simp only [rowA,channelNumber_inr,tailRows_seed hw]
      rfl
  · intro i
    rcases i with i|t
    · simp only [rowB,channelNumber_inl,tailRows_inl hw]
      rfl
    · simp only [rowB,channelNumber_inr,tailRows_seed hw]
      rfl
  · intro i
    rcases i with i|t
    · have hh : rawArity i.val = AlphabetFamily.size (T:=T) i := by
        rw [ha i,ternaryLayout_arity (by omega) (i.isLt.trans_le hw.le)]
        rfl
      simp only [rowR,rowDigits,channelNumber_inl,tailRows_inl hw,hh]
      rw [EncodingParameters.r_eq_prod]
      change _ = ∏ j : Fin (AlphabetFamily.size (T:=T) i), tailDigit k i.val j.val
      rw [← Fin.prod_ofFn]
      congr 1
      apply List.ext_getElem
      · simp [Label,Letter]
      · intro j hj hj'
        simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn]
    · simp only [rowR,rowDigits,channelNumber_inr,tailRows_seed hw,List.prod_cons,List.prod_nil,mul_one,
        tailEncoding_seed_r hk hw ha]
  · intro i v
    rcases i with i|t
    · have hv : v.val < rawArity i.val := by
        have hh := (ha i).trans (ternaryLayout_arity (by omega) (i.isLt.trans_le hw.le))
        exact v.isLt.trans_le hh.le
      simp only [rowDigits,channelNumber_inl,tailRows_inl hw,guardedLabelNumber]
      simp only [List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_range hv,Option.map_some,
        Option.getD_some]
      rfl
    · simp only [rowDigits,channelNumber_inr,tailRows_seed hw,guardedLabelNumber,List.getD_cons_zero]
      rfl

end
end TranslationTiling.FiniteCompiler.Packed
