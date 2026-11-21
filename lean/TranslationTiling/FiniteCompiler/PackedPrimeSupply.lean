import TranslationTiling.Compiler.GuardedParameters
import TranslationTiling.FiniteCompiler.PackedTernaryLayout
import TranslationTiling.Compiler.EncodingPrimeSelection

namespace TranslationTiling.FiniteCompiler.Packed

open Compiler.Size
open scoped Classical

noncomputable section

def reservedPrimes : List ℕ := [2, 3, 5, 7, 1229, 773, 1231, 797]

def pairPool (k : ℕ) : List ℕ := (List.range (guardedPairCap k + 1)).filter
  (fun p => decide (p.Prime ∧ p ∉ reservedPrimes))

def digitPool (k : ℕ) : List ℕ := (List.range (guardedDigitCap k + 1)).filter
  (fun p => decide (p.Prime ∧ guardedDigitStart k < p))

theorem pairPool_length (k : ℕ) : 36+4*k ≤ (pairPool k).length := by
  have hcount : guardedPairRanks k ≤ Nat.primeCounting (guardedPairCap k) :=
    guardedPrimeCap_count (by unfold guardedPairRanks; omega)
  let ps := (Finset.range (guardedPairCap k + 1)).filter Nat.Prime
  have hps : ps.card = Nat.primeCounting (guardedPairCap k) := by
    simp [ps, Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
  have hs : ps \ reservedPrimes.toFinset = (pairPool k).toFinset := by
    ext q
    simp only [ps, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_range, List.mem_toFinset,
      pairPool, List.mem_filter, List.mem_range, decide_eq_true_eq, and_assoc]
  have h := Finset.card_le_card_sdiff_add_card (s := ps) (t := reservedPrimes.toFinset)
  rw [hps, hs, show reservedPrimes.toFinset.card = 8 by decide] at h
  have hh := List.toFinset_card_le (pairPool k)
  unfold guardedPairRanks at hcount
  omega

theorem digitPool_length (k : ℕ) : 90+6*k ≤ (digitPool k).length := by
  have hcount : guardedDigitRanks k ≤ Nat.primeCounting (guardedDigitCap k) :=
    guardedPrimeCap_count (by unfold guardedDigitRanks; omega)
  let ps := (Finset.range (guardedDigitCap k + 1)).filter Nat.Prime
  have hps : ps.card = Nat.primeCounting (guardedDigitCap k) := by
    simp [ps, Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
  let missing := Finset.range (guardedDigitStart k + 1)
  have hs : ps \ missing = (digitPool k).toFinset := by
    ext q
    simp only [ps, missing, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_range, List.mem_toFinset,
      digitPool, List.mem_filter, List.mem_range, decide_eq_true_eq, and_assoc]
    rw [show (¬ q < guardedDigitStart k + 1) ↔ guardedDigitStart k < q by omega]
  have h := Finset.card_le_card_sdiff_add_card (s := ps) (t := missing)
  rw [hps, hs, show missing.card = guardedDigitStart k+1 by simp [missing]] at h
  have hh := List.toFinset_card_le (digitPool k)
  unfold guardedDigitRanks at hcount
  omega

theorem pairPool_nodup (k : ℕ) : (pairPool k).Nodup := (List.nodup_range).filter _
theorem digitPool_nodup (k : ℕ) : (digitPool k).Nodup := (List.nodup_range).filter _

theorem pairPool_facts {k p : ℕ} (hp : p ∈ pairPool k) :
    p.Prime ∧ p ∉ reservedPrimes ∧ p ≤ guardedPairCap k := by
  simp only [pairPool, List.mem_filter, List.mem_range, decide_eq_true_eq] at hp
  exact ⟨hp.2.1, hp.2.2, by omega⟩

theorem digitPool_facts {k p : ℕ} (hp : p ∈ digitPool k) :
    p.Prime ∧ guardedDigitStart k < p ∧ p ≤ guardedDigitCap k := by
  simp only [digitPool, List.mem_filter, List.mem_range, decide_eq_true_eq] at hp
  exact ⟨hp.2.1, hp.2.2, by omega⟩

def digitRank (i j : ℕ) : ℕ :=
  if i < 9 then 4*i+j else if i < 18 then 36+6*(i-9)+j else 90+3*(i-18)+j

theorem digitRank_lt {k i j : ℕ} (hk : 0 < k)
    (hi : i < (ternaryLayoutProfile k).width)
    (hj : j < (ternaryLayoutProfile k).arity i) : digitRank i j < 90+6*k := by
  rw [ternaryLayout_arity hk hi] at hj
  rw [ternaryLayout_width] at hi
  unfold digitRank
  split_ifs at hj ⊢ <;> omega

theorem digitRank_inj {k i j i' j' : ℕ} (hk : 0 < k)
    (hi : i < (ternaryLayoutProfile k).width) (hi' : i' < (ternaryLayoutProfile k).width)
    (hj : j < (ternaryLayoutProfile k).arity i)
    (hj' : j' < (ternaryLayoutProfile k).arity i')
    (he : digitRank i j = digitRank i' j') : i = i' ∧ j = j' := by
  rw [ternaryLayout_arity hk hi] at hj
  rw [ternaryLayout_arity hk hi'] at hj'
  unfold digitRank at he
  split_ifs at he hj hj' <;> omega

end
end TranslationTiling.FiniteCompiler.Packed
