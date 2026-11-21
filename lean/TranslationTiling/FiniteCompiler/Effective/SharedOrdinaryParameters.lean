import TranslationTiling.FiniteCompiler.Effective.SharedDigits
import TranslationTiling.FiniteCompiler.Effective.SharedOrdinaryDeck

namespace TranslationTiling.FiniteCompiler.Packed

open Compiler.Size Compiler.Effective Effective SharedCoordinates
open scoped Classical

noncomputable section

set_option maxRecDepth 10000

structure OrdinaryPairFacts (a b r : ℕ) : Prop where
  firstPrime : a.Prime
  secondPrime : b.Prime
  bigFirst : 3 < a
  lowFirst : r.Coprime a
  lowFirstSecond : (r*a).Coprime b

theorem ordinaryPairFacts {k : ℕ} (i : SharedRow k)
    (hi : i.val < (sharedRows k).length-2) :
    OrdinaryPairFacts (rowA (sharedRows k) i) (rowB (sharedRows k) i) (rowR (sharedRows k) i) := by
  have hi' : i.val < 18+2*k := by have := sharedRows_length k; omega
  unfold rowA rowB rowR rowDigits
  by_cases hf : i.val < 18
  · rw [sharedRows_fixed_at hf]
    refine ⟨?_,?_,?_,?_,?_⟩
    · exact (by decide +kernel : ∀ h : Fin 18, (sharedArithmeticRow h).1.Prime) ⟨i,hf⟩
    · exact (by decide +kernel : ∀ h : Fin 18, (sharedArithmeticRow h).2.1.Prime) ⟨i,hf⟩
    · exact (by decide +kernel : ∀ h : Fin 18, 3 < (sharedArithmeticRow h).1) ⟨i,hf⟩
    · exact (by decide +kernel : ∀ h : Fin 18,
        (sharedArithmeticRow h).2.2.prod.Coprime (sharedArithmeticRow h).1) ⟨i,hf⟩
    · exact (by decide +kernel : ∀ h : Fin 18,
        ((sharedArithmeticRow h).2.2.prod*(sharedArithmeticRow h).1).Coprime
          (sharedArithmeticRow h).2.1) ⟨i,hf⟩
  · let j := i.val-18
    have hj : j < 2*k := by dsimp [j]; omega
    have he : (i.val : ℕ) = 18+j := by dsimp [j]; omega
    rw [he,sharedRows_wang_at hj]
    let a := (sharedWangRow k j).1
    let b := (sharedWangRow k j).2.1
    let ds := (sharedWangRow k j).2.2
    obtain ⟨ha,hbp,hbr,hbc,_,hd⟩ := sharedWangRow_facts hj
    change a = 199 ∨ a = 163 at ha
    have hap : a.Prime := by rcases ha with h|h <;> rw [h] <;> decide
    have hab : a ≠ b := by
      intro e
      apply hbr
      change b ∈ sharedReservedPrimes
      rw [← e]
      rcases ha with h|h <;> simp [h,sharedReservedPrimes]
    have ba : 3 < a := by rcases ha with h|h <;> omega
    have ca : a ≤ 200 := by rcases ha with h|h <;> omega
    have hx : 1 ≤ guardedPrimeCap (2*k+136) := by
      unfold guardedPrimeCap
      have := Nat.le_mul_of_pos_right (4*(2*k+136)) (by omega : 0 < Nat.log 2 (2*k+136) + 1)
      omega
    have hra : ds.prod.Coprime a := by
      apply Nat.coprime_list_prod_left_iff.mpr
      intro d hdm
      have h := hd d hdm
      have hx' := Nat.mul_le_mul_left 200 hx
      exact (Nat.coprime_primes h.1 hap).mpr (by omega)
    have hrb : ds.prod.Coprime b := by
      apply Nat.coprime_list_prod_left_iff.mpr
      intro d hdm
      have h := hd d hdm
      have hbc' : b ≤ guardedPrimeCap (2*k+136) := hbc
      exact (Nat.coprime_primes h.1 hbp).mpr (by omega)
    exact ⟨hap,hbp,ba,hra,hrb.mul_left ((Nat.coprime_primes hap hbp).mpr hab)⟩


def sharedSlope (k : ℕ) (i : SharedRow k) : Bool := decide (i.val < 18+k)

theorem ordinaryFirst_fixed {k : ℕ} (i : SharedRow k) (hi : i.val < 18) :
    (sharedLayout k).firstSize i = rowA (sharedRows k) i :=
  if_neg (fun h => (not_le_of_gt hi) h.1)

theorem ordinaryFirst_shared {k : ℕ} (i : SharedRow k)
    (hl : 18 ≤ i.val) (hh : i.val < (sharedRows k).length-2) :
    sharedPrime (sharedSlope k i) = rowA (sharedRows k) i := by
  have hh' : i.val < 18+2*k := by have := sharedRows_length k; omega
  let j := i.val-18
  have hj : j < 2*k := by dsimp [j]; omega
  have hrow := sharedRows_wang_at hj
  have he : 18+j = i.val := by dsimp [j]; omega
  rw [he] at hrow
  unfold rowA
  rw [hrow]
  change (if decide (i.val < 18+k) then 199 else 163) = (if j < k then 199 else 163)
  have hj' : j < k ↔ i.val < 18+k := by dsimp [j]; omega
  simp [hj']

def adjustFirst {a a' b : ℕ} (h : a = a') :
    (ZMod a × ZMod b) ≃+ (ZMod a' × ZMod b) :=
  (ZMod.ringEquivCongr h).toAddEquiv.prodCongr (.refl _)

@[simp] theorem adjustFirst_natCast {a a' b : ℕ} (h : a = a') (n : ℕ) :
    adjustFirst (b:=b) h ((n : ZMod a),(n : ZMod b)) =
      ((n : ZMod a'),(n : ZMod b)) := by
  change ((ZMod.ringEquivCongr h) (n : ZMod a),(n : ZMod b)) = _
  rw [map_natCast]

def ordinaryUseful {k : ℕ} (i : SharedRow k)
    (hi : i.val < (sharedRows k).length-2) :
    SharedFactor k →+ ZMod (rowA (sharedRows k) i) × ZMod (rowB (sharedRows k) i) :=
  if hf : i.val < 18 then
    (adjustFirst (ordinaryFirst_fixed i hf)).toAddMonoidHom.comp (privateUseful (sharedLayout k) i)
  else
    (adjustFirst (ordinaryFirst_shared i (Nat.le_of_not_gt hf) hi)).toAddMonoidHom.comp
      (sharedUseful (sharedLayout k) (sharedSlope k i) i)

theorem ordinaryUseful_decode {k : ℕ} (i : SharedRow k)
    (hi : i.val < (sharedRows k).length-2) (n : ℕ) :
    ordinaryUseful i hi (decode (sharedLayout k) n) =
      ((n : ZMod (rowA (sharedRows k) i)),(n : ZMod (rowB (sharedRows k) i))) := by
  unfold ordinaryUseful
  split <;> simp only [AddMonoidHom.comp_apply,privateUseful_decode,sharedUseful_decode]
  all_goals exact adjustFirst_natCast _ _

end
end TranslationTiling.FiniteCompiler.Packed
