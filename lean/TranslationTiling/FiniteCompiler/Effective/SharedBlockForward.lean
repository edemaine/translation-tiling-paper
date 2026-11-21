import TranslationTiling.FiniteCompiler.Effective.SharedOrdinaryBlocks
import TranslationTiling.FiniteCompiler.BlockActivationInverse

namespace TranslationTiling.FiniteCompiler.Packed

open Effective SharedCoordinates
open scoped Classical

noncomputable section

variable {k : ℕ} (i : SharedRow k) (hi : i.val < (sharedRows k).length-2)

include hi in
theorem ordinaryB_ne_two : OrdinaryB i ≠ 2 := by
  by_cases hf : i.val < 18
  · unfold OrdinaryB rowB
    rw [sharedRows_fixed_at hf]
    exact (by decide +kernel : ∀ j : Fin 18, (sharedArithmeticRow j).2.1 ≠ 2) ⟨i,hf⟩
  · let j := i.val-18
    have hj : j < 2*k := by have := sharedRows_length k; dsimp [j]; omega
    have he := sharedRows_wang_at hj
    rw [show 18+j = i.val by dsimp [j]; omega] at he
    unfold OrdinaryB rowB
    rw [he]
    obtain ⟨_,_,hbr,_,_,_⟩ := sharedWangRow_facts hj
    intro h
    exact hbr (by
      change (sharedWangRow k j).2.1 ∈ sharedReservedPrimes
      rw [h]
      decide +kernel)

private theorem twoUnit {p : ℕ} (hp : p.Prime) (hne : p ≠ 2) :
    IsUnit (2 : ZMod p) :=
  (ZMod.isUnit_iff_coprime 2 p).mpr ((Nat.coprime_primes Nat.prime_two hp).mpr hne.symm)

abbrev SharedOrdinaryIndex (i : SharedRow k) :=
  OrdinaryIndex ((sharedLayout k).lowSize i) (OrdinaryA i) (OrdinaryB i)

theorem sharedBlock_bijective (j : SharedLabel i) (s : ℕ) (x : ℤ) (l : RowLow i) :
    letI : NeZero (OrdinaryA i) := ⟨(ordinaryPairFacts i hi).firstPrime.ne_zero⟩
    Function.Bijective (fun u : SharedOrdinaryIndex i =>
      ((sharedBlocks i hi j).C (l-u.1) + shift (OrdinaryA i) (OrdinaryB i) u.2,
       (sharedBlocks i hi j).T (x-(compactOffset (sharedLayout k) i s u).1) (l-u.1))) := by
  let h := ordinaryPairFacts i hi
  letI : NeZero (OrdinaryA i) := ⟨h.firstPrime.ne_zero⟩
  letI : NeZero (rowR (sharedRows k) i) := ⟨(sharedRows_moduli_positive i.isLt).1.ne'⟩
  let S := BlockShiftData.compact h.firstPrime.two_le h.secondPrime.two_le
    (twoUnit h.firstPrime (Nat.ne_of_gt (lt_trans (by decide : 2 < 3) h.bigFirst)))
    (twoUnit h.secondPrime (ordinaryB_ne_two i hi))
  let H (u : SharedOrdinaryIndex i) : ℤ := (compactOffset (sharedLayout k) i s u).1
  let B := sharedBlocks i hi j
  have hA (u : SharedOrdinaryIndex i) : (H u : ZMod (OrdinaryA i)) = S.rhoA u.2 :=
    congrArg (fun v : (RowLow i × ZMod (OrdinaryA i)) × ZMod (OrdinaryB i) => v.1.2)
      (compactFirst_residues h.lowFirst h.lowFirstSecond u)
  have hB (u : SharedOrdinaryIndex i) : (H u : ZMod (OrdinaryB i)) = S.rhoB u.2 :=
    congrArg Prod.snd (compactFirst_residues h.lowFirst h.lowFirstSecond u)
  exact (BlockShiftData.blockInverseEquiv B S H hA hB x l).bijective

end
end TranslationTiling.FiniteCompiler.Packed
