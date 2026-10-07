import LeanWang.Kari.SignedPrimrec
import Mathlib.Computability.Primrec.List
import Mathlib.Data.Int.ModEq

namespace TranslationTiling

open LeanWang.Kari.SignedPrimrec

private theorem negSucc_emod_nat (n m : ℕ) :
    Int.negSucc n % (m : ℤ) = if m = 0 then Int.negSucc n
      else if (n + 1) % m = 0 then 0 else ((m - (n + 1) % m : ℕ) : ℤ) := by
  by_cases hm : m = 0
  · simp [hm]
  rw [if_neg hm, Int.negSucc_eq, Int.neg_emod]
  rw [show (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) by simp]
  have hdiv : (m : ℤ) ∣ ((n + 1 : ℕ) : ℤ) ↔ (n + 1) % m = 0 := by
    rw [Int.natCast_dvd_natCast, Nat.dvd_iff_mod_eq_zero]
  by_cases hr : (n + 1) % m = 0
  · rw [if_pos (hdiv.mpr hr), if_pos hr]
  · rw [if_neg (fun h => hr (hdiv.mp h)), if_neg hr]
    simp only [Int.natAbs_natCast, ← Int.natCast_mod]
    rw [Int.natCast_sub (Nat.le_of_lt (Nat.mod_lt _ (Nat.pos_of_ne_zero hm)))]

/-- Euclidean remainder by a natural modulus, including modulus zero. -/
theorem int_emod_nat_primrec : Primrec₂ fun (z : ℤ) (m : ℕ) => z % (m : ℤ) := by
  have hneg : Primrec fun z : (ℤ × ℕ) × ℕ =>
      if z.1.2 = 0 then Int.negSucc z.2
      else if (z.2 + 1) % z.1.2 = 0 then 0
      else ((z.1.2 - (z.2 + 1) % z.1.2 : ℕ) : ℤ) :=
    Primrec.ite (Primrec.eq.comp (Primrec.snd.comp Primrec.fst) (Primrec.const 0))
      (intNegSucc.comp Primrec.snd)
      (Primrec.ite
        (Primrec.eq.comp (Primrec.nat_mod.comp (Primrec.succ.comp Primrec.snd)
          (Primrec.snd.comp Primrec.fst)) (Primrec.const 0))
        (Primrec.const 0)
        (intOfNat.comp (Primrec.nat_sub.comp (Primrec.snd.comp Primrec.fst)
          (Primrec.nat_mod.comp (Primrec.succ.comp Primrec.snd) (Primrec.snd.comp Primrec.fst)))))
  exact (intCasesOn Primrec.fst
    (intOfNat.comp (Primrec.nat_mod.comp Primrec.snd (Primrec.snd.comp Primrec.fst))).to₂
    hneg.to₂).of_eq fun z => by
      cases z.1 with
      | ofNat n => exact (Int.natCast_emod n z.2).symm
      | negSucc n => exact (negSucc_emod_nat n z.2).symm

end TranslationTiling
