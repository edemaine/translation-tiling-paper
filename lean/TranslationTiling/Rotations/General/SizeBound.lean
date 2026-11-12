import TranslationTiling.Rotations.General.Gadget
import Mathlib.Tactic.Linarith

namespace TranslationTiling.Rotations.General

/-- A simple bound for the period of the dimension-dependent replacement. -/
theorem cubeSide_bound (d : ℕ) : cubeSide d ≤ 2^(10*d+20) := by
  have hn : neckLength d ≤ maxSide d := by
    have h1 := Nat.lt_two_pow_self (n := neckLength d)
    have h2 : 2^(neckLength d) ≤ maxSide d := by
      apply Nat.pow_le_pow_right (by decide : 1 ≤ 2)
      unfold neckLength exponentBase
      omega
    omega
  have ht : 10 ≤ maxSide d := by
    have h : 2^4 ≤ maxSide d := by
      apply Nat.pow_le_pow_right (by decide : 1 ≤ 2)
      unfold exponentBase
      omega
    omega
  have hm : margin d ≤ 3*maxSide d := by unfold margin; omega
  have hd : d+1 ≤ 2^d := Nat.lt_two_pow_self
  calc
    cubeSide d ≤ 300*(d+1)*maxSide d := by unfold cubeSide; nlinarith
    _ ≤ 2^10 * 2^d * maxSide d := by gcongr; norm_num
    _ = 2^(10*d+20) := by
      unfold maxSide exponentBase
      rw [← pow_add,← pow_add]
      congr 1
      omega

/-- A closed-form bound for the number of voxels in the new replacement cube. -/
theorem gadget_card_bound {d : ℕ} [NeZero d] :
    (gadget : Finset (Lattice d)).card ≤ 2^(10*(d+1)^2) := by
  rw [gadget_card]
  calc
    cubeSide d ^ d ≤ (2^(10*d+20))^d := Nat.pow_le_pow_left (cubeSide_bound d) d
    _ = 2^((10*d+20)*d) := (pow_mul _ _ _).symm
    _ ≤ _ := by
      apply Nat.pow_le_pow_right (by decide : 1 ≤ 2)
      nlinarith

end TranslationTiling.Rotations.General
