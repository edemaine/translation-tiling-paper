import TranslationTiling.Rotations.General.Motions
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Positivity

/-! Equal-volume, pairwise distinct rectangular chambers in every dimension.
The two smallest exponents add to a constant; all remaining exponents are fixed.
Thus the shortest side identifies the face and every side identifies its axis. -/

namespace TranslationTiling.Rotations.General
open scoped BigOperators

abbrev Face (d : ℕ) := Fin (2*d)

def exponentBase (d : ℕ) : ℕ := 8*d+8

def sideExponent {d : ℕ} (f : Face d) (j : Fin d) : ℕ :=
  if j.val = 0 then f.val+1
  else if j.val = 1 then exponentBase d-(f.val+1)
  else exponentBase d+j.val

def boxSide {d : ℕ} (f : Face d) (j : Fin d) : ℕ := 2 ^ sideExponent f j

def volumeExponent (d : ℕ) : ℕ := exponentBase d +
  ∑ j : Fin d, if j.val < 2 then 0 else exponentBase d+j.val

def boxVolume (d : ℕ) : ℕ := 2 ^ volumeExponent d

def neckLength (d : ℕ) : ℕ := 8*d+8

def maxSide (d : ℕ) : ℕ := 2 ^ (exponentBase d+d+2)

def margin (d : ℕ) : ℕ := neckLength d+maxSide d+10

def cubeSide (d : ℕ) : ℕ := 100*(d+1)*margin d

theorem sideExponent_pos {d : ℕ} (f : Face d) (j : Fin d) : 0 < sideExponent f j := by
  have hf := f.isLt
  unfold sideExponent exponentBase
  split_ifs <;> omega

theorem boxSide_two_le {d : ℕ} (f : Face d) (j : Fin d) : 2 ≤ boxSide f j := by
  exact Nat.le_self_pow (Nat.ne_of_gt (sideExponent_pos f j)) 2

theorem sideExponent_injective {d : ℕ} (f : Face d) : Function.Injective (sideExponent f) := by
  intro i j he
  have hf := f.isLt
  apply Fin.ext
  unfold sideExponent exponentBase at he
  split_ifs at he <;> omega

theorem boxSide_injective {d : ℕ} (f : Face d) : Function.Injective (boxSide f) := by
  intro i j he
  apply sideExponent_injective f
  exact (Nat.pow_right_injective (by decide : 1 < 2)) he

theorem sideExponent_min {d : ℕ} (f : Face d) (j : Fin d) : f.val+1 ≤ sideExponent f j := by
  have hf := f.isLt
  unfold sideExponent exponentBase
  split_ifs <;> omega

theorem boxSide_lt_max {d : ℕ} (f : Face d) (j : Fin d) : boxSide f j < maxSide d := by
  apply Nat.pow_lt_pow_right (by decide : 1 < 2)
  have hf := f.isLt
  have hj := j.isLt
  unfold sideExponent exponentBase
  split_ifs <;> omega

theorem sum_sideExponent {d : ℕ} (hd : 2 ≤ d) (f : Face d) :
    ∑ j : Fin d, sideExponent f j = volumeExponent d := by
  let z : Fin d := ⟨0,by omega⟩
  let o : Fin d := ⟨1,by omega⟩
  have hf := f.isLt
  have hparts (j : Fin d) : sideExponent f j =
      (if j.val < 2 then 0 else exponentBase d+j.val) +
      (if j = z then f.val+1 else 0) +
      (if j = o then exponentBase d-(f.val+1) else 0) := by
    by_cases hz : j = z
    · subst j; simp [sideExponent,z,o]
    · by_cases ho : j = o
      · subst j; simp [sideExponent,z,o]
      · have hzv : j.val ≠ 0 := fun h => hz (Fin.ext h)
        have hov : j.val ≠ 1 := fun h => ho (Fin.ext h)
        simp only [sideExponent,if_neg hzv,if_neg hov,if_neg hz,if_neg ho]
        rw [if_neg (by omega : ¬ j.val < 2)]
        omega
  simp_rw [hparts]
  simp only [Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  unfold volumeExponent exponentBase
  omega

theorem prod_boxSide {d : ℕ} (hd : 2 ≤ d) (f : Face d) :
    ∏ j : Fin d, boxSide f j = boxVolume d := by
  unfold boxSide boxVolume
  rw [Finset.prod_pow_eq_pow_sum,sum_sideExponent hd f]

/-- Equal side multisets identify a chamber label. -/
theorem boxSide_label {d : ℕ} (hd : 2 ≤ d) (f g : Face d) (e : Equiv.Perm (Fin d))
    (he : ∀ j, boxSide f j = boxSide g (e j)) : f = g := by
  let z : Fin d := ⟨0,by omega⟩
  have hv (j : Fin d) : sideExponent f j = sideExponent g (e j) :=
    (Nat.pow_right_injective (by decide : 1 < 2)) (he j)
  have h1 := sideExponent_min g (e z)
  have h2 := sideExponent_min f (e.symm z)
  have he1 := hv z
  have he2 := hv (e.symm z)
  have hz (a : Face d) : sideExponent a z = a.val+1 := by simp [sideExponent,z]
  rw [hz] at he1
  rw [Equiv.apply_symm_apply,hz] at he2
  rw [← he1] at h1
  rw [he2] at h2
  apply Fin.ext
  omega

end TranslationTiling.Rotations.General
