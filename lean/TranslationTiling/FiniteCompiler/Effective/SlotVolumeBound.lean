import TranslationTiling.FiniteCompiler.Effective.GuardedAssembly
import TranslationTiling.FiniteCompiler.Effective.FourValueTailCore

namespace TranslationTiling.FiniteCompiler.Packed

open Compiler Compiler.Size Compiler.StripLift Rails.Strips Effective
open scoped Classical

set_option maxHeartbeats 350000
set_option maxRecDepth 2000

private theorem slotCount_linear (H : ℕ) : countCapAt 35 (fun _ => H) ≤ 2^28*(H+1) := by
  have hr : 2*radius H+1 ≤ 931*(H+1) := by unfold radius; omega
  have hw : ((List.range 17).map fun s => 2*widthAt 35 s+1).sum ≤ 200000 := by decide
  unfold countCapAt
  rw [List.sum_map_mul_left]
  calc
    _ ≤ (931*(H+1))*200000 := Nat.mul_le_mul hr hw
    _ = (931*200000)*(H+1) := by ac_rfl
    _ ≤ _ := Nat.mul_le_mul_right _ (by decide)

/-- The mass of a mask times the rail period equals the cyclic order.
Consequently the rails contribute one factor of the order to the
volume estimate, even when the period grows with the number of slots. -/
theorem slotVolume_le (H R J N L : ℕ) (hR : 0 < R) (hN : J*R ≤ N) :
    reservedVolumeCap 35 (fun _ => H) R J L ≤ 10^32*N*L*(H+1)^2 := by
  let a := countCapAt 35 (fun _ => H)
  have ha : 0 < a := by
    unfold a countCapAt
    rw [List.sum_map_mul_left]
    exact Nat.mul_pos (by positivity) (by decide)
  have hRJ : R*J ≤ N := by simpa only [Nat.mul_comm R J] using hN
  calc
    _ ≤ 2^49*(R*J)*L*a^2 := guarded_shell_bound hR ha
    _ ≤ 2^49*N*L*(2^28*(H+1))^2 :=
      Nat.mul_le_mul (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hRJ))
        (Nat.pow_le_pow_left (slotCount_linear H) _)
    _ = 2^105*N*L*(H+1)^2 := by rw [mul_pow]; ring
    _ ≤ _ := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by decide)))

/-- When the horizontal slots are short relative to the rails, the shell
volume is linear in the slot count. -/
theorem slotVolume_linear_le (H R J N L : ℕ) (hN : J*R ≤ N)
    (hH : 4*countCapAt 35 (fun _ => H)+4229 ≤ R) :
    reservedVolumeCap 35 (fun _ => H) R J L ≤
      mssPieceCap*N*L*216*4222*(4*countCapAt 35 (fun _ => H)+1) := by
  let a := countCapAt 35 (fun _ => H)
  have hfront (a R : ℕ) (h : 4*a+4229 ≤ R) :
      4*a+7*(railHeight (3*R+1)+2)+1 ≤ 4222*R := by
    unfold railHeight
    calc
      _ = (4*a+4229)+4221*R := by ring
      _ ≤ R+4221*R := Nat.add_le_add_right h _
      _ = _ := by ring
  unfold reservedVolumeCap
  dsimp only
  calc
    _ ≤ mssPieceCap*(J*L)*(216*(4222*R)*(4*a+1)) := by
      exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (hfront a R hH)))
    _ = mssPieceCap*(J*R)*L*216*4222*(4*a+1) := by ring
    _ ≤ _ := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _
      (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hN))))

/-- The extra stacking modulus is polynomial in the test cap. -/
theorem slotStack_le (X P : ℕ) (hX : 1 ≤ X) (hP : P ≤ X) :
    reservedCap X P ≤ 128*X^3 := by
  have hd : Stacking.differenceLog X ≤ 2*X+1 := by
    unfold Stacking.differenceLog
    have := Nat.log_le_self 2 (2*X)
    omega
  have h1 : 20*X^2*Stacking.differenceLog X ≤ 60*X^3 := by
    calc
      _ ≤ 20*X^2*(3*X) := Nat.mul_le_mul_left _ (by omega)
      _ = _ := by ring
  have hx2 : X ≤ X^2 := by simpa [pow_two] using Nat.mul_le_mul_left X hX
  have hx3 : X^2 ≤ X^3 := by
    rw [pow_succ X 2]
    simpa only [mul_one] using Nat.mul_le_mul_left (X^2) hX
  have hxone : 1 ≤ X^3 := (hX.trans hx2).trans hx3
  unfold reservedCap reservedThreshold
  omega

end TranslationTiling.FiniteCompiler.Packed
