import TranslationTiling.Compiler.AxisSlotEstimate
import TranslationTiling.FiniteCompiler.Effective.AxisSlotDeckCount
import TranslationTiling.FiniteCompiler.Effective.AxisSlotPolycube

namespace TranslationTiling.Compiler.Size

open FiniteCompiler FiniteCompiler.Packed AxisParameters
open FiniteCompiler.SharedCoordinates FiniteCompiler.Effective Compiler.StripLift

def axisEstimate (k m w : ℕ) :=
  let P := axisPrimeCap m (2*k*m)
  let X := SlotParameters.stackTestCap P (axisDeckCap k m ((axisRadix m w)^k))
  let H := axisRadius P m w
  10^32 * (order (fourValueLayout 0) * (P^(7*(2*k*m))*(axisFallbackCap m)^(8*m))) *
    reservedCap X P*(H+1)^2

private theorem axisStack_mono {P X Y : ℕ} (h : X ≤ Y) :
    reservedCap X P ≤ reservedCap Y P := by
  have hlog : Stacking.differenceLog X ≤ Stacking.differenceLog Y :=
    Nat.add_le_add_right (Nat.log_mono_right (Nat.mul_le_mul_left _ h)) _
  unfold reservedCap reservedThreshold
  gcongr

theorem axis_size_from_volume {P X H R N k m w : ℕ}
    (hR : 0 < R) (hNX : N/R*R ≤ N)
    (hP : P = axisPrimeCap m (2*k*m))
    (hX : X ≤ SlotParameters.stackTestCap P (axisDeckCap k m ((axisRadix m w)^k)))
    (hH : H = axisRadius P m w)
    (hN : N ≤ order (fourValueLayout 0) * (P^(7*(2*k*m))*(axisFallbackCap m)^(8*m))) :
    reservedVolumeCap 35 (fun _ => H) R (N/R) (reservedCap X P) ≤ axisEstimate k m w := by
  let Y := SlotParameters.stackTestCap P (axisDeckCap k m ((axisRadix m w)^k))
  change X ≤ Y at hX
  have hStack := axisStack_mono (P:=P) hX
  let M := order (fourValueLayout 0) * (P^(7*(2*k*m))*(axisFallbackCap m)^(8*m))
  have hV := slotVolume_le H R (N/R) N (reservedCap X P) hR hNX
  refine hV.trans ?_
  calc
    _ ≤ (10^32*M*reservedCap Y P)*(H+1)^2 :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul (Nat.mul_le_mul_left _ hN) hStack)
    _ = _ := by subst H; subst P; rfl

end TranslationTiling.Compiler.Size
