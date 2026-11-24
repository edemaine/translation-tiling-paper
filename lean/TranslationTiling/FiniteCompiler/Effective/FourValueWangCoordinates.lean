import TranslationTiling.FiniteCompiler.Effective.FourValueWangDeck
import TranslationTiling.FiniteCompiler.Effective.PackedParameterData

namespace TranslationTiling.FiniteCompiler.Packed

open Compiler SharedCoordinates
open scoped Classical

noncomputable section

set_option maxRecDepth 2000
set_option maxHeartbeats 3000000

attribute [local irreducible] wangValueModulus fourValueLow

def wangLowEquiv {k : ℕ} (w : WangDigitRow k) :
    ZMod (fourValueLow k w) ≃+* SharedCoordinates.Low (fourValueLayout k) (wangDigitRow w) :=
  ZMod.ringEquivCongr (wangDigitRow_low w).symm

theorem wangActivationSource_self {k : ℕ} (w : WangDigitRow k) (x : FourValueBase k)
    (v : WangActivationIndex w) :
    (wangActivationSource w x v).2 (wangDigitRow w) =
      x.2 (wangDigitRow w) - wangLowEquiv w v.1 := by
  simp only [wangActivationSource,SharedCoordinates.activationSource,Function.update_self]
  rw [← wangRecordLow w v,map_intCast]

theorem wangActivationSource_other {k : ℕ} (w : WangDigitRow k) (x : FourValueBase k)
    (v : WangActivationIndex w) (i : FourValueRow k) (hi : i ≠ wangDigitRow w) :
    (wangActivationSource w x v).2 i = x.2 i :=
  Function.update_of_ne hi _ _

def wangLineValue {k : ℕ} (w : WangDigitRow k) (x : Plane) : ℤ :=
  x.2 + (if w.val < k then 0 else 2)*x.1

theorem wangLineValue_source {k : ℕ} (w : WangDigitRow k) (x : FourValueBase k)
    (v : WangActivationIndex w) : wangLineValue w (wangActivationSource w x v).1 =
      wangLineValue w x.1 := by
  unfold wangLineValue
  change (x.1.2-(wangRecordHorizontal w v).2) + _ * (x.1.1-(wangRecordHorizontal w v).1) = _
  rw [wangRecordSlope]
  ring

theorem wangDigitRow_slope {k : ℕ} (w : WangDigitRow k) :
    (tailSlopes k).getD (wangDigitRow w).val 0 = if w.val < k then 0 else 2 := by
  have hw := w.isLt
  have h : (wangDigitRow w).val < (tailSlopes k).length := by simp [tailSlopes,wangDigitRow]
  rw [List.getD_eq_getElem _ _ h]
  simp [tailSlopes,Profile.slope,wangDigitRow,ternaryLayoutProfile,radixLayoutProfile,
    show ¬18+w.val < 18 by omega]

theorem wangActivationProjection_point {k : ℕ} (w : WangDigitRow k) (o : FourValueOutputGraph k)
    (x : FourValueBase k) :
    wangActivationProjection w (SharedCoordinates.point (fourValueLayout k) o x).2 =
      joinWangUseful w (fourValueLine (wangSlopeFactor w) (o.fixed x),
        (o.privateOutput x (wangDigitRow w)).2) := by
  unfold wangActivationProjection
  simp only [AddMonoidHom.comp_apply,AddEquiv.coe_toAddMonoidHom]
  congr 1
  generalize wangSlopeFactor w = s
  cases s <;> rfl

end
end TranslationTiling.FiniteCompiler.Packed
