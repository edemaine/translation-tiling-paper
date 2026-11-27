import TranslationTiling.Compiler.AxisSlotBound
import TranslationTiling.Compiler.AxisSlotWide
import TranslationTiling.FiniteCompiler.Effective.AxisSlotNumericalDeck
import TranslationTiling.FiniteCompiler.Effective.AxisSlotOrderCode
import TranslationTiling.FiniteCompiler.Effective.SlotParameterEvaluation

namespace TranslationTiling.Compiler.Size

open FiniteCompiler FiniteCompiler.Packed AxisParameters
open FiniteCompiler.SharedCoordinates FiniteCompiler.Effective Compiler.Effective Compiler.StripLift
open SlotParameters (numericalKernel numericalKernel_primrec)

noncomputable section
set_option maxHeartbeats 2500000
set_option maxRecDepth 10000
attribute [local irreducible] slotSearchCap slotPrimeAt

private theorem axisPrimeCap_primrec :
    Primrec (fun v : ℕ × ℕ => axisPrimeCap v.1 v.2) := by
  unfold axisPrimeCap axisFallbackCap slotWindowCap
  fun_prop

private theorem axisRadius_primrec :
    Primrec (fun v : ℕ × ℕ × ℕ => axisRadius v.1 v.2.1 v.2.2) := by
  unfold axisRadius
  fun_prop

private theorem axisLengthParameter_primrec : Primrec axisLengthParameter := by
  unfold axisLengthParameter
  have h := natLog_primrec 2 (by decide)
  fun_prop

private theorem axisPackedDigits_primrec :
    Primrec (fun z : ℕ × ℕ => axisPackedDigits z.1 z.2) := by
  unfold axisPackedDigits
  have h : Primrec (fun z : ℕ × ℕ => (7*z.2,6*z.2)) := by fun_prop
  have hr := axisRadix_primrec.comp h
  have hc := clog_primrec.comp (hr.pair Primrec.fst)
  fun_prop

def compileAxisWith (T : LeanWang.TileSet) (k m w : ℕ) : Tile 3 :=
  let nr := axisOrders k m
  let P := axisPrimeCap m (2*k*m)
  let Cs := numericalKernel nr.1 nr.2 :: numericalSlotTests T nr.1 k m w
  guardedAssembly (((nr.1,P,SlotParameters.stackTestCap P Cs.length),nr.2,axisRadius P m w),Cs)

private abbrev AxisInput := LeanWang.TileSet × ℕ × ℕ × ℕ

section Computability

attribute [local irreducible] axisOrders axisPrimeCap axisRadius numericalKernel numericalSlotTests

private def axisData (z : AxisInput) : GuardedAssemblyData :=
  let nr := axisOrders z.2.1 z.2.2.1
  let P := axisPrimeCap z.2.2.1 (2*z.2.1*z.2.2.1)
  let Cs := numericalKernel nr.1 nr.2 :: numericalSlotTests z.1 nr.1 z.2.1 z.2.2.1 z.2.2.2
  (((nr.1,P,SlotParameters.stackTestCap P Cs.length),nr.2,axisRadius P z.2.2.1 z.2.2.2),Cs)

private theorem axisData_primrec : Primrec axisData := by
  let nr (z : AxisInput) := axisOrders z.2.1 z.2.2.1
  have hn : Primrec nr := axisOrders_primrec.comp
    (show Primrec (fun z : AxisInput => (z.2.1,z.2.2.1)) by fun_prop)
  let P (z : AxisInput) := axisPrimeCap z.2.2.1 (2*z.2.1*z.2.2.1)
  have hP : Primrec P := axisPrimeCap_primrec.comp
    (show Primrec (fun z : AxisInput => (z.2.2.1,2*z.2.1*z.2.2.1)) by fun_prop)
  let L (z : AxisInput) :=
    numericalKernel (nr z).1 (nr z).2 :: numericalSlotTests z.1 (nr z).1 z.2.1 z.2.2.1 z.2.2.2
  let args (z : AxisInput) : LeanWang.TileSet × ℕ × ℕ × ℕ × ℕ :=
    (z.1,(nr z).1,z.2.1,z.2.2.1,z.2.2.2)
  have hargs : Primrec args := by unfold args; fun_prop
  have hker := numericalKernel_primrec.comp hn
  have htests := numericalSlotTests_primrec.comp hargs
  have hL : Primrec L := (Primrec.list_cons.comp hker htests).of_eq (by intro z; rfl)
  let X (z : AxisInput) := SlotParameters.stackTestCap (P z) (L z).length
  let H (z : AxisInput) := axisRadius (P z) z.2.2.1 z.2.2.2
  have hX : Primrec X := by unfold X SlotParameters.stackTestCap; fun_prop
  have hH : Primrec H := axisRadius_primrec.comp
    (show Primrec (fun z : AxisInput => (P z,z.2.2.1,z.2.2.2)) by fun_prop)
  let data (z : AxisInput) : GuardedAssemblyData := ((((nr z).1,P z,X z),(nr z).2,H z),L z)
  have hdata : Primrec data :=
    (((Primrec.fst.comp hn).pair (hP.pair hX)).pair ((Primrec.snd.comp hn).pair hH)).pair hL
  exact hdata.of_eq (by intro z; rfl)

theorem compileAxisWith_computable :
    Computable (fun z : AxisInput => compileAxisWith z.1 z.2.1 z.2.2.1 z.2.2.2) :=
  (guardedAssembly_computable.comp axisData_primrec.to_comp).of_eq (by intro z; rfl)

end Computability

theorem compileAxisWith_correct (T : LeanWang.TileSet) {k m w : ℕ}
    (hn : 0 < T.length) (hwm : w ≤ m) (hcap : T.length ≤ (axisRadix m w)^k) :
    let U := compileAxisWith T k m w
    U ≠ [] ∧ FaceConnected U ∧ (LeanWang.TilesPlane T ↔ TranslationTiling.Tiles U) ∧
      U.length ≤ axisEstimate k m w := by
  let s := rankedAxisParameters k m
  let P := axisPrimeCap m (2*k*m)
  have hP : SlotParameters.slotBasePrimeCap ≤ P := by
    have hA : 2048 ≤ axisFallbackCap m := threshold_le_slotSearchCap ..
    have hAA : 2048 ≤ (axisFallbackCap m)^2 :=
      (by decide : 2048 ≤ 2048^2).trans (Nat.pow_le_pow_left hA 2)
    exact hAA.trans ((le_max_left ..).trans (Nat.le_mul_of_pos_left _ (by decide : 0 < 8)))
  have h3 : 3 < P := (by decide : 3 < SlotParameters.slotBasePrimeCap).trans_le hP
  have hs : s.prime = rankedAxisPrime k m := rfl
  obtain ⟨hA,hQ⟩ := rankedAxisPrime_caps k m
  obtain ⟨hU,hconn,hiff,hvol⟩ :=
    s.numericalSlotPolycube hn hcap hs hwm (s.primeBound hP hQ) h3 hQ
  unfold compileAxisWith
  rw [s.axisOrders_eq hs]
  refine ⟨hU,hconn,hiff,hvol.trans ?_⟩
  apply axis_size_from_volume s.period_pos (Nat.div_mul_le_self ..) rfl _ rfl
    (axis_order_le s hA hQ)
  apply max_le_max_left
  apply max_le_max_left
  simpa only [List.length_cons,Nat.succ_eq_add_one] using numericalSlotTests_length T _ k m w

def compileAxis (T : LeanWang.TileSet) : Tile 3 :=
  let t := axisLengthParameter T.length
  compileAxisWith T (axisPackedDigits T.length t) (7*t) (6*t)

theorem compileAxis_computable : Computable compileAxis := by
  let t (T : LeanWang.TileSet) := axisLengthParameter T.length
  have ht : Primrec t := axisLengthParameter_primrec.comp Primrec.list_length
  have hk := axisPackedDigits_primrec.comp (Primrec.list_length.pair ht)
  have hm := Primrec.nat_mul.comp (Primrec.const 7) ht
  have hw := Primrec.nat_mul.comp (Primrec.const 6) ht
  exact (compileAxisWith_computable.comp (Primrec.id.pair (hk.pair (hm.pair hw))).to_comp).of_eq
    (by intro T; rfl)

theorem compileAxis_correct (T : LeanWang.TileSet) (hn : 0 < T.length) :
    let t := axisLengthParameter T.length
    let U := compileAxis T
    U ≠ [] ∧ FaceConnected U ∧ (LeanWang.TilesPlane T ↔ TranslationTiling.Tiles U) ∧
      U.length ≤ axisEstimate (axisPackedDigits T.length t) (7*t) (6*t) := by
  let t := axisLengthParameter T.length
  have ht : 0 < t := (by decide : 0 < 1).trans_le (le_max_left ..)
  exact compileAxisWith_correct T hn (by omega) (axisPackedDigits_capacity _ _ ht)

end
end TranslationTiling.Compiler.Size
