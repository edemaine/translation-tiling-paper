import TranslationTiling.FiniteCompiler.Effective.AxisSlotNumericalRows
import TranslationTiling.FiniteCompiler.Effective.AxisSlotKernelGeometry

namespace TranslationTiling.FiniteCompiler.Packed.AxisParameters

open SharedCoordinates Compiler.Effective
open scoped BigOperators Classical

/-- The cyclic order and the rail period are products of the numbered row moduli. -/
def axisOrders (k m : ℕ) : ℕ × ℕ :=
  let rows := List.range (20+2*k*m+8*m)
  ((1225*199*163) * (rows.map fun i =>
    let r := numericalAxisRow k m i
    r.1^2*r.2.1*r.2.2).prod,(numericalSlotLows k m).prod)

theorem axisOrders_primrec : Primrec (fun z : ℕ × ℕ => axisOrders z.1 z.2) := by
  unfold axisOrders
  have h : Primrec (fun z : (ℕ × ℕ) × ℕ => numericalAxisRow z.1.1 z.1.2 z.2) :=
    numericalAxisRow_primrec.comp (show Primrec (fun z : (ℕ × ℕ) × ℕ => (z.1.1,z.1.2,z.2)) by fun_prop)
  have hl := product_primrec.comp numericalSlotLows_primrec
  have hf : Primrec (fun z : (ℕ × ℕ) × ℕ =>
      (numericalAxisRow z.1.1 z.1.2 z.2).1^2 *
      (numericalAxisRow z.1.1 z.1.2 z.2).2.1 *
      (numericalAxisRow z.1.1 z.1.2 z.2).2.2) := by fun_prop
  exact (Primrec.nat_mul.comp (Primrec.const _)
    (product_primrec.comp (mapList (by fun_prop) hf))).pair hl

theorem axisOrders_eq {k m : ℕ} (s : AxisParameters k m) (hs : s.prime = rankedAxisPrime k m) :
    axisOrders k m = (order s.layout,s.period) := by
  have he (n : ℕ) : List.range n = (List.finRange n).map Fin.val := by
    apply List.ext_getElem
    · simp
    · intro i hi hj
      rw [List.getElem_map,List.getElem_range,List.getElem_finRange]
      rfl
  apply Prod.ext
  · simp only [axisOrders,he (20+2*k*m+8*m),List.map_ofFn,List.finRange,
      Function.comp_apply,List.prod_ofFn,order]
    congr 1
    apply Fintype.prod_equiv (slotRowEquiv k m).symm
    intro i
    let j := (slotRowEquiv k m).symm i
    have h : slotRowNumber j = i.val := by
      rw [← slotRowEquiv_val]
      exact congrArg Fin.val ((slotRowEquiv k m).apply_symm_apply i)
    rw [← h,numericalAxisRow_eq s hs]
    rfl
  · simp only [axisOrders,numericalSlotLows,he (20+2*k*m+8*m),List.map_ofFn,
      List.finRange,Function.comp_apply,List.prod_ofFn,period]
    apply Fintype.prod_equiv (slotRowEquiv k m).symm
    intro i
    let j := (slotRowEquiv k m).symm i
    have h : slotRowNumber j = i.val := by
      rw [← slotRowEquiv_val]
      exact congrArg Fin.val ((slotRowEquiv k m).apply_symm_apply i)
    rw [← h,numericalAxisRow_eq s hs]

end TranslationTiling.FiniteCompiler.Packed.AxisParameters
