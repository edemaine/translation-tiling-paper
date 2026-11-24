import TranslationTiling.FiniteCompiler.Effective.FourValueWangCoordinates

namespace TranslationTiling.FiniteCompiler.Packed

open Compiler SharedCoordinates
open scoped Classical

noncomputable section

set_option maxRecDepth 2000
set_option maxHeartbeats 3000000

attribute [local irreducible] wangValueModulus fourValueLow

private theorem wangActivation_source_read {k : ℕ} (w : WangDigitRow k) (o : FourValueOutputGraph k)
    (hd : HasFourValueDependence k (tailSlopes k) o) (x : Plane) (v : WangActivationIndex w) :
    let src := wangActivationSource w (x,0) v
    let d := -wangLowEquiv w v.1
    wangActivationProjection w (SharedCoordinates.point (fourValueLayout k) o src).2 =
      joinWangUseful w (fourValueLine (wangSlopeFactor w)
        (o.fixed (x,Function.update 0 (wangDigitRow w) d)),
        (fourValuePrivateAt o x (wangDigitRow w) d).2) := by
  dsimp only
  let src := wangActivationSource w (x,0) v
  let i := wangDigitRow w
  let d := -wangLowEquiv w v.1
  have hlow : src.2 = Function.update
      (0 : ∀ j : FourValueRow k, SharedCoordinates.Low (fourValueLayout k) j) i d := by
    funext j
    by_cases h : j = i
    · subst h
      rw [Function.update_self,wangActivationSource_self]
      simp [d]
    · rw [Function.update_of_ne h]
      exact wangActivationSource_other w (x,0) v j h
  have hline := wangLineValue_source w (x,0) v
  have hordinary : i.val < (fourValueRows k).length-2 := by
    have := fourValueRows_length k
    have := w.isLt
    change 18+w.val < _
    omega
  rw [wangActivationProjection_point,hd.privateAt_eq,show src.2 i = d by rw [hlow,Function.update_self],
    hd.privateAt_line i hordinary src.1 x (by
      rw [wangDigitRow_slope]
      by_cases h : w.val < k <;> simpa [wangLineValue,h] using hline)]
  have he : fourValueLine (wangSlopeFactor w) (o.fixed src) =
      fourValueLine (wangSlopeFactor w) (o.fixed (x,src.2)) := by
    have hs := hd.sharedAt_line (wangSlopeFactor w) src.1 x (by
      by_cases h : w.val < k <;> simpa [wangSlopeFactor,wangLineValue,h] using hline) src.2
    simpa only [Prod.eta] using hs
  rw [he,hlow]

attribute [local irreducible] joinWangUseful wangActivationProjection wangActivationSource fourValuePrivateAt

theorem fourValue_wang_active {k : ℕ} (w : WangDigitRow k) (o : FourValueOutputGraph k)
    (hd : HasFourValueDependence k (tailSlopes k) o)
    (hcover : Tiles ((fourValueWangActivation k w).toFinset.image (decodePoint (fourValueLayout k)))
      (Set.range (SharedCoordinates.point (fourValueLayout k) o))) (x : Plane) :
    ∃ j : FourValueShift.Index, j ≠ 0 ∧ ¬ ∃ t, ∀ d,
      (joinWangUseful w (0,(fourValuePrivateAt o x (wangDigitRow w) d).2)) j = t := by
  let e := (wangLowEquiv w).toEquiv.prodCongr (Equiv.refl (WangShift w))
  let c (d : SharedCoordinates.Low (fourValueLayout k) (wangDigitRow w)) :=
    joinWangUseful w (fourValueLine (wangSlopeFactor w)
      (o.fixed (x,Function.update 0 (wangDigitRow w) (-d))),
      (fourValuePrivateAt o x (wangDigitRow w) (-d)).2)
  let high (p : SharedCoordinates.Low (fourValueLayout k) (wangDigitRow w) × WangShift w) :=
    o.high (wangActivationSource w (x,0) (e.symm p)) (wangDigitRow w)
  have h := (fourValueWangActivation_iff w o).mp hcover (x,0)
  let f (v : WangActivationIndex w) :=
    (wangActivationProjection w (SharedCoordinates.point (fourValueLayout k) o
      (wangActivationSource w (x,0) v)).2 + FourValueShift.shift (m := wangValueModulus w) v.2,
      o.high (wangActivationSource w (x,0) v) (wangDigitRow w))
  change Function.Bijective f at h
  have he : f ∘ e.symm = fun p =>
      (c p.1 + FourValueShift.shift (m := wangValueModulus w) p.2,high p) := by
    funext p
    let v := e.symm p
    have h₁ : wangLowEquiv w v.1 = p.1 := (wangLowEquiv w).apply_symm_apply _
    have h₂ : v.2 = p.2 := rfl
    simp only [Function.comp_apply,f]
    rw [wangActivation_source_read w o hd x v,h₁,h₂] <;> rfl
  have hc : Function.Bijective (fun p =>
      (c p.1 + FourValueShift.shift (m := wangValueModulus w) p.2,high p)) :=
    Eq.mp (congrArg Function.Bijective he) (h.comp e.symm.bijective)
  obtain ⟨j,hj,hn⟩ := wangActivation_active w c high hc
  refine ⟨j,hj,?_⟩
  rintro ⟨t,ht⟩
  apply hn
  refine ⟨t,fun d => ?_⟩
  unfold c
  rw [joinWangUseful_nonzero w j hj]
  exact ht (-d)

end
end TranslationTiling.FiniteCompiler.Packed
