import TranslationTiling.FiniteCompiler.SharedActivation
import TranslationTiling.FiniteCompiler.SharedCoordinates

namespace TranslationTiling.FiniteCompiler.SharedCoordinates

noncomputable section

variable {I : Type*} [Fintype I] [DecidableEq I] (L : Layout I)
variable {Y J : Type*} [AddCommGroup Y]

def activationSource (i : I) (h : Plane) (l : Low L i) (x : Base L) : Base L :=
  (x.1-h, Function.update x.2 i (x.2 i-l))

def highCoordinate (i : I) (v : Ambient L) : Low L i :=
  let x := baseProjection L v
  (CyclicShear.shearEquiv (L.lowSize i) x.1.1 (x.2 i)).symm ⟨(v.2.2 i).1.1,rfl⟩

omit [Fintype I] [DecidableEq I] in
@[simp] theorem shear_highCoordinate (i : I) (v : Ambient L) :
    let x := baseProjection L v
    CyclicShear.shear (L.lowSize i) x.1.1 (x.2 i) (highCoordinate L i v) =
      (v.2.2 i).1.1 := by
  let x := baseProjection L v
  exact congrArg Subtype.val ((CyclicShear.shearEquiv (L.lowSize i) x.1.1 (x.2 i)).apply_symm_apply
    ⟨(v.2.2 i).1.1,rfl⟩)

omit [Fintype I] [DecidableEq I] in
@[simp] theorem highCoordinate_point (i : I) (o : Outputs L) (x : Base L) :
    highCoordinate L i (point L o x) = o.high x i := by
  apply CyclicShear.shear_injective (L.lowSize i) x.1.1 (x.2 i)
  have h := shear_highCoordinate L i (point L o x)
  dsimp only at h
  rw [baseProjection_point] at h
  exact h

/-- All three families of outputs can be chosen independently in any
fibre of the low projection. -/
def baseFibreEquiv (x : Base L) :
    {v : Ambient L // baseProjection L v = x} ≃
    Fixed × (∀ i, ZMod (L.firstSize i) × ZMod (L.secondSize i)) × (∀ i, Low L i) where
  toFun v := (v.val.2.1,fun i => privateUseful L i v.val.2,fun i => highCoordinate L i v.val)
  invFun y := ⟨point L ⟨fun _ => y.1, fun _ => y.2.1, fun _ => y.2.2⟩ x,
    baseProjection_point L _ x⟩
  left_inv v := by
    apply Subtype.ext
    refine Prod.ext ?_ (Prod.ext rfl ?_)
    · exact (congrArg Prod.fst v.property).symm
    · funext i
      refine Prod.ext (Prod.ext ?_ rfl) rfl
      have h := shear_highCoordinate L i v.val
      dsimp only at h
      rwa [v.property] at h
  right_inv y := by
    refine Prod.ext rfl (Prod.ext rfl ?_)
    funext i
    exact highCoordinate_point L i _ x

def ActivationBatch (i : I) (ψ : Factor L →+ Y) (h : Plane) (e : Y) (v : Ambient L) : Prop :=
  v.1 = h ∧ (v.2.2 i).1.1 = (h.1 : Square L i) ∧ ψ v.2 = e ∧
  ∀ j, j ≠ i → CyclicShear.low (L.lowSize j) (v.2.2 j).1.1 = 0

theorem sub_point_activationBatch (i : I) (ψ : Factor L →+ Y) (h : Plane) (e : Y)
    (o : Outputs L) (v : Ambient L) (x : Base L) :
    ActivationBatch L i ψ h e (v - point L o x) ↔
      let y := baseProjection L v
      activationSource L i h (h.1 : Low L i) y = x ∧
      ψ (point L o x).2 + e = ψ v.2 ∧ o.high x i = highCoordinate L i v := by
  let y := baseProjection L v
  have low_cast : CyclicShear.low (L.lowSize i) (h.1 : Square L i) = (h.1 : Low L i) := by
    simp [CyclicShear.low]
  have he (hy : (activationSource L i h (h.1 : Low L i) y) = x) :
      CyclicShear.shear (L.lowSize i) x.1.1 (x.2 i) (o.high x i) + (h.1 : Square L i) =
        CyclicShear.shear (L.lowSize i) y.1.1 (y.2 i) (o.high x i) := by
    have hs := CyclicShear.shear_source_add (L.lowSize i) y.1.1 h.1 (y.2 i)
      (h.1 : Low L i) (o.high x i) rfl
    have ha := congrArg (fun w : Base L => w.1.1) hy
    have hb := congrArg (fun w : Base L => w.2 i) hy
    change y.1.1 - h.1 = x.1.1 at ha
    simp only [activationSource, Function.update_self] at hb
    rwa [ha,hb] at hs
  change ActivationBatch L i ψ h e _ ↔
    activationSource L i h (h.1 : Low L i) y = x ∧
      ψ (point L o x).2 + e = ψ v.2 ∧ o.high x i = highCoordinate L i v
  constructor
  · rintro ⟨hh,hhi,hc,ho⟩
    have hx : activationSource L i h (h.1 : Low L i) y = x := by
      apply Prod.ext
      · change v.1 - x.1 = h at hh
        change v.1 - h = x.1
        rwa [sub_eq_iff_eq_add,add_comm, ← sub_eq_iff_eq_add] at hh
      · funext j
        by_cases hj : j = i
        · subst j
          have hr := congrArg (CyclicShear.low (L.lowSize i)) hhi
          change CyclicShear.low (L.lowSize i)
            ((v.2.2 i).1.1 - CyclicShear.shear (L.lowSize i) x.1.1 (x.2 i) (o.high x i)) = _ at hr
          rw [map_sub,CyclicShear.low_shear,low_cast] at hr
          simp only [activationSource,Function.update_self]
          change CyclicShear.low (L.lowSize i) (v.2.2 i).1.1 - (h.1 : Low L i) = _
          rwa [sub_eq_iff_eq_add,add_comm, ← sub_eq_iff_eq_add] at hr
        · have hr := ho j hj
          change CyclicShear.low (L.lowSize j)
            ((v.2.2 j).1.1 - CyclicShear.shear (L.lowSize j) x.1.1 (x.2 j) (o.high x j)) = 0 at hr
          rw [map_sub,CyclicShear.low_shear,sub_eq_zero] at hr
          simp only [activationSource,Function.update_of_ne hj]
          change CyclicShear.low (L.lowSize j) (v.2.2 j).1.1 = x.2 j
          exact hr
    refine ⟨hx, ?_, ?_⟩
    · change ψ (v.2 - (point L o x).2) = e at hc
      rw [map_sub,sub_eq_iff_eq_add,add_comm] at hc
      exact hc.symm
    · apply CyclicShear.shear_injective (L.lowSize i) y.1.1 (y.2 i)
      rw [shear_highCoordinate L i v, ← he hx]
      change (v.2.2 i).1.1 -
        CyclicShear.shear (L.lowSize i) x.1.1 (x.2 i) (o.high x i) = _ at hhi
      exact ((sub_eq_iff_eq_add.mp hhi).trans (add_comm _ _)).symm
  · rintro ⟨hx,hc,hβ⟩
    refine ⟨?_,?_,?_,?_⟩
    · change v.1 - x.1 = h
      rw [← hx]
      change v.1 - (v.1 - h) = h
      exact sub_sub_cancel _ _
    · have hsum := he hx
      have ht : CyclicShear.shear (L.lowSize i) y.1.1 (y.2 i) (o.high x i) = (v.2.2 i).1.1 := by
        rw [hβ]
        exact shear_highCoordinate L i v
      rw [ht] at hsum
      change (v.2.2 i).1.1 - CyclicShear.shear (L.lowSize i) x.1.1 (x.2 i) (o.high x i) = _
      exact sub_eq_iff_eq_add.mpr (hsum.symm.trans (add_comm _ _))
    · change ψ (v.2 - (point L o x).2) = e
      rw [map_sub,← hc,add_sub_cancel_left]
    · intro j hj
      change CyclicShear.low (L.lowSize j)
        ((v.2.2 j).1.1 - CyclicShear.shear (L.lowSize j) x.1.1 (x.2 j) (o.high x j)) = 0
      rw [map_sub,CyclicShear.low_shear, ← hx]
      change y.2 j - Function.update y.2 i (y.2 i - (h.1 : Low L i)) j = 0
      rw [Function.update_of_ne hj,sub_self]

end
end TranslationTiling.FiniteCompiler.SharedCoordinates
