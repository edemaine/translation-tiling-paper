import TranslationTiling.FiniteCompiler.Effective.AxisSlotCRT
import TranslationTiling.FiniteCompiler.SlotLift

namespace TranslationTiling.FiniteCompiler.Packed.AxisParameters

open SharedCoordinates
open scoped Classical
noncomputable section

variable {k m : ℕ} (s : AxisParameters k m)

abbrev Extra := ∀ i : AxisAddedRow k m, Private s.layout (.inr i)
abbrev ExtraLow := ∀ i : AxisAddedRow k m, SharedCoordinates.Low s.layout (.inr i)

def splitAmbient : SharedCoordinates.Ambient s.layout ≃+
    SharedCoordinates.Ambient (fourValueLayout 0) × s.Extra where
  toFun v := ((v.1,(s.splitFactor v.2).1),(s.splitFactor v.2).2)
  invFun v := (v.1.1,s.splitFactor.symm (v.1.2,v.2))
  left_inv v := Prod.ext rfl (s.splitFactor.symm_apply_apply v.2)
  right_inv v := by
    obtain ⟨⟨x,a⟩,b⟩ := v
    change ((x,(s.splitFactor (s.splitFactor.symm (a,b))).1),
      (s.splitFactor (s.splitFactor.symm (a,b))).2) = _
    rw [s.splitFactor.apply_symm_apply]
  map_add' v w := by
    change ((v.1+w.1,(s.splitFactor (v.2+w.2)).1),(s.splitFactor (v.2+w.2)).2) = _
    rw [map_add]
    rfl

def extraProjection : s.Extra →+ s.ExtraLow :=
  AddMonoidHom.pi fun i =>
    (CyclicShear.low (s.layout.lowSize (.inr i))).comp
      ((AddMonoidHom.fst ..).comp ((AddMonoidHom.fst ..).comp (Pi.evalAddMonoidHom _ i)))

def joinBase (x : FourValueBase 0) (v : s.ExtraLow) : SharedCoordinates.Base s.layout :=
  (x.1,fun | .inl i => x.2 i | .inr i => v i)

def oldSlice (o : SharedCoordinates.Outputs s.layout) (v : s.ExtraLow) : FourValueOutputGraph 0 where
  fixed x := o.fixed (s.joinBase x v)
  privateOutput x i := o.privateOutput (s.joinBase x v) (.inl i)
  high x i := o.high (s.joinBase x v) (.inl i)

def extraPoint (o : SharedCoordinates.Outputs s.layout) (p : s.ExtraLow × FourValueBase 0) :
    s.Extra :=
  (s.splitAmbient (SharedCoordinates.point s.layout o (s.joinBase p.2 p.1))).2

theorem extraPoint_low (o : SharedCoordinates.Outputs s.layout) (p : s.ExtraLow × FourValueBase 0) :
    s.extraProjection (s.extraPoint o p) = p.1 := by
  funext i
  change CyclicShear.low (s.layout.lowSize (.inr i))
    (CyclicShear.shear _ p.2.1.1 (p.1 i) (o.high (s.joinBase p.2 p.1) (.inr i))) = p.1 i
  exact CyclicShear.low_shear _ _ _ _

theorem extraProjection_surjective : Function.Surjective s.extraProjection :=
  fun v => ⟨s.extraPoint ⟨0,0,0⟩ (v,0),s.extraPoint_low _ (v,0)⟩

def oldTileLift [Fintype s.Extra] (F : Finset (SharedCoordinates.Ambient (fourValueLayout 0))) :
    Finset (SharedCoordinates.Ambient s.layout) :=
  (F.product (Finset.univ.filter fun h => s.extraProjection h = 0)).map s.splitAmbient.symm.toEquiv.toEmbedding

theorem oldTileLift_iff [Fintype s.Extra] (F : Finset (SharedCoordinates.Ambient (fourValueLayout 0)))
    (o : SharedCoordinates.Outputs s.layout) :
    Tiles (s.oldTileLift F) (Set.range (SharedCoordinates.point s.layout o)) ↔
      ∀ v, Tiles F (Set.range (SharedCoordinates.point (fourValueLayout 0) (s.oldSlice o v))) := by
  let T := F.product (Finset.univ.filter fun h => s.extraProjection h = 0)
  let G := Set.range fun p : s.ExtraLow × FourValueBase 0 =>
    (SharedCoordinates.point (fourValueLayout 0) (s.oldSlice o p.1) p.2,s.extraPoint o p)
  have hG : s.splitAmbient.symm '' G = Set.range (SharedCoordinates.point s.layout o) := by
    ext x
    constructor
    · rintro ⟨_,⟨p,rfl⟩,rfl⟩
      refine ⟨s.joinBase p.2 p.1,?_⟩
      apply s.splitAmbient.injective
      rw [AddEquiv.apply_symm_apply]
      rfl
    · rintro ⟨b,rfl⟩
      let p : s.ExtraLow × FourValueBase 0 := (fun i => b.2 (.inr i),(b.1,fun i => b.2 (.inl i)))
      have hp : s.joinBase p.2 p.1 = b := by
        refine Prod.ext rfl (funext fun i => ?_)
        cases i <;> rfl
      refine ⟨_,⟨p,rfl⟩,?_⟩
      rw [← hp]
      apply s.splitAmbient.injective
      rw [AddEquiv.apply_symm_apply]
      rfl
  have hT : T.image s.splitAmbient.symm = s.oldTileLift F := by
    simp [T,oldTileLift,Finset.map_eq_image]
  rw [← hG,← hT]
  constructor
  · intro h
    have ht := Compiler.covers_image s.splitAmbient _ _ h
    rw [Finset.image_image,Set.image_image] at ht
    simp only [Function.comp_def,AddEquiv.apply_symm_apply,Finset.image_id',Set.image_id'] at ht
    apply (tiles_product_low_kernel_iff s.extraProjection s.extraProjection_surjective F _
      (fun v => SharedCoordinates.point_injective (fourValueLayout 0) (s.oldSlice o v)) _
      (s.extraPoint_low o)).mp
    convert ht using 1
    · ext p
      simp [T]
  · intro h
    have hh := (tiles_product_low_kernel_iff s.extraProjection s.extraProjection_surjective F _
      (fun v => SharedCoordinates.point_injective (fourValueLayout 0) (s.oldSlice o v)) _
      (s.extraPoint_low o)).mpr h
    apply Compiler.covers_image s.splitAmbient.symm T G
    convert hh using 1
    · ext p
      simp [T]

end
end TranslationTiling.FiniteCompiler.Packed.AxisParameters
