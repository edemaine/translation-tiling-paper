import TranslationTiling.FiniteCompiler.Effective.SharedDeckDependence

namespace TranslationTiling.FiniteCompiler.Packed

open Effective SharedCoordinates
open scoped Classical
noncomputable section

variable {k : ℕ} {slopes : List ℕ} {o : SharedOutput k}

def sharedPrivateAt (o : SharedOutput k) (x : Plane) (i : SharedRow k)
    (d : SharedCoordinates.Low (sharedLayout k) i) : ZMod ((sharedLayout k).firstSize i) ×
      ZMod ((sharedLayout k).secondSize i) :=
  o.privateOutput (x,Function.update 0 i d) i

theorem HasSharedDependence.privateAt_eq (h : HasSharedDependence k slopes o) (x : SharedBase k)
    (i : SharedRow k) :
    o.privateOutput x i = sharedPrivateAt o x.1 i (x.2 i) :=
  h.factorLow x.1 x.2 i

theorem HasSharedDependence.privateAt_line (h : HasSharedDependence k slopes o)
    (i : SharedRow k) (hi : i.val < (sharedRows k).length-2) (x y : Plane)
    (hxy : x.2 + (slopes.getD i 0 : ℤ)*x.1 = y.2 + (slopes.getD i 0 : ℤ)*y.1)
    (d : SharedCoordinates.Low (sharedLayout k) i) :
    sharedPrivateAt o x i d = sharedPrivateAt o y i d := by
  unfold sharedPrivateAt
  let f := fun v : SharedBase k => o.privateOutput v i
  rw [show o.privateOutput (x,Function.update 0 i d) i = f (x,Function.update 0 i d) from rfl]
  change f (x,Function.update 0 i d) = f (y,Function.update 0 i d)
  rw [factor_line (sharedLayout k) f _ (h.line i hi) x,
      factor_line (sharedLayout k) f _ (h.line i hi) y,hxy]

theorem HasSharedDependence.sharedAt_line (h : HasSharedDependence k slopes o)
    (s : Bool) (x y : Plane)
    (hxy : x.2 + (if s then 0 else 2)*x.1 = y.2 + (if s then 0 else 2)*y.1)
    (u : ∀ i : SharedRow k, SharedCoordinates.Low (sharedLayout k) i) :
    sharedLine s (o.fixed (x,u)) = sharedLine s (o.fixed (y,u)) := by
  let f := fun v : SharedBase k => sharedLine s (o.fixed v)
  let m : ℤ := if s then 0 else 2
  have hp : ∀ v, f (v - (((1,-m) : Plane),0)) = f v := by
    cases s <;> exact h.shared _
  change f (x,u) = f (y,u)
  rw [factor_line (sharedLayout k) f m hp x,factor_line (sharedLayout k) f m hp y,hxy]

def seedResidues35 (x : Plane) : ZMod 35 × ZMod 35 := (x.1,x.2)

def seedRep35 (s : ZMod 35 × ZMod 35) : Plane := (s.1.val,s.2.val)

theorem HasSharedDependence.privateAt_seed (h : HasSharedDependence k slopes o)
    (t : Fin 2) (x : Plane) (d : SharedCoordinates.Low (sharedLayout k) (sharedSeedRow k t)) :
    sharedPrivateAt o x (sharedSeedRow k t) d =
      sharedPrivateAt o (seedRep35 (seedResidues35 x)) (sharedSeedRow k t) d := by
  let i := sharedSeedRow k t
  let f := fun v : SharedBase k => o.privateOutput v i
  let u := Function.update (0 : ∀ i : SharedRow k, SharedCoordinates.Low (sharedLayout k) i) i d
  let a : SharedBase k := ((35,0),0)
  let b : SharedBase k := ((0,35),0)
  have hp (w : SharedBase k) (hw : ∀ v, f (v-w) = f v) : Function.Periodic f w := by
    intro y
    simpa using (hw (y+w)).symm
  have h₁ := hp a (h.seedX t)
  have h₂ := hp b (h.seedY t)
  let s := seedResidues35 x
  obtain ⟨p,hp'⟩ := (ZMod.intCast_eq_iff 35 x.1 s.1.val).mp (by simp [s,seedResidues35])
  obtain ⟨q,hq'⟩ := (ZMod.intCast_eq_iff 35 x.2 s.2.val).mp (by simp [s,seedResidues35])
  have he : (x,u) - p • a - q • b = (seedRep35 s,u) := by
    apply Prod.ext
    · apply Prod.ext
      · simpa [a,b,seedRep35,zsmul_eq_mul,sub_eq_iff_eq_add,mul_comm] using hp'
      · simpa [a,b,seedRep35,zsmul_eq_mul,sub_eq_iff_eq_add,mul_comm] using hq'
    · simp [a,b]
  change f (x,u) = f (seedRep35 s,u)
  rw [← he,h₂.sub_zsmul_eq,h₁.sub_zsmul_eq]

end
end TranslationTiling.FiniteCompiler.Packed
