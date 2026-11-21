import TranslationTiling.FiniteCompiler.CyclicShear
import TranslationTiling.FiniteCompiler.GraphTests
import Mathlib.Data.ZMod.QuotientRing

namespace TranslationTiling.FiniteCompiler.SharedCoordinates

open scoped BigOperators

noncomputable section

/-- The first useful modulus is 1 in a Wang row. Its nontrivial first
coordinate is one of the two shared factors and is stored only once. -/
structure Layout (I : Type*) where
  lowSize : I → ℕ
  firstSize : I → ℕ
  secondSize : I → ℕ
  lowSize_pos : ∀ i, 0 < lowSize i

variable {I : Type*} [Fintype I] (L : Layout I)

abbrev Low (i : I) := ZMod (L.lowSize i)
abbrev Square (i : I) := ZMod ((L.lowSize i)^2)
abbrev Private (i : I) := (Square L i × ZMod (L.firstSize i)) × ZMod (L.secondSize i)
abbrev Fixed := (ZMod 1225 × ZMod 199) × ZMod 163
abbrev Factor := Fixed × (∀ i, Private L i)
abbrev Ambient := Plane × Factor L
abbrev Base := Plane × (∀ i, Low L i)

instance (i : I) : NeZero (L.lowSize i) := ⟨(L.lowSize_pos i).ne'⟩

def rowModulus (i : I) : ℕ := (L.lowSize i)^2 * L.firstSize i * L.secondSize i

def order : ℕ := (1225*199*163) * ∏ i, rowModulus L i

def privateCRT (i : I)
    (h₁ : Nat.Coprime ((L.lowSize i)^2) (L.firstSize i))
    (h₂ : Nat.Coprime ((L.lowSize i)^2 * L.firstSize i) (L.secondSize i)) :
    ZMod (rowModulus L i) ≃+* Private L i :=
  (ZMod.chineseRemainder h₂).trans ((ZMod.chineseRemainder h₁).prodCongr (RingEquiv.refl _))

private def fixedCRT : ZMod (1225*199*163) ≃+* Fixed :=
  (ZMod.chineseRemainder (by decide : Nat.Coprime (1225*199) 163)).trans
    ((ZMod.chineseRemainder (by decide : Nat.Coprime 1225 199)).prodCongr (RingEquiv.refl _))

def finiteCRT
    (h₁ : ∀ i, Nat.Coprime ((L.lowSize i)^2) (L.firstSize i))
    (h₂ : ∀ i, Nat.Coprime ((L.lowSize i)^2 * L.firstSize i) (L.secondSize i))
    (hrows : Pairwise (fun i j => Nat.Coprime (rowModulus L i) (rowModulus L j)))
    (hfixed : Nat.Coprime (1225*199*163) (∏ i, rowModulus L i)) :
    ZMod (order L) ≃+* Factor L :=
  (ZMod.chineseRemainder hfixed).trans
    (fixedCRT.prodCongr ((ZMod.prodEquivPi (rowModulus L) hrows).trans
      (RingEquiv.piCongrRight fun i => privateCRT L i (h₁ i) (h₂ i))))

def decode (n : ℕ) : Factor L := (((n,n),n),fun _ => ((n,n),n))

theorem finiteCRT_natCast
    (h₁ : ∀ i, Nat.Coprime ((L.lowSize i)^2) (L.firstSize i))
    (h₂ : ∀ i, Nat.Coprime ((L.lowSize i)^2 * L.firstSize i) (L.secondSize i))
    (hrows : Pairwise (fun i j => Nat.Coprime (rowModulus L i) (rowModulus L j)))
    (hfixed : Nat.Coprime (1225*199*163) (∏ i, rowModulus L i)) (n : ℕ) :
    finiteCRT L h₁ h₂ hrows hfixed (n : ZMod (order L)) = decode L n := by
  rw [map_natCast]
  rfl

/-- The two Wang slopes use the fixed factors of orders 199 and 163. -/
def sharedPrime (firstSlope : Bool) : ℕ := if firstSlope then 199 else 163

instance (firstSlope : Bool) : NeZero (sharedPrime firstSlope) := ⟨by cases firstSlope <;> decide⟩

def privateUseful (i : I) : Factor L →+ ZMod (L.firstSize i) × ZMod (L.secondSize i) where
  toFun v := ((v.2 i).1.2,(v.2 i).2)
  map_zero' := rfl
  map_add' _ _ := rfl

omit [Fintype I] in
@[simp] theorem privateUseful_decode (i : I) (n : ℕ) :
    privateUseful L i (decode L n) = ((n : ZMod (L.firstSize i)),(n : ZMod (L.secondSize i))) :=
  rfl

def sharedUseful (firstSlope : Bool) (i : I) :
    Factor L →+ ZMod (sharedPrime firstSlope) × ZMod (L.secondSize i) := by
  cases firstSlope
  · exact { toFun := fun v => (v.1.2,(v.2 i).2), map_zero' := rfl, map_add' := fun _ _ => rfl }
  · exact { toFun := fun v => (v.1.1.2,(v.2 i).2), map_zero' := rfl, map_add' := fun _ _ => rfl }

omit [Fintype I] in
@[simp] theorem sharedUseful_decode (firstSlope : Bool) (i : I) (n : ℕ) :
    sharedUseful L firstSlope i (decode L n) =
      ((n : ZMod (sharedPrime firstSlope)),(n : ZMod (L.secondSize i))) := by
  cases firstSlope <;> rfl

def sharedLineUseful (firstSlope : Bool) :
    Factor L →+ ZMod (sharedPrime firstSlope) × ZMod 1 := by
  cases firstSlope
  · refine { toFun := fun v => (v.1.2,0), map_zero' := rfl, map_add' := ?_ }
    intro x y
    exact Prod.ext rfl (zero_add _).symm
  · refine { toFun := fun v => (v.1.1.2,0), map_zero' := rfl, map_add' := ?_ }
    intro x y
    exact Prod.ext rfl (zero_add _).symm

omit [Fintype I] in
@[simp] theorem sharedLineUseful_decode (firstSlope : Bool) (n : ℕ) :
    sharedLineUseful L firstSlope (decode L n) =
      ((n : ZMod (sharedPrime firstSlope)),(n : ZMod 1)) := by
  cases firstSlope <;> exact Prod.ext rfl (Subsingleton.elim _ _)

def baseProjection : Ambient L →+ Base L where
  toFun v := (v.1, fun i => CyclicShear.low (L.lowSize i) (v.2.2 i).1.1)
  map_zero' := by
    refine Prod.ext rfl ?_
    funext i
    exact map_zero _
  map_add' x y := by
    refine Prod.ext rfl ?_
    funext i
    exact map_add _ _ _

structure Outputs where
  fixed : Base L → Fixed
  privateOutput : Base L → ∀ i, ZMod (L.firstSize i) × ZMod (L.secondSize i)
  high : Base L → ∀ i, Low L i

def point (o : Outputs L) (x : Base L) : Ambient L :=
  (x.1,o.fixed x,fun i =>
    ((CyclicShear.shear (L.lowSize i) x.1.1 (x.2 i) (o.high x i), (o.privateOutput x i).1),
      (o.privateOutput x i).2))

omit [Fintype I] in
@[simp] theorem baseProjection_point (o : Outputs L) (x : Base L) :
    baseProjection L (point L o x) = x := by
  refine Prod.ext rfl ?_
  funext i
  exact CyclicShear.low_shear _ _ _ _

omit [Fintype I] in
theorem baseProjection_surjective : Function.Surjective (baseProjection L) :=
  fun x => ⟨point L ⟨fun _ => 0,fun _ _ => 0,fun _ _ => 0⟩ x,baseProjection_point L _ x⟩

omit [Fintype I] in
theorem point_injective (o : Outputs L) : Function.Injective (point L o) :=
  Function.LeftInverse.injective (baseProjection_point L o)

def outputsOfSection (s : Base L → Ambient L) (hs : ∀ x, baseProjection L (s x) = x) :
    Outputs L where
  fixed x := (s x).2.1
  privateOutput x i := ((s x).2.2 i |>.1.2, (s x).2.2 i |>.2)
  high x i := (CyclicShear.shearEquiv (L.lowSize i) x.1.1 (x.2 i)).symm
    ⟨((s x).2.2 i).1.1, congrArg (fun z : Base L => z.2 i) (hs x)⟩

omit [Fintype I] in
@[simp] theorem point_outputsOfSection (s : Base L → Ambient L)
    (hs : ∀ x, baseProjection L (s x) = x) (x : Base L) :
    point L (outputsOfSection L s hs) x = s x := by
  refine Prod.ext ?_ ?_
  · exact (congrArg Prod.fst (hs x)).symm
  · refine Prod.ext rfl ?_
    funext i
    refine Prod.ext (Prod.ext ?_ rfl) rfl
    exact congrArg Subtype.val ((CyclicShear.shearEquiv (L.lowSize i) x.1.1 (x.2 i)).apply_symm_apply
      ⟨((s x).2.2 i).1.1, congrArg (fun z : Base L => z.2 i) (hs x)⟩)

end
end TranslationTiling.FiniteCompiler.SharedCoordinates
