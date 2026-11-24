import TranslationTiling.FiniteCompiler.Effective.FourValueActivation
import TranslationTiling.FiniteCompiler.Effective.SharedKernel
import TranslationTiling.FiniteCompiler.SharedDependence

namespace TranslationTiling.FiniteCompiler.Packed

open Compiler Compiler.Effective Effective SharedCoordinates
open scoped Classical

noncomputable section

set_option maxRecDepth 10000
set_option maxHeartbeats 3000000

def fourValueLayoutCRT (k : ℕ) : ZMod (order (fourValueLayout k)) ≃+* Factor (fourValueLayout k) := by
  rw [fourValueLayout_order]
  exact fourValueRowsCRT k

def fourValueLowVector (k : ℕ) (g : Option ℕ) : ∀ i, SharedCoordinates.Low (fourValueLayout k) i :=
  fun i => if g = some i.val then 1 else 0

@[simp] theorem fourValueLowVector_none (k : ℕ) : fourValueLowVector k none = 0 := by
  funext i
  simp [fourValueLowVector]

@[simp] theorem fourValueLowVector_some (k : ℕ) (i : FourValueRow k) :
    fourValueLowVector k (some i.val) =
      Function.update (0 : ∀ j : FourValueRow k, SharedCoordinates.Low (fourValueLayout k) j) i 1 := by
  funext j
  by_cases h : j = i
  · subst j; simp [fourValueLowVector]
  · simp [fourValueLowVector,h,show i.val ≠ j.val from fun e => h (Fin.ext e.symm)]

/-- The numerical dependence mask tests invariance for whichever useful
projection its two moduli specify. -/
theorem fourValueInvariance_iff (k : ℕ) {a b : ℕ}
    (ψ : Factor (fourValueLayout k) →+ ZMod a × ZMod b)
    (hψ : ∀ n : ℕ, ψ (decode (fourValueLayout k) n) = ((n : ZMod a),(n : ZMod b)))
    (h : Plane) (g : Option ℕ) (o : SharedCoordinates.Outputs (fourValueLayout k)) :
    Tiles ((sharedInvariance (fourValueRows k) a b h g).toFinset.image (decodePoint (fourValueLayout k)))
        (Set.range (SharedCoordinates.point (fourValueLayout k) o)) ↔
    ∀ p : SharedCoordinates.Base (fourValueLayout k), ψ (SharedCoordinates.point (fourValueLayout k) o (p - (h,fourValueLowVector k g))).2 =
      ψ (SharedCoordinates.point (fourValueLayout k) o p).2 := by
  let L := fourValueLayout k
  let shift := (h,fourValueLowVector k g)
  let proj := ψ.comp (AddMonoidHom.snd Plane (Factor L))
  apply tiles_invariance_iff (baseProjection L) proj (SharedCoordinates.point L o) (baseProjection_point L o) shift
  intro v
  let rs := fourValueRows k
  let cs := (List.range rs.length).map fun j =>
    (rowR rs j, if g = some j then 1 % rowR rs j else 0)
  have hc (c : ℕ × ℕ) : c ∈ cs ↔ ∃ i, (L.lowSize i,(fourValueLowVector k g i).val) = c := by
    have hmap (i : FourValueRow k) :
        (rowR rs i, if g = some i.val then 1 % rowR rs i else 0) =
          (L.lowSize i,(fourValueLowVector k g i).val) := by
      refine Prod.ext rfl ?_
      unfold fourValueLowVector
      split
      · change _ = (1 : ZMod (rowR rs i)).val
        rw [ZMod.val_one_eq_one_mod]
      · change _ = (0 : ZMod (rowR rs i)).val
        rw [ZMod.val_zero]
    simp only [cs,List.mem_map,List.mem_range]
    constructor
    · rintro ⟨i,hi,rfl⟩; exact ⟨⟨i,hi⟩,(hmap ⟨i,hi⟩).symm⟩
    · rintro ⟨i,rfl⟩; exact ⟨i.val,i.isLt,hmap i⟩
  unfold sharedInvariance
  rw [← fourValueLayout_order k]
  exact mem_decoded_invariance L (fourValueLayoutCRT k) ψ hψ _ (fourValueModuli_membership k)
    cs h (fourValueLowVector k g) hc v

abbrev FourValueBase (k : ℕ) := SharedCoordinates.Base (fourValueLayout k)
abbrev FourValueFactor (k : ℕ) := Factor (fourValueLayout k)

def fourValueLine (s : Bool) (v : Fixed) : ZMod (sharedPrime s) := by
  cases s
  · exact v.2
  · exact v.1.2

@[simp] theorem fourValueLineUseful_point (k : ℕ) (s : Bool) (o : FourValueOutputGraph k)
    (v : FourValueBase k) :
    sharedLineUseful (fourValueLayout k) s (SharedCoordinates.point (fourValueLayout k) o v).2 =
      (fourValueLine s (o.fixed v),0) := by
  cases s <;> rfl

def fourValueSeedRow (k : ℕ) (t : Fin 2) : FourValueRow k :=
  ⟨(fourValueRows k).length-2+t,by rw [fourValueRows_length]; have := t.isLt; omega⟩

structure HasFourValueDependence (k : ℕ) (slopes : List ℕ) (o : FourValueOutputGraph k) : Prop where
  low : ∀ i j : FourValueRow k, j ≠ i → ∀ v,
    o.privateOutput (v - lowStep (fourValueLayout k) j) i = o.privateOutput v i
  line : ∀ i : FourValueRow k, i.val < (fourValueRows k).length-2 → ∀ v,
    o.privateOutput (v - (((1,-(slopes.getD i 0 : ℤ)) : Plane),0)) i = o.privateOutput v i
  seedX : ∀ t : Fin 2, ∀ v,
    o.privateOutput (v - (((35,0) : Plane),0)) (fourValueSeedRow k t) =
      o.privateOutput v (fourValueSeedRow k t)
  seedY : ∀ t : Fin 2, ∀ v,
    o.privateOutput (v - (((0,35) : Plane),0)) (fourValueSeedRow k t) =
      o.privateOutput v (fourValueSeedRow k t)
  shared : ∀ s : Bool, ∀ v,
    fourValueLine s (o.fixed (v - (((1,if s then 0 else -2) : Plane),0))) =
      fourValueLine s (o.fixed v)

theorem fourValueDependence_iff (k : ℕ) (slopes : List ℕ) (o : FourValueOutputGraph k) :
    (∀ F ∈ sharedDependence (fourValueRows k) slopes,
      Tiles (F.toFinset.image (decodePoint (fourValueLayout k)))
        (Set.range (SharedCoordinates.point (fourValueLayout k) o))) ↔
      HasFourValueDependence k slopes o := by
  let rs := fourValueRows k
  let L := fourValueLayout k
  let own (i : FourValueRow k) := sharedInvariance rs (sharedObservedA rs i) (rowB rs i)
  let holds (F : CyclicTile) := Tiles (F.toFinset.image (decodePoint L))
    (Set.range (SharedCoordinates.point L o))
  have own_iff (i : FourValueRow k) (x : Plane) (g : Option ℕ) :
      holds (own i x g) ↔ ∀ v,
        o.privateOutput (v - (x,fourValueLowVector k g)) i = o.privateOutput v i :=
    fourValueInvariance_iff k (privateUseful L i) (privateUseful_decode L i) x g o
  have shared_iff (s : Bool) :
      holds (sharedInvariance rs (sharedPrime s) 1 (1,if s then 0 else -2) none) ↔
        ∀ v, fourValueLine s (o.fixed (v - (((1,if s then 0 else -2) : Plane),0))) =
          fourValueLine s (o.fixed v) := by
    change Tiles _ _ ↔ _
    rw [fourValueInvariance_iff k (sharedLineUseful L s) (sharedLineUseful_decode L s)]
    dsimp only [L]
    simp only [fourValueLineUseful_point,fourValueLowVector_none,Prod.mk.injEq,and_true]
  constructor
  · intro h
    refine ⟨?_,?_,?_,?_,?_⟩
    · intro i j hj
      simpa only [fourValueLowVector_some,lowStep] using (own_iff i 0 (some j.val)).mp
        (h _ (by
          unfold sharedDependence
          simp only [List.mem_append,List.mem_flatMap,List.mem_map,List.mem_range,
            List.mem_filter,decide_eq_true_eq]
          exact Or.inl (Or.inl (Or.inl ⟨i.val,i.isLt,j.val,
            ⟨j.isLt,fun e => hj (Fin.ext e)⟩,rfl⟩))))
    · intro i hi
      simpa only [fourValueLowVector_none] using (own_iff i (1,-(slopes.getD i 0 : ℤ)) none).mp
        (h _ (by
          unfold sharedDependence
          simp only [List.mem_append,List.mem_map,List.mem_range]
          exact Or.inl (Or.inl (Or.inr ⟨i.val,hi,rfl⟩))))
    · intro t
      simpa only [fourValueLowVector_none] using (own_iff (fourValueSeedRow k t) (35,0) none).mp
        (h _ (by
          unfold sharedDependence
          simp only [List.mem_append,List.mem_flatMap,List.mem_range]
          exact Or.inl (Or.inr ⟨t.val,t.isLt,by simp [rs,own,fourValueSeedRow]⟩)))
    · intro t
      simpa only [fourValueLowVector_none] using (own_iff (fourValueSeedRow k t) (0,35) none).mp
        (h _ (by
          unfold sharedDependence
          simp only [List.mem_append,List.mem_flatMap,List.mem_range]
          exact Or.inl (Or.inr ⟨t.val,t.isLt,by simp [rs,own,fourValueSeedRow]⟩)))
    · intro s
      exact (shared_iff s).mp (h _ (by cases s <;> simp [sharedDependence,sharedPrime,rs]))
  · intro h F hF
    change holds F
    simp only [sharedDependence,List.mem_append,List.mem_flatMap,List.mem_map,List.mem_range,
      List.mem_filter,decide_eq_true_eq] at hF
    rcases hF with (((⟨i,hi,j,⟨hj,hne⟩,rfl⟩|⟨i,hi,rfl⟩)|⟨t,ht,hh⟩)|hh)
    · exact (own_iff ⟨i,hi⟩ 0 (some j)).mpr
        (by simpa only [fourValueLowVector_some k ⟨j,hj⟩,lowStep] using
          h.low ⟨i,hi⟩ ⟨j,hj⟩ (fun e => hne (congrArg Fin.val e)))
    · let i' : FourValueRow k := ⟨i,lt_of_lt_of_le hi (Nat.sub_le _ _)⟩
      exact (own_iff i' (1,-(slopes.getD i 0 : ℤ)) none).mpr
        (by simpa only [fourValueLowVector_none] using h.line i' hi)
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hh
      rcases hh with rfl|rfl
      · exact (own_iff (fourValueSeedRow k ⟨t,ht⟩) (35,0) none).mpr
          (by simpa only [fourValueLowVector_none] using h.seedX ⟨t,ht⟩)
      · exact (own_iff (fourValueSeedRow k ⟨t,ht⟩) (0,35) none).mpr
          (by simpa only [fourValueLowVector_none] using h.seedY ⟨t,ht⟩)
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hh
      rcases hh with rfl|rfl
      · exact (shared_iff true).mpr (h.shared true)
      · exact (shared_iff false).mpr (h.shared false)

theorem HasFourValueDependence.factorLow {k slopes o} (h : HasFourValueDependence k slopes o)
    (x : Plane) (a : ∀ i : FourValueRow k, SharedCoordinates.Low (fourValueLayout k) i)
    (i : FourValueRow k) :
    o.privateOutput (x,a) i = o.privateOutput (x,Function.update 0 i (a i)) i :=
  factor_own_low (fourValueLayout k) (fun v => o.privateOutput v i) i
    (fun j hj => h.low i j hj) x a

variable {k : ℕ} {slopes : List ℕ} {o : FourValueOutputGraph k}

def fourValuePrivateAt (o : FourValueOutputGraph k) (x : Plane) (i : FourValueRow k)
    (d : SharedCoordinates.Low (fourValueLayout k) i) : ZMod ((fourValueLayout k).firstSize i) ×
      ZMod ((fourValueLayout k).secondSize i) :=
  o.privateOutput (x,Function.update 0 i d) i

theorem HasFourValueDependence.privateAt_eq (h : HasFourValueDependence k slopes o) (x : FourValueBase k)
    (i : FourValueRow k) :
    o.privateOutput x i = fourValuePrivateAt o x.1 i (x.2 i) :=
  h.factorLow x.1 x.2 i

theorem HasFourValueDependence.privateAt_line (h : HasFourValueDependence k slopes o)
    (i : FourValueRow k) (hi : i.val < (fourValueRows k).length-2) (x y : Plane)
    (hxy : x.2 + (slopes.getD i 0 : ℤ)*x.1 = y.2 + (slopes.getD i 0 : ℤ)*y.1)
    (d : SharedCoordinates.Low (fourValueLayout k) i) :
    fourValuePrivateAt o x i d = fourValuePrivateAt o y i d := by
  unfold fourValuePrivateAt
  let f := fun v : FourValueBase k => o.privateOutput v i
  rw [show o.privateOutput (x,Function.update 0 i d) i = f (x,Function.update 0 i d) from rfl]
  change f (x,Function.update 0 i d) = f (y,Function.update 0 i d)
  rw [factor_line (fourValueLayout k) f _ (h.line i hi) x,
      factor_line (fourValueLayout k) f _ (h.line i hi) y,hxy]

theorem HasFourValueDependence.sharedAt_line (h : HasFourValueDependence k slopes o)
    (s : Bool) (x y : Plane)
    (hxy : x.2 + (if s then 0 else 2)*x.1 = y.2 + (if s then 0 else 2)*y.1)
    (u : ∀ i : FourValueRow k, SharedCoordinates.Low (fourValueLayout k) i) :
    fourValueLine s (o.fixed (x,u)) = fourValueLine s (o.fixed (y,u)) := by
  let f := fun v : FourValueBase k => fourValueLine s (o.fixed v)
  let m : ℤ := if s then 0 else 2
  have hp : ∀ v, f (v - (((1,-m) : Plane),0)) = f v := by
    cases s <;> exact h.shared _
  change f (x,u) = f (y,u)
  rw [factor_line (fourValueLayout k) f m hp x,factor_line (fourValueLayout k) f m hp y,hxy]

def fourValueResidues35 (x : Plane) : ZMod 35 × ZMod 35 := (x.1,x.2)

def fourValueRep35 (s : ZMod 35 × ZMod 35) : Plane := (s.1.val,s.2.val)

theorem HasFourValueDependence.privateAt_seed (h : HasFourValueDependence k slopes o)
    (t : Fin 2) (x : Plane) (d : SharedCoordinates.Low (fourValueLayout k) (fourValueSeedRow k t)) :
    fourValuePrivateAt o x (fourValueSeedRow k t) d =
      fourValuePrivateAt o (fourValueRep35 (fourValueResidues35 x)) (fourValueSeedRow k t) d := by
  let i := fourValueSeedRow k t
  let f := fun v : FourValueBase k => o.privateOutput v i
  let u := Function.update (0 : ∀ i : FourValueRow k, SharedCoordinates.Low (fourValueLayout k) i) i d
  let a : FourValueBase k := ((35,0),0)
  let b : FourValueBase k := ((0,35),0)
  have hp (w : FourValueBase k) (hw : ∀ v, f (v-w) = f v) : Function.Periodic f w := by
    intro y
    simpa using (hw (y+w)).symm
  have h₁ := hp a (h.seedX t)
  have h₂ := hp b (h.seedY t)
  let s := fourValueResidues35 x
  obtain ⟨p,hp'⟩ := (ZMod.intCast_eq_iff 35 x.1 s.1.val).mp (by simp [s,fourValueResidues35])
  obtain ⟨q,hq'⟩ := (ZMod.intCast_eq_iff 35 x.2 s.2.val).mp (by simp [s,fourValueResidues35])
  have he : (x,u) - p • a - q • b = (fourValueRep35 s,u) := by
    apply Prod.ext
    · apply Prod.ext
      · simpa [a,b,fourValueRep35,zsmul_eq_mul,sub_eq_iff_eq_add,mul_comm] using hp'
      · simpa [a,b,fourValueRep35,zsmul_eq_mul,sub_eq_iff_eq_add,mul_comm] using hq'
    · simp [a,b]
  change f (x,u) = f (fourValueRep35 s,u)
  rw [← he,h₂.sub_zsmul_eq,h₁.sub_zsmul_eq]


end
end TranslationTiling.FiniteCompiler.Packed
