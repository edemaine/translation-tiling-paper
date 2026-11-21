import TranslationTiling.FiniteCompiler.Effective.ConcreteSharedCRT
import TranslationTiling.FiniteCompiler.Effective.SharedKernel
import TranslationTiling.FiniteCompiler.SharedDependence

namespace TranslationTiling.FiniteCompiler.Packed

open Compiler Compiler.Effective Effective SharedCoordinates
open scoped Classical

noncomputable section

instance (k : ℕ) : NeZero (order (sharedLayout k)) := by
  rw [sharedLayout_order]
  infer_instance

def sharedLayoutCRT (k : ℕ) : ZMod (order (sharedLayout k)) ≃+* Factor (sharedLayout k) := by
  rw [sharedLayout_order]
  exact sharedRowsCRT k

abbrev SharedRow (k : ℕ) := Fin (sharedRows k).length

theorem sharedModuli_membership (k r : ℕ) :
    r ∈ guardedModuli (sharedRows k) ↔ ∃ i : SharedRow k, (sharedLayout k).lowSize i = r := by
  simp only [guardedModuli,List.mem_map,List.mem_range,sharedLayout]
  constructor
  · rintro ⟨i,hi,rfl⟩; exact ⟨⟨i,hi⟩,rfl⟩
  · rintro ⟨i,rfl⟩; exact ⟨i.val,i.isLt,rfl⟩

theorem sharedOther_membership (k : ℕ) (i : SharedRow k) (r : ℕ) :
    r ∈ guardedOther (sharedRows k) i ↔
      ∃ j : SharedRow k, j ≠ i ∧ (sharedLayout k).lowSize j = r := by
  simp only [guardedOther,List.mem_map,List.mem_filter,List.mem_range,decide_eq_true_eq,sharedLayout]
  constructor
  · rintro ⟨j,⟨hj,hne⟩,rfl⟩; exact ⟨⟨j,hj⟩,fun h => hne (congrArg Fin.val h),rfl⟩
  · rintro ⟨j,hne,rfl⟩; exact ⟨j.val,⟨j.isLt,fun h => hne (Fin.ext h)⟩,rfl⟩

def lowVector (k : ℕ) (g : Option ℕ) : ∀ i, SharedCoordinates.Low (sharedLayout k) i :=
  fun i => if g = some i.val then 1 else 0

@[simp] theorem lowVector_none (k : ℕ) : lowVector k none = 0 := by
  funext i
  simp [lowVector]

@[simp] theorem lowVector_some (k : ℕ) (i : SharedRow k) :
    lowVector k (some i.val) =
      Function.update (0 : ∀ j : SharedRow k, SharedCoordinates.Low (sharedLayout k) j) i 1 := by
  funext j
  by_cases h : j = i
  · subst j; simp [lowVector]
  · simp [lowVector,h,show i.val ≠ j.val from fun e => h (Fin.ext e.symm)]

/-- The numerical dependence mask tests invariance for whichever useful
projection its two moduli specify. -/
theorem sharedInvariance_iff (k : ℕ) {a b : ℕ}
    (ψ : Factor (sharedLayout k) →+ ZMod a × ZMod b)
    (hψ : ∀ n : ℕ, ψ (decode (sharedLayout k) n) = ((n : ZMod a),(n : ZMod b)))
    (h : Plane) (g : Option ℕ) (o : SharedCoordinates.Outputs (sharedLayout k)) :
    Tiles ((sharedInvariance (sharedRows k) a b h g).toFinset.image (decodePoint (sharedLayout k)))
        (Set.range (SharedCoordinates.point (sharedLayout k) o)) ↔
    ∀ p : SharedCoordinates.Base (sharedLayout k), ψ (SharedCoordinates.point (sharedLayout k) o (p - (h,lowVector k g))).2 =
      ψ (SharedCoordinates.point (sharedLayout k) o p).2 := by
  let L := sharedLayout k
  let shift := (h,lowVector k g)
  let proj := ψ.comp (AddMonoidHom.snd Plane (Factor L))
  apply tiles_invariance_iff (baseProjection L) proj (SharedCoordinates.point L o) (baseProjection_point L o) shift
  intro v
  let rs := sharedRows k
  let cs := (List.range rs.length).map fun j =>
    (rowR rs j, if g = some j then 1 % rowR rs j else 0)
  have hc (c : ℕ × ℕ) : c ∈ cs ↔ ∃ i, (L.lowSize i,(lowVector k g i).val) = c := by
    have hmap (i : SharedRow k) :
        (rowR rs i, if g = some i.val then 1 % rowR rs i else 0) =
          (L.lowSize i,(lowVector k g i).val) := by
      refine Prod.ext rfl ?_
      unfold lowVector
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
  rw [← sharedLayout_order k]
  exact mem_decoded_invariance L (sharedLayoutCRT k) ψ hψ _ (sharedModuli_membership k)
    cs h (lowVector k g) hc v

abbrev SharedOutput (k : ℕ) := SharedCoordinates.Outputs (sharedLayout k)
abbrev SharedBase (k : ℕ) := SharedCoordinates.Base (sharedLayout k)
abbrev SharedFactor (k : ℕ) := Factor (sharedLayout k)

def sharedLine (s : Bool) (v : Fixed) : ZMod (sharedPrime s) := by
  cases s
  · exact v.2
  · exact v.1.2

@[simp] theorem sharedLineUseful_point (k : ℕ) (s : Bool) (o : SharedOutput k)
    (v : SharedBase k) :
    sharedLineUseful (sharedLayout k) s (SharedCoordinates.point (sharedLayout k) o v).2 =
      (sharedLine s (o.fixed v),0) := by
  cases s <;> rfl

def sharedSeedRow (k : ℕ) (t : Fin 2) : SharedRow k :=
  ⟨(sharedRows k).length-2+t,by rw [sharedRows_length]; have := t.isLt; omega⟩

structure HasSharedDependence (k : ℕ) (slopes : List ℕ) (o : SharedOutput k) : Prop where
  low : ∀ i j : SharedRow k, j ≠ i → ∀ v,
    o.privateOutput (v - lowStep (sharedLayout k) j) i = o.privateOutput v i
  line : ∀ i : SharedRow k, i.val < (sharedRows k).length-2 → ∀ v,
    o.privateOutput (v - (((1,-(slopes.getD i 0 : ℤ)) : Plane),0)) i = o.privateOutput v i
  seedX : ∀ t : Fin 2, ∀ v,
    o.privateOutput (v - (((35,0) : Plane),0)) (sharedSeedRow k t) =
      o.privateOutput v (sharedSeedRow k t)
  seedY : ∀ t : Fin 2, ∀ v,
    o.privateOutput (v - (((0,35) : Plane),0)) (sharedSeedRow k t) =
      o.privateOutput v (sharedSeedRow k t)
  shared : ∀ s : Bool, ∀ v,
    sharedLine s (o.fixed (v - (((1,if s then 0 else -2) : Plane),0))) =
      sharedLine s (o.fixed v)

theorem sharedDependence_iff (k : ℕ) (slopes : List ℕ) (o : SharedOutput k) :
    (∀ F ∈ sharedDependence (sharedRows k) slopes,
      Tiles (F.toFinset.image (decodePoint (sharedLayout k)))
        (Set.range (SharedCoordinates.point (sharedLayout k) o))) ↔
      HasSharedDependence k slopes o := by
  let rs := sharedRows k
  let L := sharedLayout k
  let own (i : SharedRow k) := sharedInvariance rs (sharedObservedA rs i) (rowB rs i)
  let holds (F : CyclicTile) := Tiles (F.toFinset.image (decodePoint L))
    (Set.range (SharedCoordinates.point L o))
  have own_iff (i : SharedRow k) (x : Plane) (g : Option ℕ) :
      holds (own i x g) ↔ ∀ v,
        o.privateOutput (v - (x,lowVector k g)) i = o.privateOutput v i :=
    sharedInvariance_iff k (privateUseful L i) (privateUseful_decode L i) x g o
  have shared_iff (s : Bool) :
      holds (sharedInvariance rs (sharedPrime s) 1 (1,if s then 0 else -2) none) ↔
        ∀ v, sharedLine s (o.fixed (v - (((1,if s then 0 else -2) : Plane),0))) =
          sharedLine s (o.fixed v) := by
    change Tiles _ _ ↔ _
    rw [sharedInvariance_iff k (sharedLineUseful L s) (sharedLineUseful_decode L s)]
    dsimp only [L]
    simp only [sharedLineUseful_point,lowVector_none,Prod.mk.injEq,and_true]
  constructor
  · intro h
    refine ⟨?_,?_,?_,?_,?_⟩
    · intro i j hj
      simpa only [lowVector_some,lowStep] using (own_iff i 0 (some j.val)).mp
        (h _ (by
          unfold sharedDependence
          simp only [List.mem_append,List.mem_flatMap,List.mem_map,List.mem_range,
            List.mem_filter,decide_eq_true_eq]
          exact Or.inl (Or.inl (Or.inl ⟨i.val,i.isLt,j.val,
            ⟨j.isLt,fun e => hj (Fin.ext e)⟩,rfl⟩))))
    · intro i hi
      simpa only [lowVector_none] using (own_iff i (1,-(slopes.getD i 0 : ℤ)) none).mp
        (h _ (by
          unfold sharedDependence
          simp only [List.mem_append,List.mem_map,List.mem_range]
          exact Or.inl (Or.inl (Or.inr ⟨i.val,hi,rfl⟩))))
    · intro t
      simpa only [lowVector_none] using (own_iff (sharedSeedRow k t) (35,0) none).mp
        (h _ (by
          unfold sharedDependence
          simp only [List.mem_append,List.mem_flatMap,List.mem_range]
          exact Or.inl (Or.inr ⟨t.val,t.isLt,by simp [rs,own,sharedSeedRow]⟩)))
    · intro t
      simpa only [lowVector_none] using (own_iff (sharedSeedRow k t) (0,35) none).mp
        (h _ (by
          unfold sharedDependence
          simp only [List.mem_append,List.mem_flatMap,List.mem_range]
          exact Or.inl (Or.inr ⟨t.val,t.isLt,by simp [rs,own,sharedSeedRow]⟩)))
    · intro s
      exact (shared_iff s).mp (h _ (by cases s <;> simp [sharedDependence,sharedPrime,rs]))
  · intro h F hF
    change holds F
    simp only [sharedDependence,List.mem_append,List.mem_flatMap,List.mem_map,List.mem_range,
      List.mem_filter,decide_eq_true_eq] at hF
    rcases hF with (((⟨i,hi,j,⟨hj,hne⟩,rfl⟩|⟨i,hi,rfl⟩)|⟨t,ht,hh⟩)|hh)
    · exact (own_iff ⟨i,hi⟩ 0 (some j)).mpr
        (by simpa only [lowVector_some k ⟨j,hj⟩,lowStep] using
          h.low ⟨i,hi⟩ ⟨j,hj⟩ (fun e => hne (congrArg Fin.val e)))
    · let i' : SharedRow k := ⟨i,lt_of_lt_of_le hi (Nat.sub_le _ _)⟩
      exact (own_iff i' (1,-(slopes.getD i 0 : ℤ)) none).mpr
        (by simpa only [lowVector_none] using h.line i' hi)
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hh
      rcases hh with rfl|rfl
      · exact (own_iff (sharedSeedRow k ⟨t,ht⟩) (35,0) none).mpr
          (by simpa only [lowVector_none] using h.seedX ⟨t,ht⟩)
      · exact (own_iff (sharedSeedRow k ⟨t,ht⟩) (0,35) none).mpr
          (by simpa only [lowVector_none] using h.seedY ⟨t,ht⟩)
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hh
      rcases hh with rfl|rfl
      · exact (shared_iff true).mpr (h.shared true)
      · exact (shared_iff false).mpr (h.shared false)

theorem HasSharedDependence.factorLow {k slopes o} (h : HasSharedDependence k slopes o)
    (x : Plane) (a : ∀ i : SharedRow k, SharedCoordinates.Low (sharedLayout k) i)
    (i : SharedRow k) :
    o.privateOutput (x,a) i = o.privateOutput (x,Function.update 0 i (a i)) i :=
  factor_own_low (sharedLayout k) (fun v => o.privateOutput v i) i
    (fun j hj => h.low i j hj) x a

end
end TranslationTiling.FiniteCompiler.Packed
