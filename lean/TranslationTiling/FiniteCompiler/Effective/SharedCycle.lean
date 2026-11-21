import TranslationTiling.FiniteCompiler.Effective.SharedKernel
import TranslationTiling.FiniteCompiler.FixedCycleTests

namespace TranslationTiling.FiniteCompiler.SharedCoordinates

open Compiler.Effective
open TranslationTiling.FiniteCompiler.Effective
open scoped Classical

noncomputable section

variable {I : Type*} [Fintype I] (L : Layout I)

abbrev Useful (i : I) := ZMod (L.firstSize i) × ZMod (L.secondSize i)

def usefulProjection : Ambient L →+ (∀ i, Useful L i) where
  toFun v := fun i => privateUseful L i v.2
  map_zero' := rfl
  map_add' _ _ := rfl

omit [Fintype I] in
@[simp] theorem usefulProjection_point (o : Outputs L) (x : Base L) :
    usefulProjection L (point L o x) = o.privateOutput x := rfl

omit [Fintype I] in
theorem base_useful_surjective :
    Function.Surjective (fun v : Ambient L => (baseProjection L v, usefulProjection L v)) := by
  rintro ⟨x,y⟩
  let o : Outputs L := ⟨fun _ => 0,fun _ => y,fun _ _ => 0⟩
  exact ⟨point L o x, Prod.ext (baseProjection_point L o x) rfl⟩

/-- A row with a predecessor changes its low coordinate when that
predecessor's private useful output is nonzero. -/
def cycleOffset (predecessor : I → Option I) (step : I → ℕ)
    (e : ∀ i, Useful L i) : ∀ i, Low L i :=
  fun i => match predecessor i with
    | none => 0
    | some j => if e j = 0 then 0 else (step i : Low L i)

def privateCycleRow (predecessor : I → Option I) (step : I → ℕ) (i : I) : CycleRow :=
  match predecessor i with
  | none => (L.lowSize i,1,1,[0])
  | some j => (L.lowSize i,L.firstSize j,L.secondSize j,
      triggerTable (L.firstSize j) (L.secondSize j) (step i))

variable [∀ i, NeZero (L.firstSize i)] [∀ i, NeZero (L.secondSize i)]

private theorem privateCycleRow_test (predecessor : I → Option I) (step : I → ℕ) (i : I) (n : ℕ) :
    CycleRowTest (privateCycleRow L predecessor step i) n ↔
      (n : Low L i) = cycleOffset L predecessor step (fun j => privateUseful L j (decode L n)) i := by
  cases h : predecessor i with
  | none =>
    rw [privateCycleRow, h, cycleRowTest_zero]
    simp [cycleOffset,h,ZMod.natCast_eq_zero_iff,Nat.dvd_iff_mod_eq_zero]
  | some j =>
    let e : Useful L j := ((n : ZMod (L.firstSize j)),(n : ZMod (L.secondSize j)))
    have hv := triggerTable_apply (step i) e
    simp only [privateCycleRow, cycleOffset, h, privateUseful_decode, CycleRowTest,
      ← (ZMod.val_injective (L.lowSize i)).eq_iff, ZMod.val_natCast]
    simp only [e, ZMod.val_natCast] at hv
    rw [hv]
    by_cases hz : ((n : ZMod (L.firstSize j)),(n : ZMod (L.secondSize j))) = 0
    · simp [hz]
    · simp [hz]

/-- The raw cycle rows tile a graph exactly when their offset permutations
are bijections. Shared coordinates are free in this test. -/
theorem tiles_private_cycle_iff [NeZero (order L)] (crt : ZMod (order L) ≃+* Factor L)
    (predecessor : I → Option I) (step : I → ℕ) (rows : List CycleRow)
    (hrows : ∀ y, y ∈ rows ↔ ∃ i, privateCycleRow L predecessor step i = y)
    (o : Outputs L) :
    Tiles ((cycleCodes (order L) rows).toFinset.image (decodePoint L)) (Set.range (point L o)) ↔
      ∀ (x : Plane) (k : ∀ i, Low L i), Function.Bijective
        (fun e => e + o.privateOutput (x,k - cycleOffset L predecessor step e)) := by
  have hf (v : Ambient L) :
      v ∈ (cycleCodes (order L) rows).toFinset.image (decodePoint L) ↔
      baseProjection L v = (0,cycleOffset L predecessor step (usefulProjection L v)) := by
    unfold cycleCodes
    rw [decoded_range_filter_iff L crt _ _
      (fun f => ∀ i, CyclicShear.low (L.lowSize i) (f.2 i).1.1 =
        cycleOffset L predecessor step (fun j => privateUseful L j f) i) (fun n => ?_)]
    · constructor
      · rintro ⟨hh,hk⟩
        exact Prod.ext hh (funext hk)
      · intro h
        exact ⟨congrArg Prod.fst h,fun i => congrFun (congrArg Prod.snd h) i⟩
    · simp only [decide_eq_true_eq, CycleTest, hrows, forall_exists_index, forall_apply_eq_imp_iff]
      simp only [privateCycleRow_test, CyclicShear.low_natCast, decode]
  rw [tiles_offset_iff_permutation (baseProjection L) (usefulProjection L) (point L o)
    (baseProjection_point L o) (base_useful_surjective L)
    (fun e => ((0 : Plane),cycleOffset L predecessor step e)) _ hf]
  constructor
  · intro h x k
    simpa only [Prod.mk_sub_mk,sub_zero,usefulProjection_point] using h (x,k)
  · rintro h ⟨x,k⟩
    simpa only [Prod.mk_sub_mk,sub_zero,usefulProjection_point] using h x k

theorem tiles_private_cycle_exclusion_iff [NeZero (order L)]
    (crt : ZMod (order L) ≃+* Factor L)
    {t : ℕ} [NeZero t] (cycle : ZMod t ↪ I)
    (U : ∀ j, AddSubgroup (Low L (cycle j)))
    (step : ∀ j, U j) (hspan : ∀ j u, u ∈ U j →
      ∃ d : ℕ, d • (step j : Low L (cycle j)) = u)
    (pred : I → Option I) (stepCode : I → ℕ)
    (hon : ∀ j, pred (cycle j) = some (cycle (j-1)))
    (hoff : ∀ i, (∀ j, cycle j ≠ i) → pred i = none)
    (hstep : ∀ j, (stepCode (cycle j) : Low L (cycle j)) = step j)
    (rows : List CycleRow) (hrows : ∀ y, y ∈ rows ↔ ∃ i, privateCycleRow L pred stepCode i = y)
    (o : Outputs L) (g : Plane → ∀ i, Low L i → Useful L i)
    (hlocal : ∀ x k i, o.privateOutput (x,k) i = g x i (k i)) :
    Tiles ((cycleCodes (order L) rows).toFinset.image (decodePoint L)) (Set.range (point L o)) ↔
      ∀ x, ∃ j, ¬ DigitActive (g x (cycle j)) (U j) := by
  let d : ∀ j, Useful L (cycle (j-1)) → U j := cycleGeneratorMaps cycle U step
  have hd (e : ∀ i, Useful L i) :
      cycleOffset L pred stepCode e = cycleShift cycle U d e := by
    funext i
    by_cases hi : ∃ j, cycle j = i
    · obtain ⟨j,rfl⟩ := hi
      simp only [cycleOffset,hon,cycleShift_apply,d,cycleGeneratorMaps]
      split <;> simp_all
    · have he : ∀ j, cycle j ≠ i := by simpa only [not_exists] using hi
      rw [cycleShift_eq_zero cycle U d e he]
      simp [cycleOffset,hoff i he]
  have hm (x : Plane) (k : ∀ i, Low L i) :
      (fun e => e + o.privateOutput (x,k-cycleOffset L pred stepCode e)) =
        cycleMap cycle U d (g x) k := by
    funext e i
    simp only [Pi.add_apply,hlocal,hd,cycleMap,Pi.sub_apply]
  rw [tiles_private_cycle_iff L crt pred stepCode rows hrows o]
  constructor
  · intro h x
    apply (cycleMap_generator_bijective_iff cycle U step hspan (g x)).mp
    intro k
    rw [← hm x k]
    exact h x k
  · intro h x k
    rw [hm x k]
    exact (cycleMap_generator_bijective_iff cycle U step hspan (g x)).mpr (h x) k

end

end TranslationTiling.FiniteCompiler.SharedCoordinates
