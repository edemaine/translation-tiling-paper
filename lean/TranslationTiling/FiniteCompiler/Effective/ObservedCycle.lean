import TranslationTiling.FiniteCompiler.Effective.SharedCycle

namespace TranslationTiling.FiniteCompiler.SharedCoordinates

open Compiler.Effective
open TranslationTiling.FiniteCompiler.Effective
open scoped Classical

noncomputable section

variable {I : Type*} [Fintype I] (L : Layout I)

variable (a b : I → ℕ)
  (observe : Factor L →+ (∀ i, ZMod (a i) × ZMod (b i)))
  (hdecode : ∀ n i, observe (decode L n) i = ((n : ZMod (a i)),(n : ZMod (b i))))

abbrev Observed (i : I) := ZMod (a i) × ZMod (b i)

def observedCycleOffset (predecessor : I → Option I) (step : I → ℕ)
    (e : ∀ i, Observed a b i) : ∀ i, Low L i :=
  fun i => match predecessor i with
    | none => 0
    | some j => if e j = 0 then 0 else (step i : Low L i)

def observedCycleRow (predecessor : I → Option I) (step : I → ℕ) (i : I) : CycleRow :=
  match predecessor i with
  | none => (L.lowSize i,1,1,[0])
  | some j => (L.lowSize i,a j,b j,
      triggerTable (a j) (b j) (step i))

variable [∀ i, NeZero (a i)] [∀ i, NeZero (b i)]

omit [Fintype I] in
include hdecode in
private theorem observedCycleRow_test (predecessor : I → Option I) (step : I → ℕ) (i : I) (n : ℕ) :
    CycleRowTest (observedCycleRow L a b predecessor step i) n ↔
      (n : Low L i) = observedCycleOffset L a b predecessor step (observe (decode L n)) i := by
  cases h : predecessor i with
  | none =>
    rw [observedCycleRow, h, cycleRowTest_zero]
    simp [observedCycleOffset,h,ZMod.natCast_eq_zero_iff,Nat.dvd_iff_mod_eq_zero]
  | some j =>
    let e : Observed a b j := ((n : ZMod (a j)),(n : ZMod (b j)))
    have hv := triggerTable_apply (step i) e
    simp only [observedCycleRow, observedCycleOffset, h, hdecode, CycleRowTest,
      ← (ZMod.val_injective (L.lowSize i)).eq_iff, ZMod.val_natCast]
    simp only [e, ZMod.val_natCast] at hv
    rw [hv]
    by_cases hz : ((n : ZMod (a j)),(n : ZMod (b j))) = 0
    · simp [hz]
    · simp [hz]

include hdecode in
/-- The raw cycle rows tile a graph exactly when their offset permutations
are bijections on the selected output coordinates. -/
theorem tiles_observed_cycle_iff [NeZero (order L)] (crt : ZMod (order L) ≃+* Factor L)
    (predecessor : I → Option I) (step : I → ℕ) (rows : List CycleRow)
    (hrows : ∀ y, y ∈ rows ↔ ∃ i, observedCycleRow L a b predecessor step i = y)
    (hsurj : Function.Surjective (fun v : Ambient L => (baseProjection L v, observe v.2)))
    (o : Outputs L) :
    Tiles ((cycleCodes (order L) rows).toFinset.image (decodePoint L)) (Set.range (point L o)) ↔
      ∀ (x : Plane) (k : ∀ i, Low L i), Function.Bijective
        (fun e => e + observe (point L o (x,k - observedCycleOffset L a b predecessor step e)).2) := by
  have hf (v : Ambient L) :
      v ∈ (cycleCodes (order L) rows).toFinset.image (decodePoint L) ↔
      baseProjection L v = (0,observedCycleOffset L a b predecessor step (observe v.2)) := by
    unfold cycleCodes
    rw [decoded_range_filter_iff L crt _ _
      (fun f => ∀ i, CyclicShear.low (L.lowSize i) (f.2 i).1.1 =
        observedCycleOffset L a b predecessor step (observe f) i) (fun n => ?_)]
    · constructor
      · rintro ⟨hh,hk⟩
        exact Prod.ext hh (funext hk)
      · intro h
        exact ⟨congrArg Prod.fst h,fun i => congrFun (congrArg Prod.snd h) i⟩
    · simp only [decide_eq_true_eq, CycleTest, hrows, forall_exists_index, forall_apply_eq_imp_iff]
      have hl (i : I) : CyclicShear.low (L.lowSize i) ((decode L n).2 i).1.1 =
          (n : Low L i) := CyclicShear.low_natCast _ _
      simp only [observedCycleRow_test L a b observe hdecode, hl]
  rw [tiles_offset_iff_permutation (baseProjection L) (observe.comp (AddMonoidHom.snd _ _)) (point L o)
    (baseProjection_point L o) (hsurj)
    (fun e => ((0 : Plane),observedCycleOffset L a b predecessor step e)) _ hf]
  have hsnd (v : Ambient L) : (AddMonoidHom.snd Plane (Factor L)) v = v.2 := rfl
  constructor
  · intro h x k
    simpa only [Prod.mk_sub_mk,sub_zero,AddMonoidHom.comp_apply,hsnd] using h (x,k)
  · rintro h ⟨x,k⟩
    simpa only [Prod.mk_sub_mk,sub_zero,AddMonoidHom.comp_apply,hsnd] using h x k

include hdecode in
theorem tiles_observed_cycle_exclusion_iff [NeZero (order L)]
    (crt : ZMod (order L) ≃+* Factor L)
    {t : ℕ} [NeZero t] (cycle : ZMod t ↪ I)
    (U : ∀ j, AddSubgroup (Low L (cycle j)))
    (step : ∀ j, U j) (hspan : ∀ j u, u ∈ U j →
      ∃ d : ℕ, d • (step j : Low L (cycle j)) = u)
    (pred : I → Option I) (stepCode : I → ℕ)
    (hon : ∀ j, pred (cycle j) = some (cycle (j-1)))
    (hoff : ∀ i, (∀ j, cycle j ≠ i) → pred i = none)
    (hstep : ∀ j, (stepCode (cycle j) : Low L (cycle j)) = step j)
    (rows : List CycleRow) (hrows : ∀ y, y ∈ rows ↔ ∃ i, observedCycleRow L a b pred stepCode i = y)
    (hsurj : Function.Surjective (fun v : Ambient L => (baseProjection L v, observe v.2)))
    (o : Outputs L) (g : Plane → ∀ i, Low L i → Observed a b i)
    (hlocal : ∀ x k i, observe (point L o (x,k)).2 i = g x i (k i)) :
    Tiles ((cycleCodes (order L) rows).toFinset.image (decodePoint L)) (Set.range (point L o)) ↔
      ∀ x, ∃ j, ¬ DigitActive (g x (cycle j)) (U j) := by
  let d : ∀ j, Observed a b (cycle (j-1)) → U j := cycleGeneratorMaps cycle U step
  have hd (e : ∀ i, Observed a b i) :
      observedCycleOffset L a b pred stepCode e = cycleShift cycle U d e := by
    funext i
    by_cases hi : ∃ j, cycle j = i
    · obtain ⟨j,rfl⟩ := hi
      simp only [observedCycleOffset,hon,cycleShift_apply,d,cycleGeneratorMaps]
      split <;> simp_all
    · have he : ∀ j, cycle j ≠ i := by simpa only [not_exists] using hi
      rw [cycleShift_eq_zero cycle U d e he]
      simp [observedCycleOffset,hoff i he]
  have hm (x : Plane) (k : ∀ i, Low L i) :
      (fun e => e + observe (point L o (x,k-observedCycleOffset L a b pred stepCode e)).2) =
        cycleMap cycle U d (g x) k := by
    funext e i
    simp only [Pi.add_apply,hlocal,hd,cycleMap,Pi.sub_apply]
  rw [tiles_observed_cycle_iff L a b observe hdecode crt pred stepCode rows hrows hsurj o]
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
