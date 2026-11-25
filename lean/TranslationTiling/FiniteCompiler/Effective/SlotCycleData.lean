import TranslationTiling.FiniteCompiler.Effective.SlotCycle
import TranslationTiling.FiniteCompiler.Effective.FourValueDigits
import TranslationTiling.FiniteCompiler.Effective.SlotObservations

namespace TranslationTiling.FiniteCompiler.Packed.SlotParameters

open SharedCoordinates
open scoped Classical
noncomputable section

variable {k m : ℕ} (s : SlotParameters k m)

abbrev RowLabel : SlotRow k m → Type
  | .inl i => FourValueLabel i
  | .inr (.inl _) => Fin 3
  | .inr (.inr _) => Unit

def Observed (i : SlotRow k m) (a : RowLabel i) : Type :=
  match i with
  | .inl j => ZMod ((fourValueLayout 0).firstSize j) × ZMod ((fourValueLayout 0).secondSize j)
  | .inr (.inl j) => ZMod (s.marker j a)
  | .inr (.inr _) => ZMod 1

instance observed_add (i : SlotRow k m) (a : RowLabel i) : AddCommGroup (s.Observed i a) := by
  rcases i with i | i | i <;> unfold Observed <;> infer_instance

instance observed_fintype (i : SlotRow k m) (a : RowLabel i) : Fintype (s.Observed i a) := by
  rcases i with i | i | i
  · unfold Observed
    infer_instance
  · haveI : NeZero (s.marker i a) := ⟨(s.prime_isPrime (.inl (i,some a))).ne_zero⟩
    exact inferInstanceAs (Fintype (ZMod (s.marker i a)))
  · exact inferInstanceAs (Fintype (ZMod 1))

instance observed_decEq (i : SlotRow k m) (a : RowLabel i) : DecidableEq (s.Observed i a) :=
  Classical.decEq _

def readForRow (i : SlotRow k m) (a : RowLabel i) : Factor s.layout →+ s.Observed i a :=
  match i with
  | .inl j => privateUseful s.layout (.inl j)
  | .inr (.inl j) => s.observeMarker j a
  | .inr (.inr _) => 0

def cycleRead (a : ∀ i : SlotRow k m, RowLabel i) : Factor s.layout →+ (∀ i, s.Observed i (a i)) :=
  AddMonoidHom.pi fun i => s.readForRow i (a i)

theorem cycleRead_target (a : ∀ i : SlotRow k m, RowLabel i) : Function.Surjective
    (fun v : SharedCoordinates.Ambient s.layout => (baseProjection s.layout v,s.cycleRead a v.2)) := by
  rintro ⟨x,y⟩
  let f (i : SlotRow k m) : ZMod (s.layout.firstSize i) × ZMod (s.layout.secondSize i) :=
    match i with
    | .inl j => y (.inl j)
    | .inr (.inl j) =>
      let b := a (.inr (.inl j))
      (0,(s.markerCRT j).symm (Function.update 0 b (y (.inr (.inl j)))))
    | .inr (.inr _) => 0
  let o : SharedCoordinates.Outputs s.layout := ⟨0,fun _ => f,0⟩
  refine ⟨SharedCoordinates.point s.layout o x,Prod.ext (baseProjection_point s.layout o x) ?_⟩
  funext i
  rcases i with i | i | i
  · rfl
  · let j := a (.inr (.inl i))
    let u : ∀ v, ZMod (s.marker i v) := Function.update 0 j (y (.inr (.inl i)))
    change s.markerRead i j ((s.markerCRT i).symm u) = y (.inr (.inl i))
    rw [← markerCRT_apply]
    exact (congrFun ((s.markerCRT i).apply_symm_apply u) j).trans (Function.update_self ..)
  · exact Subsingleton.elim (α := ZMod 1) _ _

def labelSubgroup (i : SlotRow k m) (a : RowLabel i) : AddSubgroup (SharedCoordinates.Low s.layout i) :=
  match i with
  | .inl j => fourValueDigitSubgroup j a
  | .inr (.inl _) => ⊤
  | .inr (.inr _) => ⊥

def labelStep (i : SlotRow k m) (a : RowLabel i) : s.labelSubgroup i a :=
  match i with
  | .inl j => ⟨(fourValueStep j a : SharedCoordinates.Low (fourValueLayout 0) j),fourValueStep_mem j a⟩
  | .inr (.inl _) => ⟨1,AddSubgroup.mem_top _⟩
  | .inr (.inr _) => 0

theorem labelStep_spans (i : SlotRow k m) (a : RowLabel i) (u : SharedCoordinates.Low s.layout i)
    (hu : u ∈ s.labelSubgroup i a) :
    ∃ n : ℕ, n • (s.labelStep i a : SharedCoordinates.Low s.layout i) = u := by
  rcases i with i | i | i
  · exact fourValueStep_spans i a u hu
  · change ∃ n : ℕ, n • (1 : SharedCoordinates.Low s.layout (Sum.inr (Sum.inl i))) = u
    exact ⟨u.val,by rw [nsmul_eq_mul,mul_one,ZMod.natCast_zmod_val]⟩
  · have h : u = 0 := AddSubgroup.mem_bot.mp hu
    exact ⟨0,by simp [h]⟩

section Cycle
variable [Fintype (Factor s.layout)]

def rowCycleMask {t : ℕ} [NeZero t] (cycle : ZMod t ↪ SlotRow k m)
    (a : ∀ i : SlotRow k m, RowLabel i) : Finset (SharedCoordinates.Ambient s.layout) :=
  productCycle s.layout cycle (fun j => s.labelSubgroup (cycle j) (a (cycle j)))
    (fun j => s.labelStep (cycle j) (a (cycle j))) (s.cycleRead a)

theorem rowCycleMask_vertical {t : ℕ} [NeZero t] (cycle : ZMod t ↪ SlotRow k m)
    (a : ∀ i : SlotRow k m, RowLabel i) {q : SharedCoordinates.Ambient s.layout}
    (hq : q ∈ s.rowCycleMask cycle a) : q.1 = 0 := by
  have h := @productCycle_vertical (SlotRow k m) _ s.layout _
    (fun i => s.Observed i (a i)) _ _ _ t _ cycle
    (fun j => s.labelSubgroup (cycle j) (a (cycle j)))
    (fun j => s.labelStep (cycle j) (a (cycle j))) (s.cycleRead a) q
  exact h hq

theorem rowCycleMask_iff {t : ℕ} [NeZero t] (cycle : ZMod t ↪ SlotRow k m)
    (a : ∀ i : SlotRow k m, RowLabel i)
    (o : SharedCoordinates.Outputs s.layout) (f : Plane → ∀ i, SharedCoordinates.Low s.layout i → s.Observed i (a i))
    (h : ∀ x k i, s.cycleRead a (SharedCoordinates.point s.layout o (x,k)).2 i = f x i (k i)) :
    Tiles (s.rowCycleMask cycle a) (Set.range (SharedCoordinates.point s.layout o)) ↔
      ∀ x, ∃ j, ¬ DigitActive (f x (cycle j)) (s.labelSubgroup (cycle j) (a (cycle j))) :=
  productCycle_iff s.layout cycle _ _ (fun j => s.labelStep_spans (cycle j) (a (cycle j)))
    _ (s.cycleRead_target a) o f h

/-- The mask has the graph-kernel mass even when the surrounding tests
have no common solution. The graph with zero outputs suffices here. -/
theorem rowCycleMask_satisfiable {t : ℕ} [NeZero t] (cycle : ZMod t ↪ SlotRow k m)
    (a : ∀ i : SlotRow k m, RowLabel i) :
    ∃ o : SharedCoordinates.Outputs s.layout,
      Tiles (s.rowCycleMask cycle a) (Set.range (SharedCoordinates.point s.layout o)) := by
  let o : SharedCoordinates.Outputs s.layout := ⟨0,0,0⟩
  refine ⟨o,(s.rowCycleMask_iff cycle a o (fun _ _ _ => 0) ?_).mpr ?_⟩
  · intro x v i
    rcases i with i | i | i
    · rfl
    · change s.markerRead i (a (.inr (.inl i))) 0 = 0
      exact map_zero _
    · rfl
  · intro x
    exact ⟨0,fun ⟨_,_,_,hn⟩ => hn rfl⟩

end Cycle
end
end TranslationTiling.FiniteCompiler.Packed.SlotParameters
