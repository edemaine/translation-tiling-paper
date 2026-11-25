import TranslationTiling.FiniteCompiler.Effective.SlotCRT
import TranslationTiling.FiniteCompiler.SlotActivation

namespace TranslationTiling.FiniteCompiler.Packed

open SharedCoordinates
open scoped Classical BigOperators

noncomputable section

namespace SlotParameters

variable {k m : ℕ} (s : SlotParameters k m)

/-- The observation of a slot keeps any one of its three private outputs.
The other two can be filled freely during a word test. -/
def markerRead (i : WangSlot k m) (j : Fin 3) :
    ZMod (s.layout.secondSize (.inr (.inl i))) →+ ZMod (s.marker i j) :=
  (ZMod.castHom (Finset.dvd_prod_of_mem (s.marker i) (Finset.mem_univ j))
    (ZMod (s.marker i j))).toAddMonoidHom

def markerCRT (i : WangSlot k m) :
    ZMod (s.layout.secondSize (.inr (.inl i))) ≃+* (∀ j, ZMod (s.marker i j)) := by
  change ZMod (∏ j, s.marker i j) ≃+* (∀ j, ZMod (s.marker i j))
  refine ZMod.prodEquivPi _ ?_
  intro a b hab
  apply (Nat.coprime_primes (s.prime_isPrime (.inl (i,some a)))
    (s.prime_isPrime (.inl (i,some b)))).mpr
  intro h
  have ht := Prod.mk.inj (Sum.inl.inj (s.prime_injective h))
  exact hab (Option.some.inj ht.2)

@[simp] theorem markerCRT_apply (i : WangSlot k m)
    (v : ZMod (s.layout.secondSize (.inr (.inl i)))) (j : Fin 3) :
    s.markerCRT i v j = s.markerRead i j v := by
  unfold markerCRT markerRead
  exact ZMod.prodEquivPi_apply _ _ _ _

def observeMarker (i : WangSlot k m) (j : Fin 3) :
    Factor s.layout →+ ZMod (s.marker i j) :=
  (s.markerRead i j).comp ((AddMonoidHom.snd ..).comp (privateUseful s.layout (.inr (.inl i))))

def observeFallback (i : SlotFallback m) :
    Factor s.layout →+ ZMod (s.fallback i) :=
  (AddMonoidHom.snd ..).comp (privateUseful s.layout (.inr (.inr i)))

abbrev SlotIndex (S : Finset (Fin m)) := {i : Fin m // i ∈ S} × Option (Fin 3)

def observationPrime (slope : Bool) (digit : Fin k) {S : Finset (Fin m)}
    (i : SlotIndex S) : ℕ :=
  match i.2 with
  | none => s.fallback (slope,i.1,false)
  | some label => s.marker (slope,digit,i.1) label

def observe (slope : Bool) (digit : Fin k) {S : Finset (Fin m)} (i : SlotIndex S) :
    Factor s.layout →+ ZMod (s.observationPrime slope digit i) :=
  match i with
  | (i,none) => s.observeFallback (slope,i,false)
  | (i,some label) => s.observeMarker (slope,digit,i) label

private theorem extendDependent {A B : Type*} [Fintype A] (e : A ↪ B) {D : B → Type*}
    [∀ i, Zero (D i)] (v : ∀ i, D (e i)) :
    ∃ f : ∀ i, D i, ∀ i, f (e i) = v i := by
  have h (S : Finset A) : ∃ f : ∀ i, D i, ∀ i ∈ S, f (e i) = v i := by
    induction S using Finset.induction_on with
    | empty => exact ⟨0,by simp⟩
    | @insert a S ha ih =>
      obtain ⟨f,hf⟩ := ih
      refine ⟨Function.update f (e a) (v a),fun i hi => ?_⟩
      rcases Finset.mem_insert.mp hi with rfl|hi
      · exact Function.update_self _ _ _
      · have hne : e i ≠ e a := fun he => ha (e.injective he ▸ hi)
        rw [Function.update_of_ne hne,hf i hi]
  obtain ⟨f,hf⟩ := h Finset.univ
  exact ⟨f,fun i => hf i (Finset.mem_univ i)⟩

private def observedRow (slope : Bool) (digit : Fin k) (S : Finset (Fin m)) :
    ({i : Fin m // i ∈ S} × Bool) ↪ SlotRow k m where
  toFun
    | (i,false) => .inr (.inr (slope,i,false))
    | (i,true) => .inr (.inl (slope,digit,i))
  inj' := by
    rintro ⟨i,_ | _⟩ ⟨j,_ | _⟩ h
    · have hp := Sum.inr.inj (Sum.inr.inj h)
      exact Prod.ext (Subtype.ext (congrArg (fun x : SlotFallback m => x.2.1) hp)) rfl
    · exact (Sum.inr_ne_inl (Sum.inr.inj h)).elim
    · exact (Sum.inl_ne_inr (Sum.inr.inj h)).elim
    · have hp := Sum.inl.inj (Sum.inr.inj h)
      exact Prod.ext (Subtype.ext (congrArg (fun x : WangSlot k m => x.2.2) hp)) rfl

/-- The two kinds of observations can be prescribed independently of the
base input and all of the high coordinates. -/
theorem observe_target (slope : Bool) (digit : Fin k) (S : Finset (Fin m))
    (x : SharedCoordinates.Base s.layout) (high : ∀ i, SharedCoordinates.Low s.layout i)
    (u : ∀ i : SlotIndex S, ZMod (s.observationPrime slope digit i)) :
    ∃ v : SharedCoordinates.Ambient s.layout, baseProjection s.layout v = x ∧
      (∀ i : SlotIndex S, s.observe slope digit i v.2 = u i) ∧
      ∀ i, highCoordinate s.layout i v = high i := by
  let e := observedRow slope digit S
  let useful (v : {i : Fin m // i ∈ S} × Bool) :
      ZMod (s.layout.firstSize (e v)) × ZMod (s.layout.secondSize (e v)) :=
    match v with
    | (i,false) => (0,u (i,none))
    | (i,true) => (0,(s.markerCRT (slope,digit,i)).symm (fun j => u (i,some j)))
  obtain ⟨f,hf⟩ := extendDependent e
    (D := fun i => ZMod (s.layout.firstSize i) × ZMod (s.layout.secondSize i)) useful
  let o : SharedCoordinates.Outputs s.layout := ⟨fun _ => 0,fun _ => f,fun _ => high⟩
  refine ⟨SharedCoordinates.point s.layout o x,baseProjection_point s.layout o x,fun j => ?_,
    fun i => highCoordinate_point s.layout i o x⟩
  rcases j with ⟨i,_ | j⟩
  · have h := congrArg Prod.snd (hf (i,false))
    exact h
  · have h := congrArg Prod.snd (hf (i,true))
    change s.markerRead (slope,digit,i) j (f (.inr (.inl (slope,digit,i)))).2 = _
    change (f (.inr (.inl (slope,digit,i)))).2 =
      (s.markerCRT (slope,digit,i)).symm (fun j => u (i,some j)) at h
    rw [h,← markerCRT_apply]
    exact congrFun ((s.markerCRT (slope,digit,i)).apply_symm_apply (fun j => u (i,some j))) j

end SlotParameters

end

end TranslationTiling.FiniteCompiler.Packed
