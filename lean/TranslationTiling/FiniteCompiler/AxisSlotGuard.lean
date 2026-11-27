import TranslationTiling.FiniteCompiler.Effective.SlotCycle

/-! A slot with a product low coordinate and shared marker outputs. A guard
can read any one marker along any one axis of that slot. -/

namespace TranslationTiling.FiniteCompiler.AxisSlot

open SharedCoordinates
open scoped Classical

noncomputable section

variable {p q : ℕ}

abbrev Label := Bool × Fin 3

/-- The first axis is selected by `false`. -/
def axis (p q : ℕ) (a : Bool) := if a then q else p

variable (hpq : p.Coprime q)

def axisEmbed (a : Bool) : ZMod (axis p q a) →+ ZMod (p*q) :=
  (ZMod.chineseRemainder hpq).symm.toAddMonoidHom.comp (by
    cases a
    · exact AddMonoidHom.inl _ _
    · exact AddMonoidHom.inr _ _)

def axisSubgroup (a : Bool) : AddSubgroup (ZMod (p*q)) :=
  (axisEmbed hpq a).range

def axisGenerator (a : Bool) : axisSubgroup hpq a :=
  ⟨axisEmbed hpq a 1, ⟨1,rfl⟩⟩

theorem axisGenerator_spans [NeZero p] [NeZero q] (a : Bool)
    (v : ZMod (p*q)) (hv : v ∈ axisSubgroup hpq a) :
    ∃ j : ℕ, j • (axisGenerator hpq a : ZMod (p*q)) = v := by
  obtain ⟨w,rfl⟩ := hv
  have : NeZero (axis p q a) := by cases a <;> assumption
  refine ⟨w.val,?_⟩
  change w.val • axisEmbed hpq a 1 = axisEmbed hpq a w
  rw [←map_nsmul,nsmul_eq_mul,mul_one,ZMod.natCast_zmod_val]

theorem mem_firstAxis_iff {v w : ZMod (p*q)} :
    v-w ∈ axisSubgroup hpq false ↔
      (ZMod.chineseRemainder hpq v).2 = (ZMod.chineseRemainder hpq w).2 := by
  let e := ZMod.chineseRemainder hpq
  constructor
  · rintro ⟨z,hz⟩
    have h := congrArg (fun t => (e t).2) hz
    change (e (e.symm (z,0))).2 = (e (v-w)).2 at h
    rw [e.apply_symm_apply,map_sub] at h
    exact sub_eq_zero.mp h.symm
  · intro h
    refine ⟨(e (v-w)).1,e.injective ?_⟩
    change e (e.symm ((e (v-w)).1,0)) = _
    rw [e.apply_symm_apply]
    exact Prod.ext rfl (by rw [map_sub]; exact (sub_eq_zero.mpr h).symm)

theorem mem_secondAxis_iff {v w : ZMod (p*q)} :
    v-w ∈ axisSubgroup hpq true ↔
      (ZMod.chineseRemainder hpq v).1 = (ZMod.chineseRemainder hpq w).1 := by
  let e := ZMod.chineseRemainder hpq
  constructor
  · rintro ⟨z,hz⟩
    have h := congrArg (fun t => (e t).1) hz
    change (e (e.symm (0,z))).1 = (e (v-w)).1 at h
    rw [e.apply_symm_apply,map_sub] at h
    exact sub_eq_zero.mp h.symm
  · intro h
    refine ⟨(e (v-w)).2,e.injective ?_⟩
    change e (e.symm (0,(e (v-w)).2)) = _
    rw [e.apply_symm_apply]
    exact Prod.ext (by rw [map_sub]; exact (sub_eq_zero.mpr h).symm) rfl

theorem firstAxisActive_iff {Y : Type*} (f : ZMod p × ZMod q → Y) :
    DigitActive (fun v => f (ZMod.chineseRemainder hpq v)) (axisSubgroup hpq false) ↔
      ∃ (u v : ZMod p) (w : ZMod q), f (u,w) ≠ f (v,w) := by
  let e := ZMod.chineseRemainder hpq
  constructor
  · rintro ⟨v,w,h,hd⟩
    change f (e v) ≠ f (e w) at hd
    have he : (e v).2 = (e w).2 := (mem_firstAxis_iff hpq).mp h
    refine ⟨(e v).1,(e w).1,(e v).2,?_⟩
    have hw : ((e w).1,(e v).2) = e w := Prod.ext rfl he
    simpa only [Prod.mk.eta,hw] using hd
  · rintro ⟨u,v,w,h⟩
    refine ⟨e.symm (u,w),e.symm (v,w), (mem_firstAxis_iff hpq).mpr ?_,?_⟩
    · change (e (e.symm (u,w))).2 = (e (e.symm (v,w))).2
      simp
    · change f (e (e.symm (u,w))) ≠ f (e (e.symm (v,w)))
      simpa using h

theorem secondAxisActive_iff {Y : Type*} (f : ZMod p × ZMod q → Y) :
    DigitActive (fun v => f (ZMod.chineseRemainder hpq v)) (axisSubgroup hpq true) ↔
      ∃ (u : ZMod p) (v w : ZMod q), f (u,v) ≠ f (u,w) := by
  let e := ZMod.chineseRemainder hpq
  constructor
  · rintro ⟨v,w,h,hd⟩
    change f (e v) ≠ f (e w) at hd
    have he : (e v).1 = (e w).1 := (mem_secondAxis_iff hpq).mp h
    refine ⟨(e v).1,(e v).2,(e w).2,?_⟩
    have hw : ((e v).1,(e w).2) = e w := Prod.ext he rfl
    simpa only [Prod.mk.eta,hw] using hd
  · rintro ⟨u,v,w,h⟩
    refine ⟨e.symm (u,v),e.symm (u,w), (mem_secondAxis_iff hpq).mpr ?_,?_⟩
    · change (e (e.symm (u,v))).1 = (e (e.symm (u,w))).1
      simp
    · change f (e (e.symm (u,v))) ≠ f (e (e.symm (u,w)))
      simpa using h

/-- Nonconstancy on the entire slot supplies an axis and a slice that
witness it. -/
theorem exists_active_axis {Y : Type*} (f : ZMod (p*q) → Y)
    (h : ∃ v w, f v ≠ f w) : ∃ a, DigitActive f (axisSubgroup hpq a) := by
  let e := ZMod.chineseRemainder hpq
  obtain ⟨v,w,hn⟩ := h
  let F (z : ZMod p × ZMod q) := f (e.symm z)
  have hF : (fun z => F (e z)) = f := by funext z; simp [F]
  by_cases h : F (e v) = F ((e w).1,(e v).2)
  · refine ⟨true,?_⟩
    rw [←hF,secondAxisActive_iff hpq F]
    refine ⟨(e w).1,(e v).2,(e w).2,?_⟩
    simpa only [←h, F, e.symm_apply_apply] using hn
  · refine ⟨false,?_⟩
    rw [←hF,firstAxisActive_iff hpq F]
    exact ⟨(e v).1,(e w).1,(e v).2,h⟩

theorem firstAxisOnly {Y : Type*} (f : ZMod p → Y)
    (h : ∃ u v, f u ≠ f v) (a : Bool) :
    DigitActive (fun v => f (ZMod.chineseRemainder hpq v).1) (axisSubgroup hpq a) ↔
      a = false := by
  cases a
  · have he := firstAxisActive_iff hpq (f ∘ Prod.fst)
    simp only [Function.comp_apply] at he
    rw [he]
    obtain ⟨u,v,huv⟩ := h
    exact ⟨fun _ => rfl, fun _ => ⟨u,v,0,huv⟩⟩
  · have he := secondAxisActive_iff hpq (f ∘ Prod.fst)
    simp only [Function.comp_apply] at he
    rw [he]
    simp

theorem secondAxisOnly {Y : Type*} (f : ZMod q → Y)
    (h : ∃ u v, f u ≠ f v) (a : Bool) :
    DigitActive (fun v => f (ZMod.chineseRemainder hpq v).2) (axisSubgroup hpq a) ↔
      a = true := by
  cases a
  · have he := firstAxisActive_iff hpq (f ∘ Prod.snd)
    simp only [Function.comp_apply] at he
    rw [he]
    simp
  · have he := secondAxisActive_iff hpq (f ∘ Prod.snd)
    simp only [Function.comp_apply] at he
    rw [he]
    obtain ⟨u,v,huv⟩ := h
    exact ⟨fun _ => rfl, fun _ => ⟨0,u,v,huv⟩⟩

end

end TranslationTiling.FiniteCompiler.AxisSlot
