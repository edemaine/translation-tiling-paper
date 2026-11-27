import TranslationTiling.FiniteCompiler.Effective.AxisSlotNumericalDependencies
import TranslationTiling.FiniteCompiler.Effective.AxisSlotGeneratorCode
import TranslationTiling.FiniteCompiler.Effective.AxisSlotDependence

namespace TranslationTiling.FiniteCompiler.Packed.AxisParameters

open SharedCoordinates Compiler Compiler.Effective

set_option maxHeartbeats 700000
attribute [local irreducible] slotSearchCap slotPrimeAt axisPrimeAt numericalFallback numericalMarker

/-- The useful prime is constant along a line and independent of the
low coordinates outside the selected rows. -/
def numericalLocalMasks (N k m p slope : ℕ) (excluded : List ℕ) : List CyclicTile :=
  numericalSlotInvariance N k m 1 p (1,-(slope : ℤ)) none ::
    (((List.range (20+2*k*m+8*m)).filter fun j => decide (j ∉ excluded)).map fun j =>
      numericalSlotInvariance N k m 1 p 0 (some j))

private abbrev LocalMaskInput := ℕ × ℕ × ℕ × ℕ × ℕ × List ℕ

theorem numericalLocalMasks_primrec : Primrec (fun z : LocalMaskInput =>
    numericalLocalMasks z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2.1 z.2.2.2.2.2) := by
  unfold numericalLocalMasks
  apply consList
  · apply numericalSlotInvariance_primrec.comp (g := fun z : LocalMaskInput =>
      ((z.1,z.2.1,z.2.2.1),(1,z.2.2.2.1),(1,-(z.2.2.2.2.1 : ℤ)),none))
    fun_prop
  · have hd : Primrec (fun z : LocalMaskInput => (z.2.1,z.2.2.1)) := by fun_prop
    have hc : Primrec (fun z : ℕ × ℕ => List.range (20+2*z.1*z.2+8*z.2)) := by fun_prop
    have hr := hc.comp hd
    have ht : PrimrecPred (fun z : LocalMaskInput × ℕ => z.2 ∉ z.1.2.2.2.2.2) := by fun_prop
    have hf := filterList (p := fun z j => j ∉ z.2.2.2.2.2) hr ht
    let args (z : LocalMaskInput × ℕ) :
        (ℕ × ℕ × ℕ) × (ℕ × ℕ) × Plane × Option ℕ :=
      ((z.1.1,z.1.2.1,z.1.2.2.1),(1,z.1.2.2.2.1),0,some z.2)
    have hargs : Primrec args := by unfold args; fun_prop
    have hmask := numericalSlotInvariance_primrec.comp hargs
    exact mapList hf hmask


private def numericalSlope (g : Bool) : ℕ := if g then 0 else 2

private def numericalExcluded (k m : ℕ) (g : Bool) (i : ℕ) : List ℕ :=
  (List.range k).map fun d => 20+wangCode k m g d i

/-- The single-marker tests for both directions and all numbered slots. -/
def numericalMarkerMasks (N k m : ℕ) : List CyclicTile :=
  [false,true].flatMap fun g =>
    (List.range k).flatMap fun d =>
      (List.range m).flatMap fun i =>
        (List.range 3).flatMap fun j =>
          let a := wangCode k m g d i
          numericalLocalMasks N k m (numericalMarker k m a j) (numericalSlope g) [20+a]

/-- A low-coordinate shift by a specified residue. -/
def numericalAxisTargets (k m row z : ℕ) : CongruenceList :=
  (List.range (20+2*k*m+8*m)).map fun i =>
    ((numericalAxisRow k m i).1, if row = i then z else 0)

def numericalOtherAxis (N k m p : ℕ) (g : Bool) (i : ℕ) (a : Bool) (d : ℕ) : CyclicTile :=
  let j := wangCode k m g d i
  let z := axisGeneratorCode (axisPrimeAt k m j 3) (axisPrimeAt k m j 4) (!a)
  invarianceCodes N (numericalSlotLows k m) 1 p 0 (numericalAxisTargets k m (20+j) z)

/-- Every fallback is independent of the opposite axis in each digit of its position. -/
def numericalFallbackAt (N k m : ℕ) (g : Bool) (i : ℕ) (a : Bool) : List CyclicTile :=
  let p := numericalFallback m (axisFallbackCode m g i a false)
  numericalLocalMasks N k m p (numericalSlope g) (numericalExcluded k m g i) ++
    (List.range k).map (numericalOtherAxis N k m p g i a)

def numericalFallbackMasks (N k m : ℕ) : List CyclicTile :=
  [false,true].flatMap fun g =>
    (List.range m).flatMap fun i =>
      [false,true].flatMap fun a => numericalFallbackAt N k m g i a

@[fun_prop] private theorem slotBoolValue_primrec : Primrec Bool.toNat :=
  Primrec.dom_bool _

@[fun_prop] theorem wangCode_primrec : Primrec (fun z : ℕ × ℕ × Bool × ℕ × ℕ =>
    wangCode z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2) := by
  unfold wangCode SlotParameters.wangCode
  fun_prop

@[fun_prop] theorem axisFallbackCode_primrec : Primrec (fun z : ℕ × Bool × ℕ × Bool × Bool =>
    axisFallbackCode z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2) := by
  unfold axisFallbackCode
  fun_prop

@[fun_prop] private theorem numericalSlope_primrec : Primrec numericalSlope :=
  Primrec.dom_bool _

@[fun_prop] private theorem numericalExcluded_primrec : Primrec (fun z : ℕ × ℕ × Bool × ℕ =>
    numericalExcluded z.1 z.2.1 z.2.2.1 z.2.2.2) := by
  unfold numericalExcluded
  apply mapList (Primrec.list_range.comp Primrec.fst)
  fun_prop

private abbrev FallbackArgs := ((ℕ × ℕ × ℕ) × Bool) × ℕ
private abbrev MarkerArgs := ((((ℕ × ℕ × ℕ) × Bool) × ℕ) × ℕ) × ℕ

theorem numericalMarkerMasks_primrec : Primrec (fun z : ℕ × ℕ × ℕ =>
    numericalMarkerMasks z.1 z.2.1 z.2.2) := by
  unfold numericalMarkerMasks
  apply flatMapList (Primrec.const [false,true])
  apply flatMapList (by fun_prop)
  apply flatMapList (by fun_prop)
  apply flatMapList (Primrec.const (List.range 3))
  let code (z : MarkerArgs) :=
    wangCode z.1.1.1.1.2.1 z.1.1.1.1.2.2 z.1.1.1.2 z.1.1.2 z.1.2
  have hc : Primrec code := by unfold code; fun_prop
  let markArgs (z : MarkerArgs) : ℕ × ℕ × ℕ × ℕ :=
    (z.1.1.1.1.2.1,z.1.1.1.1.2.2,code z,z.2)
  have hmarkArgs : Primrec markArgs := by unfold markArgs; fun_prop
  have hm := numericalMarker_primrec.comp hmarkArgs
  let input (z : MarkerArgs) : LocalMaskInput :=
    (z.1.1.1.1.1,z.1.1.1.1.2.1,z.1.1.1.1.2.2,
      (fun w : ℕ × ℕ × ℕ × ℕ => numericalMarker w.1 w.2.1 w.2.2.1 w.2.2.2) (markArgs z),
      numericalSlope z.1.1.1.2,[20+code z])
  have hrow : Primrec (fun z : MarkerArgs => 20+code z) := Primrec.nat_add.comp (Primrec.const 20) hc
  have hlist := Primrec.list_cons.comp hrow (Primrec.const ([] : List ℕ))
  have hs : Primrec (fun z : MarkerArgs => numericalSlope z.1.1.1.2) :=
    numericalSlope_primrec.comp (by fun_prop)
  have hN : Primrec (fun z : MarkerArgs => z.1.1.1.1.1) := by fun_prop
  have hk : Primrec (fun z : MarkerArgs => z.1.1.1.1.2.1) := by fun_prop
  have hm' : Primrec (fun z : MarkerArgs => z.1.1.1.1.2.2) := by fun_prop
  have ha : Primrec input :=
    (hN.pair (hk.pair (hm'.pair (hm.pair (hs.pair hlist))))).of_eq (by intro z; rfl)
  have hres := numericalLocalMasks_primrec.comp ha
  exact hres.of_eq (by intro z; rfl)

private abbrev AxisTargetInput := ℕ × ℕ × ℕ × ℕ

@[fun_prop] theorem numericalAxisTargets_primrec :
    Primrec (fun z : AxisTargetInput => numericalAxisTargets z.1 z.2.1 z.2.2.1 z.2.2.2) := by
  unfold numericalAxisTargets
  apply mapList (by fun_prop)
  have h := Primrec.fst.comp (numericalAxisRow_primrec.comp (show Primrec
    (fun z : AxisTargetInput × ℕ => (z.1.1,z.1.2.1,z.2)) by fun_prop))
  fun_prop

private abbrev OtherAxisArgs := ℕ × ℕ × ℕ × ℕ × Bool × ℕ × Bool × ℕ

@[fun_prop] theorem numericalOtherAxis_primrec :
    Primrec (fun z : OtherAxisArgs => numericalOtherAxis z.1 z.2.1 z.2.2.1 z.2.2.2.1
      z.2.2.2.2.1 z.2.2.2.2.2.1 z.2.2.2.2.2.2.1 z.2.2.2.2.2.2.2) := by
  let j (z : OtherAxisArgs) := wangCode z.2.1 z.2.2.1 z.2.2.2.2.1 z.2.2.2.2.2.2.2 z.2.2.2.2.2.1
  have hj : Primrec j := by unfold j; fun_prop
  have hp := axisPrimeAt_primrec.comp (show Primrec (fun z : OtherAxisArgs =>
    (z.2.1,z.2.2.1,j z,(3:ℕ))) by fun_prop)
  have hq := axisPrimeAt_primrec.comp (show Primrec (fun z : OtherAxisArgs =>
    (z.2.1,z.2.2.1,j z,(4:ℕ))) by fun_prop)
  have ha : Primrec (fun z : OtherAxisArgs => !z.2.2.2.2.2.2.1) :=
    (Primrec.dom_bool Bool.not).comp (by fun_prop)
  have hv := axisGeneratorCode_primrec.comp (hp.pair (hq.pair ha))
  have hl := numericalSlotLows_primrec.comp (show Primrec (fun z : OtherAxisArgs =>
    (z.2.1,z.2.2.1)) by fun_prop)
  let v (z : OtherAxisArgs) :=
    axisGeneratorCode (axisPrimeAt z.2.1 z.2.2.1 (j z) 3) (axisPrimeAt z.2.1 z.2.2.1 (j z) 4) (!z.2.2.2.2.2.2.1)
  have hv' : Primrec v := hv
  let args (z : OtherAxisArgs) : (ℕ × List ℕ) × (ℕ × ℕ) × Plane × CongruenceList :=
    ((z.1,numericalSlotLows z.2.1 z.2.2.1),(1,z.2.2.2.1),0,
      numericalAxisTargets z.2.1 z.2.2.1 (20+j z) (v z))
  have hargs : Primrec args := by unfold args; fun_prop
  exact (invarianceCodes_primrec.comp hargs).of_eq (by intro z; rfl)

private abbrev FallbackAtArgs := (FallbackArgs × Bool)

@[fun_prop] theorem numericalFallbackAt_primrec :
    Primrec (fun z : FallbackAtArgs =>
      numericalFallbackAt z.1.1.1.1 z.1.1.1.2.1 z.1.1.1.2.2 z.1.1.2 z.1.2 z.2) := by
  let p (z : FallbackAtArgs) := numericalFallback z.1.1.1.2.2
    (axisFallbackCode z.1.1.1.2.2 z.1.1.2 z.1.2 z.2 false)
  have hp : Primrec p := by unfold p; fun_prop
  unfold numericalFallbackAt
  apply appendList
  · apply numericalLocalMasks_primrec.comp (g := fun z : FallbackAtArgs =>
      (z.1.1.1.1,z.1.1.1.2.1,z.1.1.1.2.2,p z,numericalSlope z.1.1.2,
        numericalExcluded z.1.1.1.2.1 z.1.1.1.2.2 z.1.1.2 z.1.2))
    fun_prop
  · apply mapList (by fun_prop)
    apply numericalOtherAxis_primrec.comp (g := fun z : FallbackAtArgs × ℕ =>
      (z.1.1.1.1.1,z.1.1.1.1.2.1,z.1.1.1.1.2.2,p z.1,
        z.1.1.1.2,z.1.1.2,z.1.2,z.2))
    fun_prop

theorem numericalFallbackMasks_primrec : Primrec (fun z : ℕ × ℕ × ℕ =>
    numericalFallbackMasks z.1 z.2.1 z.2.2) := by
  unfold numericalFallbackMasks
  apply flatMapList (Primrec.const [false,true])
  apply flatMapList (by fun_prop)
  exact flatMapList (Primrec.const [false,true]) numericalFallbackAt_primrec

noncomputable section
open scoped Classical
set_option allowUnsafeReducibility true
attribute [local reducible] AxisParameters.layout AxisParameters.low

variable {k m : ℕ} (s : AxisParameters k m)
local instance numericalLocalMasksDecEq : DecidableEq (SharedCoordinates.Ambient s.layout) :=
  fun a b => Classical.propDecidable (a = b)

private theorem numericalOneObservation_correct (hs : s.prime = rankedAxisPrime k m)
    {p : ℕ} (ψ : Factor s.layout →+ ZMod p)
    (hψ : ∀ n : ℕ, ψ (decode s.layout n) = (n : ZMod p))
    (h : Plane) (target : Option (AxisRow k m)) :
    (numericalSlotInvariance (order s.layout) k m 1 p h
      (target.map slotRowNumber)).toFinset.image (decodePoint s.layout) =
      productInvariance s.layout ψ (h,s.optionalLowStep target) := by
  let joint := (0 : Factor s.layout →+ ZMod 1).prod ψ
  have hjoint (n : ℕ) : joint (decode s.layout n) = ((n : ZMod 1),(n : ZMod p)) :=
    Prod.ext (Subsingleton.elim _ _) (hψ n)
  refine (s.numericalSlotInvariance_correct hs joint hjoint h target).trans ?_
  ext v
  simp [productInvariance,joint]

/-- Decoding the numerical list gives the line test and all requested
low-coordinate independence tests for this observed prime. -/
theorem numericalLocalMasks_correct (hs : s.prime = rankedAxisPrime k m)
    {p : ℕ} (ψ : Factor s.layout →+ ZMod p)
    (hψ : ∀ n : ℕ, ψ (decode s.layout n) = (n : ZMod p))
    (slope : ℕ) (excluded : List ℕ) (F : Finset (SharedCoordinates.Ambient s.layout)) :
    (∃ G ∈ numericalLocalMasks (order s.layout) k m p slope excluded,
      G.toFinset.image (decodePoint s.layout) = F) ↔
    F = productInvariance s.layout ψ ((1,-(slope : ℤ)),0) ∨
      ∃ i : AxisRow k m, slotRowNumber i ∉ excluded ∧
        F = productInvariance s.layout ψ (0,s.optionalLowStep (some i)) := by
  have hzero : s.optionalLowStep none = 0 := by
    funext i
    simp [optionalLowStep]
  have hline := s.numericalOneObservation_correct hs ψ hψ (1,-(slope : ℤ)) none
  rw [hzero] at hline
  simp only [Option.map_none] at hline
  simp only [numericalLocalMasks,List.mem_cons,List.mem_map,List.mem_filter,List.mem_range,
    decide_eq_true_eq]
  constructor
  · rintro ⟨G,rfl | ⟨j,⟨hj,hout⟩,rfl⟩,rfl⟩
    · exact Or.inl hline
    · let i := (slotRowEquiv k m).symm ⟨j,hj⟩
      have he : slotRowNumber i = j := by
        rw [← slotRowEquiv_val]
        exact congrArg Fin.val ((slotRowEquiv k m).apply_symm_apply ⟨j,hj⟩)
      exact Or.inr ⟨i,he.symm ▸ hout,by
        simpa only [Option.map_some,he] using s.numericalOneObservation_correct hs ψ hψ 0 (some i)⟩
  · rintro (rfl | ⟨i,hi,rfl⟩)
    · exact ⟨_,Or.inl rfl,hline⟩
    · refine ⟨_,Or.inr ⟨slotRowNumber i,⟨?_,hi⟩,rfl⟩,?_⟩
      · rw [← slotRowEquiv_val]
        exact (slotRowEquiv k m i).isLt
      · exact s.numericalOneObservation_correct hs ψ hψ 0 (some i)

private theorem numericalSlope_cast (g : Bool) : (numericalSlope g : ℤ) = slopeNumber g := by
  cases g <;> rfl

private theorem numericalExcluded_mem (g : Bool) (i : Fin m) (a : AxisRow k m) :
    slotRowNumber a ∈ numericalExcluded k m g i ↔ a ∈ controls g i := by
  simp only [numericalExcluded,List.mem_map,List.mem_range,controls,Set.mem_range]
  constructor
  · rintro ⟨j,hj,he⟩
    refine ⟨⟨j,hj⟩,(slotRowEquiv k m).injective (Fin.ext ?_)⟩
    simpa only [slotRowEquiv_val,wangRow,slotRowNumber] using he
  · rintro ⟨d,rfl⟩
    exact ⟨d.val,d.isLt,rfl⟩

theorem numericalMarkerAt_correct (hs : s.prime = rankedAxisPrime k m)
    (g : Bool) (d : Fin k) (i : Fin m) (j : Fin 3) (F : Finset (SharedCoordinates.Ambient s.layout)) :
    (∃ G ∈ numericalLocalMasks (order s.layout) k m (numericalMarker k m (wangCode k m g d i) j)
        (numericalSlope g) [20+wangCode k m g d i],
        G.toFinset.image (decodePoint s.layout) = F) ↔ F ∈ s.markerTests (g,d,i) j := by
  rw [numericalMarker_eq s hs, s.numericalLocalMasks_correct hs _ (s.observedMarker_decode (g,d,i) j)]
  simp only [markerTests,numericalSlope_cast,s.optionalLowStep_some,List.mem_cons,List.not_mem_nil,or_false,
    List.mem_map,Finset.mem_toList,Finset.mem_erase,Finset.mem_univ,and_true]
  have he (a : AxisRow k m) : slotRowNumber a = 20+wangCode k m g d i ↔ a = wangRow (g,d,i) := by
    change slotRowNumber a = slotRowNumber (wangRow (g,d,i)) ↔ _
    rw [← slotRowEquiv_val, ← slotRowEquiv_val, ← Fin.ext_iff, (slotRowEquiv k m).injective.eq_iff]
  simp only [he,eq_comm (a := F)]

theorem numericalMarkerMasks_correct (hs : s.prime = rankedAxisPrime k m)
    (F : Finset (SharedCoordinates.Ambient s.layout)) :
    (∃ G ∈ numericalMarkerMasks (order s.layout) k m,
        G.toFinset.image (decodePoint s.layout) = F) ↔ ∃ i j, F ∈ s.markerTests i j := by
  simp only [numericalMarkerMasks,List.mem_flatMap,List.mem_range]
  constructor
  · rintro ⟨G,⟨g,_,d,hd,i,hi,j,hj,hG⟩,he⟩
    exact ⟨(g,⟨d,hd⟩,⟨i,hi⟩),⟨j,hj⟩,
      (s.numericalMarkerAt_correct hs g ⟨d,hd⟩ ⟨i,hi⟩ ⟨j,hj⟩ F).mp ⟨G,hG,he⟩⟩
  · rintro ⟨⟨g,d,i⟩,j,h⟩
    obtain ⟨G,hG,he⟩ := (s.numericalMarkerAt_correct hs g d i j F).mpr h
    exact ⟨G,⟨g,by cases g <;> simp,d.val,d.isLt,i.val,i.isLt,j.val,j.isLt,hG⟩,he⟩

private theorem numericalAxisTargets_mem (hs : s.prime = rankedAxisPrime k m)
    (i : WangSlot k m) (a : Bool) (c : ℕ × ℕ) :
    c ∈ numericalAxisTargets k m (slotRowNumber (wangRow i))
        ((AxisSlot.axisGenerator (s.lowAxis_coprime i) a).val.val) ↔
      ∃ j, (s.layout.lowSize j, ((s.axisStep i a).2 j).val) = c := by
  let h (j : AxisRow k m) :=
    ((numericalAxisRow k m (slotRowNumber j)).1,
      if slotRowNumber (wangRow i) = slotRowNumber j then
        (AxisSlot.axisGenerator (s.lowAxis_coprime i) a).val.val else 0)
  have hinj : Function.Injective (slotRowNumber (k := k) (m := m)) := by
    intro u v e
    apply (slotRowEquiv k m).injective
    exact Fin.ext (by simpa only [slotRowEquiv_val] using e)
  have he (j : AxisRow k m) : h j = (s.layout.lowSize j, ((s.axisStep i a).2 j).val) := by
    unfold h
    rw [numericalAxisRow_eq s hs j]
    by_cases he : j = wangRow i
    · subst j
      dsimp only [axisStep]
      rw [Function.update_self,ite_eq_left rfl]
    · have hn : slotRowNumber (wangRow i) ≠ slotRowNumber j := fun h => he (hinj h).symm
      dsimp only [axisStep]
      rw [ite_eq_right hn,Function.update_of_ne he,Pi.zero_apply,ZMod.val_zero]
  simp only [numericalAxisTargets,List.mem_map,List.mem_range]
  constructor
  · rintro ⟨r,hr,hc⟩
    let j := (slotRowEquiv k m).symm ⟨r,hr⟩
    have hval : slotRowNumber j = r := by
      rw [← slotRowEquiv_val]
      exact congrArg Fin.val ((slotRowEquiv k m).apply_symm_apply ⟨r,hr⟩)
    refine ⟨j,(he j).symm.trans ?_⟩
    simpa only [h,hval] using hc
  · rintro ⟨j,rfl⟩
    refine ⟨slotRowNumber j,?_,he j⟩
    rw [← slotRowEquiv_val]
    exact (slotRowEquiv k m j).isLt

private theorem numericalOtherAxis_correct (hs : s.prime = rankedAxisPrime k m)
    (g : Bool) (i : Fin m) (a : Bool) (d : Fin k) :
    let p := numericalFallback m (axisFallbackCode m g i a false)
    (numericalOtherAxis (order s.layout) k m p g i a d).toFinset.image (decodePoint s.layout) =
      productInvariance s.layout (s.observeFallback (g,i,a,false)) (s.axisStep (g,d,i) (!a)) := by
  dsimp only
  rw [numericalFallback_eq s hs]
  let ψ := s.observeFallback (g,i,a,false)
  let joint := (0 : Factor s.layout →+ ZMod 1).prod ψ
  have hj (n : ℕ) : joint (decode s.layout n) =
      ((n : ZMod 1),(n : ZMod (s.fallback (g,i,a,false)))) :=
    Prod.ext (Subsingleton.elim _ _) (s.observedFallback_decode _ n)
  dsimp only [numericalOtherAxis]
  have h₃ : axisPrimeAt k m (wangCode k m g d i) 3 = s.lowAxis (g,d,i) false :=
    lowAxisCode_eq s hs g d i false
  have h₄ : axisPrimeAt k m (wangCode k m g d i) 4 = s.lowAxis (g,d,i) true :=
    lowAxisCode_eq s hs g d i true
  rw [h₃,h₄]
  rw [axisGeneratorCode_correct]
  refine (s.numericalInvariance_correct joint hj _ (s.numericalSlotLows_mem hs) _
    0 (s.axisStep (g,d,i) (!a)).2 (s.numericalAxisTargets_mem hs (g,d,i) (!a))).trans ?_
  have he : ((0:Plane),(s.axisStep (g,d,i) (!a)).2) = s.axisStep (g,d,i) (!a) := rfl
  rw [he]
  have hz (v : Factor s.layout) : joint v = 0 ↔ ψ v = 0 := by simp [joint]
  ext v
  simp only [productInvariance,Finset.mem_filter,Finset.mem_union,ne_eq,hz,ψ]

theorem numericalFallbackAt_correct (hs : s.prime = rankedAxisPrime k m)
    (g : Bool) (i : Fin m) (a : Bool) (F : Finset (SharedCoordinates.Ambient s.layout)) :
    (∃ G ∈ numericalFallbackAt (order s.layout) k m g i a,
        G.toFinset.image (decodePoint s.layout) = F) ↔ F ∈ s.fallbackTests g i a := by
  simp only [numericalFallbackAt,List.mem_append,or_and_right,exists_or]
  have h := s.numericalLocalMasks_correct hs (s.observeFallback (g,i,a,false))
    (s.observedFallback_decode (g,i,a,false)) (numericalSlope g) (numericalExcluded k m g i) F
  have ht := s.numericalOtherAxis_correct hs g i a
  rw [numericalFallback_eq s hs,h]
  simp only [fallbackTests,numericalSlope_cast,s.optionalLowStep_some,List.mem_cons,List.mem_append,
    List.mem_map,Finset.mem_toList,Finset.mem_filter,Finset.mem_univ,true_and,numericalExcluded_mem,
    List.mem_range,List.mem_finRange,eq_comm (a := F)]
  have haxis :
      (∃ G, (∃ d < k, numericalOtherAxis (order s.layout) k m (s.fallback (g,i,a,false))
        g i a d = G) ∧ G.toFinset.image (decodePoint s.layout) = F) ↔
      ∃ d : Fin k, productInvariance s.layout (s.observeFallback (g,i,a,false))
        (s.axisStep (g,d,i) (!a)) = F := by
    constructor
    · rintro ⟨G,⟨d,hd,rfl⟩,hG⟩
      have hh := ht ⟨d,hd⟩
      dsimp only at hh
      rw [numericalFallback_eq s hs] at hh
      exact ⟨⟨d,hd⟩,hh.symm.trans hG⟩
    · rintro ⟨d,hd⟩
      refine ⟨_,⟨d.val,d.isLt,rfl⟩,?_⟩
      have hh := ht d
      dsimp only at hh
      rw [numericalFallback_eq s hs] at hh
      exact hh.trans hd
  rw [haxis,or_assoc]

theorem numericalFallbackMasks_correct (hs : s.prime = rankedAxisPrime k m)
    (F : Finset (SharedCoordinates.Ambient s.layout)) :
    (∃ G ∈ numericalFallbackMasks (order s.layout) k m,
        G.toFinset.image (decodePoint s.layout) = F) ↔ ∃ g i a, F ∈ s.fallbackTests g i a := by
  simp only [numericalFallbackMasks,List.mem_flatMap,List.mem_range]
  constructor
  · rintro ⟨G,⟨g,_,i,hi,a,_,hG⟩,he⟩
    exact ⟨g,⟨i,hi⟩,a,(s.numericalFallbackAt_correct hs g ⟨i,hi⟩ a F).mp ⟨G,hG,he⟩⟩
  · rintro ⟨g,i,a,h⟩
    obtain ⟨G,hG,he⟩ := (s.numericalFallbackAt_correct hs g i a F).mpr h
    exact ⟨G,⟨g,by cases g <;> simp,i.val,i.isLt,a,by cases a <;> simp,hG⟩,he⟩

end
end TranslationTiling.FiniteCompiler.Packed.AxisParameters
