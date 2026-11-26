import TranslationTiling.FiniteCompiler.Effective.SlotNumericalDependencies
import TranslationTiling.FiniteCompiler.Effective.SlotDependence

namespace TranslationTiling.FiniteCompiler.Packed.SlotParameters

open SharedCoordinates Compiler Compiler.Effective

set_option maxHeartbeats 700000
attribute [local irreducible] slotSearchCap slotPrimeAt

/-- The useful prime is constant along a line and independent of the
low coordinates outside the selected rows. -/
def numericalLocalMasks (N k m p slope : ℕ) (excluded : List ℕ) : List CyclicTile :=
  numericalSlotInvariance N k m 1 p (1,-(slope : ℤ)) none ::
    (((List.range (20+2*k*m+4*m)).filter fun j => decide (j ∉ excluded)).map fun j =>
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
    have hc : Primrec (fun z : ℕ × ℕ => List.range (20+2*z.1*z.2+4*z.2)) := by fun_prop
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

/-- The observed fallback is allowed to depend on all digits of its slot. -/
def numericalFallbackMasks (N k m : ℕ) : List CyclicTile :=
  [false,true].flatMap fun g =>
    (List.range m).flatMap fun i =>
      numericalLocalMasks N k m (numericalFallback m (fallbackCode m g i false))
        (numericalSlope g) (numericalExcluded k m g i)

@[fun_prop] private theorem slotBoolValue_primrec : Primrec Bool.toNat :=
  Primrec.dom_bool _

@[fun_prop] theorem wangCode_primrec : Primrec (fun z : ℕ × ℕ × Bool × ℕ × ℕ =>
    wangCode z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2) := by
  unfold wangCode
  fun_prop

@[fun_prop] theorem fallbackCode_primrec : Primrec (fun z : ℕ × Bool × ℕ × Bool =>
    fallbackCode z.1 z.2.1 z.2.2.1 z.2.2.2) := by
  unfold fallbackCode
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

theorem numericalFallbackMasks_primrec : Primrec (fun z : ℕ × ℕ × ℕ =>
    numericalFallbackMasks z.1 z.2.1 z.2.2) := by
  unfold numericalFallbackMasks
  apply flatMapList (Primrec.const [false,true])
  apply flatMapList (by fun_prop)
  let fallArgs (z : FallbackArgs) : ℕ × ℕ :=
    (z.1.1.2.2,fallbackCode z.1.1.2.2 z.1.2 z.2 false)
  have hfallArgs : Primrec fallArgs := by unfold fallArgs; fun_prop
  have hp := numericalFallback_primrec.comp hfallArgs
  let input (z : FallbackArgs) : LocalMaskInput :=
    (z.1.1.1,z.1.1.2.1,z.1.1.2.2,
      numericalFallback z.1.1.2.2 (fallbackCode z.1.1.2.2 z.1.2 z.2 false),
      numericalSlope z.1.2,numericalExcluded z.1.1.2.1 z.1.1.2.2 z.1.2 z.2)
  have hs : Primrec (fun z : FallbackArgs => numericalSlope z.1.2) :=
    numericalSlope_primrec.comp (by fun_prop)
  have hx := numericalExcluded_primrec.comp (show Primrec (fun z : FallbackArgs =>
    (z.1.1.2.1,z.1.1.2.2,z.1.2,z.2)) by fun_prop)
  have hN : Primrec (fun z : FallbackArgs => z.1.1.1) := by fun_prop
  have hk : Primrec (fun z : FallbackArgs => z.1.1.2.1) := by fun_prop
  have hm : Primrec (fun z : FallbackArgs => z.1.1.2.2) := by fun_prop
  have ha : Primrec input :=
    (hN.pair (hk.pair (hm.pair (hp.pair (hs.pair hx))))).of_eq (by intro z; rfl)
  have hres := numericalLocalMasks_primrec.comp ha
  exact hres.of_eq (by intro z; rfl)

noncomputable section
open scoped Classical

variable {k m : ℕ} (s : SlotParameters k m)
local instance numericalLocalMasksDecEq : DecidableEq (SharedCoordinates.Ambient s.layout) :=
  fun a b => Classical.propDecidable (a = b)

private theorem numericalOneObservation_correct (hs : s.prime = rankedSlotPrime k m)
    {p : ℕ} (ψ : Factor s.layout →+ ZMod p)
    (hψ : ∀ n : ℕ, ψ (decode s.layout n) = (n : ZMod p))
    (h : Plane) (target : Option (SlotRow k m)) :
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
theorem numericalLocalMasks_correct (hs : s.prime = rankedSlotPrime k m)
    {p : ℕ} (ψ : Factor s.layout →+ ZMod p)
    (hψ : ∀ n : ℕ, ψ (decode s.layout n) = (n : ZMod p))
    (slope : ℕ) (excluded : List ℕ) (F : Finset (SharedCoordinates.Ambient s.layout)) :
    (∃ G ∈ numericalLocalMasks (order s.layout) k m p slope excluded,
      G.toFinset.image (decodePoint s.layout) = F) ↔
    F = productInvariance s.layout ψ ((1,-(slope : ℤ)),0) ∨
      ∃ i : SlotRow k m, slotRowNumber i ∉ excluded ∧
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

private theorem numericalExcluded_mem (g : Bool) (i : Fin m) (a : SlotRow k m) :
    slotRowNumber a ∈ numericalExcluded k m g i ↔ a ∈ controls g i := by
  simp only [numericalExcluded,List.mem_map,List.mem_range,controls,Set.mem_range]
  constructor
  · rintro ⟨j,hj,he⟩
    refine ⟨⟨j,hj⟩,(slotRowEquiv k m).injective (Fin.ext ?_)⟩
    simpa only [slotRowEquiv_val,wangRow,slotRowNumber] using he
  · rintro ⟨d,rfl⟩
    exact ⟨d.val,d.isLt,rfl⟩

theorem numericalMarkerAt_correct (hs : s.prime = rankedSlotPrime k m)
    (g : Bool) (d : Fin k) (i : Fin m) (j : Fin 3) (F : Finset (SharedCoordinates.Ambient s.layout)) :
    (∃ G ∈ numericalLocalMasks (order s.layout) k m (numericalMarker k m (wangCode k m g d i) j)
        (numericalSlope g) [20+wangCode k m g d i],
        G.toFinset.image (decodePoint s.layout) = F) ↔ F ∈ s.markerTests (g,d,i) j := by
  rw [numericalMarker_eq s hs, s.numericalLocalMasks_correct hs _ (s.observedMarker_decode (g,d,i) j)]
  simp only [markerTests,numericalSlope_cast,s.optionalLowStep_some,List.mem_cons,List.not_mem_nil,or_false,
    List.mem_map,Finset.mem_toList,Finset.mem_erase,Finset.mem_univ,and_true]
  have he (a : SlotRow k m) : slotRowNumber a = 20+wangCode k m g d i ↔ a = wangRow (g,d,i) := by
    change slotRowNumber a = slotRowNumber (wangRow (g,d,i)) ↔ _
    rw [← slotRowEquiv_val, ← slotRowEquiv_val, ← Fin.ext_iff, (slotRowEquiv k m).injective.eq_iff]
  simp only [he,eq_comm (a := F)]

theorem numericalFallbackAt_correct (hs : s.prime = rankedSlotPrime k m)
    (g : Bool) (i : Fin m) (F : Finset (SharedCoordinates.Ambient s.layout)) :
    (∃ G ∈ numericalLocalMasks (order s.layout) k m (numericalFallback m (fallbackCode m g i false))
        (numericalSlope g) (numericalExcluded k m g i),
        G.toFinset.image (decodePoint s.layout) = F) ↔ F ∈ s.fallbackTests g i := by
  rw [numericalFallback_eq s hs, s.numericalLocalMasks_correct hs _ (s.observedFallback_decode (g,i,false))]
  simp only [fallbackTests,numericalSlope_cast,s.optionalLowStep_some,List.mem_cons,List.mem_map,
    Finset.mem_toList,Finset.mem_filter,Finset.mem_univ,true_and,numericalExcluded_mem,eq_comm (a := F)]

theorem numericalMarkerMasks_correct (hs : s.prime = rankedSlotPrime k m)
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

theorem numericalFallbackMasks_correct (hs : s.prime = rankedSlotPrime k m)
    (F : Finset (SharedCoordinates.Ambient s.layout)) :
    (∃ G ∈ numericalFallbackMasks (order s.layout) k m,
        G.toFinset.image (decodePoint s.layout) = F) ↔ ∃ g i, F ∈ s.fallbackTests g i := by
  simp only [numericalFallbackMasks,List.mem_flatMap,List.mem_range]
  constructor
  · rintro ⟨G,⟨g,_,i,hi,hG⟩,he⟩
    exact ⟨g,⟨i,hi⟩,(s.numericalFallbackAt_correct hs g ⟨i,hi⟩ F).mp ⟨G,hG,he⟩⟩
  · rintro ⟨g,i,h⟩
    obtain ⟨G,hG,he⟩ := (s.numericalFallbackAt_correct hs g i F).mpr h
    exact ⟨G,⟨g,by cases g <;> simp,i.val,i.isLt,hG⟩,he⟩

end

end TranslationTiling.FiniteCompiler.Packed.SlotParameters
