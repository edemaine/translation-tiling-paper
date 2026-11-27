import TranslationTiling.FiniteCompiler.Effective.AxisSlotNumericalRows
import TranslationTiling.FiniteCompiler.Effective.AxisSlotNumericalInvariance
import TranslationTiling.FiniteCompiler.Effective.AxisSlotFrame

namespace TranslationTiling.FiniteCompiler.Packed.AxisParameters

open SharedCoordinates Compiler Compiler.Effective

/-- Low residues of the zero vector or the generator at one chosen row. -/
def numericalLowTargets (k m : ℕ) (target : Option ℕ) : CongruenceList :=
  (List.range (20+2*k*m+8*m)).map fun i =>
    let r := (numericalAxisRow k m i).1
    (r,if target = some i then 1 % r else 0)

theorem numericalLowTargets_primrec :
    Primrec (fun z : ℕ × ℕ × Option ℕ => numericalLowTargets z.1 z.2.1 z.2.2) := by
  unfold numericalLowTargets
  apply mapList (by fun_prop)
  have h : Primrec (fun z : (ℕ × ℕ × Option ℕ) × ℕ => (z.1.1,z.1.2.1,z.2)) := by fun_prop
  have hl := Primrec.fst.comp (numericalAxisRow_primrec.comp h)
  fun_prop

/-- A numerical dependence test reads a useful pair and shifts either
along its line or by one generator in the base. -/
def numericalSlotInvariance (N k m a b : ℕ) (h : Plane) (target : Option ℕ) : CyclicTile :=
  invarianceCodes N (numericalSlotLows k m) a b h (numericalLowTargets k m target)

private abbrev NumericalInvarianceArgs := (ℕ × ℕ × ℕ) × (ℕ × ℕ) × Plane × Option ℕ

theorem numericalSlotInvariance_primrec :
    Primrec (fun z : (ℕ × ℕ × ℕ) × (ℕ × ℕ) × Plane × Option ℕ =>
      numericalSlotInvariance z.1.1 z.1.2.1 z.1.2.2 z.2.1.1 z.2.1.2 z.2.2.1 z.2.2.2) := by
  have hl := numericalSlotLows_primrec.comp (show Primrec (fun z : NumericalInvarianceArgs => z.1.2) by fun_prop)
  have hc := numericalLowTargets_primrec.comp
    (show Primrec (fun z : NumericalInvarianceArgs => (z.1.2.1,z.1.2.2,z.2.2.2)) by fun_prop)
  have h : Primrec (fun z : NumericalInvarianceArgs =>
      ((z.1.1,numericalSlotLows z.1.2.1 z.1.2.2),z.2.1,z.2.2.1,
        numericalLowTargets z.1.2.1 z.1.2.2 z.2.2.2)) := by fun_prop
  exact invarianceCodes_primrec.comp h

/-- The arithmetic rows are independent of each added low coordinate. -/
def numericalAnchorMasks (N k m : ℕ) : List CyclicTile :=
  (List.range 20).flatMap fun i =>
    let row := numericalAxisRow k m i
    (((List.range (20+2*k*m+8*m)).filter fun j => decide (20 ≤ j)).map fun j =>
      numericalSlotInvariance N k m row.2.1 row.2.2 0 (some j))

private abbrev AnchorIndex := ((ℕ × ℕ × ℕ) × ℕ) × ℕ

theorem numericalAnchorMasks_primrec :
    Primrec (fun z : ℕ × ℕ × ℕ => numericalAnchorMasks z.1 z.2.1 z.2.2) := by
  unfold numericalAnchorMasks
  apply flatMapList (Primrec.const (List.range 20))
  have hr : Primrec (fun z : (ℕ × ℕ × ℕ) × ℕ => List.range (20+2*z.1.2.1*z.1.2.2+8*z.1.2.2)) := by
    fun_prop
  have hg : PrimrecPred (fun z : AnchorIndex => 20 ≤ z.2) := by fun_prop
  apply mapList (filterList (p := fun _ j => 20 ≤ j) hr hg)
  have hp : Primrec (fun z : AnchorIndex => (z.1.1.2.1,z.1.1.2.2,z.1.2)) := by fun_prop
  have hl := numericalAxisRow_primrec.comp hp
  apply numericalSlotInvariance_primrec.comp (g := fun z : AnchorIndex =>
    (z.1.1,(numericalAxisRow z.1.1.2.1 z.1.1.2.2 z.1.2).2,0,some z.2))
  fun_prop

noncomputable section
open scoped Classical

variable {k m : ℕ} (s : AxisParameters k m)
local instance numericalDependenciesAmbientDecEq : DecidableEq (SharedCoordinates.Ambient s.layout) :=
  fun a b => Classical.propDecidable (a = b)

def optionalLowStep (target : Option (AxisRow k m)) (i : AxisRow k m) :
    SharedCoordinates.Low s.layout i := if target = some i then 1 else 0

private theorem numericalLowTargets_mem (hs : s.prime = rankedAxisPrime k m)
    (target : Option (AxisRow k m)) (c : ℕ × ℕ) :
    c ∈ numericalLowTargets k m (target.map slotRowNumber) ↔
      ∃ i, (s.layout.lowSize i,(s.optionalLowStep target i).val) = c := by
  have htarget (i : AxisRow k m) :
      target.map slotRowNumber = some (slotRowNumber i) ↔ target = some i := by
    cases target with
    | none => simp
    | some j =>
      simp only [Option.map_some,Option.some.injEq,← slotRowEquiv_val]
      exact ⟨fun h => (slotRowEquiv k m).injective (Fin.ext h), fun h => congrArg (fun u : AxisRow k m => (slotRowEquiv k m u).val) h⟩
  have hdata (i : AxisRow k m) :
      (let r := (numericalAxisRow k m (slotRowNumber i)).1
       (r, if target.map slotRowNumber = some (slotRowNumber i) then 1 % r else 0)) =
        (s.layout.lowSize i,(s.optionalLowStep target i).val) := by
    dsimp only
    rw [numericalAxisRow_eq s hs i]
    by_cases hi : target = some i
    · simp [optionalLowStep,hi,ZMod.val_one_eq_one_mod]
    · simp [optionalLowStep,hi,mt (htarget i).mp hi]
  simp only [numericalLowTargets,List.mem_map,List.mem_range]
  constructor
  · rintro ⟨i,hi,h⟩
    let a := (slotRowEquiv k m).symm ⟨i,hi⟩
    have he : slotRowNumber a = i := by
      rw [← slotRowEquiv_val]
      exact congrArg Fin.val ((slotRowEquiv k m).apply_symm_apply ⟨i,hi⟩)
    refine ⟨a,(hdata a).symm.trans ?_⟩
    simpa only [he] using h
  · rintro ⟨a,rfl⟩
    refine ⟨slotRowNumber a,?_,hdata a⟩
    rw [← slotRowEquiv_val]
    exact (slotRowEquiv k m a).isLt

theorem numericalSlotInvariance_correct (hs : s.prime = rankedAxisPrime k m)
    {a b : ℕ} (ψ : Factor s.layout →+ ZMod a × ZMod b)
    (hψ : ∀ n : ℕ, ψ (decode s.layout n) = ((n : ZMod a),(n : ZMod b)))
    (h : Plane) (target : Option (AxisRow k m)) :
    (numericalSlotInvariance (order s.layout) k m a b h (target.map slotRowNumber)).toFinset.image
        (decodePoint s.layout) = productInvariance s.layout ψ (h,s.optionalLowStep target) :=
  s.numericalInvariance_correct ψ hψ _ (s.numericalSlotLows_mem hs) _ h _
    (s.numericalLowTargets_mem hs target)

theorem optionalLowStep_some (r : AxisRow k m) :
    (0,s.optionalLowStep (some r)) = lowStep s.layout r := by
  refine Prod.ext rfl (funext fun i => ?_)
  change s.optionalLowStep (some r) i = Function.update (0 : ∀ j : AxisRow k m, SharedCoordinates.Low s.layout j) r 1 i
  by_cases hi : i = r
  · subst i
    simp [optionalLowStep]
  · simp [optionalLowStep,hi,Ne.symm hi,Function.update_of_ne]

private theorem numericalAnchorAt_correct (hs : s.prime = rankedAxisPrime k m)
    (i : FourValueRow 0) (r : AxisAddedRow k m) :
    let row := numericalAxisRow k m i.val
    (numericalSlotInvariance (order s.layout) k m row.2.1 row.2.2 0
      (some (slotRowNumber (.inr r)))).toFinset.image (decodePoint s.layout) =
        productInvariance s.layout (privateUseful s.layout (.inl i)) (lowStep s.layout (.inr r)) := by
  dsimp only
  have h := numericalAxisRow_eq s hs (.inl i)
  simp only [slotRowNumber] at h
  rw [h,← s.optionalLowStep_some]
  exact s.numericalSlotInvariance_correct hs (privateUseful s.layout (.inl i))
    (privateUseful_decode s.layout (.inl i)) 0 (some (.inr r))

theorem numericalAnchorMasks_correct (hs : s.prime = rankedAxisPrime k m)
    (F : Finset (SharedCoordinates.Ambient s.layout)) :
    (∃ G ∈ numericalAnchorMasks (order s.layout) k m, G.toFinset.image (decodePoint s.layout) = F) ↔
      F ∈ s.anchorTests := by
  unfold numericalAnchorMasks anchorTests
  simp only [List.mem_flatMap,List.mem_map,List.mem_range,List.mem_filter,decide_eq_true_eq,
    Finset.mem_toList,Finset.mem_univ,true_and,Prod.exists]
  constructor
  · rintro ⟨G,⟨i,hi,j,⟨hj,hj'⟩,rfl⟩,rfl⟩
    let a : FourValueRow 0 := ⟨i,by simpa using hi⟩
    let r := (slotRowEquiv k m).symm ⟨j,hj⟩
    have hnum : slotRowNumber r = j := by
      rw [← slotRowEquiv_val]
      exact congrArg Fin.val ((slotRowEquiv k m).apply_symm_apply ⟨j,hj⟩)
    obtain ⟨b,hb⟩ : ∃ b : AxisAddedRow k m, r = .inr b := by
      cases h : r with
      | inl a =>
        have hlt : a.val < 20 := by simpa using a.isLt
        have he : a.val = j := by simpa only [h,slotRowNumber] using hnum
        omega
      | inr b => exact ⟨b,rfl⟩
    have hrow : slotRowNumber (.inr b) = j := by rw [← hb,hnum]
    exact ⟨a,b,by simpa only [hrow] using (s.numericalAnchorAt_correct hs a b).symm⟩
  · rintro ⟨i,r,rfl⟩
    let j := slotRowNumber (.inr r)
    have hbound : j < 20+2*k*m+8*m := by
      rw [show j = (slotRowEquiv k m (.inr r)).val from (slotRowEquiv_val _).symm]
      exact (slotRowEquiv k m (.inr r)).isLt
    have hge : 20 ≤ j := by
      rcases r with ⟨g,d,r⟩ | ⟨g,r,a,b⟩ <;> simp only [j,slotRowNumber] <;> omega
    refine ⟨_,⟨i.val,by simpa using i.isLt,j,⟨hbound,hge⟩,rfl⟩,?_⟩
    exact s.numericalAnchorAt_correct hs i r

end

end TranslationTiling.FiniteCompiler.Packed.AxisParameters
