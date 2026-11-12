import TranslationTiling.FiniteCompiler.Effective.Compiler
import TranslationTiling.FiniteCompiler.Effective.SparseCorrect
import TranslationTiling.FiniteCompiler.Effective.DigitTest
import TranslationTiling.FiniteCompiler.ConstraintCycles

namespace TranslationTiling.FiniteCompiler.Effective
open Compiler.Effective
open scoped Classical
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def configurations (T : System) (spec : List NumericalSpec) : Slots T → CycleConfiguration :=
  fun s =>
    let i := (channelEquiv T).symm s
    let e := spec.getD s.val (false,0,0)
    ((parameters T).r i,rawOtherDigits (parameterData T) (channelKey i) e.2.2,
      rawA (parameterData T) e.2.1,rawB (parameterData T) e.2.1,e.1)

theorem rawConfigurations_eq (T : System) (spec : List NumericalSpec) :
    rawConfigurations (parameterData T) spec = List.ofFn (configurations T spec) := by
  apply List.ext_getElem
  · simp only [rawConfigurations,List.length_map,List.length_range,List.length_ofFn]
    rfl
  · intro k hk hk'
    have hkm : k < T.width + 2 := by simpa only [List.length_ofFn] using hk'
    simp only [rawConfigurations,List.getElem_map,List.getElem_range,List.getElem_ofFn]
    change (rawR (parameterData T) (denseChannelKey T.width k),_,_,_,_) = _
    have he : denseChannelKey T.width k = channelKey ((channelEquiv T).symm ⟨k,hkm⟩) := by
      simpa only [Equiv.apply_symm_apply] using denseChannelKey_eq T ((channelEquiv T).symm ⟨k,hkm⟩)
    have he' : denseChannelKey (parameterData T).1 k = channelKey ((channelEquiv T).symm ⟨k,hkm⟩) := he
    simp only [he,he',rawR_eq,configurations]

structure SpecMatches (spec : List NumericalSpec) {t : ℕ}
    (cycle : ZMod t ↪ Channel T) (labels : ∀ j, Label T (cycle j)) : Prop where
  on : ∀ j, spec.getD ((channelEquiv T) (cycle j)).val (false,0,0) =
    (true,channelKey (cycle (j-1)),labelKey (cycle j) (labels j))
  off : ∀ i, (∀ j, cycle j ≠ i) →
    (spec.getD ((channelEquiv T) i).val (false,0,0)).1 = false

def configurations_match {T : System} {t : ℕ} [NeZero t]
    (spec : List NumericalSpec) (cycle : ZMod t ↪ Channel T)
    (labels : ∀ j, Label T (cycle j)) (hs : SpecMatches spec cycle labels) :
    SparseConfigMatches (parameters T) (configurations T spec) cycle labels := by
  refine ⟨fun j => rawOtherDigits (parameterData T) (channelKey (cycle j))
      (labelKey (cycle j) (labels j)),?_,?_,?_⟩
  · intro j
    simp only [configurations,Equiv.symm_apply_apply,hs.on j,rawA_eq,rawB_eq]
  · intro j n
    exact rawOtherDigits_test T (cycle j) (labels j) n
  · intro i hi
    simp only [configurations,Equiv.symm_apply_apply,hs.off i hi]
    trivial

theorem specifiedGadgets_correct {T : System} {t : ℕ} [NeZero t]
    (spec : List NumericalSpec) (cycle : ZMod t ↪ Channel T)
    (labels : ∀ j, Label T (cycle j)) (hs : SpecMatches spec cycle labels) :
    ((sparseGadgets (rawOrder (parameterData T)) (rawConfigurations (parameterData T) spec)).map
      (fun xs => xs.toFinset.image (decodeNumericalPoint (parameters T)))).toFinset =
      sparseCycleTiles (parameters T) cycle labels := by
  rw [rawOrder_eq,rawConfigurations_eq]
  exact sparseGadgets_correct (configurations_match spec cycle labels hs)

theorem rawWordSpec_get (T : System) (w : List ℕ) (k : ℕ) (hk : k < T.width + 2) :
    (rawWordSpec (parameterData T) w).getD k (false,0,0) =
      if k < T.width then (true,denseChannelKey T.width (differenceResidue T.width k 1),w.getD k 0)
      else (false,denseChannelKey T.width k,0) := by
  have hd : (parameterData T).1 = T.width := rfl
  simp only [rawWordSpec,hd,List.getD_eq_getElem?_getD,List.getElem?_map,
    List.getElem?_range hk,Option.map_some,Option.getD_some]

theorem predecessor_value (T : System) (j : ZMod T.width) :
    differenceResidue T.width ((columnResidueEquiv T).symm j).val 1 =
      ((columnResidueEquiv T).symm (j-1)).val := by
  have hv {m : ℕ} [NeZero m] (k : ZMod m) : ((ZMod.finEquiv m).symm k).val = k.val := by
    cases m with
    | zero => exact False.elim (NeZero.ne 0 rfl)
    | succ m => rfl
  have h1 : ((columnResidueEquiv T).symm j).val = j.val := hv j
  have h2 : ((columnResidueEquiv T).symm (j-1)).val = (j-1).val := hv (j-1)
  rw [differenceResidue_eq,h1,h2,ZMod.natCast_zmod_val,Nat.cast_one]

theorem rawWordSpec_matches (T : System) (w : Word T) :
    SpecMatches (rawWordSpec (parameterData T) (wordList w)) (ordinaryCycle T) (ordinaryCycleLabels w) := by
  constructor
  · intro j
    let n := (columnResidueEquiv T).symm j
    have hn : ((channelEquiv T) (ordinaryCycle T j)).val = n.val := by rfl
    rw [hn,rawWordSpec_get T _ _ (by omega),if_pos n.isLt,predecessor_value]
    have hd := denseChannelKey_eq T (ordinaryCycle T (j-1))
    change denseChannelKey T.width ((columnResidueEquiv T).symm (j-1)).val = _ at hd
    rw [hd]
    apply congrArg (fun a => (true,channelKey (ordinaryCycle T (j-1)),a))
    simp only [wordList,List.getD_eq_getElem?_getD,List.getElem?_ofFn,dif_pos n.isLt,Option.getD_some]
    rfl
  · intro i hi
    cases i with
    | inl n =>
      apply False.elim
      apply hi (columnResidueEquiv T n)
      change Sum.inl ((columnResidueEquiv T).symm (columnResidueEquiv T n)) = Sum.inl n
      rw [Equiv.symm_apply_apply]
    | inr t =>
      have hn : ((channelEquiv T) (Sum.inr t)).val = T.width + t.val := by rfl
      rw [hn,rawWordSpec_get T _ _ (by omega),if_neg (by omega)]

theorem rawSeedSpec_get (T : System) (t n j k : ℕ) (hk : k < T.width + 2) :
    (rawSeedSpec (parameterData T) t n j).getD k (false,0,0) =
      if k = T.width + t then (true,denseChannelKey T.width n,0)
      else if k = n then (true,Nat.pair 1 t,j)
      else (false,denseChannelKey T.width k,0) := by
  have hd : (parameterData T).1 = T.width := rfl
  simp only [rawSeedSpec,hd,List.getD_eq_getElem?_getD,List.getElem?_map,
    List.getElem?_range hk,Option.map_some,Option.getD_some]

theorem rawSeedSpec_matches (T : System) (t : Fin 2) (n : Column T) (j : Symbol T) :
    SpecMatches (rawSeedSpec (parameterData T) t.val n.val j.val)
      (seedCycle t n) (seedCycleLabels t n j) := by
  constructor
  · intro z
    fin_cases z
    · change (rawSeedSpec (parameterData T) t.val n.val j.val).getD (T.width+t.val) (false,0,0) =
        (true,channelKey (Sum.inl n : Channel T),0)
      rw [rawSeedSpec_get T _ _ _ _ (by omega),if_pos rfl]
      have hd := denseChannelKey_eq T (Sum.inl n)
      change denseChannelKey T.width n.val = _ at hd
      rw [hd]
    · change (rawSeedSpec (parameterData T) t.val n.val j.val).getD n.val (false,0,0) =
        (true,Nat.pair 1 t.val,j.val)
      rw [rawSeedSpec_get T _ _ _ _ (by omega),if_neg (by omega),if_pos rfl]
  · intro i hi
    have hs := hi 0
    have hn := hi 1
    cases i with
    | inl m =>
      have hv : ((channelEquiv T) (Sum.inl m)).val = m.val := by rfl
      have hmn : m.val ≠ n.val := fun he => hn (congrArg Sum.inl (Fin.ext he).symm)
      rw [hv,rawSeedSpec_get T _ _ _ _ (by omega),if_neg (by omega),if_neg hmn]
    | inr s =>
      have hv : ((channelEquiv T) (Sum.inr s)).val = T.width + s.val := by rfl
      have hst : s.val ≠ t.val := fun he => hs (congrArg Sum.inr (Fin.ext he).symm)
      rw [hv,rawSeedSpec_get T _ _ _ _ (by omega),if_neg (by omega),if_neg (by omega)]

end
end TranslationTiling.FiniteCompiler.Effective
