import TranslationTiling.FiniteCompiler.Effective.Specifications

/-! Numerical serialization of an arbitrary injective exclusion cycle. -/
namespace TranslationTiling.FiniteCompiler.Effective
open Compiler.Effective
open scoped Classical
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def rawCycleSpec (d : ParameterData) (keys labs : List ℕ) : List NumericalSpec :=
  (List.range (d.1+2)).map fun k =>
    let j := keys.idxOf (denseChannelKey d.1 k)
    if j<keys.length then
      (true,keys.getD (differenceResidue keys.length j 1) 0,labs.getD j 0)
    else (false,0,0)

@[fun_prop] theorem rawCycleSpec_primrec :
    Primrec (fun d : ParameterData × List ℕ × List ℕ => rawCycleSpec d.1 d.2.1 d.2.2) := by
  unfold rawCycleSpec
  fun_prop

def cycleKeys {T : System} {m : ℕ} (cy : ZMod (m+1) ↪ Channel T) : List ℕ :=
  List.ofFn fun j : Fin (m+1) => channelKey (cy j)

def cycleLabels {T : System} {m : ℕ} (cy : ZMod (m+1) ↪ Channel T)
    (lab : ∀ j, Label T (cy j)) : List ℕ :=
  List.ofFn fun j : Fin (m+1) => labelKey (cy j) (lab j)

private theorem cycleKeys_idx {T : System} {m : ℕ}
    (cy : ZMod (m+1) ↪ Channel T) (j : ZMod (m+1)) :
    (cycleKeys cy).idxOf (channelKey (cy j))=j.val := by
  have hd : (cycleKeys cy).Nodup := List.nodup_ofFn.mpr (by
    intro a b h
    exact cy.injective (channelKey_injective T h))
  have h := hd.idxOf_getElem j.val (by simpa only [cycleKeys,List.length_ofFn] using (ZMod.val_lt j))
  have hj : (⟨j.val,ZMod.val_lt j⟩ : Fin (m+1))=j := by rfl
  simpa only [cycleKeys,List.getElem_ofFn,hj] using h

private theorem cycleKeys_get {T : System} {m : ℕ}
    (cy : ZMod (m+1) ↪ Channel T) (j : ZMod (m+1)) :
    (cycleKeys cy).getD j.val 0=channelKey (cy j) := by
  simp only [cycleKeys,List.getD_eq_getElem?_getD,List.getElem?_ofFn,dif_pos (ZMod.val_lt j),Option.getD_some]
  rfl

private theorem cycleLabels_get {T : System} {m : ℕ}
    (cy : ZMod (m+1) ↪ Channel T) (lab : ∀ j, Label T (cy j)) (j : ZMod (m+1)) :
    (cycleLabels cy lab).getD j.val 0=labelKey (cy j) (lab j) := by
  simp only [cycleLabels,List.getD_eq_getElem?_getD,List.getElem?_ofFn,dif_pos (ZMod.val_lt j),Option.getD_some]
  rfl

theorem rawCycleSpec_matches {T : System} {m : ℕ}
    (cy : ZMod (m+1) ↪ Channel T) (lab : ∀ j, Label T (cy j)) :
    SpecMatches (rawCycleSpec (parameterData T) (cycleKeys cy) (cycleLabels cy lab)) cy lab := by
  have hg (i : Channel T) :
      (rawCycleSpec (parameterData T) (cycleKeys cy) (cycleLabels cy lab)).getD
        ((channelEquiv T) i).val (false,0,0) =
      let j := (cycleKeys cy).idxOf (channelKey i)
      if j<m+1 then
        (true,(cycleKeys cy).getD (differenceResidue (m+1) j 1) 0,
          (cycleLabels cy lab).getD j 0)
      else (false,0,0) := by
    have hk := ((channelEquiv T) i).isLt
    have hd : (parameterData T).1=T.width := rfl
    simp only [rawCycleSpec,hd,List.getD_eq_getElem?_getD,List.getElem?_map,
      List.getElem?_range hk,Option.map_some,Option.getD_some,denseChannelKey_eq,
      cycleKeys,List.length_ofFn]
  constructor
  · intro j
    rw [hg,cycleKeys_idx]
    dsimp only
    rw [if_pos (ZMod.val_lt j)]
    have hp : differenceResidue (m+1) j.val 1=(j-1).val := by
      rw [differenceResidue_eq,ZMod.natCast_zmod_val,Nat.cast_one]
    rw [hp,cycleKeys_get,cycleLabels_get]
  · intro i hi
    rw [hg]
    have hn : ¬(cycleKeys cy).idxOf (channelKey i)<m+1 := by
      intro h
      have hm : channelKey i∈cycleKeys cy := List.idxOf_lt_length_iff.mp (by simpa [cycleKeys] using h)
      obtain ⟨j,hj⟩ := List.mem_ofFn.mp hm
      exact hi j (channelKey_injective T hj)
    rw [if_neg hn]

end
end TranslationTiling.FiniteCompiler.Effective
