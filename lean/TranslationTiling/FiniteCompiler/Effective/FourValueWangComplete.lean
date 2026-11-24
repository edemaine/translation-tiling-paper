import TranslationTiling.FiniteCompiler.Effective.FourValueWangCoordinates

namespace TranslationTiling.FiniteCompiler.Packed

open Compiler SharedCoordinates
open scoped Classical

noncomputable section

set_option maxRecDepth 2500
set_option maxHeartbeats 3000000

attribute [local irreducible] wangValueModulus fourValueLow fourValueOutput

abbrev WangChoice := {j : FourValueShift.Index // j ≠ 0}

def wangBlockOutput {k : ℕ} (w : WangDigitRow k) (j : WangChoice)
    (d : SharedCoordinates.Low (fourValueLayout k) (wangDigitRow w)) :
    WangShift w :=
  match (wangBlocks w j.val j.property).decode d with
  | .inl (_,y) => FourValueShift.blockOutput (m := wangValueModulus w) 0 y
  | .inr (_,y) => FourValueShift.blockOutput (m := wangValueModulus w) j.val y

def wangBlockHigh {k : ℕ} (w : WangDigitRow k) (j : WangChoice) (p : ℤ)
    (d : SharedCoordinates.Low (fourValueLayout k) (wangDigitRow w)) :
    SharedCoordinates.Low (fourValueLayout k) (wangDigitRow w) :=
  (wangBlocks w j.val j.property).T p d

theorem wang_block_active {k : ℕ} (w : WangDigitRow k) (j u : WangChoice) :
    (¬ ∃ t, ∀ d, wangBlockOutput w j d u.val = t) ↔ u = j := by
  constructor
  · intro h
    by_contra hn
    apply h
    refine ⟨0,fun d => ?_⟩
    unfold wangBlockOutput
    have huv : u.val ≠ j.val := fun e => hn (Subtype.ext e)
    cases hd : (wangBlocks w j.val j.property).decode d with
    | inl a => simp only [hd,FourValueShift.blockOutput,Function.update_of_ne u.property,Pi.zero_apply]
    | inr a => simp only [hd,FourValueShift.blockOutput,Function.update_of_ne huv,Pi.zero_apply]
  · intro huv
    subst u
    rintro ⟨t,ht⟩
    let D := wangBlocks w j.val j.property
    let index : Fin (wangValueModulus_representation w j.val j.property).choose_spec.choose :=
      ⟨0,(wangValueModulus_representation w j.val j.property).choose_spec.choose_spec.2.1⟩
    have out (y : ZMod (wangValueModulus w j.val)) :
        wangBlockOutput w j (D.decode.symm (.inr (index,y))) j.val = y := by
      unfold wangBlockOutput
      change (match D.decode (D.decode.symm (.inr (index,y))) with
        | .inl (_,q) => FourValueShift.blockOutput (m := wangValueModulus w) 0 q
        | .inr (_,q) => FourValueShift.blockOutput (m := wangValueModulus w) j.val q) j.val = y
      rw [D.decode.apply_symm_apply] <;> exact Function.update_self _ _ _
    have h₀ := (out 0).symm.trans (ht (D.decode.symm (.inr (index,0))))
    have h₁ := (out 1).symm.trans (ht (D.decode.symm (.inr (index,1))))
    letI : Fact (1 < wangValueModulus w j.val) := ⟨wangValueModulus_big w j.val⟩
    exact zero_ne_one (h₀.trans h₁.symm)


theorem fourValue_wang_complete {k : ℕ} (w : WangDigitRow k) (o : FourValueOutputGraph k)
    (hmodel : ∀ x : FourValueBase k, ∃ (j : WangChoice) (shift : WangShift w),
      ∀ v : WangActivationIndex w,
        let src := wangActivationSource w x v
        wangActivationProjection w (SharedCoordinates.point (fourValueLayout k) o src).2 =
          wangBlockOutput w j (src.2 (wangDigitRow w)) + shift ∧
        o.high src (wangDigitRow w) =
          wangBlockHigh w j src.1.1 (src.2 (wangDigitRow w))) :
    Tiles ((fourValueWangActivation k w).toFinset.image (decodePoint (fourValueLayout k)))
      (Set.range (SharedCoordinates.point (fourValueLayout k) o)) := by
  apply (fourValueWangActivation_iff w o).mpr
  intro x
  obtain ⟨j,c,hj⟩ := hmodel x
  let e := (wangLowEquiv w).toEquiv.prodCongr (Equiv.refl (WangShift w))
  let H (u : SharedCoordinates.Low (fourValueLayout k) (wangDigitRow w) × WangShift w) :=
    (wangRecordHorizontal w (e.symm u)).1
  have hH (u : SharedCoordinates.Low (fourValueLayout k) (wangDigitRow w) × WangShift w)
      (i : FourValueShift.Index) :
      (H u : ZMod (wangValueModulus w i)) = u.2 i -
        FourValueShift.shift (m := wangValueModulus w) u.2 i :=
    wangRecordShift w (e.symm u) i
  have hbij := FourValueShift.partition_bijective (m := wangValueModulus w)
    (wangValueModulus_big w) j.val (wangBlocks w j.val j.property) x.1.1
    (x.2 (wangDigitRow w)) H hH
  have htrans := ((Equiv.addRight c).prodCongr (Equiv.refl _)).bijective.comp (hbij.comp e.bijective)
  convert htrans using 2
  rename_i v
  simp only [Function.comp_apply]
  have hs := hj v
  dsimp only at hs
  rw [hs.1,hs.2,wangActivationSource_self]
  have he : H (e v) = (wangRecordHorizontal w v).1 := by simp [H]
  rw [he]
  have efst : (e v).1 = wangLowEquiv w v.1 := rfl
  have esnd : (e v).2 = v.2 := rfl
  have hpos : (wangActivationSource w x v).1.1 = x.1.1-(wangRecordHorizontal w v).1 := rfl
  rw [efst,esnd,hpos]
  have hpair (y : WangShift w × SharedCoordinates.Low (fourValueLayout k) (wangDigitRow w)) :
      (Equiv.prodCongr (Equiv.addRight c) (Equiv.refl _)) y = (y.1 + c,y.2) := rfl
  rw [hpair]
  apply Prod.ext
  · unfold wangBlockOutput
    cases (wangBlocks w j.val j.property).decode (x.2 (wangDigitRow w) - wangLowEquiv w v.1) <;>
      funext i <;> simp only [Pi.add_apply,FourValueShift.blockOutput] <;> abel
  · rfl

end
end TranslationTiling.FiniteCompiler.Packed
