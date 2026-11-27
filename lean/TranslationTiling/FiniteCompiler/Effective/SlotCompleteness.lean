import TranslationTiling.FiniteCompiler.Effective.SlotDecode
import TranslationTiling.FiniteCompiler.Effective.SlotModelDependence
import TranslationTiling.FiniteCompiler.Effective.SlotModelActivation

namespace TranslationTiling.FiniteCompiler.Packed.SlotParameters

open PairSmall GuardedCompiler SharedCoordinates Effective
open scoped Classical
noncomputable section

local instance slotCompletenessFrame : SeedFrame := compactSeedFrame
set_option maxRecDepth 5000

variable {k m w : ℕ} {T : LeanWang.TileSet} (c : Code T ((slotRadix m w)^k))
local instance slotCompletenessAlphabet : AlphabetFamily (system c) := GuardedCompiler.alphabet c

def arithmeticPicker (W : WordArray (system c)) : FourValuePicker 0 where
  fixed i hi z :=
    let j : Fin 18 := ⟨i.val,hi⟩
    (show arithmeticRow j = i from Fin.ext rfl) ▸ arithmeticLetterEquiv c j (W (arithmeticColumn j) z)
  wang a _ := Fin.elim0 a

def wordPicker (W : WordArray (system c)) : SlotPicker k m :=
  fun (g,d,i) z => slotState (wangLetterEquiv c g (W (wangColumn g) z) d) i

variable (s : SlotParameters k m)

theorem slice_model (old : FourValueOutputGraph 0) (pick : SlotPicker k m) (v : s.ExtraLow) :
    s.oldSlice (s.slotModel old pick) v = old :=
  rfl

theorem model_dependencies (pick₀ : FourValuePicker 0) (pick : SlotPicker k m) :
    s.cycleDependencies (s.slotModel (fourValueModel pick₀) pick) := by
  let o₀ := fourValueModel pick₀
  let o := s.slotModel o₀ pick
  refine ⟨?_,?_,s.model_markerTests o₀ pick⟩
  · intro F hF
    obtain ⟨f,hf,rfl⟩ := List.mem_map.mp hF
    apply (s.oldTileLift_iff _ o).mpr
    intro v
    rw [s.slice_model o₀ pick v]
    obtain ⟨⟨d,G⟩,hrecord,rfl⟩ := List.mem_map.mp hf
    apply (fourValueHolds_shift d G o₀).mpr
    apply fourValueBaseline_holds 0 pick₀ G
    apply List.mem_cons_of_mem
    rw [← arithmeticMaskRecords_original]
    exact List.mem_map.mpr ⟨(d,G),hrecord,rfl⟩
  · intro F hF
    obtain ⟨⟨i,j⟩,_,rfl⟩ := List.mem_map.mp hF
    apply (productInvariance_iff _ _ _ o).mpr
    intro x
    change o₀.privateOutput (s.oldBase (x-lowStep s.layout (.inr j))) i =
      o₀.privateOutput (s.oldBase x) i
    have he : s.oldBase (x-lowStep s.layout (.inr j)) = s.oldBase x := by
      refine Prod.ext (by simp [oldBase,lowStep]) (funext fun a => ?_)
      simp [oldBase,lowStep]
      rfl
    rw [he]

theorem model_activations (W : WordArray (system c)) (hw : w ≤ m) :
    s.activationHolds (s.slotModel (fourValueModel (arithmeticPicker c W)) (wordPicker c W)) hw := by
  intro g d S hS
  have := shiftCount_neZero (selected_nonempty hw hS)
  change Tiles (s.mask g d S) _
  apply s.model_mask
  intro x
  exact slotState_meets hw (wangLetterEquiv c g (W (wangColumn g) (slotLine g x)) d) S hS

theorem model_letter (W : WordArray (system c)) (x : Plane)
    (i : Fin 18 ⊕ Bool) (a : Letter (system c) (columnIndex i)) :
    s.letterActive c (s.slotModel (fourValueModel (arithmeticPicker c W)) (wordPicker c W)) x i a ↔
      a = W (columnIndex i) (lineValue (system c) (columnIndex i) x) := by
  let p := arithmeticPicker c W
  let o := fourValueModel p
  let q := wordPicker c W
  rcases i with i | g
  · let v := arithmeticRow i
    change DigitActive (fourValuePrivateAt (s.oldSlice (s.slotModel o q) 0) x v)
      (fourValueDigitSubgroup v (arithmeticLetterEquiv c i a)) ↔ _
    rw [s.slice_model o q 0,fourValueModel_fixed_active p v i.isLt,arithmeticLine c]
    change arithmeticLetterEquiv c i a =
      arithmeticLetterEquiv c i (W (arithmeticColumn i) (lineValue (system c) (arithmeticColumn i) x)) ↔ _
    exact (arithmeticLetterEquiv c i).injective.eq_iff
  · let b := W (wangColumn g) (lineValue (system c) (wangColumn g) x)
    change (∀ d, SlotWords.Reads (s.Active (s.slotModel o q) g d (slotLine g x))
      (wangLetterEquiv c g a d)) ↔ a = b
    have he (d : Fin k) (i : Fin m) (j : Fin 3) :
        s.Active (s.slotModel o q) g d (slotLine g x) i j ↔
          SlotWords.Uses (wangLetterEquiv c g b d) i j := by
      rw [s.model_marker_active o q]
      change slotState (wangLetterEquiv c g (W (wangColumn g) (slotLine g x)) d) i = some j ↔ _
      rw [wangLine c,slotState_uses]
    constructor
    · intro h
      apply (wangLetterEquiv c g).injective
      funext d
      symm
      apply (SlotWords.reads_uses_iff _ _).mp
      exact fun i => (he d i.val _).mp (h d i)
    · rintro rfl d i
      exact (he d i.val _).mpr ⟨i.property,rfl⟩

end
end TranslationTiling.FiniteCompiler.Packed.SlotParameters
