import TranslationTiling.FiniteCompiler.Effective.SharedOrdinaryCorrect
import TranslationTiling.FiniteCompiler.ChannelDigitBlocks

namespace TranslationTiling.FiniteCompiler.Packed

open Compiler.Effective Effective SharedCoordinates
open scoped Classical
noncomputable section

set_option maxRecDepth 10000

variable {k : ℕ} (i : SharedRow k) (hi : i.val < (sharedRows k).length-2)

include hi in
theorem sharedDigit_representation (j : SharedLabel i) :
    ∃ A B : ℕ, 0 < A ∧ 0 < B ∧ sharedDigit i j = A*OrdinaryA i+B*OrdinaryB i := by
  let ds := rowDigits (sharedRows k) i
  have hm : ds[j.val] ∈ ds := List.getElem_mem j.isLt
  have haux : sharedDigit i j = ds[j.val] := rfl
  rw [haux]
  generalize hd : ds[j.val] = d at hm ⊢
  change d ∈ ((sharedRows k).getD i.val (0,0,[])).2.2 at hm
  unfold OrdinaryA OrdinaryB rowA rowB
  by_cases hf : i.val < 18
  · rw [sharedRows_fixed_at hf] at hm ⊢
    change d ∈ (profile1.row i.val).map Prod.fst at hm
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hm
    have h := (profile1_valid.2.2.2.2.1 i.val
      (List.mem_range.mpr (by have hw : profile1.width = 20 := rfl; omega))).2 v hv
    exact ⟨v.2.1,v.2.2,h⟩
  · let j' := i.val-18
    have hj' : j' < 2*k := by have := sharedRows_length k; dsimp [j']; omega
    have e : 18+j' = i.val := by dsimp [j']; omega
    have he := sharedRows_wang_at hj'
    rw [e] at he
    rw [he] at hm ⊢
    exact sharedWangRow_representation hj' hm

def sharedBlockCount (j : SharedLabel i) : ℕ × ℕ :=
  ((sharedDigit_representation i hi j).choose,
    (sharedDigit_representation i hi j).choose_spec.choose)

theorem sharedBlockCount_spec (j : SharedLabel i) :
    let c := sharedBlockCount i hi j
    0 < c.1 ∧ 0 < c.2 ∧ sharedDigit i j = c.1*OrdinaryA i + c.2*OrdinaryB i :=
  (sharedDigit_representation i hi j).choose_spec.choose_spec

def sharedBaseBlocks (j : SharedLabel i) : LabeledBlocks (ZMod (sharedDigit i j))
    (Fin (sharedBlockCount i hi j).1) (Fin (sharedBlockCount i hi j).2)
    (OrdinaryA i) (OrdinaryB i) := by
  letI : NeZero (OrdinaryA i) := ⟨(ordinaryPairFacts i hi).firstPrime.ne_zero⟩
  letI : NeZero (sharedDigit i j) := ⟨(sharedDigit_prime i j).ne_zero⟩
  exact LabeledBlocks.digit _ _ _ _ _ (sharedBlockCount_spec i hi j).2.2

abbrev SharedOtherDigits (j : SharedLabel i) :=
  ∀ q : {q : SharedLabel i // q ≠ j}, ZMod (sharedDigit i q)

def sharedBlocks (j : SharedLabel i) :
    LabeledBlocks (RowLow i) (Fin (sharedBlockCount i hi j).1 × SharedOtherDigits i j)
      (Fin (sharedBlockCount i hi j).2 × SharedOtherDigits i j) (OrdinaryA i) (OrdinaryB i) :=
  (LabeledBlocks.onCoordinate (fun q => ZMod (sharedDigit i q)) j (sharedBaseBlocks i hi j)).transport
    (sharedDigitCRT i).toEquiv

@[simp] theorem sharedBlocks_C (j : SharedLabel i) (w : RowLow i) :
    (sharedBlocks i hi j).C w = (sharedBaseBlocks i hi j).C (sharedDigitCRT i w j) := by
  simp [sharedBlocks]

theorem sharedBlocks_active (j q : SharedLabel i) :
    DigitActive (fun w => ((sharedBlocks i hi j).C w).2) (sharedDigitSubgroup i q) ↔ q = j := by
  constructor
  · rintro ⟨w,w',hw,hn⟩
    by_contra hj
    apply hn
    simp only [sharedBlocks_C]
    rw [(sharedDigitSubgroup_sub i q w w').mp hw j (Ne.symm hj)]
  · intro h
    subst q
    let c : Fin (sharedBlockCount i hi j).2 := ⟨0,(sharedBlockCount_spec i hi j).2.1⟩
    obtain ⟨u,hu⟩ := (sharedBaseBlocks i hi j).privateOutput_surjective c 0
    obtain ⟨v,hv⟩ := (sharedBaseBlocks i hi j).privateOutput_surjective c 1
    let U := (sharedDigitCRT i).symm (Pi.single j u)
    let V := (sharedDigitCRT i).symm (Pi.single j v)
    refine ⟨U,V,(sharedDigitSubgroup_sub i j U V).mpr ?_,?_⟩
    · intro l hl
      simp [U,V,Pi.single_eq_of_ne hl]
    · letI : Fact (1 < OrdinaryB i) := ⟨(ordinaryPairFacts i hi).secondPrime.one_lt⟩
      simpa [U,V,hu,hv] using (zero_ne_one : (0 : ZMod (OrdinaryB i)) ≠ 1)

end
end TranslationTiling.FiniteCompiler.Packed
