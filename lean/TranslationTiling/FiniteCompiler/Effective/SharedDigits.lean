import TranslationTiling.FiniteCompiler.Effective.SharedDeckDependence

namespace TranslationTiling.FiniteCompiler.Packed

open Effective SharedCoordinates
open scoped Classical BigOperators
noncomputable section

variable {k : ℕ} (i : SharedRow k)

abbrev SharedLabel := Fin (rowDigits (sharedRows k) i).length

def sharedDigit (j : SharedLabel i) : ℕ := (rowDigits (sharedRows k) i)[j.val]

private theorem sharedDigits_memFactors {p : ℕ} (h : p ∈ rowDigits (sharedRows k) i) :
    p ∈ rowFactors (sharedLayout k) (fun j => rowDigits (sharedRows k) j) i :=
  List.mem_append_left _ (List.mem_append_left _ h)

theorem sharedDigit_prime (j : SharedLabel i) : (sharedDigit i j).Prime :=
  sharedRowFactors_prime i _ (sharedDigits_memFactors i (List.getElem_mem j.isLt))

theorem sharedDigits_nodup : (rowDigits (sharedRows k) i).Nodup :=
  (List.nodup_append'.mp (List.nodup_append'.mp (sharedRowFactors_nodup i)).1).1

theorem sharedDigits_prod : ∏ j : SharedLabel i, sharedDigit i j = (sharedLayout k).lowSize i := by
  rw [← Fin.prod_ofFn]
  congr 1
  apply List.ext_getElem
  · simp
  · intro j hj hj'
    simp only [List.getElem_ofFn,sharedDigit]

def sharedDigitCRT : SharedCoordinates.Low (sharedLayout k) i ≃+* (∀ j : SharedLabel i, ZMod (sharedDigit i j)) := by
  unfold SharedCoordinates.Low
  rw [← sharedDigits_prod i]
  apply ZMod.prodEquivPi
  intro j l hne
  apply (Nat.coprime_primes (sharedDigit_prime i j) (sharedDigit_prime i l)).mpr
  intro h
  apply hne
  exact (List.nodup_iff_injective_get.mp (sharedDigits_nodup i)) (by exact h)

def sharedDigitSubgroup (j : SharedLabel i) :
    AddSubgroup (SharedCoordinates.Low (sharedLayout k) i) where
  carrier := {x | ∀ l : SharedLabel i, l ≠ j → sharedDigitCRT i x l = 0}
  zero_mem' := fun l _ => by simp
  add_mem' := fun {_ _} hx hy l hl => by simpa only [map_add,Pi.add_apply,hx l hl,hy l hl,add_zero]
  neg_mem' := fun {_} hx l hl => by simp only [map_neg,Pi.neg_apply,hx l hl,neg_zero]

@[simp] theorem sharedDigitSubgroup_iff (j : SharedLabel i) (x : SharedCoordinates.Low (sharedLayout k) i) :
    x ∈ sharedDigitSubgroup i j ↔ ∀ l : SharedLabel i, l ≠ j → sharedDigitCRT i x l = 0 := Iff.rfl

theorem sharedDigitSubgroup_sub (j : SharedLabel i) (x y : SharedCoordinates.Low (sharedLayout k) i) :
    x - y ∈ sharedDigitSubgroup i j ↔
      ∀ l : SharedLabel i, l ≠ j → sharedDigitCRT i x l = sharedDigitCRT i y l := by
  simp only [sharedDigitSubgroup_iff,map_sub,Pi.sub_apply,sub_eq_zero]

def sharedStep (j : SharedLabel i) : ℕ := (sharedLayout k).lowSize i / sharedDigit i j

theorem sharedStep_mem (j : SharedLabel i) :
    (sharedStep i j : SharedCoordinates.Low (sharedLayout k) i) ∈ sharedDigitSubgroup i j := by
  have hp := sharedDigit_prime i j
  have hr : sharedStep i j = ∏ l ∈ (Finset.univ.erase j), sharedDigit i l := by
    unfold sharedStep
    rw [← sharedDigits_prod i,← Finset.prod_erase_mul _ _ (Finset.mem_univ j)]
    exact Nat.mul_div_cancel _ hp.pos
  intro l hl
  rw [map_natCast]
  change (sharedStep i j : ZMod (sharedDigit i l)) = 0
  apply (ZMod.natCast_eq_zero_iff _ _).mpr
  rw [hr]
  exact Finset.dvd_prod_of_mem _ (Finset.mem_erase.mpr ⟨hl,Finset.mem_univ _⟩)

private theorem sharedStep_ne (j : SharedLabel i) :
    (sharedStep i j : SharedCoordinates.Low (sharedLayout k) i) ≠ 0 := by
  have hp := sharedDigit_prime i j
  have h := (sharedLayout k).lowSize_pos i
  have hd : sharedDigit i j ∣ (sharedLayout k).lowSize i := by
    rw [← sharedDigits_prod i]
    exact Finset.dvd_prod_of_mem _ (Finset.mem_univ j)
  intro he
  exact Nat.not_dvd_of_pos_of_lt (Nat.div_pos (Nat.le_of_dvd h hd) hp.pos)
    (Nat.div_lt_self h hp.one_lt) ((ZMod.natCast_eq_zero_iff _ _).mp he)

theorem sharedStep_spans (j : SharedLabel i)
    (u : SharedCoordinates.Low (sharedLayout k) i) (hu : u ∈ sharedDigitSubgroup i j) :
    ∃ n : ℕ, n • (sharedStep i j : SharedCoordinates.Low (sharedLayout k) i) = u := by
  let : Fact (sharedDigit i j).Prime := ⟨sharedDigit_prime i j⟩
  let g : SharedCoordinates.Low (sharedLayout k) i := sharedStep i j
  let v := sharedDigitCRT i g j
  have hv : v ≠ 0 := by
    intro he
    apply sharedStep_ne i j
    apply (sharedDigitCRT i).injective
    funext l
    by_cases hl : l=j
    · subst l; simpa only [map_zero,Pi.zero_apply] using he
    · simpa only [map_zero,Pi.zero_apply] using sharedStep_mem i j l hl
  let a := sharedDigitCRT i u j / v
  refine ⟨a.val,?_⟩
  apply (sharedDigitCRT i).injective
  funext l
  simp only [map_nsmul,Pi.smul_apply]
  by_cases hl : l=j
  · subst l
    change a.val • v = sharedDigitCRT i u j
    rw [nsmul_eq_mul,ZMod.natCast_zmod_val]
    exact div_mul_cancel₀ _ hv
  · rw [sharedStep_mem i j l hl,hu l hl,nsmul_zero]

end
end TranslationTiling.FiniteCompiler.Packed
