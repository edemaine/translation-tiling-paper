import TranslationTiling.FiniteCompiler.Effective.FourValueDependence

namespace TranslationTiling.FiniteCompiler.Packed

open Effective SharedCoordinates
open scoped Classical BigOperators
noncomputable section

variable {k : ℕ} (i : FourValueRow k)

abbrev FourValueLabel := Fin (rowDigits (fourValueRows k) i).length

def fourValueDigit (j : FourValueLabel i) : ℕ := (rowDigits (fourValueRows k) i)[j.val]

private theorem fourValueDigits_memFactors {p : ℕ} (h : p ∈ rowDigits (fourValueRows k) i) :
    p ∈ rowFactorsWith (fourValueLayout k) (fun j => rowDigits (fourValueRows k) j) (fourValueSecondFactors k) i :=
  List.mem_append_left _ (List.mem_append_left _ h)

theorem fourValueDigit_prime (j : FourValueLabel i) : (fourValueDigit i j).Prime :=
  fourValueRowFactors_prime i _ (fourValueDigits_memFactors i (List.getElem_mem j.isLt))

theorem fourValueDigits_nodup : (rowDigits (fourValueRows k) i).Nodup :=
  (List.nodup_append'.mp (List.nodup_append'.mp (fourValueRowFactors_nodup i)).1).1

theorem fourValueDigits_prod : ∏ j : FourValueLabel i, fourValueDigit i j = (fourValueLayout k).lowSize i := by
  rw [← Fin.prod_ofFn]
  congr 1
  apply List.ext_getElem
  · simp
  · intro j hj hj'
    simp only [List.getElem_ofFn,fourValueDigit]

def fourValueDigitCRT : SharedCoordinates.Low (fourValueLayout k) i ≃+* (∀ j : FourValueLabel i, ZMod (fourValueDigit i j)) := by
  unfold SharedCoordinates.Low
  rw [← fourValueDigits_prod i]
  apply ZMod.prodEquivPi
  intro j l hne
  apply (Nat.coprime_primes (fourValueDigit_prime i j) (fourValueDigit_prime i l)).mpr
  intro h
  apply hne
  exact (List.nodup_iff_injective_get.mp (fourValueDigits_nodup i)) (by exact h)

def fourValueDigitSubgroup (j : FourValueLabel i) :
    AddSubgroup (SharedCoordinates.Low (fourValueLayout k) i) where
  carrier := {x | ∀ l : FourValueLabel i, l ≠ j → fourValueDigitCRT i x l = 0}
  zero_mem' := fun l _ => by simp
  add_mem' := fun {_ _} hx hy l hl => by simpa only [map_add,Pi.add_apply,hx l hl,hy l hl,add_zero]
  neg_mem' := fun {_} hx l hl => by simp only [map_neg,Pi.neg_apply,hx l hl,neg_zero]

@[simp] theorem fourValueDigitSubgroup_iff (j : FourValueLabel i) (x : SharedCoordinates.Low (fourValueLayout k) i) :
    x ∈ fourValueDigitSubgroup i j ↔ ∀ l : FourValueLabel i, l ≠ j → fourValueDigitCRT i x l = 0 := Iff.rfl

theorem fourValueDigitSubgroup_sub (j : FourValueLabel i) (x y : SharedCoordinates.Low (fourValueLayout k) i) :
    x - y ∈ fourValueDigitSubgroup i j ↔
      ∀ l : FourValueLabel i, l ≠ j → fourValueDigitCRT i x l = fourValueDigitCRT i y l := by
  simp only [fourValueDigitSubgroup_iff,map_sub,Pi.sub_apply,sub_eq_zero]

def fourValueStep (j : FourValueLabel i) : ℕ := (fourValueLayout k).lowSize i / fourValueDigit i j

theorem fourValueStep_mem (j : FourValueLabel i) :
    (fourValueStep i j : SharedCoordinates.Low (fourValueLayout k) i) ∈ fourValueDigitSubgroup i j := by
  have hp := fourValueDigit_prime i j
  have hr : fourValueStep i j = ∏ l ∈ (Finset.univ.erase j), fourValueDigit i l := by
    unfold fourValueStep
    rw [← fourValueDigits_prod i,← Finset.prod_erase_mul _ _ (Finset.mem_univ j)]
    exact Nat.mul_div_cancel _ hp.pos
  intro l hl
  rw [map_natCast]
  change (fourValueStep i j : ZMod (fourValueDigit i l)) = 0
  apply (ZMod.natCast_eq_zero_iff _ _).mpr
  rw [hr]
  exact Finset.dvd_prod_of_mem _ (Finset.mem_erase.mpr ⟨hl,Finset.mem_univ _⟩)

private theorem fourValueStep_ne (j : FourValueLabel i) :
    (fourValueStep i j : SharedCoordinates.Low (fourValueLayout k) i) ≠ 0 := by
  have hp := fourValueDigit_prime i j
  have h := (fourValueLayout k).lowSize_pos i
  have hd : fourValueDigit i j ∣ (fourValueLayout k).lowSize i := by
    rw [← fourValueDigits_prod i]
    exact Finset.dvd_prod_of_mem _ (Finset.mem_univ j)
  intro he
  exact Nat.not_dvd_of_pos_of_lt (Nat.div_pos (Nat.le_of_dvd h hd) hp.pos)
    (Nat.div_lt_self h hp.one_lt) ((ZMod.natCast_eq_zero_iff _ _).mp he)

theorem fourValueStep_spans (j : FourValueLabel i)
    (u : SharedCoordinates.Low (fourValueLayout k) i) (hu : u ∈ fourValueDigitSubgroup i j) :
    ∃ n : ℕ, n • (fourValueStep i j : SharedCoordinates.Low (fourValueLayout k) i) = u := by
  let : Fact (fourValueDigit i j).Prime := ⟨fourValueDigit_prime i j⟩
  let g : SharedCoordinates.Low (fourValueLayout k) i := fourValueStep i j
  let v := fourValueDigitCRT i g j
  have hv : v ≠ 0 := by
    intro he
    apply fourValueStep_ne i j
    apply (fourValueDigitCRT i).injective
    funext l
    by_cases hl : l=j
    · subst l; simpa only [map_zero,Pi.zero_apply] using he
    · simpa only [map_zero,Pi.zero_apply] using fourValueStep_mem i j l hl
  let a := fourValueDigitCRT i u j / v
  refine ⟨a.val,?_⟩
  apply (fourValueDigitCRT i).injective
  funext l
  simp only [map_nsmul,Pi.smul_apply]
  by_cases hl : l=j
  · subst l
    change a.val • v = fourValueDigitCRT i u j
    rw [nsmul_eq_mul,ZMod.natCast_zmod_val]
    exact div_mul_cancel₀ _ hv
  · rw [fourValueStep_mem i j l hl,hu l hl,nsmul_zero]

end
end TranslationTiling.FiniteCompiler.Packed
