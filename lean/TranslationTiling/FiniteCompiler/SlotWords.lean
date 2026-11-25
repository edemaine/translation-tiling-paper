import Mathlib.Algebra.BigOperators.Ring.Nat
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.Ring

namespace TranslationTiling.FiniteCompiler.SlotWords

open scoped Classical BigOperators

/-- A word chooses exactly `w` slots and gives each a label in `Fin q`. -/
abbrev Word (m w q : ℕ) :=
  Σ S : {S : Finset (Fin m) // S.card = w}, (↑S.val : Type) → Fin q

variable {m w q : ℕ}

/-- Every selected label is active in the slot assigned to it. -/
def Reads (active : Fin m → Fin q → Prop) (v : Word m w q) : Prop :=
  ∀ i : (↑v.1.val : Type), active i (v.2 i)

def Uses (v : Word m w q) (i : Fin m) (j : Fin q) : Prop :=
  ∃ hi : i ∈ v.1.val, v.2 ⟨i,hi⟩ = j

/-- Tests of the selected labels distinguish words of the same weight. -/
theorem reads_uses_iff (u v : Word m w q) : Reads (Uses u) v ↔ u = v := by
  constructor
  · intro h
    obtain ⟨⟨S,hS⟩,f⟩ := u
    obtain ⟨⟨T,hT⟩,g⟩ := v
    have hsub : T ⊆ S := fun i hi => (h ⟨i,hi⟩).choose
    have hST : T = S := Finset.eq_of_subset_of_card_le hsub (by omega)
    subst T
    congr 1
    funext i
    exact (h i).choose_spec
  · rintro rfl i
    exact ⟨i.property,rfl⟩

/-- A positive activation test for every subset of size `m + 1 - w`
forces at least `w` active slots, so a word can be decoded. -/
theorem exists_reads (hw : w ≤ m) (active : Fin m → Fin q → Prop)
    (h : ∀ J : Finset (Fin m), J.card = m + 1 - w →
      ∃ i ∈ J, ∃ j, active i j) : ∃ v : Word m w q, Reads active v := by
  classical
  let S := Finset.univ.filter fun i => ∃ j, active i j
  have hcard : w ≤ S.card := by
    by_contra! hlt
    have hcompl : m + 1 - w ≤ Sᶜ.card := by
      have hs := Finset.card_compl S
      rw [Fintype.card_fin] at hs
      omega
    obtain ⟨J,hJ,hJc⟩ := Finset.exists_subset_card_eq hcompl
    obtain ⟨i,hi,j,hij⟩ := h J hJc
    exact (Finset.mem_compl.mp (hJ hi)) (Finset.mem_filter.mpr ⟨Finset.mem_univ _,j,hij⟩)
  obtain ⟨T,hT,hTc⟩ := Finset.exists_subset_card_eq hcard
  have H (i : (↑T : Type)) : ∃ j, active i j := (Finset.mem_filter.mp (hT i.property)).2
  exact ⟨⟨⟨T,hTc⟩,fun i => (H i).choose⟩,fun i => (H i).choose_spec⟩

/-- The digit alphabet has one codeword for each support and labeling. -/
theorem card_word : Fintype.card (Word m w q) = m.choose w * q^w := by
  classical
  have hs : Fintype.card {S : Finset (Fin m) // S.card = w} = m.choose w := by
    rw [Fintype.card_of_subtype (Finset.univ.powersetCard w) (by simp),
      Finset.card_powersetCard,Finset.card_univ,Fintype.card_fin]
  have h (S : {S : Finset (Fin m) // S.card = w}) :
      Fintype.card ((↑S.val : Type) → Fin q) = q^w := by
    simp [Fintype.card_pi,S.property]
  unfold Word
  rw [Fintype.card_sigma]
  simp_rw [h]
  simp [hs]

/-- Selecting exactly three quarters of the slots loses at most a
factor of one plus the number of slots from the full four-letter alphabet. -/
theorem four_pow_le_weighted (t : ℕ) :
    4^(4*t) ≤ (4*t+1) * Fintype.card (Word (4*t) (3*t) 3) := by
  rw [card_word]
  let f (j : ℕ) := (4*t).choose j * 3^j
  change 4^(4*t) ≤ (4*t+1) * f (3*t)
  have hstep (j : ℕ) : f (j+1) * (j+1) = f j * (3*(4*t-j)) := by
    unfold f
    rw [pow_succ]
    calc
      _ = ((4*t).choose (j+1)*(j+1))*3^j*3 := by ring
      _ = _ := by rw [Nat.choose_succ_right_eq]; ring
  have hup (j : ℕ) (hj : j < 3*t) : f j ≤ f (j+1) := by
    refine Nat.le_of_mul_le_mul_right ?_ (by omega : 0 < j+1)
    rw [hstep]
    exact Nat.mul_le_mul_left _ (by omega)
  have hdown (j : ℕ) (hj : 3*t ≤ j) : f (j+1) ≤ f j := by
    refine Nat.le_of_mul_le_mul_right ?_ (by omega : 0 < j+1)
    rw [hstep]
    exact Nat.mul_le_mul_left _ (by omega)
  have hbelow (j : ℕ) : ∀ i ≤ j, j ≤ 3*t → f i ≤ f j := by
    induction j with
    | zero =>
      intro i hi _
      simpa only [Nat.le_zero.mp hi] using (le_rfl : f 0 ≤ f 0)
    | succ j ih =>
      intro i hi hj
      by_cases h : i = j+1
      · simp [h]
      · exact (ih i (by omega) (by omega)).trans (hup j (by omega))
  have habove (j : ℕ) : f (3*t+j) ≤ f (3*t) := by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [Nat.add_succ]
      exact (hdown (3*t+j) (by omega)).trans ih
  have hpeak (j : ℕ) : f j ≤ f (3*t) := by
    by_cases h : j ≤ 3*t
    · exact hbelow _ _ h le_rfl
    · have hh := habove (j-3*t)
      rwa [Nat.add_sub_of_le (by omega : 3*t ≤ j)] at hh
  calc
    4^(4*t) = ∑ j ∈ Finset.range (4*t+1), f j := by
      simpa [f,mul_comm] using (add_pow (3:ℕ) 1 (4*t))
    _ ≤ (4*t+1) * f (3*t) := by
      simpa using (Finset.sum_le_sum (s := Finset.range (4*t+1))
        (f := f) (g := fun _ => f (3*t)) (fun j _ => hpeak j))

end TranslationTiling.FiniteCompiler.SlotWords
