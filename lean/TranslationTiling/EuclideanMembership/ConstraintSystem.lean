import TranslationTiling.EuclideanMembership.ProbeSyntax
import TranslationTiling.EuclideanMembership.EffectiveCompactness

namespace TranslationTiling.EuclideanMembership
noncomputable section
variable {d : ℕ}

abbrev PackingIndex (d : ℕ) := Lattice d × Lattice d × Lattice d × Lattice d × Probe d
abbrev ConstraintIndex (d : ℕ) := ℕ ⊕ (Lattice d ⊕ (PackingIndex d ⊕ Probe d))

instance (priority := 2000) constraintIndexEncodable (d : ℕ) : Encodable (ConstraintIndex d) :=
  (inferInstance : Primcodable (ConstraintIndex d)).toEncodable

def constraint (P : Tile d) (ar af : Bool) (i : ConstraintIndex d) : Formula := by
  classical
  exact Sum.elim (reciprocalFormula d)
    (Sum.elim (slotFormula ar af)
      (Sum.elim (fun t : PackingIndex d =>
        if t.1=t.2.1 ∨ t.2.2.1 ∉ P ∨ t.2.2.2.1 ∉ P then fTrue
        else packingFormula P t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2)
        (coverageFormula P))) i

def constraints (P : Tile d) (ar af : Bool) (n : ℕ) : Formula :=
  ((Encodable.decode (α := ConstraintIndex d) n).map (constraint P ar af)).getD fTrue

theorem constraints_iff (P : Tile d) (ar af : Bool) (x : Assignment) :
    (∀ n, Holds (constraints P ar af n) 0 (coordinates x)) ↔ Model ar af P x := by
  classical
  have he : (∀ n, Holds (constraints P ar af n) 0 (coordinates x)) ↔
      ∀ i, Holds (constraint P ar af i) 0 (coordinates x) := by
    constructor
    · intro h i
      have hh := h (Encodable.encode i)
      simpa only [constraints,Encodable.encodek,Option.map_some,Option.getD_some] using hh
    · intro h n
      unfold constraints
      cases Encodable.decode (α := ConstraintIndex d) n with
      | none => exact holds_true _
      | some i => exact h i
  rw [he]
  constructor
  · intro h
    have hs (z : Lattice d) := (slotFormula_iff ar af x z).mp (h (Sum.inr (Sum.inl z)))
    refine ⟨fun n => (reciprocalFormula_iff n x).mp (h (Sum.inl n)),hs,?_,?_⟩
    · intro z w hzw hz hw p hp q hq a hboth
      have hh := h (Sum.inr (Sum.inr (Sum.inl (z,w,p,q,a))))
      change Holds (if z=w ∨ p ∉ P ∨ q ∉ P then fTrue else packingFormula P z w p q a) 0 (coordinates x) at hh
      have hi : ¬ (z=w ∨ p ∉ P ∨ q ∉ P) := by simp only [hzw,hp,hq,not_true_eq_false,or_self,not_false_eq_true]
      rw [if_neg hi,packingFormula_iff] at hh
      rcases hh with he | he | hn | hn
      · have he' := hz
        unfold Enabled at he'
        linarith
      · have he' := hw
        unfold Enabled at he'
        linarith
      · exact hn hboth.1
      · exact hn hboth.2
    · intro a
      exact (coverageFormula_iff P a x).mp (h (Sum.inr (Sum.inr (Sum.inr a))))
  · intro h i
    rcases i with n | z | ⟨z,w,p,q,a⟩ | a
    · exact (reciprocalFormula_iff n x).mpr (h.reciprocal n)
    · exact (slotFormula_iff ar af x z).mpr (h.slots z)
    · change Holds (if z=w ∨ p ∉ P ∨ q ∉ P then fTrue else packingFormula P z w p q a) 0 (coordinates x)
      split
      · exact holds_true _
      · rename_i hi
        have hh : z ≠ w ∧ p ∈ P ∧ q ∈ P := by simpa only [not_or,not_not] using hi
        apply (packingFormula_iff P z w p q a x).mpr
        rcases (h.slots z).1 with hz | hz
        · exact Or.inl hz
        · rcases (h.slots w).1 with hw | hw
          · exact Or.inr (Or.inl hw)
          · have hn := h.packing z w hh.1 hz hw p hh.2.1 q hh.2.2 a
            exact Or.inr (Or.inr (not_and_or.mp hn))
    · exact (coverageFormula_iff P a x).mpr (h.coverage a)

theorem satisfiable_iff_model (P : Tile d) (ar af : Bool) :
    Satisfiable (constraints P ar af) ↔ ∃ x : Assignment, Model ar af P x := by
  simp only [Satisfiable,constraints_iff]
end
end TranslationTiling.EuclideanMembership
