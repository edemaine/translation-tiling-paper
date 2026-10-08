import TranslationTiling.Connectivity
import Mathlib.Tactic.FinCases

/-! Coordinate paths, with explicit predicates describing where they may run. -/

namespace TranslationTiling

abbrev FacePath {d : ℕ} (P : Lattice d → Prop) (x y : Lattice d) :=
  Relation.ReflTransGen (fun a b => P a ∧ P b ∧ FaceAdjacent a b) x y

namespace FacePath

theorem adjacent_symm {d : ℕ} {x y : Lattice d} (h : FaceAdjacent x y) :
    FaceAdjacent y x := by
  obtain ⟨k, h | h⟩ := h
  · exact ⟨k, Or.inr h⟩
  · exact ⟨k, Or.inl h⟩

theorem reverse {d : ℕ} {P : Lattice d → Prop} {x y : Lattice d}
    (h : FacePath P x y) : FacePath P y x := by
  apply Relation.reflTransGen_swap.mp
  exact h.mono fun _ _ hab => ⟨hab.2.1, hab.1, adjacent_symm hab.2.2⟩

theorem mono {d : ℕ} {P Q : Lattice d → Prop} {x y : Lattice d}
    (h : FacePath P x y) (hPQ : ∀ z, P z → Q z) : FacePath Q x y :=
  Relation.ReflTransGen.mono (fun a b hab => ⟨hPQ a hab.1, hPQ b hab.2.1, hab.2.2⟩) h

theorem step {d : ℕ} {P : Lattice d → Prop} {x y : Lattice d}
    (hx : P x) (hy : P y) (h : FaceAdjacent x y) : FacePath P x y :=
  Relation.ReflTransGen.single ⟨hx, hy, h⟩

/-- Change one coordinate, staying in an interval on which the predicate holds. -/
theorem axis {d : ℕ} (P : Lattice d → Prop) (x : Lattice d) (k : Fin d) (b : ℤ)
    (hP : ∀ t, min (x k) b ≤ t → t ≤ max (x k) b → P (Function.update x k t)) :
    FacePath P x (Function.update x k b) := by
  have forward (a : ℤ) (n : ℕ)
      (h : ∀ t, a ≤ t → t ≤ a + n → P (Function.update x k t)) :
      FacePath P (Function.update x k a) (Function.update x k (a + n)) := by
    induction n with
    | zero => simpa using (Relation.ReflTransGen.refl :
        FacePath P (Function.update x k a) (Function.update x k a))
    | succ n ih =>
      have prev := ih (fun t ht hu => h t ht (by omega))
      apply prev.tail
      refine ⟨h _ (by omega) (by omega), h _ (by omega) (by omega), k, Or.inl ?_⟩
      funext j
      by_cases hj : j = k
      · subst j; simp; omega
      · simp [hj]
  by_cases hb : x k ≤ b
  · have he : x k + ((b - x k).toNat : ℤ) = b := by omega
    have h := forward (x k) (b - x k).toNat (by
      intro t ht hu
      apply hP t <;> simp only [min_eq_left hb, max_eq_right hb] <;> omega)
    rw [he] at h
    simpa only [Function.update_eq_self] using h
  · have he : b + ((x k - b).toNat : ℤ) = x k := by omega
    have h := forward b (x k - b).toNat (by
      intro t ht hu
      apply hP t <;> simp only [min_eq_right (by omega : b ≤ x k),
        max_eq_left (by omega : b ≤ x k)] <;> omega)
    rw [he] at h
    simpa only [Function.update_eq_self] using reverse h

/-- A lattice rectangle is face connected. -/
theorem box3 (P : Lattice 3 → Prop) (lo hi x y : Lattice 3)
    (hx : ∀ k, lo k ≤ x k ∧ x k ≤ hi k)
    (hy : ∀ k, lo k ≤ y k ∧ y k ≤ hi k)
    (hP : ∀ z, (∀ k, lo k ≤ z k ∧ z k ≤ hi k) → P z) : FacePath P x y := by
  have update_bounds (z : Lattice 3) (k : Fin 3)
      (hz : ∀ j, lo j ≤ z j ∧ z j ≤ hi j) (t : ℤ)
      (ht : min (z k) (y k) ≤ t) (hu : t ≤ max (z k) (y k)) :
      ∀ j, lo j ≤ (Function.update z k t) j ∧
        (Function.update z k t) j ≤ hi j := by
    intro j
    by_cases hj : j = k
    · subst j; simp only [Function.update_self]
      have := hz k; have := hy k
      rcases le_total (z k) (y k) with h | h
      · rw [min_eq_left h] at ht; rw [max_eq_right h] at hu; omega
      · rw [min_eq_right h] at ht; rw [max_eq_left h] at hu; omega
    · simpa [Function.update_of_ne hj] using hz j
  have h0 := axis P x 0 (y 0) (fun t ht hu => hP _ (update_bounds x 0 hx t ht hu))
  have hx0 := update_bounds x 0 hx (y 0) (min_le_right _ _) (le_max_right _ _)
  have h1 := axis P (Function.update x 0 (y 0)) 1 (y 1)
    (fun t ht hu => hP _ (update_bounds _ 1 hx0 t ht hu))
  have hx1 := update_bounds _ 1 hx0 (y 1) (min_le_right _ _) (le_max_right _ _)
  have h2 := axis P (Function.update (Function.update x 0 (y 0)) 1 (y 1)) 2 (y 2)
    (fun t ht hu => hP _ (update_bounds _ 2 hx1 t ht hu))
  have he : Function.update (Function.update (Function.update x 0 (y 0)) 1 (y 1))
      2 (y 2) = y := by funext k; fin_cases k <;> simp
  exact he ▸ (h0.trans h1).trans h2

end FacePath
end TranslationTiling
