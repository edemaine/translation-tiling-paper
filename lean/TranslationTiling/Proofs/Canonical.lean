import TranslationTiling.External.Sudoku
import TranslationTiling.Proofs.Arithmetic

namespace TranslationTiling.Sudoku

theorem lowValuation_sound (r : ℕ) (hp : r.Prime) (z : ℤ) (u : ℕ)
    (h : lowValuation r z = some u) : z ≠ 0 ∧ padicValInt r z = u := by
  letI : Fact r.Prime := ⟨hp⟩
  unfold lowValuation at h
  split at h
  · rename_i hr
    cases h
    exact ⟨fun hz => hr (hz ▸ dvd_zero _), padicValInt.eq_zero_of_not_dvd hr⟩
  · rename_i hr
    have hd : (r : ℤ) ∣ z := not_not.mp hr
    split at h
    · rename_i hsq
      cases h
      have hz : z ≠ 0 := fun hz => hsq (hz ▸ dvd_zero _)
      have h1 : 1 ≤ padicValInt r z := by
        have hd1 : (r : ℤ) ^ 1 ∣ z := by simpa using hd
        exact ((padicValInt_dvd_iff (p := r) 1 z).mp hd1).resolve_left hz
      have h2 : padicValInt r z < 2 := by
        by_contra hn
        exact hsq ((padicValInt_dvd_iff (p := r) 2 z).mpr (Or.inr (by omega)))
      exact ⟨hz, by omega⟩
    · cases h

theorem lastDigit_eq_lowDigit (r : ℕ) (hp : r.Prime) (z : ℤ) (u : ℕ)
    (h : lowValuation r z = some u) : (lastDigit r hp z).val = lowDigit r z := by
  by_cases hd : (r : ℤ) ∣ z
  · have hsq : ¬ (r : ℤ) ^ 2 ∣ z := by
      intro hs
      simp [lowValuation, hd, hs] at h
    simpa only [lowDigit, if_pos hd] using lastDigit_eq_div_of_dvd_not_sq_dvd r hp hd hsq
  · simpa only [lowDigit, if_neg hd] using lastDigit_eq_of_not_dvd r hp hd

/-- The paper's canonical array, with an arbitrary decoration at height zero. -/
noncomputable def canonical {T : LeanWang.TileSet}
    (τ : ℕ × ℕ → LeanWang.TileIn T)
    (zeroTile : LeanWang.TileIn T := τ (0, 0)) : Array T := fun _ m =>
  (lastDigit p (by decide) m, lastDigit q (by decide) m,
    if m = 0 then zeroTile else τ (padicValInt p m, padicValInt q m))

theorem canonical_nonconstantColumns {T : LeanWang.TileSet}
    (τ : ℕ × ℕ → LeanWang.TileIn T) (zeroTile : LeanWang.TileIn T := τ (0, 0)) :
    NonconstantColumns (canonical τ zeroTile) := by
  constructor
  · intro n
    refine ⟨1, 2, ?_⟩
    intro he
    have hv := congrArg Units.val he
    change (lastDigit p (by decide) 1).val = (lastDigit p (by decide) 2).val at hv
    rw [lastDigit_one, Units.val_one, lastDigit_two p (by decide) (by decide)] at hv
    exact (by decide : (1 : ZMod p) ≠ 2) hv
  · intro n
    refine ⟨1, 2, ?_⟩
    intro he
    have hv := congrArg Units.val he
    change (lastDigit q (by decide) 1).val = (lastDigit q (by decide) 2).val at hv
    rw [lastDigit_one, Units.val_one, lastDigit_two q (by decide) (by decide)] at hv
    exact (by decide : (1 : ZMod q) ≠ 2) hv

end TranslationTiling.Sudoku
