import TranslationTiling.Proofs.WordResidues
import TranslationTiling.Proofs.Wang
import TranslationTiling.SudokuArithmetic.Soundness

namespace TranslationTiling.Sudoku

private theorem allowed_one_constant {T : LeanWang.TileSet} (t : LeanWang.TileIn T) :
    Allowed T (fun _ => (1, 1, t)) := by
  refine ⟨0, 1, Or.inr (by decide), Or.inr (by decide), fun _ _ => t, ?_, ?_⟩
  · change ValidRectangle T 1 1 _
    constructor <;> intro u v h <;> omega
  · intro n
    simp only [zero_mul, zero_add]
    refine ⟨?_, ?_, ?_⟩
    · intro u _ _
      change (1 : ZMod p) = lowDigit p 1
      decide
    · intro v _ _
      change (1 : ZMod q) = lowDigit q 1
      decide
    · intro u v _ _ hu hv
      trivial

private theorem valid_shiftedRectangle {T : LeanWang.TileSet}
    (τ : ℕ × ℕ → LeanWang.TileIn T) (hτ : LeanWang.ValidQuarterTiling T τ)
    (k l w h : ℕ) :
    ValidRectangle T w h (fun u v => τ (k + u.val, l + v.val)) := by
  constructor
  · intro u v hu
    simpa only [Nat.add_assoc] using hτ.1 (k + u.val, l + v.val)
  · intro u v hv
    simpa only [Nat.add_assoc] using hτ.2 (k + u.val, l + v.val)

/-- The canonical decorated solution satisfies every integer-slope line.
This completeness direction is proved without the imported soundness hypothesis. -/
theorem canonical_lineRule {T : LeanWang.TileSet}
    (τ : ℕ × ℕ → LeanWang.TileIn T) (hτ : LeanWang.ValidQuarterTiling T τ)
    (zeroTile : LeanWang.TileIn T := τ (0, 0)) : LineRule (canonical τ zeroTile) := by
  intro d e
  by_cases hzero : d = 0 ∧ e = 0
  · obtain ⟨rfl, rfl⟩ := hzero
    simpa [canonical] using allowed_one_constant zeroTile
  have hde : d ≠ 0 ∨ e ≠ 0 := by tauto
  obtain ⟨k, aₚ, bₚ, hdₚ, heₚ, hprimₚ⟩ := exists_primitive_pair p (by decide) d e hde
  obtain ⟨l, aᵩ, bᵩ, hdᵩ, heᵩ, hprimᵩ⟩ := exists_primitive_pair q (by decide) d e hde
  obtain ⟨a, haₚ, haᵩ⟩ := exists_twoPrime_residue aₚ aᵩ
  obtain ⟨b, hbₚ, hbᵩ⟩ := exists_twoPrime_residue bₚ bᵩ
  have hprimP : ¬ (p : ℤ) ∣ a ∨ ¬ (p : ℤ) ∣ b := by
    rcases hprimₚ with ha | hb
    · exact Or.inl (fun h => ha (haₚ.dvd_iff.mp h))
    · exact Or.inr (fun h => hb (hbₚ.dvd_iff.mp h))
  have hprimQ : ¬ (q : ℤ) ∣ a ∨ ¬ (q : ℤ) ∣ b := by
    rcases hprimᵩ with ha | hb
    · exact Or.inl (fun h => ha (haᵩ.dvd_iff.mp h))
    · exact Or.inr (fun h => hb (hbᵩ.dvd_iff.mp h))
  refine ⟨a, b, hprimP, hprimQ, fun u v => τ (k + u.val, l + v.val),
    valid_shiftedRectangle τ hτ k l _ _, ?_⟩
  intro n
  have hrowP : d * (n.val : ℤ) + e = (p : ℤ) ^ k * (aₚ * n.val + bₚ) := by
    rw [hdₚ, heₚ]
    ring
  have hrowQ : d * (n.val : ℤ) + e = (q : ℤ) ^ l * (aᵩ * n.val + bᵩ) := by
    rw [hdᵩ, heᵩ]
    ring
  refine ⟨?_, ?_, ?_⟩
  · intro u hu _
    have hdata := normalized_line_data p (by decide) k u a b aₚ bₚ n.val haₚ hbₚ hu
    change (lastDigit p (by decide) (d * n.val + e)).val = lowDigit p (a * n.val + b)
    rw [hrowP]
    exact hdata.2.1
  · intro v hv _
    have hdata := normalized_line_data q (by decide) l v a b aᵩ bᵩ n.val haᵩ hbᵩ hv
    change (lastDigit q (by decide) (d * n.val + e)).val = lowDigit q (a * n.val + b)
    rw [hrowQ]
    exact hdata.2.1
  · intro u v hu hv _ _
    have hp := normalized_line_data p (by decide) k u a b aₚ bₚ n.val haₚ hbₚ hu
    have hq := normalized_line_data q (by decide) l v a b aᵩ bᵩ n.val haᵩ hbᵩ hv
    have hn : d * (n.val : ℤ) + e ≠ 0 := hrowP ▸ hp.1
    have hpv : padicValInt p (d * (n.val : ℤ) + e) = k + u := hrowP ▸ hp.2.2
    have hqv : padicValInt q (d * (n.val : ℤ) + e) = l + v := hrowQ ▸ hq.2.2
    change (if d * (n.val : ℤ) + e = 0 then zeroTile
      else τ (padicValInt p (d * n.val + e), padicValInt q (d * n.val + e))) = τ (k + u, l + v)
    rw [if_neg hn, hpv, hqv]

/-- The explicit decorated Sudoku problem has exactly the Wang tilability instances. -/
theorem sudoku_iff_wang (T : LeanWang.TileSet) :
    LeanWang.TilesPlane T ↔ ∃ W : Array T, LineRule W ∧ NonconstantColumns W := by
  constructor
  · intro hT
    obtain ⟨τ, hτ⟩ := (wang_plane_iff_quadrant T).mp hT
    exact ⟨canonical τ, canonical_lineRule τ hτ, canonical_nonconstantColumns τ⟩
  · rintro ⟨W, hW, hcols⟩
    exact (wang_plane_iff_quadrant T).mpr (soundness T W hW hcols)

end TranslationTiling.Sudoku
