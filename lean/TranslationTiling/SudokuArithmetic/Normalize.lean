import TranslationTiling.SudokuArithmetic.Rescale

/-! Simultaneous straightening of the two arithmetic components. -/

set_option maxRecDepth 2000

namespace TranslationTiling.Sudoku

theorem FullAffineApproximation.straighten {r : ℕ} (hp : r.Prime)
    {V : Column → ℤ → (ZMod r)ˣ} {A B C : ZMod r}
    (hH : FullAffineApproximation V A B C) (hB : B ≠ 0) (u v : ℤ)
    (hu : (u : ZMod r) = -(B⁻¹ * A)) (hv : (v : ZMod r) = -(B⁻¹ * C)) :
    FullAffineApproximation (arithmeticReparametrize V 1 u v) 0 B 0 := by
  let : Fact r.Prime := ⟨hp⟩
  have hh := hH.reparametrize hp 1 u v hB (by simp)
  have hau : A + B * (u : ZMod r) = 0 := by
    rw [hu, mul_neg, ← mul_assoc, mul_inv_cancel₀ hB, one_mul, add_neg_cancel]
  have hcv : C + B * (v : ZMod r) = 0 := by
    rw [hv, mul_neg, ← mul_assoc, mul_inv_cancel₀ hB, one_mul, add_neg_cancel]
  simpa only [hau, hcv, Int.cast_one, mul_one] using hh

def Normalized {T : LeanWang.TileSet} (W : Array T) (Bₚ : ZMod p) (Bᵩ : ZMod q) : Prop :=
  Bₚ ≠ 0 ∧ Bᵩ ≠ 0 ∧
    FullAffineApproximation (fun n m => (W n m).1) 0 Bₚ 0 ∧
    FullAffineApproximation (fun n m => (W n m).2.1) 0 Bᵩ 0

theorem exists_normalize {T : LeanWang.TileSet} {W : Array T}
    (hW : LineRule W) (hcols : NonconstantColumns W) :
    ∃ (u v : ℤ) (Bₚ : ZMod p) (Bᵩ : ZMod q),
      Normalized (reparametrize W 1 u v) Bₚ Bᵩ := by
  let : Fact p.Prime := ⟨by decide⟩
  let : Fact q.Prime := ⟨by decide⟩
  obtain ⟨⟨Aₚ, Bₚ, Cₚ, hBₚ, hHₚ⟩, ⟨Aᵩ, Bᵩ, Cᵩ, hBᵩ, hHᵩ⟩⟩ :=
    decorated_initial_structure W hW hcols
  obtain ⟨uₚ, huₚ⟩ := ZMod.intCast_surjective (-(Bₚ⁻¹ * Aₚ))
  obtain ⟨vₚ, hvₚ⟩ := ZMod.intCast_surjective (-(Bₚ⁻¹ * Cₚ))
  obtain ⟨uᵩ, huᵩ⟩ := ZMod.intCast_surjective (-(Bᵩ⁻¹ * Aᵩ))
  obtain ⟨vᵩ, hvᵩ⟩ := ZMod.intCast_surjective (-(Bᵩ⁻¹ * Cᵩ))
  obtain ⟨u, hup, huq⟩ := exists_twoPrime_residue uₚ uᵩ
  obtain ⟨v, hvp, hvq⟩ := exists_twoPrime_residue vₚ vᵩ
  refine ⟨u, v, Bₚ, Bᵩ, hBₚ, hBᵩ, ?_, ?_⟩
  · exact FullAffineApproximation.straighten (by decide)
      ⟨Or.inr (Or.inl hBₚ), hHₚ⟩ hBₚ u v
      (hup.cast_eq.trans huₚ) (hvp.cast_eq.trans hvₚ)
  · exact FullAffineApproximation.straighten (by decide)
      ⟨Or.inr (Or.inl hBᵩ), hHᵩ⟩ hBᵩ u v
      (huq.cast_eq.trans huᵩ) (hvq.cast_eq.trans hvᵩ)

theorem arithmetic_rescale_nonconstant {r : ℕ} (hp : r.Prime) (hlarge : 200 < r)
    (hr : r ^ 2 ≤ Width) {V : Column → ℤ → (ZMod r)ˣ} (hV : ArithmeticLineRule r V)
    {B : ZMod r} (hB : B ≠ 0) (hH : FullAffineApproximation V 0 B 0) :
    ∀ n, ∃ m m', arithmeticReparametrize V r 0 0 n m ≠
      arithmeticReparametrize V r 0 0 n m' := by
  obtain ⟨A₁, B₁, C₁, hH₁⟩ := arithmetic_initial_affine r hr hp hlarge _
    (arithmeticReparametrize_lineRule hV r 0 0)
  have hB₁ := rescale_vertical_coefficient hp hlarge hr hV hB hH hH₁
  exact hH₁.nonconstant hp hlarge (by rwa [hB₁])

theorem normalized_rescale_p_nonconstant {T : LeanWang.TileSet} {W : Array T}
    (hW : LineRule W) {Bₚ : ZMod p} {Bᵩ : ZMod q} (hN : Normalized W Bₚ Bᵩ) :
    NonconstantColumns (reparametrize W p 0 0) := by
  refine ⟨arithmetic_rescale_nonconstant (by decide) (by decide) (by decide)
    (arithmeticLineRule_p hW) hN.1 hN.2.2.1, ?_⟩
  have hh := hN.2.2.2.reparametrize (by decide) p 0 0 hN.2.1 (by decide)
  exact hh.nonconstant (by decide) (by decide)
    (by let : Fact q.Prime := ⟨by decide⟩; exact mul_ne_zero hN.2.1 (by decide))

theorem normalized_rescale_q_nonconstant {T : LeanWang.TileSet} {W : Array T}
    (hW : LineRule W) {Bₚ : ZMod p} {Bᵩ : ZMod q} (hN : Normalized W Bₚ Bᵩ) :
    NonconstantColumns (reparametrize W q 0 0) := by
  refine ⟨?_, arithmetic_rescale_nonconstant (by decide) (by decide) (by decide)
    (arithmeticLineRule_q hW) hN.2.1 hN.2.2.2⟩
  have hh := hN.2.2.1.reparametrize (by decide) q 0 0 hN.1 (by decide)
  exact hh.nonconstant (by decide) (by decide)
    (by let : Fact p.Prime := ⟨by decide⟩; exact mul_ne_zero hN.1 (by decide))

theorem no_positive_vertical_period {T : LeanWang.TileSet} {W : Array T}
    (hW : LineRule W) (hcols : NonconstantColumns W) {M : ℤ} (hM : 0 < M) :
    ¬ (∀ n m, W n (m + M) = W n m) := by
  intro hperiod
  exact ArithmeticRule.no_positive_vertical_period (by decide) (by decide)
    (arithmeticRestriction_lineRule p (by decide) _ (arithmeticLineRule_p hW))
    (arithmeticRestriction_nonconstant p (by decide) _ hcols.1) hM
    (fun n m => congrArg Prod.fst (hperiod (smallColumn p (by decide) n) m))

end TranslationTiling.Sudoku
