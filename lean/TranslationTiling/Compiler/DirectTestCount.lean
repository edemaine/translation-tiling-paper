import TranslationTiling.Compiler.ClosedBudget

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace TranslationTiling.Compiler.Size

open scoped Classical BigOperators
noncomputable section

def cycleCountExponentFor (u : ℕ) : ℕ := u ^ 2 * channelCount
def testCountExponentFor (u : ℕ) : ℕ := cycleCountExponentFor u + channelCount + 10
def cycleCountExponent : ℕ := cycleCountExponentFor usefulCap
def testCountExponent : ℕ := testCountExponentFor usefulCap
def directTestCap (b : ℕ) : ℕ := b ^ testCountExponent

variable {T : LeanWang.TileSet} {E : EncodingParameters T} {b u : ℕ}

theorem cycleTiles_card_le (hb : ParameterBudget E b)
    (hu : ∀ i, E.a i ≤ u ∧ E.b i ≤ u)
    {t : ℕ} [NeZero t] (cycle : ZMod t ↪ Channel T)
    (labels : ∀ j, Label T (cycle j)) :
    (cycleTiles E cycle labels).card ≤ b ^ (cycleCountExponentFor u) := by
  have ht : t ≤ channelCount := by
    simpa only [ZMod.card, channelCount] using
      Fintype.card_le_of_injective cycle cycle.injective
  have hU (i : Channel T) (j : Label T i) :
      Fintype.card (digitSubgroup E i j) ≤ b := by
    have h := Fintype.card_le_of_injective
      (fun x : digitSubgroup E i j => (x : K E i)) Subtype.val_injective
    exact h.trans (by simpa only [K, ZMod.card] using hb.r i)
  have hP (i : Channel T) : Fintype.card (P E i) ≤ u ^ 2 := by
    simpa only [P, Fintype.card_prod, ZMod.card, pow_two] using
      Nat.mul_le_mul (hu i).1 (hu i).2
  unfold cycleTiles
  apply (Finset.card_image_le.trans (le_of_eq Finset.card_univ)).trans
  rw [Fintype.card_pi]
  calc
    _ ≤ ∏ _j : ZMod t, b ^ (u ^ 2) := by
      apply Finset.prod_le_prod
      intro j _
      rw [Fintype.card_fun]
      exact (Nat.pow_le_pow_left (hU _ _) _).trans
        (Nat.pow_le_pow_right (by have := hb.two; omega) (hP _))
    _ = b ^ (u ^ 2 * t) := by simp [← pow_mul]
    _ ≤ _ := Nat.pow_le_pow_right (by have := hb.two; omega) (Nat.mul_le_mul_left _ ht)

theorem wordConstraintTiles_card_le (hb : ParameterBudget E b)
    (hu : ∀ i, E.a i ≤ u ∧ E.b i ≤ u)
    (hL : labelsBound T.length ≤ b) :
    (wordConstraintTiles E).card ≤ b ^ ((cycleCountExponentFor u) + channelCount) := by
  have hwords : Fintype.card (Word T) ≤ b ^ channelCount := by
    rw [Fintype.card_fun]
    have hs := (label_card_le T (.inl (0 : Sudoku.Column))).trans hL
    change Fintype.card (Symbol T) ≤ b at hs
    apply (Nat.pow_le_pow_left hs _).trans
    apply Nat.pow_le_pow_right (by have := hb.two; omega)
    simp only [Column, Fintype.card_eq_nat_card, Nat.card_fin]
    rw [channelCount_eq, residueModulus_eq]
    omega
  unfold wordConstraintTiles
  apply Finset.card_biUnion_le.trans
  calc
    _ ≤ ∑ _w ∈ (Finset.univ.filter (fun w : Word T => w ∉ allowedWords T)),
        b ^ (cycleCountExponentFor u) :=
      Finset.sum_le_sum (fun _ _ => cycleTiles_card_le hb hu _ _)
    _ ≤ Fintype.card (Word T) * b ^ (cycleCountExponentFor u) := by
      simp only [Finset.sum_const, smul_eq_mul]
      exact Nat.mul_le_mul_right _ (Finset.card_filter_le _ _)
    _ ≤ b ^ channelCount * b ^ (cycleCountExponentFor u) := Nat.mul_le_mul_right _ hwords
    _ = _ := by rw [← pow_add]; congr 1; omega

theorem seedConstraintTiles_card_le (hb : ParameterBudget E b)
    (hu : ∀ i, E.a i ≤ u ∧ E.b i ≤ u)
    (hC : channelCount ≤ b) (hL : labelsBound T.length ≤ b) :
    (seedConstraintTiles E).card ≤ b ^ ((cycleCountExponentFor u) + 3) := by
  have hN : Fintype.card (Column T) ≤ b := by
    apply le_trans (b := channelCount) _ hC
    simp only [Column, Fintype.card_eq_nat_card, Nat.card_fin]
    rw [channelCount_eq, residueModulus_eq]
    omega
  have hs := (label_card_le T (.inl (0 : Sudoku.Column))).trans hL
  change Fintype.card (Symbol T) ≤ b at hs
  have hindex : Fintype.card (Fin 2 × Column T × Symbol T) ≤ b ^ 3 := by
    simp only [Fintype.card_prod, Fintype.card_fin]
    calc
      _ ≤ b * (b * b) := Nat.mul_le_mul hb.two (Nat.mul_le_mul hN hs)
      _ = _ := by ring
  unfold seedConstraintTiles
  apply Finset.card_biUnion_le.trans
  calc
    _ ≤ ∑ _q ∈ (Finset.univ.filter (fun q : Fin 2 × Column T × Symbol T =>
        ¬ SeedSet q.1 q.2.2)), b ^ (cycleCountExponentFor u) :=
      Finset.sum_le_sum (fun _ _ => cycleTiles_card_le hb hu _ _)
    _ ≤ Fintype.card (Fin 2 × Column T × Symbol T) * b ^ (cycleCountExponentFor u) := by
      simp only [Finset.sum_const, smul_eq_mul]
      exact Nat.mul_le_mul_right _ (Finset.card_filter_le _ _)
    _ ≤ b ^ 3 * b ^ (cycleCountExponentFor u) := Nat.mul_le_mul_right _ hindex
    _ = _ := by rw [← pow_add]; congr 1; omega

theorem dependenceTiles_card_le (hb : ParameterBudget E b) (hC : channelCount ≤ b) :
    (dependenceTiles E).card ≤ b ^ 4 := by
  have hN : Fintype.card (Column T) ≤ b := by
    apply le_trans (b := channelCount) _ hC
    simp only [Column, Fintype.card_eq_nat_card, Nat.card_fin]
    rw [channelCount_eq, residueModulus_eq]
    omega
  have hsub (i : Channel T) : Fintype.card {j : Channel T // j ≠ i} ≤ b :=
    (Fintype.card_le_of_injective Subtype.val Subtype.val_injective).trans hC
  have hpair : Fintype.card (Σ i : Channel T, {j : Channel T // j ≠ i}) ≤ b * b := by
    rw [Fintype.card_sigma]
    apply (Finset.sum_le_sum (fun i _ => hsub i)).trans
    simpa only [Finset.sum_const, Finset.card_univ, smul_eq_mul, channelCount] using
      Nat.mul_le_mul_right b hC
  unfold dependenceTiles
  apply (Finset.card_image_le.trans (le_of_eq Finset.card_univ)).trans
  simp only [DependenceIndex, Fintype.card_sum, Fintype.card_prod,
    Fintype.card_fin, Fintype.card_bool]
  have h2 := hb.two
  have hp : b ^ 2 ≤ b ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have hsq : b ^ 2 + b + 4 ≤ b ^ 4 := by nlinarith [sq_nonneg (b - 2 : ℤ)]
  nlinarith

/-- Count the actual finite families, retaining the fixed useful-output sizes.
This avoids the exponentially wasteful powerset of the ambient support. -/
theorem testTiles_card_le_direct (hb : ParameterBudget E b)
    (hu : ∀ i, E.a i ≤ u ∧ E.b i ≤ u)
    (hC : channelCount ≤ b) (hL : labelsBound T.length ≤ b) :
    (testTiles E).card ≤ b ^ testCountExponentFor u := by
  have h2 := hb.two
  have h1 : 1 ≤ b := by omega
  let e := (cycleCountExponentFor u) + channelCount + 4
  have hdep := dependenceTiles_card_le hb hC
  have hword := wordConstraintTiles_card_le hb hu hL
  have hseed := seedConstraintTiles_card_le hb hu hC hL
  have hbound : ∀ k ≤ e, b ^ k ≤ b ^ e := fun _ hk => Nat.pow_le_pow_right h1 hk
  have hsingle : 1 ≤ b ^ e := Nat.one_le_pow _ _ h1
  have hact : (Finset.univ.image (ordinaryActivationTile E)).card ≤ b ^ e := by
    apply Finset.card_image_le.trans
    rw [Finset.card_univ]
    have hN : Fintype.card (Column T) ≤ channelCount := by
      simp only [Column, Fintype.card_eq_nat_card, Nat.card_fin]
      rw [channelCount_eq, residueModulus_eq]
      omega
    exact (hN.trans hC).trans (by simpa using hbound 1 (by dsimp [e]; omega))
  have hseeds : (Finset.univ.image (seedActivationTile E)).card ≤ b ^ e := by
    apply Finset.card_image_le.trans
    rw [Finset.card_univ, Fintype.card_fin]
    exact h2.trans (by simpa using hbound 1 (by dsimp [e]; omega))
  have hsum : (testTiles E).card ≤ 6 * b ^ e := by
    unfold testTiles
    have h := Finset.card_union_le
      ({kernelTile E} ∪ dependenceTiles E ∪ wordConstraintTiles E ∪ seedConstraintTiles E ∪
        Finset.univ.image (ordinaryActivationTile E)) (Finset.univ.image (seedActivationTile E))
    have h' := Finset.card_union_le
      ({kernelTile E} ∪ dependenceTiles E ∪ wordConstraintTiles E ∪ seedConstraintTiles E)
        (Finset.univ.image (ordinaryActivationTile E))
    have h'' := Finset.card_union_le
      ({kernelTile E} ∪ dependenceTiles E ∪ wordConstraintTiles E) (seedConstraintTiles E)
    have h''' := Finset.card_union_le ({kernelTile E} ∪ dependenceTiles E) (wordConstraintTiles E)
    have h'''' := Finset.card_union_le {kernelTile E} (dependenceTiles E)
    simp only [Finset.card_singleton] at h''''
    have hd := hdep.trans (hbound 4 (by dsimp [e]; omega))
    have hw := hword.trans (hbound _ (by dsimp [e]; omega))
    have hs := hseed.trans (hbound _ (by dsimp [e]; omega))
    omega
  apply hsum.trans
  have h6 : 6 ≤ b ^ 6 := by
    exact (by decide : 6 ≤ 2 ^ 6).trans (Nat.pow_le_pow_left h2 6)
  unfold testCountExponentFor
  change 6 * b ^ e ≤ b ^ (e + 6)
  rw [pow_add b e 6]
  simpa only [Nat.mul_comm] using Nat.mul_le_mul_left (b ^ e) h6

end
end TranslationTiling.Compiler.Size
