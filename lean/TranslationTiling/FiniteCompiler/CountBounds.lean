import TranslationTiling.FiniteCompiler.SupportBounds

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace TranslationTiling.FiniteCompiler.Size

open scoped Classical BigOperators
noncomputable section

def cycleCountExponent (T : System) := 3 * channelCount T
def testCountExponent (T : System) := cycleCountExponent T + channelCount T + 10

variable {T : System} {E : EncodingParameters T} {b : ℕ}

theorem cycleTiles_card_le (hb : ParameterBudget E b)
    {t : ℕ} [NeZero t] (cycle : ZMod t ↪ Channel T)
    (labels : ∀ j, Label T (cycle j)) :
    (sparseCycleTiles E cycle labels).card ≤ b ^ cycleCountExponent T := by
  have ht : t ≤ channelCount T := by
    simpa only [ZMod.card, channel_card] using
      Fintype.card_le_of_injective cycle cycle.injective
  have hU (i : Channel T) (j : Label T i) :
      Fintype.card (digitSubgroup E i j) ≤ b := by
    have h := Fintype.card_le_of_injective
      (fun x : digitSubgroup E i j => (x : K E i)) Subtype.val_injective
    exact h.trans (by simpa only [K, ZMod.card] using hb.r i)
  have hP (i : Channel T) : Fintype.card (P E i) ≤ b ^ 2 := by
    simpa only [P, Fintype.card_prod, ZMod.card, pow_two] using
      Nat.mul_le_mul (hb.a i) (hb.usefulB i)
  apply (sparseCycleTiles_card_le E cycle labels).trans
  calc
    _ ≤ ∏ _j : ZMod t, (b ^ 2 * b) :=
      Finset.prod_le_prod (fun j _ => Nat.mul_le_mul (hP _) (hU _ _))
    _ = b ^ (3 * t) := by simp only [← pow_succ, Finset.prod_const, Finset.card_univ,
        ZMod.card, ← pow_mul]
    _ ≤ _ := Nat.pow_le_pow_right (by have := hb.two; omega) (Nat.mul_le_mul_left 3 ht)

theorem wordConstraintTiles_card_le (hb : ParameterBudget E b)
    (hL : T.alphabet + 1 ≤ b) :
    (wordConstraintTiles E).card ≤ b ^ ((cycleCountExponent T) + channelCount T) := by
  have hwords : Fintype.card (Word T) ≤ b ^ channelCount T := by
    rw [Fintype.card_fun]
    have hs := (label_card_le T (.inl (0 : Column T))).trans hL
    change Fintype.card (Symbol T) ≤ b at hs
    apply (Nat.pow_le_pow_left hs _).trans
    apply Nat.pow_le_pow_right (by have := hb.two; omega)
    simp only [Column, Fintype.card_eq_nat_card, Nat.card_fin]
    unfold channelCount
    omega
  unfold wordConstraintTiles
  apply Finset.card_biUnion_le.trans
  calc
    _ ≤ ∑ _w ∈ (Finset.univ.filter (fun w : Word T => w ∉ allowedWords T)),
        b ^ (cycleCountExponent T) :=
      Finset.sum_le_sum (fun _ _ => cycleTiles_card_le hb _ _)
    _ ≤ Fintype.card (Word T) * b ^ (cycleCountExponent T) := by
      simp only [Finset.sum_const, smul_eq_mul]
      exact Nat.mul_le_mul_right _ (Finset.card_filter_le _ _)
    _ ≤ b ^ channelCount T * b ^ (cycleCountExponent T) := Nat.mul_le_mul_right _ hwords
    _ = _ := by rw [← pow_add]; congr 1; omega

theorem seedConstraintTiles_card_le (hb : ParameterBudget E b)
    (hC : channelCount T ≤ b) (hL : T.alphabet + 1 ≤ b) :
    (seedConstraintTiles E).card ≤ b ^ ((cycleCountExponent T) + 3) := by
  have hN : Fintype.card (Column T) ≤ b := by
    apply le_trans (b := channelCount T) _ hC
    simp only [Column, Fintype.card_eq_nat_card, Nat.card_fin]
    unfold channelCount
    omega
  have hs := (label_card_le T (.inl (0 : Column T))).trans hL
  change Fintype.card (Symbol T) ≤ b at hs
  have hindex : Fintype.card (Fin 2 × Column T × Symbol T) ≤ b ^ 3 := by
    calc
      _ = 2 * (Fintype.card (Column T) * Fintype.card (Symbol T)) := by
        rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_prod]
      _ ≤ b * (b * b) := Nat.mul_le_mul hb.two (Nat.mul_le_mul hN hs)
      _ = _ := by ring
  unfold seedConstraintTiles
  apply Finset.card_biUnion_le.trans
  calc
    _ ≤ ∑ _q ∈ (Finset.univ.filter (fun q : Fin 2 × Column T × Symbol T =>
        ¬ SeedSet T q.1 q.2.2)), b ^ (cycleCountExponent T) :=
      Finset.sum_le_sum (fun _ _ => cycleTiles_card_le hb _ _)
    _ ≤ Fintype.card (Fin 2 × Column T × Symbol T) * b ^ (cycleCountExponent T) := by
      simp only [Finset.sum_const, smul_eq_mul]
      exact Nat.mul_le_mul_right _ (Finset.card_filter_le _ _)
    _ ≤ b ^ 3 * b ^ (cycleCountExponent T) := Nat.mul_le_mul_right _ hindex
    _ = _ := by rw [← pow_add]; congr 1; omega

theorem dependenceTiles_card_le (hb : ParameterBudget E b) (hC : channelCount T ≤ b) :
    (dependenceTiles E).card ≤ b ^ 4 := by
  have hN : Fintype.card (Column T) ≤ b := by
    apply le_trans (b := channelCount T) _ hC
    simp only [Column, Fintype.card_eq_nat_card, Nat.card_fin]
    unfold channelCount
    omega
  have hsub (i : Channel T) : Fintype.card {j : Channel T // j ≠ i} ≤ b :=
    (Fintype.card_le_of_injective Subtype.val Subtype.val_injective).trans
      (by simpa only [channel_card] using hC)
  have hpair : Fintype.card (Σ i : Channel T, {j : Channel T // j ≠ i}) ≤ b * b := by
    rw [Fintype.card_sigma]
    apply (Finset.sum_le_sum (fun i _ => hsub i)).trans
    simpa only [Finset.sum_const, Finset.card_univ, smul_eq_mul, channel_card] using
      Nat.mul_le_mul_right b hC
  unfold dependenceTiles
  apply (Finset.card_image_le.trans (le_of_eq Finset.card_univ)).trans
  simp only [DependenceIndex, Fintype.card_sum, Fintype.card_prod,
    Fintype.card_fin, Fintype.card_bool]
  have h2 := hb.two
  have hp : b ^ 2 ≤ b ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have hsq : b ^ 2 + b + 4 ≤ b ^ 4 := by nlinarith [sq_nonneg (b - 2 : ℤ)]
  have hwidth : T.width ≤ b := by simpa [Column] using hN
  nlinarith

/-- Count the sparse finite families with their variable useful-output sizes.
This avoids the exponentially wasteful powerset of the ambient support. -/
theorem testTiles_card_le_direct (hb : ParameterBudget E b)
    (hC : channelCount T ≤ b) (hL : T.alphabet + 1 ≤ b) :
    (testTiles E).card ≤ b ^ testCountExponent T := by
  have h2 := hb.two
  have h1 : 1 ≤ b := by omega
  let e := (cycleCountExponent T) + channelCount T + 4
  have hdep := dependenceTiles_card_le hb hC
  have hword := wordConstraintTiles_card_le hb hL
  have hseed := seedConstraintTiles_card_le hb hC hL
  have hbound : ∀ k ≤ e, b ^ k ≤ b ^ e := fun _ hk => Nat.pow_le_pow_right h1 hk
  have hsingle : 1 ≤ b ^ e := Nat.one_le_pow _ _ h1
  have hact : (Finset.univ.image (ordinaryActivationTile E)).card ≤ b ^ e := by
    apply Finset.card_image_le.trans
    rw [Finset.card_univ]
    have hN : Fintype.card (Column T) ≤ channelCount T := by
      simp only [Column, Fintype.card_eq_nat_card, Nat.card_fin]
      unfold channelCount
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
  unfold testCountExponent
  change 6 * b ^ e ≤ b ^ (e + 6)
  rw [pow_add b e 6]
  simpa only [Nat.mul_comm] using Nat.mul_le_mul_left (b ^ e) h6

end
end TranslationTiling.FiniteCompiler.Size
