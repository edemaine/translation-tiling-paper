import TranslationTiling.FiniteCompiler.CountBounds
import TranslationTiling.Compiler.ClosedGeometryBound

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace TranslationTiling.FiniteCompiler.Size

open scoped Classical BigOperators
noncomputable section

def commonCap (b C : ℕ) : ℕ := b ^ (12 * C)
def stackPolynomial (x : ℕ) : ℕ := x * (2 * (8 * x ^ 5 + x + 3))

theorem le_commonCap {b C : ℕ} (hC : 1 ≤ C) : b ≤ commonCap b C := by
  exact Nat.le_self_pow (by omega : 12 * C ≠ 0) b

theorem cyclicOrder_le {T : System} {E : EncodingParameters T} {b : ℕ}
    (hb : ParameterBudget E b) : E.cyclicOrder ≤ b ^ (4 * channelCount T + 2) := by
  have hblock (i : Channel T) : E.blockModulus i ≤ b ^ 4 := by
    unfold EncodingParameters.blockModulus
    calc
      _ ≤ b ^ 2 * b * b := by
        gcongr
        · exact hb.r i
        · exact hb.a i
        · exact hb.usefulB i
      _ = _ := by ring
  unfold EncodingParameters.cyclicOrder
  calc
    _ ≤ b ^ 2 * ∏ _i : Channel T, b ^ 4 :=
      Nat.mul_le_mul (Nat.pow_le_pow_left hb.width 2)
        (Finset.prod_le_prod (fun i _ => hblock i))
    _ = b ^ 2 * (b ^ 4) ^ channelCount T := by simp only [Finset.prod_const,
        Finset.card_univ, channel_card]
    _ = _ := by rw [← pow_mul, ← pow_add]; congr 1; omega

theorem cyclicOrder_le_commonCap {T : System} {E : EncodingParameters T} {b : ℕ}
    (hb : ParameterBudget E b) : E.cyclicOrder ≤ commonCap b (channelCount T) :=
  (cyclicOrder_le hb).trans (Nat.pow_le_pow_right (by have := hb.two; omega)
    (by unfold channelCount; omega))

theorem testTiles_card_le_commonCap {T : System} {E : EncodingParameters T} {b : ℕ}
    (hb : ParameterBudget E b) (hC : channelCount T ≤ b) (hL : T.alphabet + 1 ≤ b) :
    (testTiles E).card ≤ commonCap b (channelCount T) :=
  (testTiles_card_le_direct hb hC hL).trans
    (Nat.pow_le_pow_right (by have := hb.two; omega)
      (by unfold testCountExponent cycleCountExponent channelCount; omega))

theorem exists_cyclic_tile_of_budget {T : System} {E : EncodingParameters T} {b : ℕ}
    (hb : ParameterBudget E b) (hC : channelCount T ≤ b) (hL : T.alphabet + 1 ≤ b)
    {P : Prop} (hcorrect : P ↔ ∃ A : Set (Ambient E), Solves E A) :
    ∃ m : ℕ, 0 < m ∧ m ≤ stackPolynomial (commonCap b (channelCount T)) ∧
      ∃ F : Finset (Plane × ZMod m), F.Nonempty ∧
        (P ↔ ∃ A, Tiles F A) ∧
        ∀ f ∈ F, f.1.1.natAbs ≤ horizontalCap b ∧ f.1.2.natAbs ≤ horizontalCap b := by
  let x := commonCap b (channelCount T)
  let s := Fintype.card (TestIndex E)
  have hs : 0 < s := Fintype.card_pos
  have hsbound : s ≤ x := by
    simpa only [s, TestIndex, Fintype.card_coe] using testTiles_card_le_commonCap hb hC hL
  have hV : E.cyclicOrder ≤ x := cyclicOrder_le_commonCap hb
  let threshold := 8 * x ^ 5 + x + 3
  obtain ⟨q, hq, hqlarge, hqbound⟩ := Nat.bertrand threshold (by dsimp [threshold]; omega)
  have hlarge : E.cyclicOrder < q := by dsimp [threshold] at hqlarge; omega
  have hbig : 8 * s ^ 5 + 3 ≤ q := by
    have hpow := Nat.pow_le_pow_left hsbound 5
    dsimp [threshold] at hqlarge
    omega
  obtain ⟨Es, hpart, hfull⟩ := Compiler.Size.partition_at_prime s q hs hq hbig
  let : NeZero q := ⟨hq.ne_zero⟩
  let : Nonempty (Fin s) := ⟨⟨0, hs⟩⟩
  let ei : TestIndex E ≃ Fin s := Fintype.equivFin _
  let Fs : Fin s → Finset (Ambient E) := fun i => testTile E (ei.symm i)
  have hFs (i : Fin s) : (Fs i).Nonempty := testTile_nonempty E (ei.symm i)
  have hEs : ∀ i, (Es i).Nonempty := hfull.nonempty
  have hnonempty := Stacking.stack_nonempty hFs hEs
  have hstack := Stacking.exists_tiles_stack_iff (F := Fs) hpart hfull hEs
  have hcop : Nat.Coprime E.cyclicOrder q := by
    apply Nat.Coprime.symm
    apply (hq.coprime_iff_not_dvd).mpr
    intro hd
    exact (not_le_of_gt hlarge) (Nat.le_of_dvd E.cyclicOrder_pos hd)
  let ec : (Ambient E × ZMod q) ≃+ (Plane × ZMod (E.cyclicOrder * q)) :=
    (AddEquiv.prodAssoc).trans
      (AddEquiv.prodCongr (AddEquiv.refl Plane)
        ((AddEquiv.prodCongr (finiteFactorEquiv E) (AddEquiv.refl (ZMod q))).trans
          (ZMod.chineseRemainder hcop).toAddEquiv.symm))
  refine ⟨E.cyclicOrder * q, Nat.mul_pos E.cyclicOrder_pos hq.pos,
    (by exact Nat.mul_le_mul hV hqbound),
    (Stacking.stack Fs Es).image ec, hnonempty.image ec, ?_, ?_⟩
  · have hsys : (∃ A : Set (Ambient E), Solves E A) ↔
        ∃ A : Set (Ambient E), ∀ i, Stacking.Covers (Fs i) A := by
      constructor
      · rintro ⟨A, hA⟩
        exact ⟨A, fun i => hA _ (ei.symm i).property⟩
      · rintro ⟨A, hA⟩
        refine ⟨A, (solves_iff_index E A).mpr ?_⟩
        intro i
        simpa only [Fs, Equiv.symm_apply_apply] using hA (ei i)
    exact hcorrect.trans (hsys.trans (hstack.trans (Compiler.exists_covers_image_iff ec _)))
  · intro f hf
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hf
    obtain ⟨i, hi, _⟩ := Stacking.mem_stack.mp hg
    exact testTile_horizontal_bound hb (ei.symm i).property hi

end
end TranslationTiling.FiniteCompiler.Size
