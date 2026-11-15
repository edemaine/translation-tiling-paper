import TranslationTiling.FiniteCompiler.TernaryBounds
import TranslationTiling.FiniteCompiler.CompactParameters
import TranslationTiling.FiniteCompiler.TernarySystem

namespace TranslationTiling.FiniteCompiler.Size
open Compiler.Size
open scoped Classical BigOperators
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem exists_cyclic_tile_of_caps {T : System} {E : EncodingParameters T} {b : ℕ}
    (hb : ParameterBudget E b) (hC : channelCount T ≤ b) (hL : T.alphabet + 1 ≤ b)
    (vCap sCap : ℕ) (hVcap : E.cyclicOrder ≤ vCap) (hscap : (testTiles E).card ≤ sCap)
    {P : Prop} (hcorrect : P ↔ ∃ A : Set (Ambient E), Solves E A) :
    ∃ m : ℕ, 0 < m ∧ m ≤ separateModulusCap vCap sCap ∧
      ∃ F : Finset (Plane × ZMod m), F.Nonempty ∧
        (P ↔ ∃ A, Tiles F A) ∧
        ∀ f ∈ F, f.1.1.natAbs ≤ horizontalCap b ∧ f.1.2.natAbs ≤ horizontalCap b := by
  let s := Fintype.card (TestIndex E)
  have hs : 0 < s := Fintype.card_pos
  have hsbound : s ≤ sCap := by
    simpa only [s, TestIndex, Fintype.card_coe] using hscap
  let threshold := 8 * sCap ^ 5 + vCap + 3
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
    (by exact Nat.mul_le_mul hVcap hqbound),
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


theorem exists_connected_tile_ternary_channel_bound (T : System) (W : LeanWang.TileSet)
    (hB : T.alphabet = 3) (hC : 20 * Sudoku.Width + 2 ≤ channelCount T)
    (hS : ∀ n, (T.slope n).natAbs ≤ Sudoku.Width)
    (hcorrect : ∀ E : EncodingParameters T,
      LeanWang.TilesPlane W ↔ ∃ A : Set (Ambient E), Solves E A) :
    ∃ P : Tile 3, P ≠ [] ∧ FaceConnected P ∧
      (LeanWang.TilesPlane W ↔ TranslationTiling.Tiles P) ∧
      cubeCount P ≤ channelCount T ^ (3510 * channelCount T) := by
  have hc : 1202≤channelCount T := by
    have hw : 61≤Sudoku.Width := by norm_num [Sudoku.Width,Sudoku.q]
    omega
  obtain ⟨E,_,_,hcompact⟩ := exists_compact_parameters T hc hB
  have hp : SmallPrimes E := ⟨fun i => ⟨(hcompact.1 i).1.trans (Nat.pow_le_pow_right (by omega) (by decide)),
    (hcompact.1 i).2.trans (Nat.pow_le_pow_right (by omega) (by decide))⟩,
    fun i j => (hcompact.2.1 i j).trans (Nat.pow_le_pow_right (by omega) (by decide))⟩
  have hb := smallPrimes_budget E hB hp hC hS
  have h1 : 1 ≤ channelCount T := by unfold channelCount; omega
  have hself : channelCount T ≤ channelCount T ^ 73 := Nat.le_self_pow (by decide) _
  have hL : T.alphabet + 1 ≤ channelCount T ^ 73 := by
    rw [hB]
    have : 4 ≤ channelCount T := by
      have : 4 ≤ Sudoku.Width := by norm_num [Sudoku.Width,Sudoku.p,Sudoku.q]
      omega
    exact this.trans hself
  obtain ⟨m, hm, hcap, F, hF, hiff, hcoord⟩ := exists_cyclic_tile_of_caps hb hself hL
    (channelCount T ^ (119 * channelCount T)) (channelCount T ^ (30 * channelCount T))
    (ternary_cyclicOrder_le E hB hp hC) (ternary_testTiles_card_le E hB hp hC hS) (hcorrect E)
  obtain ⟨P,hP,hconn,hiffP,hsize⟩ := Compiler.Size.exists_bounded_connected_tile hm
    (hcap.trans (ternary_modulus_cap_le hC)) F hF hiff hcoord
  exact ⟨P,hP,hconn,hiffP,hsize.trans (ternary_geometry_bound hC le_rfl hb.two)⟩

end
end TranslationTiling.FiniteCompiler.Size
