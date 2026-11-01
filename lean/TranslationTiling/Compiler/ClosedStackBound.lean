import TranslationTiling.Compiler.ClosedBudget
import TranslationTiling.Compiler.Consolidation

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace TranslationTiling.Compiler.Size

open scoped Classical
noncomputable section

/-- A prime at least this large admits the required difference partition. -/
theorem partition_at_prime (s q : ℕ) (hs : 0 < s) (hq : q.Prime)
    (hbig : 8 * s ^ 5 + 3 ≤ q) :
    ∃ E : Fin s → Finset (ZMod q),
      Stacking.IsColorPartition E ∧ Stacking.HasFullDifferences E := by
  let : Fact q.Prime := ⟨hq⟩
  have hq2 : 2 < q := by omega
  obtain ⟨E, _, hpart, hfull⟩ := (by
    by_cases hs1 : s = 1
    · subst s
      let c : Stacking.Coloring q 1 := fun _ => 0
      apply Stacking.exists_partition_of_nonzero_coloring c
      intro ν d _hd
      have hν : (0 : Fin 1) = ν := Subsingleton.elim _ _
      exact ⟨d, 0, hν, hν, sub_zero d⟩
    · have hs2 : 2 ≤ s := by omega
      have hodd : q % 2 = 1 := hq.eq_two_or_odd.resolve_left (by omega)
      have hqm : q = 2 * (q / 2) + 1 := by omega
      have hm : 4 * s ^ 5 + 1 ≤ q / 2 := by omega
      obtain ⟨c, hc⟩ := Stacking.exists_coloring_nonzero_differences hs2 hqm hm
      exact Stacking.exists_partition_of_nonzero_coloring c hc :
    ∃ E : Fin s → Finset (ZMod q),
      (∀ i, (E i).Nonempty) ∧ (∀ x, ∃! i, x ∈ E i) ∧
        ∀ i d, ∃ x ∈ E i, ∃ y ∈ E i, x - y = d)
  exact ⟨E, hpart, hfull⟩

def stackCap (b : ℕ) : ℕ := 2 * (8 * (2 ^ supportVolume b) ^ 5 + finiteCap b + 3)
def modulusCap (b : ℕ) : ℕ := finiteCap b * stackCap b

/-- Consolidation with an explicit upper bound on the stacking prime, rather
than an unbounded search through encoded certificates. -/
theorem exists_bounded_cyclic_tile {T : LeanWang.TileSet} {E : EncodingParameters T}
    {b : ℕ} (hb : ParameterBudget E b) :
    ∃ m : ℕ, 0 < m ∧ m ≤ modulusCap b ∧
      ∃ F : Finset (Plane × ZMod m), F.Nonempty ∧
        (LeanWang.TilesPlane T ↔ ∃ A, Tiles F A) ∧
        ∀ f ∈ F, f.1.1.natAbs ≤ horizontalCap b ∧ f.1.2.natAbs ≤ horizontalCap b := by
  let s := Fintype.card (TestIndex E)
  have hs : 0 < s := Fintype.card_pos
  have hsbound : s ≤ 2 ^ supportVolume b := by
    simpa only [s, TestIndex, Fintype.card_coe] using testTiles_card_le hb
  let threshold := 8 * (2 ^ supportVolume b) ^ 5 + finiteCap b + 3
  obtain ⟨q, hq, hqlarge, hqbound⟩ := Nat.bertrand threshold (by dsimp [threshold]; omega)
  have hlarge : E.cyclicOrder < q := by
    have h := cyclicOrder_le hb
    dsimp [threshold] at hqlarge
    omega
  have hbig : 8 * s ^ 5 + 3 ≤ q := by
    have hpow := Nat.pow_le_pow_left hsbound 5
    dsimp [threshold] at hqlarge
    omega
  obtain ⟨Es, hpart, hfull⟩ := partition_at_prime s q hs hq hbig
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
    Nat.mul_le_mul (cyclicOrder_le hb) hqbound,
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
    exact (finite_system_iff_wang Sudoku.soundness E).trans
      (hsys.trans (hstack.trans (exists_covers_image_iff ec _)))
  · intro f hf
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hf
    obtain ⟨i, hi, _⟩ := Stacking.mem_stack.mp hg
    exact testTile_horizontal_bound hb (ei.symm i).property hi

end
end TranslationTiling.Compiler.Size
