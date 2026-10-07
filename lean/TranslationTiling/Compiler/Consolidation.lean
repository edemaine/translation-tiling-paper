import TranslationTiling.Compiler.Completeness
import TranslationTiling.Compiler.CyclicFactorCRT
import TranslationTiling.Compiler.EncodingPrimeSelection
import TranslationTiling.Proofs.CyclicStacking
import TranslationTiling.Compiler.EffectivePartition

namespace TranslationTiling.Compiler

noncomputable section
open scoped Classical

theorem covers_image {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    [DecidableEq G] [DecidableEq H]
    (e : G ≃+ H) (F : Finset G) (A : Set G) (hA : Tiles F A) :
    Tiles (F.image e) (e '' A) := by
  classical
  apply Stacking.covers_iff_exactTiling.mpr
  have h := exactTiling_transport e (Stacking.covers_iff_exactTiling.mp hA)
  have he : e '' (F : Set G) = (F.image e : Set H) := by
    ext x
    simp
  rwa [he] at h

theorem exists_covers_image_iff {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    [DecidableEq G] [DecidableEq H]
    (e : G ≃+ H) (F : Finset G) :
    (∃ A : Set G, Tiles F A) ↔ ∃ B : Set H, Tiles (F.image e) B := by
  classical
  constructor
  · rintro ⟨A, hA⟩
    exact ⟨e '' A, covers_image e F A hA⟩
  · rintro ⟨B, hB⟩
    have h := covers_image e.symm (F.image e) B hB
    have he : (F.image e).image e.symm = F := by
      ext x
      simp
    exact ⟨e.symm '' B, he ▸ h⟩

/-- The actual finite constraint family consolidates to one tile with a cyclic
finite factor. Both directions hold for arbitrary tilings of the output. -/
theorem exists_cyclic_tile (sound : Sudoku.Soundness) (T : LeanWang.TileSet) :
    ∃ Q : ℕ, 0 < Q ∧ ∃ F : Finset (Plane × ZMod Q), F.Nonempty ∧
      (LeanWang.TilesPlane T ↔ ∃ A : Set (Plane × ZMod Q), Tiles F A) := by
  classical
  let E := encodingParameters T
  let s := Fintype.card (TestIndex E)
  have hs : 0 < s := Fintype.card_pos
  let ei : TestIndex E ≃ Fin s := Fintype.equivFin _
  let Fs : Fin s → Finset (Ambient E) := fun i => testTile E (ei.symm i)
  have hFs (i : Fin s) : (Fs i).Nonempty := testTile_nonempty E (ei.symm i)
  obtain ⟨q, hq, hlarge, Es, hpart, hfull⟩ :=
    Effective.effective_partition s hs E.cyclicOrder
  letI : NeZero q := ⟨hq.ne_zero⟩
  letI : Nonempty (Fin s) := ⟨⟨0, hs⟩⟩
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
    (Stacking.stack Fs Es).image ec, hnonempty.image ec, ?_⟩
  have hsys : (∃ A : Set (Ambient E), Solves E A) ↔
      ∃ A : Set (Ambient E), ∀ i, Stacking.Covers (Fs i) A := by
    constructor
    · rintro ⟨A, hA⟩
      exact ⟨A, fun i => hA _ (ei.symm i).property⟩
    · rintro ⟨A, hA⟩
      refine ⟨A, (solves_iff_index E A).mpr ?_⟩
      intro i
      simpa only [Fs, Equiv.symm_apply_apply] using hA (ei i)
  exact (finite_system_iff_wang sound E).trans
    (hsys.trans (hstack.trans (exists_covers_image_iff ec _)))

end

end TranslationTiling.Compiler
