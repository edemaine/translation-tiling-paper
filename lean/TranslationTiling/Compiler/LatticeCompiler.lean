import TranslationTiling.Compiler.Consolidation
import TranslationTiling.Compiler.LatticeCompleteness

namespace TranslationTiling.Compiler

noncomputable section
open scoped Classical

theorem covers_shift {G : Type*} [AddCommGroup G] [DecidableEq G]
    (F : Finset G) (t : G) {A : Set G} (hA : Tiles F A) :
    Tiles (F.image (fun f => f + t)) {a | a + t ∈ A} := by
  apply Stacking.covers_iff_unique_tile.mpr
  intro x
  obtain ⟨f, hf, hu⟩ := Stacking.covers_iff_unique_tile.mp hA x
  refine ⟨⟨f.val + t, Finset.mem_image.mpr ⟨f.val, f.property, rfl⟩⟩, ?_, ?_⟩
  · change x - (f.val + t) + t ∈ A
    simpa only [sub_add_eq_sub_sub, sub_add_cancel] using hf
  · intro g hg
    obtain ⟨u, huF, hug⟩ := Finset.mem_image.mp g.property
    have huA : x - u ∈ A := by
      change x - g.val + t ∈ A at hg
      simpa only [← hug, sub_add_eq_sub_sub, sub_add_cancel] using hg
    have huf := congrArg Subtype.val (hu ⟨u, huF⟩ huA)
    exact Subtype.ext (hug.symm.trans (congrArg (· + t) huf))

theorem exists_covers_shift_iff {G : Type*} [AddCommGroup G] [DecidableEq G]
    (F : Finset G) (t : G) :
    (∃ A : Set G, Tiles F A) ↔ ∃ B : Set G, Tiles (F.image (fun f => f + t)) B := by
  constructor
  · rintro ⟨A, hA⟩
    exact ⟨_, covers_shift F t hA⟩
  · rintro ⟨B, hB⟩
    have h := covers_shift (F.image (fun f => f + t)) (-t) hB
    have he : (F.image (fun f => f + t)).image (fun f => f + -t) = F := by
      ext x
      simp
    exact ⟨_, he ▸ h⟩

/-- The concrete two-prime construction, finite consolidation, and MSS
assembly produce a finite integer tile with both tilability directions. -/
theorem exists_integer_tile (sound : Sudoku.Soundness) (rigid : MSS.Rigidity)
    (T : LeanWang.TileSet) :
    ∃ F : Finset (Lattice 3), F.Nonempty ∧
      (LeanWang.TilesPlane T ↔ ∃ A : Set (Lattice 3), Tiles F A) := by
  obtain ⟨Q, hQ, F, hF, hcorrect⟩ := exists_cyclic_tile sound T
  obtain ⟨f, hf⟩ := hF
  let F₀ := F.image (fun x => x - f)
  have h0 : 0 ∈ F₀ := Finset.mem_image.mpr ⟨f, hf, sub_self f⟩
  have hshift : (∃ A : Set (Plane × ZMod Q), Tiles F A) ↔ ∃ A, Tiles F₀ A := by
    simpa only [F₀, sub_eq_add_neg] using exists_covers_shift_iff F (-f)
  let U := CyclicQuotient.representatives Q F₀
  let G := LatticeGeometry.assembled Q U
  have hU0 : 0 ∈ U := CyclicQuotient.zero_mem_representatives Q h0
  have hG0 : 0 ∈ G := (LatticeGeometry.mem_assembled Q U 0).mpr
    ⟨0, hU0, 0, LatticeGeometry.zero_mem_part Q 0, by simp⟩
  exact ⟨G, ⟨0, hG0⟩,
    hcorrect.trans (hshift.trans (LatticeGeometry.assembled_iff_quotient rigid Q hQ F₀ h0))⟩

end

end TranslationTiling.Compiler
