import TranslationTiling.FiniteCompiler.Effective.Families

namespace TranslationTiling.FiniteCompiler.Effective
open Compiler Compiler.Effective
open scoped Classical
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 500000

theorem decodedTile_eq_image {T : System} (E : EncodingParameters T) (F : CyclicTile) :
    F.toFinset.image (decodeNumericalPoint E) =
      (cyclicTileSet E.cyclicOrder F).image (ambientCyclicEquiv E).symm := by
  rw [cyclicTileSet,Finset.image_image]
  apply Finset.image_congr
  intro f _
  change (f.1,numericalFactor E f.2) = _
  rw [numericalFactor_eq]
  rfl

theorem decodedFamily_card {T : System} (E : EncodingParameters T) (Fs : List CyclicTile) :
    (decodedFamily E Fs).card = (Fs.toFinset.image (cyclicTileSet E.cyclicOrder)).card := by
  have he : decodedFamily E Fs =
      (Fs.toFinset.image (cyclicTileSet E.cyclicOrder)).image
        (fun F => F.image (ambientCyclicEquiv E).symm) := by
    ext F
    simp only [decodedFamily,List.mem_toFinset,List.mem_map,Finset.mem_image,decodedTile_eq_image]
    constructor
    · rintro ⟨xs,hxs,rfl⟩; exact ⟨_,⟨xs,hxs,rfl⟩,rfl⟩
    · rintro ⟨_,⟨xs,hxs,rfl⟩,rfl⟩; exact ⟨xs,hxs,rfl⟩
  rw [he]
  apply Finset.card_image_of_injective
  exact Finset.image_injective (ambientCyclicEquiv E).symm.injective

theorem canonicalDecoded_correct {T : System} (E : EncodingParameters T)
    (H : ℕ) (Fs : List CyclicTile)
    (hb : ∀ F ∈ Fs, ∀ f ∈ F, f.1.1.natAbs ≤ H ∧ f.1.2.natAbs ≤ H) :
    decodedFamily E (canonicalFamily H E.cyclicOrder Fs) = decodedFamily E Fs := by
  have he (F : CyclicTile) (hF : F ∈ Fs) :
      (canonicalTile H E.cyclicOrder F).toFinset.image (decodeNumericalPoint E) =
        F.toFinset.image (decodeNumericalPoint E) := by
    rw [decodedTile_eq_image,canonicalTile_correct H E.cyclicOrder E.cyclicOrder_pos F
        (fun f hf => ⟨by have ha := (hb F hF f hf).1; rcases Int.natAbs_eq f.1.1 with h | h <;> omega,
          by have ha := (hb F hF f hf).2; rcases Int.natAbs_eq f.1.2 with h | h <;> omega⟩),
      ← decodedTile_eq_image]
  ext F
  simp only [mem_decodedFamily,canonicalFamily,List.mem_dedup,List.mem_map]
  constructor
  · rintro ⟨xs,⟨ys,hys,rfl⟩,hxs⟩
    exact ⟨ys,hys,(he ys hys).symm.trans hxs⟩
  · rintro ⟨ys,hys,rfl⟩
    exact ⟨_,⟨ys,hys,rfl⟩,he ys hys⟩

theorem rawFamily_horizontal (T : System) (p : Payload) (hp : PayloadCorrect T p)
    (hpos : ∀ n, 0 ≤ T.slope n) (hS : ∀ n, (T.slope n).natAbs ≤ Sudoku.Width) :
    ∀ F ∈ rawFamily (parameterData T,p), ∀ f ∈ F,
      f.1.1.natAbs ≤ rawHorizontal (parameterData T) ∧
      f.1.2.natAbs ≤ rawHorizontal (parameterData T) := by
  intro F hF f hf
  have hm : F.toFinset.image (decodeNumericalPoint (parameters T)) ∈ testTiles (parameters T) := by
    rw [← rawFamily_correct T p hp hpos]
    exact (mem_decodedFamily _ _ _).mpr ⟨F,hF,rfl⟩
  exact Size.testTile_horizontal_bound (parameters_budget T Sudoku.Width hS).1 hm
    (Finset.mem_image.mpr ⟨f,List.mem_toFinset.mpr hf,rfl⟩)

theorem canonicalInputFamily_correct (T : System) (p : Payload) (hp : PayloadCorrect T p)
    (hpos : ∀ n, 0 ≤ T.slope n) (hS : ∀ n, (T.slope n).natAbs ≤ Sudoku.Width) :
    decodedFamily (parameters T) (canonicalInputFamily (parameterData T,p)) = testTiles (parameters T) := by
  unfold canonicalInputFamily
  rw [rawOrder_eq,canonicalDecoded_correct _ _ _ (rawFamily_horizontal T p hp hpos hS),
    rawFamily_correct T p hp hpos]

theorem canonicalInputFamily_length (T : System) (p : Payload) (hp : PayloadCorrect T p)
    (hpos : ∀ n, 0 ≤ T.slope n) (hS : ∀ n, (T.slope n).natAbs ≤ Sudoku.Width) :
    (canonicalInputFamily (parameterData T,p)).length = (testTiles (parameters T)).card := by
  rw [← canonicalInputFamily_correct T p hp hpos hS,decodedFamily_card]
  unfold canonicalInputFamily
  rw [rawOrder_eq]
  exact canonicalFamily_length _ _ _

end
end TranslationTiling.FiniteCompiler.Effective
