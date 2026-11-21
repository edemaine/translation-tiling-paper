import TranslationTiling.Compiler.FiniteNormalizedInput
import TranslationTiling.Compiler.EmptyInputBound
import TranslationTiling.Examples

namespace TranslationTiling.Compiler.Size

open scoped Classical
noncomputable section

/-- A fixed finite table on normalized inputs of a specified length.
Its entries can also be computed for lengths at most ten using Jeandel–Rao. -/
def smallLookup (n : ℕ) (hn : 0 < n) (T : LeanWang.TileSet) : Tile 3 :=
  if LeanWang.TilesPlane (decodeInput n (inputIndex n hn T)) then [0] else emptyTile

theorem smallLookup_computable (n : ℕ) (hn : 0 < n) : Computable (smallLookup n hn) :=
  (Effective.finFunction_primrec (fun i : Fin (inputs n).length =>
    if LeanWang.TilesPlane (decodeInput n i) then [0] else emptyTile)).to_comp.comp
    (inputIndex_primrec n hn).to_comp

theorem smallLookup_facts (n : ℕ) (hn : 0 < n) (T : LeanWang.TileSet)
    (h : T.length = n) :
    smallLookup n hn T ≠ [] ∧ FaceConnected (smallLookup n hn T) ∧
      (LeanWang.TilesPlane T ↔ TranslationTiling.Tiles (smallLookup n hn T)) ∧
      (smallLookup n hn T).length ≤ 2^250 := by
  have he := normalize_tilesPlane T
  unfold smallLookup
  rw [decodeInput_index n hn T h]
  by_cases ht : LeanWang.TilesPlane (normalize T)
  · rw [ite_eq_left ht]
    refine ⟨by simp, ?_, iff_of_true (he.mp ht) (tiles_singleton 0), by norm_num⟩
    intro p hp q hq
    rw [List.mem_singleton.mp hp, List.mem_singleton.mp hq]
  · rw [ite_eq_right ht]
    obtain ⟨hne,hc,hnontile,hsize⟩ := emptyTile_facts
    exact ⟨hne,hc,iff_of_false (fun h => ht (he.mpr h)) hnontile,hsize⟩

end
end TranslationTiling.Compiler.Size
