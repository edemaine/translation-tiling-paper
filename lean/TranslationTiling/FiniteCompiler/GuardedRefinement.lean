import TranslationTiling.FiniteCompiler.ColumnRefinement
import TranslationTiling.FiniteCompiler.GuardedSystem

namespace TranslationTiling.FiniteCompiler.GuardedCompiler

open PairSmall
open scoped Classical
noncomputable section

local instance refinedSeedFrame : SeedFrame := compactSeedFrame

variable {T : LeanWang.TileSet} {d : ℕ} (code : Code T d)

local instance refinedAlphabet : AlphabetFamily (system code) := alphabet code
attribute [local instance] ColumnRefinement.family

variable (S : ColumnRefinement (system code))

def refinedPatterns : List (PartialTest S.system) :=
  (patterns code).map S.expand

/-- The choice of one letter per line is enough to recover a Wang tiling. -/
theorem wang_of_refined_selection (W : WordArray S.system)
    (hs : ∀ t : Fin 2, ∃ x : Plane, ∀ i,
      LetterSeedSet S.system t i (W i (lineValue S.system i x)))
    (hr : ∀ x p, p ∈ refinedPatterns code S → p.columns.Nonempty →
      ¬ p.Matches (fun i => W i (lineValue S.system i x))) : LeanWang.TilesPlane T := by
  let V := S.unpackArray W
  have hseed (t : Fin 2) : ∃ x : Plane, ∀ i,
      LetterSeedSet (system code) t i (V i (lineValue (system code) i x)) := by
    obtain ⟨x,hx⟩ := hs t
    refine ⟨x,?_⟩
    intro i
    have he := S.unpack_seed hx i
    rwa [S.unpack_line] at he
  have havoid (x : Plane) (p : PartialTest (system code)) (hp : p ∈ patterns code)
      (hne : p.columns.Nonempty) :
      ¬ p.Matches (fun i => V i (lineValue (system code) i x)) := by
    intro hm
    have he := S.expand_matches p (fun j => W j (lineValue S.system j x))
    rw [S.unpack_line] at he
    exact hr x (S.expand p) (List.mem_map.mpr ⟨p,hp,rfl⟩) (S.expand_nonempty hne) (he.mpr hm)
  obtain ⟨hp,hq,hg⟩ := patterns_complete code V havoid
  exact Sudoku.PairBoard.guarded_soundness T _ hg hp hq (nonconstant_of_seeds code V hseed)

theorem refined_deck_equiv (E : EncodingParameters S.system) : LeanWang.TilesPlane T ↔
    ∃ A : Set (Ambient E), ∀ F ∈ partialDeck E (refinedPatterns code S), Tiles F A := by
  constructor
  · intro h
    obtain ⟨W, hW, hs⟩ := exists_wordArray_of_wang code h
    let V := S.packArray W
    have hs' (t : Fin 2) (j : Column S.system) (x : Plane)
        (hx : SharedSeed.residue S.system x ∈ seedActiveRegion S.system t) :
        LetterSeedSet S.system t j (V j (lineValue S.system j x)) := by
      have he : SharedSeed.residue (system code) x ∈ seedActiveRegion (system code) t := hx
      have ht := S.pack_seed (fun i => hs t i x he) j
      exact ht
    have hS := CommonModel.common_solution E V (S.pack_lineRule hW) hs'
    refine ⟨_, tiles_partialDeck_of_solves E _ hS ?_⟩
    intro p hp w hw
    simp only [refinedPatterns, List.mem_map] at hp
    obtain ⟨p,hp,rfl⟩ := hp
    change Allowed (system code) (S.unpackWord w) at hw
    exact fun hm => patterns_sound code p hp _ hw ((S.expand_matches p w).mp hm)
  · rintro ⟨A,hA⟩
    obtain ⟨W,hs,hr⟩ := partialDeck_array E _ hA
    exact wang_of_refined_selection code S W hs hr

end
end TranslationTiling.FiniteCompiler.GuardedCompiler
