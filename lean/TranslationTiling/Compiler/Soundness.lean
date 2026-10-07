import TranslationTiling.Compiler.EncodedSystem
import TranslationTiling.Compiler.Activation
import TranslationTiling.Proofs.SudokuSoundness

set_option maxRecDepth 1000

namespace TranslationTiling.Compiler

noncomputable section

variable {T : LeanWang.TileSet} (E : EncodingParameters T)

/-- The active labels of any common tiling give the concrete decorated Sudoku
system. No gadget correctness assumption is used here. -/
def activeSystemOfSolves {A : Set (Ambient E)} (hA : Solves E A) : Sudoku.ActiveSystem T := by
  classical
  let o := (exists_graph_of_solves E hA).choose
  have ho : graph o = A := (exists_graph_of_solves E hA).choose_spec
  have hsol := (solves_iff E (graph o)).mp (ho.symm ▸ hA)
  have hd := hsol.2.1
  have hw := hsol.2.2.1
  have hs := hsol.2.2.2.1
  have ha := hsol.2.2.2.2.1
  have hb := hsol.2.2.2.2.2
  have hdep := (dependenceTiles_iff E o).mp hd
  have hword := (wordConstraintTiles_iff E o hdep).mp hw
  have hseed := (seedConstraintTiles_iff E o hdep).mp hs
  have hline (n : Column T) (d e : ℤ) :
      lineValue n (0, d * n.val + e) = lineValue n (d, e) := by
    simp only [lineValue, zero_mul, add_zero]
    ring
  refine {
    labels := fun n m => Finset.univ.filter (Active E o (.inl n) (0, m))
    nonempty := ?_
    allowed := ?_
    seed₁ := ?_
    seed₂ := ?_
  }
  · intro n m
    obtain ⟨j, hj⟩ := ordinary_active_of_tile E o hdep n (ha n) (0, m)
    exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩⟩
  · intro d e w hw
    apply hword (d, e) w
    intro n
    exact (active_ordinary_iff E hdep n (hline n d e) (w n)).mp
      (Finset.mem_filter.mp (hw n)).2
  · obtain ⟨x, hx⟩ := seed_active_somewhere_of_tile E o hdep (0 : Fin 2) (hb 0)
    refine ⟨x.1, x.2, ?_⟩
    intro n j hj
    have hord := (active_ordinary_iff E hdep n (hline n x.1 x.2) j).mp
      (Finset.mem_filter.mp hj).2
    simpa [SeedSet] using hseed 0 n x j hx hord
  · obtain ⟨x, hx⟩ := seed_active_somewhere_of_tile E o hdep (1 : Fin 2) (hb 1)
    refine ⟨x.1, x.2, ?_⟩
    intro n j hj
    have hord := (active_ordinary_iff E hdep n (hline n x.1 x.2) j).mp
      (Finset.mem_filter.mp hj).2
    simpa [SeedSet] using hseed 1 n x j hx hord

theorem wang_of_solves (sound : Sudoku.Soundness) {A : Set (Ambient E)}
    (hA : Solves E A) : LeanWang.TilesPlane T :=
  Sudoku.activeSystem_tilesPlane sound (activeSystemOfSolves E hA)

end

end TranslationTiling.Compiler
