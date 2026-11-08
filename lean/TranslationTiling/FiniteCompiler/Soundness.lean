import TranslationTiling.FiniteCompiler.EncodedSystem
import TranslationTiling.FiniteCompiler.Activation

namespace TranslationTiling.FiniteCompiler

noncomputable section

/-- Every common tiling yields a line-rule array meeting both seed predicates. -/
theorem array_of_solves {T : System} (E : EncodingParameters T)
    {A : Set (Ambient E)} (hA : Solves E A) :
    ∃ W : WordArray T, LineRule T W ∧
      ∀ t : Fin 2, ∃ x : Plane, ∀ n, SeedSet T t (W n (lineValue T n x)) := by
  classical
  obtain ⟨o, rfl⟩ := exists_graph_of_solves E hA
  obtain ⟨_, hd, hw, hs, ha, hb⟩ := (solves_iff E (graph o)).mp hA
  have hdep := (dependenceTiles_iff E o).mp hd
  have hword := (wordConstraintTiles_iff E o hdep).mp hw
  have hseed := (seedConstraintTiles_iff E o hdep).mp hs
  have hactive (n : Column T) (m : ℤ) : ∃ j, Active E o (.inl n) (0, m) j :=
    ordinary_active_of_tile E o hdep n (ha n) (0, m)
  choose W hW using hactive
  have hW' (n : Column T) (x : Plane) : Active E o (.inl n) x (W n (lineValue T n x)) :=
    (active_ordinary_iff E hdep n (by simp : lineValue T n (0, lineValue T n x) =
      lineValue T n x) _).mp (hW n _)
  refine ⟨W, fun x => hword x _ (fun n => hW' n x), ?_⟩
  intro t
  obtain ⟨x, hx⟩ := seed_active_somewhere_of_tile E o hdep t (hb t)
  exact ⟨x, fun n => hseed t n x _ hx (hW' n x)⟩

end
end TranslationTiling.FiniteCompiler
