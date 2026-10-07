import TranslationTiling.Proofs.FiniteSearch
import LeanWang.Kari.Final
import TranslationTiling.Proofs.Dimension
import TranslationTiling.Proofs.Euclidean
import TranslationTiling.Connectivity
import TranslationTiling.Proofs.FiniteConnectivity

namespace TranslationTiling

/-- Complexity consequences require an actual compiler with computability and correctness proofs. -/
theorem coRE_hard_of_reduction (r : WangReduction) : LeanWang.CoREHard (@Tiles 3) := by
  intro α _ P hP
  exact (LeanWang.Kari.domino_problem_coRE_hard P hP).trans
    ⟨r.tile, r.computable, r.correct⟩

theorem coRE_complete_of_reduction (r : WangReduction) :
    LeanWang.CoREComplete (@Tiles 3) :=
  ⟨tiles_coRE 3, coRE_hard_of_reduction r⟩

theorem undecidable_of_reduction (r : WangReduction) :
    ¬ ComputablePred (@Tiles 3) := by
  intro h
  exact LeanWang.Kari.domino_problem_undecidable
    (ComputablePred.computable_of_manyOneReducible ⟨r.tile, r.computable, r.correct⟩ h)

/-- The same computable reduction works in every fixed dimension at least three. -/
theorem coRE_complete_in_dimension (r : WangReduction) {d : ℕ} (hd : 3 ≤ d) :
    LeanWang.CoREComplete (@Tiles d) := by
  refine ⟨tiles_coRE d, ?_⟩
  intro α _ P hP
  exact (coRE_hard_of_reduction r P hP).trans
    ⟨fun F => F.map (pad hd), padTile_computable hd,
      fun F => (tiles_pad_iff hd F).symm⟩

theorem realTiles_coRE (d : ℕ) : LeanWang.CoREPred (@RealTiles d) :=
  (tiles_coRE d).of_eq fun F => (not_congr (realTiles_iff_tiles F)).symm

theorem real_coRE_complete_of_reduction (r : WangReduction) :
    LeanWang.CoREComplete (@RealTiles 3) := by
  refine ⟨realTiles_coRE 3, ?_⟩
  intro α _ P hP
  exact (coRE_hard_of_reduction r P hP).trans
    ⟨id, Computable.id, fun F => (realTiles_iff_tiles F).symm⟩

/-- Connected output suffices for hardness of the connected-input problem. -/
theorem connected_hard_of_reduction (r : ConnectedWangReduction) :
    LeanWang.CoREHard (@ConnectedTiles 3) := by
  intro α _ P hP
  refine (LeanWang.Kari.domino_problem_coRE_hard P hP).trans
    ⟨r.tile, r.computable, ?_⟩
  intro T
  constructor
  · intro ht
    have hn : T ≠ [] := by
      intro he
      obtain ⟨τ, _⟩ := ht
      have hmem := (τ (0, 0)).property
      simp [he] at hmem
    exact ⟨r.connected T hn, (r.correct T).mp ht⟩
  · intro ht
    exact (r.correct T).mpr ht.2

theorem connected_complete_of_reduction (r : ConnectedWangReduction) :
    LeanWang.CoREComplete (@ConnectedTiles 3) :=
  ⟨connectedTiles_coRE 3, connected_hard_of_reduction r⟩

/-- The least undecidable dimension follows from the reduction and planar decidability. -/
theorem optimal_dimension_of_planar (r : WangReduction)
    (planar : ComputablePred (@Tiles 2)) :
    IsLeast {d : ℕ | ¬ ComputablePred (@Tiles d)} 3 := by
  refine ⟨undecidable_of_reduction r, ?_⟩
  intro d hd
  by_contra h
  have hdim : d ≤ 2 := by omega
  exact hd (ComputablePred.computable_of_manyOneReducible
    ⟨fun F : Tile d => F.map (pad hdim), padTile_computable hdim,
      fun F => (tiles_pad_iff hdim F).symm⟩ planar)

end TranslationTiling
