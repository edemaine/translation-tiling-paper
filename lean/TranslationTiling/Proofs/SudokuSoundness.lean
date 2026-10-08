import TranslationTiling.External.Sudoku
import TranslationTiling.Proofs.Wang
import Mathlib.Tactic.NormNum

namespace TranslationTiling.Sudoku

/-- The active-label properties obtained from dependence, exclusions, and
activation by `Compiler.activeSystemOfSolves` in `Compiler.Soundness`. -/
structure ActiveSystem (T : LeanWang.TileSet) where
  labels : Column → ℤ → Finset (Symbol T)
  nonempty : ∀ n m, (labels n m).Nonempty
  allowed : ∀ d e : ℤ, ∀ w : Column → Symbol T,
    (∀ n, w n ∈ labels n (d * n.val + e)) → Allowed T w
  seed₁ : ∃ d e : ℤ, ∀ n, ∀ s ∈ labels n (d * n.val + e),
    s.1.val = 1 ∧ s.2.1.val = 1
  seed₂ : ∃ d e : ℤ, ∀ n, ∀ s ∈ labels n (d * n.val + e),
    s.1.val = 2 ∧ s.2.1.val = 2

/-- Extracting any active label gives the line rule and nonconstancy of both arithmetic columns. -/
theorem activeSystem_tilesPlane (sound : Soundness) {T : LeanWang.TileSet}
    (S : ActiveSystem T) : LeanWang.TilesPlane T := by
  classical
  let W : Array T := fun n m => (S.nonempty n m).choose
  have hw (n m) : W n m ∈ S.labels n m := (S.nonempty n m).choose_spec
  have hrule : LineRule W := fun d e => S.allowed d e (fun n => W n (d * n.val + e))
    (fun n => hw n _)
  obtain ⟨d₁, e₁, hs₁⟩ := S.seed₁
  obtain ⟨d₂, e₂, hs₂⟩ := S.seed₂
  have hnonconstant : NonconstantColumns W := by
    constructor
    · intro n
      refine ⟨d₁ * n.val + e₁, d₂ * n.val + e₂, ?_⟩
      intro h
      have he := congrArg (fun s : (ZMod p)ˣ => s.val) h
      rw [(hs₁ n _ (hw n _)).1, (hs₂ n _ (hw n _)).1] at he
      exact (by decide : (1 : ZMod p) ≠ 2) he
    · intro n
      refine ⟨d₁ * n.val + e₁, d₂ * n.val + e₂, ?_⟩
      intro h
      have he := congrArg (fun s : (ZMod q)ˣ => s.val) h
      rw [(hs₁ n _ (hw n _)).2, (hs₂ n _ (hw n _)).2] at he
      exact (by decide : (1 : ZMod q) ≠ 2) he
  exact (wang_plane_iff_quadrant T).mpr (sound T W hrule hnonconstant)

end TranslationTiling.Sudoku
