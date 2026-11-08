import TranslationTiling.FiniteCompiler.StackBound
import TranslationTiling.FiniteCompiler.PolynomialBudget

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace TranslationTiling.FiniteCompiler.Size

open Compiler.Size
noncomputable section

def geometryPolynomial (x : ℕ) : ℕ :=
  Compiler.Size.geometryCap (horizontalCap x) (stackPolynomial x)

theorem horizontalCap_mono {a b : ℕ} (h : a ≤ b) : horizontalCap a ≤ horizontalCap b := by
  unfold horizontalCap indexCap pairCap
  gcongr

theorem geometryCap_mono {H H' M M' : ℕ} (hH : H ≤ H') (hM : M ≤ M') :
    Compiler.Size.geometryCap H M ≤ Compiler.Size.geometryCap H' M' := by
  unfold Compiler.Size.geometryCap Compiler.Size.latticeSide Compiler.Size.latticeRadius
  gcongr

theorem geometryPolynomial_powerBound : PowerBound geometryPolynomial := by
  have hpair {f : ℕ → ℕ} (hf : PowerBound f) : PowerBound (fun x => pairCap (f x)) :=
    (hf.mul hf).add ((PowerBound.const 2).mul hf)
  have hJ := hpair (hpair (hpair (hpair PowerBound.id)))
  have hH := PowerBound.id.mul
    (((PowerBound.id.pow 5).mul (hJ.add (PowerBound.const 1))).add (PowerBound.const 1))
  have hM := PowerBound.id.mul ((PowerBound.const 2).mul
    ((((PowerBound.const 8).mul (PowerBound.id.pow 5)).add PowerBound.id).add
      (PowerBound.const 3)))
  have hS := ((PowerBound.const 2).mul ((PowerBound.const 1000).mul
    ((((PowerBound.const 2).mul hH).add hM).add (PowerBound.const 1)))).add (PowerBound.const 3)
  exact (hS.pow 3).mul ((((PowerBound.const 3).mul (hS.pow 3)).add (PowerBound.const 6)).pow 3)

theorem exists_connected_tile_of_budget {T : System} {E : EncodingParameters T} {b : ℕ}
    (hb : ParameterBudget E b) (hC : channelCount T ≤ b) (hL : T.alphabet + 1 ≤ b)
    (W : LeanWang.TileSet)
    (hcorrect : LeanWang.TilesPlane W ↔ ∃ A : Set (Ambient E), Solves E A) :
    ∃ P : Tile 3, P ≠ [] ∧ FaceConnected P ∧
      (LeanWang.TilesPlane W ↔ TranslationTiling.Tiles P) ∧
      cubeCount P ≤ geometryPolynomial (commonCap b (channelCount T)) := by
  obtain ⟨m, hm, hcap, F, hF, hiff, hcoord⟩ :=
    exists_cyclic_tile_of_budget hb hC hL hcorrect
  obtain ⟨P, hP, hconn, hiffP, hcubes⟩ :=
    Compiler.Size.exists_bounded_connected_tile hm hcap F hF hiff hcoord
  refine ⟨P, hP, hconn, hiffP, hcubes.trans ?_⟩
  apply geometryCap_mono
  · exact horizontalCap_mono (le_commonCap (by unfold channelCount; omega))
  · exact le_rfl

/-- Retain the two polynomial degrees in the connected cube bound. -/
theorem exists_connected_tile_channel_bound_of_degrees (B S d g : ℕ)
    (hd : PowerBoundAt d (parameterBase B S))
    (hg : PowerBoundAt g geometryPolynomial)
    (T : System) (W : LeanWang.TileSet)
    (hB : T.alphabet = B) (hS : ∀ n, (T.slope n).natAbs ≤ S)
    (hcorrect : ∀ E : EncodingParameters T,
      LeanWang.TilesPlane W ↔ ∃ A : Set (Ambient E), Solves E A) :
    ∃ P : Tile 3, P ≠ [] ∧ FaceConnected P ∧
      (LeanWang.TilesPlane W ↔ TranslationTiling.Tiles P) ∧
      cubeCount P ≤ channelCount T ^ ((12 * d * g) * channelCount T) := by
  obtain ⟨E, hb, hC, hL⟩ := exists_parameterBudget T S hS
  obtain ⟨P, hP, hconn, hiff, hcubes⟩ :=
    exists_connected_tile_of_budget hb hC hL W (hcorrect E)
  have hC2 : 2 ≤ channelCount T := by unfold channelCount; omega
  have hbase : parameterBase T.alphabet S (channelCount T) ≤ channelCount T ^ d := by
    rw [hB]
    exact hd _ hC2
  have hX : 2 ≤ commonCap (parameterBase T.alphabet S (channelCount T)) (channelCount T) :=
    hb.two.trans (le_commonCap (by omega))
  refine ⟨P, hP, hconn, hiff, hcubes.trans ?_⟩
  calc
    _ ≤ commonCap (parameterBase T.alphabet S (channelCount T)) (channelCount T) ^ g := hg _ hX
    _ = parameterBase T.alphabet S (channelCount T) ^ (12 * channelCount T * g) := by
      rw [commonCap, ← pow_mul]
    _ ≤ (channelCount T ^ d) ^ (12 * channelCount T * g) := Nat.pow_le_pow_left hbase _
    _ = _ := by rw [← pow_mul]; congr 1; ring


/-- Uniformity in the alphabet and slope bound makes logarithmically many
bit channels give a single constant in the final cube bound. -/
theorem exists_connected_tile_channel_bound (B S : ℕ) :
    ∃ K : ℕ, ∀ (T : System) (W : LeanWang.TileSet),
      T.alphabet = B → (∀ n, (T.slope n).natAbs ≤ S) →
      (∀ E : EncodingParameters T,
        LeanWang.TilesPlane W ↔ ∃ A : Set (Ambient E), Solves E A) →
      ∃ P : Tile 3, P ≠ [] ∧ FaceConnected P ∧
        (LeanWang.TilesPlane W ↔ TranslationTiling.Tiles P) ∧
        cubeCount P ≤ channelCount T ^ (K * channelCount T) := by
  obtain ⟨d, hd⟩ := parameterBase_powerBound B S
  obtain ⟨g, hg⟩ := geometryPolynomial_powerBound
  exact ⟨12 * d * g, exists_connected_tile_channel_bound_of_degrees B S d g hd hg⟩

end
end TranslationTiling.FiniteCompiler.Size
