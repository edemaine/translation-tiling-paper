import TranslationTiling.Compiler.PolynomialPrimes
import TranslationTiling.Compiler.DirectTestCount
import TranslationTiling.Compiler.ClosedGeometryBound
import TranslationTiling.Compiler.PowerBounds
import Mathlib.Data.Nat.Log

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

/-!
# A singly exponential bound by Wang tile count

There is a fixed `K` such that `n` distinct Wang tiles can be simulated by a
nonempty face-connected polycube with at most `(n+2)^(K*(n+1))` cubes. This is
`2^O(n log n)`. The bound uses polynomially bounded digit primes and counts the
actual cycle-test maps, whose useful-output domains have fixed cardinality.
This uses bounded admissible parameter choices in the existing encoding.
-/

namespace TranslationTiling.Compiler.Size

open scoped Classical BigOperators
noncomputable section

def polynomialParameterBase (x : ℕ) : ℕ :=
  polynomialPrimeCap x + usefulCap + residueModulus + channelCount +
    (arithmeticAlphabet * x + 1) + 2

def singleParameterCap (n : ℕ) : ℕ :=
  polynomialParameterBase (n + 2) ^ labelsBound n

theorem polynomialParameterBase_powerBound : PowerBound polynomialParameterBase := by
  have hL := ((PowerBound.const arithmeticAlphabet).mul PowerBound.id).add (PowerBound.const 1)
  have hQ := ((PowerBound.const 8).mul
    (((PowerBound.const digitStart).add ((PowerBound.const channelCount).mul hL)).add
      (PowerBound.const 2))).pow 2
  exact (((((hQ.add (PowerBound.const usefulCap)).add (PowerBound.const residueModulus)).add
    (PowerBound.const channelCount)).add hL).add (PowerBound.const 2))

theorem exists_single_parameterBudget (T : LeanWang.TileSet) :
    ∃ E : EncodingParameters T, ParameterBudget E (singleParameterCap T.length) ∧
      (∀ i, E.a i ≤ usefulCap ∧ E.b i ≤ usefulCap) ∧
      channelCount ≤ singleParameterCap T.length ∧
      labelsBound T.length ≤ singleParameterCap T.length := by
  obtain ⟨E, hu, hp⟩ := exists_polynomial_parameters T
  let c := polynomialParameterBase (T.length + 2)
  have hc : 2 ≤ c := by dsimp [c, polynomialParameterBase]; omega
  have hL : 1 ≤ labelsBound T.length := by unfold labelsBound; omega
  have hcp : c ≤ singleParameterCap T.length := by
    change c ≤ c ^ labelsBound T.length
    simpa using Nat.pow_le_pow_right (by omega : 1 ≤ c) hL
  have hr (i : Channel T) : E.r i ≤ singleParameterCap T.length := by
    rw [E.r_eq_prod]
    calc
      _ ≤ ∏ _j : Label T i, c := Finset.prod_le_prod (fun j _ =>
        (hp i j).trans (by dsimp [c, polynomialParameterBase]; omega))
      _ = c ^ Fintype.card (Label T i) := by simp
      _ ≤ _ := Nat.pow_le_pow_right (by omega) (label_card_le T i)
  have hwidth : residueModulus ≤ c := by dsimp [c, polynomialParameterBase]; omega
  have huseful : usefulCap ≤ c := by dsimp [c, polynomialParameterBase]; omega
  have hchannel : channelCount ≤ c := by dsimp [c, polynomialParameterBase]; omega
  have hlabels : labelsBound T.length ≤ c := by
    dsimp [c, polynomialParameterBase, labelsBound]
    nlinarith
  refine ⟨E, ⟨hc.trans hcp, hwidth.trans hcp, hr,
    fun i => (hu i).1.trans (huseful.trans hcp),
    fun i => (hu i).2.trans (huseful.trans hcp)⟩,
    hu, hchannel.trans hcp, hlabels.trans hcp⟩

def singleCubeBound (n : ℕ) : ℕ :=
  geometryCap (horizontalCap (singleParameterCap n))
    (boundedModulusCap (singleParameterCap n) (directTestCap (singleParameterCap n)))

theorem exists_connected_tile_single_bound (T : LeanWang.TileSet) :
    ∃ P : Tile 3, P ≠ [] ∧ FaceConnected P ∧
      (LeanWang.TilesPlane T ↔ TranslationTiling.Tiles P) ∧
      cubeCount P ≤ singleCubeBound T.toFinset.card := by
  obtain ⟨E, hb, hu, hC, hL⟩ := exists_single_parameterBudget T.dedup
  obtain ⟨m, hm, hcap, F, hF, hcorrect, hcoord⟩ :=
    exists_cyclic_tile_of_card_le hb _ (testTiles_card_le_direct hb hu hC hL)
  obtain ⟨P, hP, hconn, hiff, hcount⟩ :=
    exists_bounded_connected_tile hm hcap F hF hcorrect hcoord
  have hd : LeanWang.TilesPlane T ↔ LeanWang.TilesPlane T.dedup :=
    LeanWang.tilesPlane_congr (by intro t; simp)
  refine ⟨P, hP, hconn, hd.trans hiff, ?_⟩
  change cubeCount P ≤ singleCubeBound T.dedup.length at hcount
  simpa only [List.card_toFinset] using hcount

theorem single_geometry_powerBound :
    PowerBound (fun b => geometryCap (horizontalCap b) (boundedModulusCap b (directTestCap b))) := by
  have hpair {f : ℕ → ℕ} (hf : PowerBound f) : PowerBound (fun b => pairCap (f b)) :=
    (hf.mul hf).add ((PowerBound.const 2).mul hf)
  have hJ := hpair (hpair (hpair (hpair PowerBound.id)))
  have hH := PowerBound.id.mul
    (((PowerBound.id.pow 5).mul (hJ.add (PowerBound.const 1))).add (PowerBound.const 1))
  have hV := PowerBound.id.pow (4 * channelCount + 2)
  have hs := PowerBound.id.pow testCountExponent
  have hM := hV.mul ((PowerBound.const 2).mul
    ((((PowerBound.const 8).mul (hs.pow 5)).add hV).add (PowerBound.const 3)))
  have hS := ((PowerBound.const 2).mul ((PowerBound.const 1000).mul
    ((((PowerBound.const 2).mul hH).add hM).add (PowerBound.const 1)))).add (PowerBound.const 3)
  exact (hS.pow 3).mul ((((PowerBound.const 3).mul (hS.pow 3)).add (PowerBound.const 6)).pow 3)

/-- A coefficient-one bound with a single fixed constant, uniform in the input. -/
theorem singleCubeBound_le_power :
    ∃ K : ℕ, ∀ n, singleCubeBound n ≤ (n + 2) ^ (K * (n + 1)) := by
  obtain ⟨d, hd⟩ := polynomialParameterBase_powerBound
  obtain ⟨e, he⟩ := single_geometry_powerBound
  refine ⟨d * (arithmeticAlphabet + 1) * e, fun n => ?_⟩
  have hbase : 2 ≤ polynomialParameterBase (n + 2) := by
    unfold polynomialParameterBase; omega
  have hL : 1 ≤ labelsBound n := by unfold labelsBound; omega
  have hcap : 2 ≤ singleParameterCap n := by
    unfold singleParameterCap
    exact hbase.trans (by simpa using Nat.pow_le_pow_right (by omega) hL)
  have hlabels : labelsBound n ≤ (arithmeticAlphabet + 1) * (n + 1) := by
    unfold labelsBound; nlinarith
  calc
    singleCubeBound n ≤ singleParameterCap n ^ e := he _ hcap
    _ ≤ ((n + 2) ^ d) ^ (labelsBound n * e) := by
      unfold singleParameterCap
      rw [← pow_mul]
      exact Nat.pow_le_pow_left (hd _ (by omega)) _
    _ = (n + 2) ^ (d * labelsBound n * e) := by rw [← pow_mul]; congr 1; ring
    _ ≤ _ := Nat.pow_le_pow_right (by omega)
      (by nlinarith [Nat.mul_le_mul_left (d * e) hlabels])

theorem exists_connected_tile_power_bound :
    ∃ K : ℕ, ∀ T : LeanWang.TileSet,
      ∃ P : Tile 3, P ≠ [] ∧ FaceConnected P ∧
        (LeanWang.TilesPlane T ↔ TranslationTiling.Tiles P) ∧
        cubeCount P ≤ (T.toFinset.card + 2) ^ (K * (T.toFinset.card + 1)) := by
  obtain ⟨K, hK⟩ := singleCubeBound_le_power
  refine ⟨K, fun T => ?_⟩
  obtain ⟨P, hP, hconn, hiff, hcount⟩ := exists_connected_tile_single_bound T
  exact ⟨P, hP, hconn, hiff, hcount.trans (hK _)⟩

/-- The same estimate written explicitly as a binary exponential with a
linear-times-logarithmic exponent. `Nat.log` is the floor logarithm. -/
theorem singleCubeBound_le_exp_log :
    ∃ K : ℕ, ∀ n,
      singleCubeBound n ≤ 2 ^ (K * (n + 1) * (Nat.log 2 (n + 2) + 1)) := by
  obtain ⟨K, hK⟩ := singleCubeBound_le_power
  refine ⟨K, fun n => (hK n).trans ?_⟩
  have hn : n + 2 ≤ 2 ^ (Nat.log 2 (n + 2) + 1) :=
    (Nat.lt_pow_succ_log_self (by decide : 1 < 2) (n + 2)).le
  apply (Nat.pow_le_pow_left hn (K * (n + 1))).trans
  rw [← pow_mul]
  exact le_of_eq (by congr 1; ring)

theorem exists_connected_tile_exp_log_bound :
    ∃ K : ℕ, ∀ T : LeanWang.TileSet,
      ∃ P : Tile 3, P ≠ [] ∧ FaceConnected P ∧
        (LeanWang.TilesPlane T ↔ TranslationTiling.Tiles P) ∧
        cubeCount P ≤ 2 ^ (K * (T.toFinset.card + 1) *
          (Nat.log 2 (T.toFinset.card + 2) + 1)) := by
  obtain ⟨K, hK⟩ := singleCubeBound_le_exp_log
  refine ⟨K, fun T => ?_⟩
  obtain ⟨P, hP, hconn, hiff, hcount⟩ := exists_connected_tile_single_bound T
  exact ⟨P, hP, hconn, hiff, hcount.trans (hK _)⟩

end
end TranslationTiling.Compiler.Size
