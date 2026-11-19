import TranslationTiling.FiniteCompiler.Effective.NineCompiler
import TranslationTiling.FiniteCompiler.Effective.MixedCompiler
import TranslationTiling.FiniteCompiler.Effective.JointCompiler
import TranslationTiling.FiniteCompiler.TernaryConstruction
import TranslationTiling.FiniteCompiler.ExplicitDegrees
import TranslationTiling.Compiler.BitChannelSize

set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

/-! # An end-to-end `n^O(log log n)` connected-polycube bound

The constant is uniform in the number of distinct Wang tiles. The theorem
includes nonemptiness, face connectedness, and both tilability directions.
-/

namespace TranslationTiling.Compiler.Size

open scoped Classical
noncomputable section

theorem tileIn_card (T : LeanWang.TileSet) [Fintype (LeanWang.TileIn T)] :
    Fintype.card (LeanWang.TileIn T) = T.toFinset.card := by
  let e : LeanWang.TileIn T ≃ ↥T.toFinset := {
    toFun := fun t => ⟨t.val, List.mem_toFinset.mpr t.property⟩
    invFun := fun t => ⟨t.val, List.mem_toFinset.mp t.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  exact (Fintype.card_congr e).trans (Fintype.card_coe _)

/-- Conversion of the ternary channel count, including its eighteen fixed positions. -/
theorem ternary_channel_cap_bound (n : ℕ) :
    (Sudoku.Width * (Nat.log 2 (n + 2) + 1 + 18) + 2) ^
        (3510 * (Sudoku.Width * (Nat.log 2 (n + 2) + 1 + 18) + 2)) ≤
      2 ^ ((2 * 10 ^ 10) * (Nat.log 2 (n + 2) + 1) *
        (Nat.log 2 (Nat.log 2 (n + 2) + 2) + 1)) := by
  let l := Nat.log 2 (n + 2) + 1
  have hl : 2 ≤ l := by
    have := Nat.le_log_of_pow_le (b := 2) (x := 1) (y := n + 2) (by decide) (by norm_num)
    dsimp [l]
    omega
  have hcap : Sudoku.Width * (l + 18) + 2 ≤ (10 * Sudoku.Width) * l + 2 := by nlinarith
  have hcubes : (Sudoku.Width * (l + 18) + 2) ^ (3510 * (Sudoku.Width * (l + 18) + 2)) ≤
      ((10 * Sudoku.Width) * l + 2) ^ (3510 * ((10 * Sudoku.Width) * l + 2)) :=
    (Nat.pow_le_pow_left hcap _).trans
      (Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_left _ hcap))
  have hlog := linear_channel_cap_le_exp_log_narrow (10 * Sudoku.Width) 3510 l
    (by norm_num [Sudoku.Width,Sudoku.p,Sudoku.q]) (by omega)
  have hcoeff : 11 * 3510 * (10 * Sudoku.Width + 2) ≤ 2 * 10 ^ 10 := by
    norm_num [Sudoku.Width,Sudoku.p,Sudoku.q]
  have hexp := Nat.mul_le_mul_right (l * (Nat.log 2 (l + 1) + 1)) hcoeff
  exact hcubes.trans (hlog.trans (Nat.pow_le_pow_right (by decide)
    (by simpa only [Nat.mul_assoc,l,Nat.add_assoc] using hexp)))

/-- Retain the channel-count estimate before converting logarithms. -/
theorem exists_connected_tile_ternary_count_bound (T : LeanWang.TileSet) :
    ∃ P : Tile 3, P ≠ [] ∧ FaceConnected P ∧
      (LeanWang.TilesPlane T ↔ TranslationTiling.Tiles P) ∧
      cubeCount P ≤ (Sudoku.Width * (Nat.log 2 (T.toFinset.card + 2) + 1 + 18) + 2) ^
        (3510 * (Sudoku.Width * (Nat.log 2 (T.toFinset.card + 2) + 1 + 18) + 2)) := by
  letI : Fintype (LeanWang.TileIn T) := Fintype.ofFinite _
  let l := Nat.log 2 (T.toFinset.card + 2) + 1
  have ht : Fintype.card (LeanWang.TileIn T) ≤ 2 ^ l := by
    rw [tileIn_card]
    exact (by omega : T.toFinset.card ≤ T.toFinset.card + 2).trans
      (Nat.lt_pow_succ_log_self (by decide : 1 < 2) _).le
  have hp : Fintype.card (ZMod Sudoku.p)ˣ ≤ Sudoku.p := by
    simpa only [ZMod.card] using Fintype.card_le_of_injective
      (fun u : (ZMod Sudoku.p)ˣ => u.val) Units.val_injective
  have hq : Fintype.card (ZMod Sudoku.q)ˣ ≤ Sudoku.q := by
    simpa only [ZMod.card] using Fintype.card_le_of_injective
      (fun u : (ZMod Sudoku.q)ˣ => u.val) Units.val_injective
  have hcard : Fintype.card (Sudoku.Symbol T) ≤ 2 ^ (l + 16) := by
    calc
      _ ≤ Sudoku.p * (Sudoku.q * 2 ^ l) := by
        have he : Fintype.card (Sudoku.Symbol T) = Fintype.card (ZMod Sudoku.p)ˣ *
            (Fintype.card (ZMod Sudoku.q)ˣ * Fintype.card (LeanWang.TileIn T)) := by
          simp only [Fintype.card_eq_nat_card,Sudoku.Symbol,Nat.card_prod]
        rw [he]
        exact Nat.mul_le_mul hp (Nat.mul_le_mul hq ht)
      _ = (Sudoku.p * Sudoku.q) * 2 ^ l := by ring
      _ ≤ 2 ^ 16 * 2 ^ l := Nat.mul_le_mul_right _ (by norm_num [Sudoku.p,Sudoku.q])
      _ = _ := by rw [← pow_add]; congr 1; omega
  obtain ⟨code,hcode⟩ := BitChannels.exists_bit_code (Sudoku.Symbol T) (l + 16) hcard
  have hwidth : 20 * Sudoku.Width + 2 ≤ FiniteCompiler.channelCount (FiniteCompiler.TernarySystem.system code) := by
    change 20 * Sudoku.Width + 2 ≤ Sudoku.Width * (l + 16 + 2) + 2
    have hl : 2 ≤ l := by
      have := Nat.le_log_of_pow_le (b := 2) (x := 1) (y := T.toFinset.card + 2)
        (by decide) (by norm_num)
      dsimp [l]
      omega
    nlinarith
  obtain ⟨P,hP,hconn,hiff,hcubes⟩ := FiniteCompiler.Size.exists_connected_tile_ternary_channel_bound
    (FiniteCompiler.TernarySystem.system code) T rfl hwidth
    (FiniteCompiler.TernarySystem.slope_bound code)
    (fun E => FiniteCompiler.TernarySystem.finite_system_iff_wang code hcode E)
  refine ⟨P,hP,hconn,hiff,?_⟩
  simpa only [FiniteCompiler.channelCount,FiniteCompiler.TernarySystem.system,Nat.add_assoc,l] using hcubes

/-- The full ternary-channel reduction with an explicit binary-exponent coefficient. -/
theorem exists_connected_tile_quasipolynomial_explicit_bound (T : LeanWang.TileSet) :
    ∃ P : Tile 3, P ≠ [] ∧ FaceConnected P ∧
      (LeanWang.TilesPlane T ↔ TranslationTiling.Tiles P) ∧
      cubeCount P ≤ 2 ^ ((2 * 10 ^ 10) * (Nat.log 2 (T.toFinset.card + 2) + 1) *
        (Nat.log 2 (Nat.log 2 (T.toFinset.card + 2) + 2) + 1)) := by
  obtain ⟨P,hP,hconn,hiff,hcubes⟩ := exists_connected_tile_ternary_count_bound T
  exact ⟨P,hP,hconn,hiff,hcubes.trans (ternary_channel_cap_bound T.toFinset.card)⟩

/-- The same numerical estimate as a power of the number of tiles plus two. -/
theorem exists_connected_tile_quasipolynomial_explicit_power_bound (T : LeanWang.TileSet) :
    ∃ P : Tile 3, P ≠ [] ∧ FaceConnected P ∧
      (LeanWang.TilesPlane T ↔ TranslationTiling.Tiles P) ∧
      cubeCount P ≤ (T.toFinset.card + 2) ^
        (2 * (2 * 10 ^ 10) * (Nat.log 2 (Nat.log 2 (T.toFinset.card + 2) + 2) + 1)) := by
  obtain ⟨P, hP, hconn, hiff, hcubes⟩ := exists_connected_tile_quasipolynomial_explicit_bound T
  exact ⟨P, hP, hconn, hiff, hcubes.trans (exp_iterated_log_le_power ((2 * 10 ^ 10)) T.toFinset.card)⟩

/-- The coefficient is uniform in the number of distinct tiles, including zero. -/
theorem exists_connected_tile_quasipolynomial_bound :
    ∃ K : ℕ, ∀ T : LeanWang.TileSet,
      ∃ P : Tile 3, P ≠ [] ∧ FaceConnected P ∧
        (LeanWang.TilesPlane T ↔ TranslationTiling.Tiles P) ∧
        cubeCount P ≤ 2 ^ (K * (Nat.log 2 (T.toFinset.card + 2) + 1) *
          (Nat.log 2 (Nat.log 2 (T.toFinset.card + 2) + 2) + 1)) :=
  ⟨(2 * 10 ^ 10), exists_connected_tile_quasipolynomial_explicit_bound⟩

/-- The shorter mixed-radix code, before conversion to real logarithms. -/
theorem exists_connected_tile_mixed_count_bound (T : LeanWang.TileSet) (hn : 0 < T.toFinset.card) :
    ∃ P : Tile 3, P ≠ [] ∧ FaceConnected P ∧
      (LeanWang.TilesPlane T ↔ TranslationTiling.Tiles P) ∧
      cubeCount P ≤ (max (Sudoku.Width * FiniteCompiler.Effective.mixedWidth T.toFinset.card + 2) 256) ^
        (33 * (Sudoku.Width * FiniteCompiler.Effective.mixedWidth T.toFinset.card)+466)*
        3^(4*(Sudoku.Width * FiniteCompiler.Effective.mixedWidth T.toFinset.card)+4) := by
  have hn' : 0 < T.dedup.length := by simpa only [List.card_toFinset] using hn
  obtain ⟨hne,hc,ht,hb⟩ := FiniteCompiler.Effective.mixedCompileCore_channel_bound T.dedup hn'
  have hd : LeanWang.TilesPlane T ↔ LeanWang.TilesPlane T.dedup :=
    LeanWang.tilesPlane_congr (by intro t; simp)
  refine ⟨FiniteCompiler.Effective.mixedCompileCore T.dedup,hne,hc,hd.trans ht,?_⟩
  apply (List.toFinset_card_le _).trans
  simpa only [List.card_toFinset,FiniteCompiler.channelCount,FiniteCompiler.Effective.mixedSystem,
    FiniteCompiler.TaggedSystem.system,FiniteCompiler.primeBudget] using hb

/-- Full ternary capacity with seed predicates tested on whole codewords. -/
theorem exists_connected_tile_joint_count_bound (T : LeanWang.TileSet) (hn : 0<T.toFinset.card) :
    ∃ P : Tile 3, P≠[] ∧ FaceConnected P ∧
      (LeanWang.TilesPlane T ↔ TranslationTiling.Tiles P) ∧
      cubeCount P≤(max (Sudoku.Width*FiniteCompiler.Effective.jointWidth T.toFinset.card+2) 256)^
        (33*(Sudoku.Width*FiniteCompiler.Effective.jointWidth T.toFinset.card)+98)*
        3^(4*(Sudoku.Width*FiniteCompiler.Effective.jointWidth T.toFinset.card)+4) := by
  have hn' : 0<T.dedup.length := by simpa only [List.card_toFinset] using hn
  obtain ⟨hne,hc,ht,hb⟩ := FiniteCompiler.Effective.jointCompileCore_channel_bound T.dedup hn'
  have hd : LeanWang.TilesPlane T ↔ LeanWang.TilesPlane T.dedup :=
    LeanWang.tilesPlane_congr (by intro t; simp)
  refine ⟨FiniteCompiler.Effective.jointCompileCore T.dedup,hne,hc,hd.trans ht,?_⟩
  apply (List.toFinset_card_le _).trans
  simpa only [List.card_toFinset,FiniteCompiler.Effective.jointSystem,
    FiniteCompiler.JointSystem.system,FiniteCompiler.primeBudget,FiniteCompiler.channelCount] using hb

/-- The explicit opposite-edge test handles one distinct Wang tile. -/
theorem exists_connected_tile_one_quasipolynomial_bound (T : LeanWang.TileSet)
    (hT : T.toFinset.card=1) :
    ∃ P : Tile 3, P≠[] ∧ FaceConnected P ∧
      (LeanWang.TilesPlane T ↔ TranslationTiling.Tiles P) ∧ cubeCount P≤2^250 := by
  have hlen : T.dedup.length=1 := by simpa only [List.card_toFinset] using hT
  obtain ⟨hne,hc,ht,_⟩ := FiniteCompiler.Effective.nineCompile_facts T.dedup
  have hd : LeanWang.TilesPlane T ↔ LeanWang.TilesPlane T.dedup :=
    LeanWang.tilesPlane_congr (by intro t; simp)
  have hb := FiniteCompiler.Effective.nineCompile_single_bound T.dedup hlen
  exact ⟨_,hne,hc,hd.trans ht,(List.toFinset_card_le _).trans hb⟩

/-- A finite periodicity test handles at most three distinct Wang tiles. -/
theorem exists_connected_tile_small_quasipolynomial_bound (T : LeanWang.TileSet)
    (hT : T.toFinset.card≤3) :
    ∃ P : Tile 3, P≠[] ∧ FaceConnected P ∧
      (LeanWang.TilesPlane T ↔ TranslationTiling.Tiles P) ∧ cubeCount P≤2^250 := by
  have hlen : T.dedup.length≤3 := by simpa only [List.card_toFinset] using hT
  obtain ⟨hne,hc,ht,_⟩ := FiniteCompiler.Effective.nineCompile_facts T.dedup
  have hd : LeanWang.TilesPlane T ↔ LeanWang.TilesPlane T.dedup :=
    LeanWang.tilesPlane_congr (by intro t; simp)
  have hb := FiniteCompiler.Effective.nineCompile_small_bound T.dedup hlen
  exact ⟨_,hne,hc,hd.trans ht,(List.toFinset_card_le _).trans hb⟩

end
end TranslationTiling.Compiler.Size
