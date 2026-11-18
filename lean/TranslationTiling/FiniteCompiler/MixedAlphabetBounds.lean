import TranslationTiling.FiniteCompiler.MixedAlphabetSystem
import TranslationTiling.FiniteCompiler.MixedParameters
import TranslationTiling.FiniteCompiler.FixedBounds
import TranslationTiling.FiniteCompiler.Effective.JointCode

namespace TranslationTiling.FiniteCompiler.MixedAlphabetSystem
open scoped Classical BigOperators
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
variable {T : LeanWang.TileSet} (code : Code T) (E : Parameters code)
local instance : AlphabetFamily (system code) := family code

theorem nonempty_of_mem_testTiles {F : Finset (Ambient E)} (hF : F∈testTiles code E) : F.Nonempty := by
  rcases Finset.mem_union.mp hF with hF | hF
  · exact FiniteCompiler.nonempty_of_mem_testTiles E hF
  · obtain ⟨q,_,hF⟩ := Finset.mem_biUnion.mp hF
    exact nonempty_of_mem_fixedCycleTiles E _ _ hF

theorem test_card {F : Finset (Ambient E)} (hF : F∈testTiles code E) : F.card≤MassSize.mass E := by
  rcases Finset.mem_union.mp hF with hF | hF
  · exact MassSize.test_card E F hF
  · obtain ⟨q,_,hF⟩ := Finset.mem_biUnion.mp hF
    obtain rfl := Finset.mem_singleton.mp hF
    exact MassSize.graphTile_card_le E _ 0 _ (by intro g hg; exact (mem_offsetTile E _ g).mp hg)

theorem test_horizontal {H : ℕ} (hb : CompactSupport.Bound E H)
    (hS : ∀ n, ((system code).slope n).natAbs≤16)
    {F : Finset (Ambient E)} (hF : F∈testTiles code E) {g : Ambient E} (hg : g∈F) :
    g.1.1.natAbs≤H ∧ g.1.2.natAbs≤H := by
  rcases Finset.mem_union.mp hF with hF | hF
  · exact CompactSupport.test_horizontal E hb hS hF hg
  · obtain ⟨q,_,hF⟩ := Finset.mem_biUnion.mp hF
    obtain rfl := Finset.mem_singleton.mp hF
    have hh : g.1=0 := congrArg Prod.fst ((mem_offsetTile E _ g).mp hg)
    simp [hh]

theorem slope_bound : ∀ n, ((system code).slope n).natAbs≤16 := by
  intro n
  change ((finProdFinEquiv.symm n : Sudoku.Column × Fin 3).1.val : ℤ).natAbs≤16
  rw [Int.natAbs_natCast]
  have h := (finProdFinEquiv.symm n : Sudoku.Column × Fin 3).1.isLt
  norm_num [Sudoku.Column,Sudoku.Width,Sudoku.q] at h
  omega

theorem seedTiles_card (hcap : 24*T.length≤216) : (seedTiles code E).card≤6912 := by
  unfold seedTiles
  apply Finset.card_biUnion_le.trans
  simp only [fixedCycleTiles,Finset.card_singleton,Finset.sum_const,smul_eq_mul,mul_one]
  apply (Finset.card_filter_le _ _).trans
  have hc : Fintype.card (Sudoku.Symbol T)≤24*T.length := by
    let f : Sudoku.Symbol T → Fin (24*T.length) := fun s =>
      ⟨Effective.jointIndex T s,Effective.jointIndex_lt T s⟩
    simpa using Fintype.card_le_of_injective f (fun s u h =>
      Effective.jointIndex_injective T (congrArg Fin.val h))
  have hcol : Fintype.card Sudoku.Column=16 := by simp only [Fintype.card_eq_nat_card,Sudoku.Column,Sudoku.Width,Sudoku.q,Nat.card_fin]
  simp only [Finset.card_univ,Fintype.card_prod,Fintype.card_fin,hcol]
  nlinarith

theorem base_card (W : ℕ) (hW : Fintype.card (Word (system code))=W) :
    (FiniteCompiler.testTiles E).card≤W+2603 := by
  have hdep := FixedSize.dependence_card E
  have hword : (wordConstraintTiles E).card≤W := by
    unfold wordConstraintTiles
    apply Finset.card_biUnion_le.trans
    simp only [fixedCycleTiles,Finset.card_singleton,Finset.sum_const,smul_eq_mul,mul_one]
    exact (Finset.card_filter_le _ _).trans_eq (by simp only [Finset.card_univ,hW])
  have hseed : seedConstraintTiles E=∅ := by
    ext F
    constructor
    · intro hF
      exfalso
      obtain ⟨q,hq,_⟩ := Finset.mem_biUnion.mp hF
      exact (Finset.mem_filter.mp hq).2 trivial
    · simp
  have hact : (Finset.univ.image (ordinaryActivationTile E)).card≤48 := by
    exact Finset.card_image_le.trans_eq (by simp only [Finset.card_univ,Column,Fintype.card_fin]; rfl)
  have hsact : (Finset.univ.image (seedActivationTile E)).card≤2 := by
    exact Finset.card_image_le.trans_eq (by simp)
  unfold FiniteCompiler.testTiles
  rw [hseed,Finset.union_empty]
  have h1 := Finset.card_union_le ({kernelTile E}∪dependenceTiles E) (wordConstraintTiles E)
  have h2 := Finset.card_union_le ({kernelTile E}∪dependenceTiles E∪wordConstraintTiles E)
    (Finset.univ.image (ordinaryActivationTile E))
  have h3 := Finset.card_union_le
    ({kernelTile E}∪dependenceTiles E∪wordConstraintTiles E∪Finset.univ.image (ordinaryActivationTile E))
    (Finset.univ.image (seedActivationTile E))
  have h0 := Finset.card_union_le {kernelTile E} (dependenceTiles E)
  simp only [Finset.card_singleton] at h0
  change (dependenceTiles E).card≤(48+2)^2+48+4 at hdep
  omega

theorem testTiles_card (W : ℕ) (hW : Fintype.card (Word (system code))=W)
    (hWlo : 10000≤W) (hcap : 24*T.length≤216) : (testTiles code E).card≤3*W := by
  have hbase := base_card code E W hW
  have hseed := seedTiles_card code E hcap
  exact (Finset.card_union_le _ _).trans (by omega)

end
end TranslationTiling.FiniteCompiler.MixedAlphabetSystem
