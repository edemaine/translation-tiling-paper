import TranslationTiling.FiniteCompiler.SparseTernaryModel
import TranslationTiling.FiniteCompiler.MassBounds
import TranslationTiling.FiniteCompiler.CompactSupport
import TranslationTiling.FiniteCompiler.FixedBounds

namespace TranslationTiling.FiniteCompiler.SparseTernary
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
variable {T : LeanWang.TileSet} (E : EncodingParameters (system T))

theorem nonempty_of_mem_testFamily {F : Finset (Ambient E)} (hF : F∈testFamily E) : F.Nonempty := by
  rcases Finset.mem_union.mp hF with hF | hF
  · exact FiniteCompiler.nonempty_of_mem_testTiles E hF
  · obtain ⟨q,_,hF⟩ := Finset.mem_biUnion.mp hF
    exact nonempty_of_mem_fixedCycleTiles E _ _ hF

theorem test_card {F : Finset (Ambient E)} (hF : F∈testFamily E) :
    F.card≤MassSize.mass E := by
  rcases Finset.mem_union.mp hF with hF | hF
  · exact MassSize.test_card E F hF
  · obtain ⟨q,_,hF⟩ := Finset.mem_biUnion.mp hF
    obtain rfl := Finset.mem_singleton.mp hF
    exact MassSize.graphTile_card_le E _ 0 _ (by intro g hg; exact (mem_offsetTile E _ g).mp hg)

theorem test_horizontal_coarse {b : ℕ} (hb : Size.ParameterBudget E b)
    {F : Finset (Ambient E)} (hF : F∈testFamily E) {g : Ambient E} (hg : g∈F) :
    g.1.1.natAbs≤Size.horizontalCap b ∧ g.1.2.natAbs≤Size.horizontalCap b := by
  rcases Finset.mem_union.mp hF with hF | hF
  · exact Size.testTile_horizontal_bound hb hF hg
  · obtain ⟨q,_,hF⟩ := Finset.mem_biUnion.mp hF
    obtain rfl := Finset.mem_singleton.mp hF
    have hh : g.1=0 := congrArg Prod.fst ((mem_offsetTile E _ g).mp hg)
    simp [hh]

theorem base_card : (FiniteCompiler.testTiles E).card≤3^(system T).width+
    ((system T).width^2+6*(system T).width+11) := by
  let S := system T
  have hdep := FixedSize.dependence_card E
  have hword : (wordConstraintTiles E).card≤3^S.width := by
    unfold wordConstraintTiles
    apply Finset.card_biUnion_le.trans
    simp only [fixedCycleTiles,Finset.card_singleton,Finset.sum_const,smul_eq_mul,mul_one]
    apply (Finset.card_filter_le _ _).trans
    have hb : (system T).alphabet=3 := rfl
    change Fintype.card (Column (system T) → Fin 3)≤3^(system T).width
    simp [Column]
  have hseed : seedConstraintTiles E=∅ := by
    ext F
    constructor
    · intro hF
      exfalso
      obtain ⟨q,hq,_⟩ := Finset.mem_biUnion.mp hF
      exact (Finset.mem_filter.mp hq).2 trivial
    · intro hF
      simp at hF
  have hact : (Finset.univ.image (ordinaryActivationTile E)).card≤S.width := by
    exact Finset.card_image_le.trans_eq (by simp only [Finset.card_univ,Column,Fintype.card_fin]; rfl)
  have hsact : (Finset.univ.image (seedActivationTile E)).card≤2 := by
    exact Finset.card_image_le.trans_eq (by simp)
  unfold FiniteCompiler.testTiles
  rw [hseed,Finset.union_empty]
  have h1 := Finset.card_union_le ({kernelTile E}∪dependenceTiles E)
    (wordConstraintTiles E)
  have h2 := Finset.card_union_le ({kernelTile E}∪dependenceTiles E∪wordConstraintTiles E)
    (Finset.univ.image (ordinaryActivationTile E))
  have h3 := Finset.card_union_le
    ({kernelTile E}∪dependenceTiles E∪wordConstraintTiles E∪Finset.univ.image (ordinaryActivationTile E))
    (Finset.univ.image (seedActivationTile E))
  have h0 := Finset.card_union_le {kernelTile E} (dependenceTiles E)
  simp only [Finset.card_singleton] at h0
  dsimp only [S] at *
  nlinarith


theorem seedTiles_card : (seedTiles E).card≤288 := by
  unfold seedTiles
  apply Finset.card_biUnion_le.trans
  simp only [fixedCycleTiles,Finset.card_singleton,Finset.sum_const,smul_eq_mul,mul_one]
  apply (Finset.card_filter_le _ _).trans
  have hc : Fintype.card Sudoku.Column=16 := by
    simp only [Fintype.card_eq_nat_card,Sudoku.Column,Sudoku.Width,Sudoku.q,Nat.card_fin]
  simp only [Finset.card_univ,Fintype.card_prod,Fintype.card_fin,hc]
  norm_num

theorem testFamily_card : (testFamily E).card≤3^((system T).width+1) := by
  have hw : 48≤(system T).width := by have := raw_width_le T.length; change 48≤width T.length; omega
  have hpoly := FixedSize.quadratic_le_three (system T).width (by omega)
  have hs : 288≤3^(system T).width :=
    (by decide : 288≤3^48).trans (Nat.pow_le_pow_right (by decide) hw)
  have hc := Finset.card_union_le (testTiles E) (seedTiles E)
  have hb := base_card E
  have hseed := seedTiles_card E
  unfold testFamily
  rw [pow_succ']
  nlinarith

theorem test_horizontal {H : ℕ} (hb : CompactSupport.Bound E H)
    {F : Finset (Ambient E)} (hF : F∈testFamily E) {g : Ambient E} (hg : g∈F) :
    g.1.1.natAbs≤H ∧ g.1.2.natAbs≤H := by
  rcases Finset.mem_union.mp hF with hF|hF
  · exact CompactSupport.test_horizontal E hb (slope_bound T) hF hg
  · obtain ⟨q,_,hF⟩ := Finset.mem_biUnion.mp hF
    obtain rfl := Finset.mem_singleton.mp hF
    have hh : g.1=0 := congrArg Prod.fst ((mem_offsetTile E _ g).mp hg)
    simp [hh]

end
end TranslationTiling.FiniteCompiler.SparseTernary
