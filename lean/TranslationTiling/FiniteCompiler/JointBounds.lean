import TranslationTiling.FiniteCompiler.JointSystem
import TranslationTiling.FiniteCompiler.MassBounds

namespace TranslationTiling.FiniteCompiler.JointSystem
open scoped Classical BigOperators
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
variable {T : LeanWang.TileSet} {m : ℕ} (code : Code T m)
    (E : EncodingParameters (system code))

theorem nonempty_of_mem_testTiles {F : Finset (Ambient E)} (hF : F∈testTiles code E) : F.Nonempty := by
  rcases Finset.mem_union.mp hF with hF | hF
  · exact FiniteCompiler.nonempty_of_mem_testTiles E hF
  · obtain ⟨q,_,hF⟩ := Finset.mem_biUnion.mp hF
    exact nonempty_of_mem_fixedCycleTiles E _ _ hF

theorem test_card {F : Finset (Ambient E)} (hF : F∈testTiles code E) :
    F.card≤MassSize.mass E := by
  rcases Finset.mem_union.mp hF with hF | hF
  · exact MassSize.test_card E F hF
  · obtain ⟨q,_,hF⟩ := Finset.mem_biUnion.mp hF
    obtain rfl := Finset.mem_singleton.mp hF
    exact MassSize.graphTile_card_le E _ 0 _ (by intro g hg; exact (mem_offsetTile E _ g).mp hg)

theorem test_horizontal {b : ℕ} (hb : Size.ParameterBudget E b)
    {F : Finset (Ambient E)} (hF : F∈testTiles code E) {g : Ambient E} (hg : g∈F) :
    g.1.1.natAbs≤Size.horizontalCap b ∧ g.1.2.natAbs≤Size.horizontalCap b := by
  rcases Finset.mem_union.mp hF with hF | hF
  · exact Size.testTile_horizontal_bound hb hF hg
  · obtain ⟨q,_,hF⟩ := Finset.mem_biUnion.mp hF
    obtain rfl := Finset.mem_singleton.mp hF
    have hh : g.1=0 := congrArg Prod.fst ((mem_offsetTile E _ g).mp hg)
    simp [hh]

theorem seedTiles_card : (seedTiles code E).card≤32*3^m := by
  unfold seedTiles
  apply Finset.card_biUnion_le.trans
  simp only [fixedCycleTiles,Finset.card_singleton,Finset.sum_const,smul_eq_mul,mul_one]
  apply (Finset.card_filter_le _ _).trans
  have hc : Fintype.card (Sudoku.Symbol T)≤3^m := by
    simpa using Fintype.card_le_of_injective code.word code.injective
  have hcol : Fintype.card Sudoku.Column=16 := by
    simp only [Fintype.card_eq_nat_card,Sudoku.Column,Sudoku.Width,Sudoku.q,Nat.card_fin]
  simp only [Finset.card_univ,Fintype.card_prod,Fintype.card_fin,hcol]
  nlinarith

theorem base_card : (FiniteCompiler.testTiles E).card≤3^(system code).width+
    ((system code).width^2+6*(system code).width+11) := by
  let S := system code
  have hdep := FixedSize.dependence_card E
  have hword : (wordConstraintTiles E).card≤3^S.width := by
    unfold wordConstraintTiles
    apply Finset.card_biUnion_le.trans
    simp only [fixedCycleTiles,Finset.card_singleton,Finset.sum_const,smul_eq_mul,mul_one]
    apply (Finset.card_filter_le _ _).trans
    have hb : (system code).alphabet=3 := rfl
    change Fintype.card (Column (system code) → Fin 3)≤3^(system code).width
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

theorem testTiles_card (hm : 3≤m) : (testTiles code E).card≤3^((system code).width+1) := by
  have hw : 4≤(system code).width := by
    change 4≤Sudoku.Width*m
    norm_num [Sudoku.Width,Sudoku.q]
    omega
  have hpoly := FixedSize.quadratic_le_three (system code).width hw
  have hseed : 32*3^m≤3^(system code).width := by
    change 32*3^m≤3^(Sudoku.Width*m)
    calc
      _ ≤ 3^4*3^m := Nat.mul_le_mul_right _ (by norm_num)
      _ = 3^(m+4) := by rw [←pow_add]; congr 1; omega
      _ ≤ _ := Nat.pow_le_pow_right (by decide) (by norm_num [Sudoku.Width,Sudoku.q]; omega)
  have hc := Finset.card_union_le (FiniteCompiler.testTiles E) (seedTiles code E)
  have hb := base_card code E
  have hs := seedTiles_card code E
  unfold testTiles
  rw [pow_succ']
  nlinarith

end
end TranslationTiling.FiniteCompiler.JointSystem
