import TranslationTiling.FiniteCompiler.SparseSmallSystem
import TranslationTiling.FiniteCompiler.MassBounds
import TranslationTiling.FiniteCompiler.CompactSupport
import TranslationTiling.FiniteCompiler.FixedBounds

namespace TranslationTiling.FiniteCompiler.SparseSmall
open scoped Classical BigOperators
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
variable {T : LeanWang.TileSet} {d : ℕ} (code : Code T d)
local instance : AlphabetFamily (system code) := family code

 theorem slope_bound : ∀ n, ((system code).slope n).natAbs≤16 := by
  intro n
  obtain ⟨r,rfl⟩ := roleEquiv.surjective n
  cases r with
  | inl j => simpa [system,slope] using (Nat.le_of_lt (j.isLt.trans (by decide : 12<16)))
  | inr r =>
    cases r with
    | inl j => simpa [system,slope] using Nat.le_of_lt j.isLt
    | inr j => fin_cases j <;> norm_num [system,slope,Sudoku.Sparse.position]

 theorem nonempty_of_mem_testTiles {E : EncodingParameters (system code)}
    {F : Finset (Ambient E)} (hF : F∈testTiles E) : F.Nonempty :=
  FiniteCompiler.nonempty_of_mem_testTiles E hF

 theorem test_card (E : EncodingParameters (system code)) {F : Finset (Ambient E)}
    (hF : F∈testTiles E) : F.card≤MassSize.mass E := MassSize.test_card E F hF

 theorem test_horizontal (E : EncodingParameters (system code)) {H : ℕ}
    (hb : CompactSupport.Bound E H) {F : Finset (Ambient E)} (hF : F∈testTiles E)
    {g : Ambient E} (hg : g∈F) : g.1.1.natAbs≤H ∧ g.1.2.natAbs≤H :=
  CompactSupport.test_horizontal E hb (slope_bound code) hF hg

 theorem letter_card (hd : d≤10) (n : Column (system code)) :
    Fintype.card (Letter (system code) n)≤10 := by
  change Fintype.card (Fin (arity d n))≤10
  rw [Fintype.card_fin]
  unfold arity
  split <;> first | omega | split <;> omega

 theorem testTiles_card (E : EncodingParameters (system code)) (hd : d≤10)
    (W : ℕ) (hW : Fintype.card (Word (system code))=W) (hlo : 2000≤W) :
    (testTiles E).card≤3*W := by
  have hdep := FixedSize.dependence_card E
  change (dependenceTiles E).card≤(31+2)^2+31+4 at hdep
  have hword : (wordConstraintTiles E).card≤W := by
    unfold wordConstraintTiles
    apply Finset.card_biUnion_le.trans
    simp only [fixedCycleTiles,Finset.card_singleton,Finset.sum_const,smul_eq_mul,mul_one]
    exact (Finset.card_filter_le _ _).trans_eq (by simp only [Finset.card_univ,hW])
  have hseed : (seedConstraintTiles E).card≤620 := by
    unfold seedConstraintTiles
    apply Finset.card_biUnion_le.trans
    simp only [fixedCycleTiles,Finset.card_singleton,Finset.sum_const,smul_eq_mul,mul_one]
    apply (Finset.card_filter_le _ _).trans
    simp only [Finset.card_univ,Fintype.card_prod,Fintype.card_fin]
    have hc : Fintype.card (Σ n : Column (system code), Letter (system code) n)≤310 := by
      rw [Fintype.card_sigma]
      calc
        _ ≤ ∑ _n : Column (system code), 10 := Finset.sum_le_sum (fun n _ => letter_card code hd n)
        _ = 310 := by simp [Column,system]
    omega
  have hact : (Finset.univ.image (ordinaryActivationTile E)).card≤31 :=
    Finset.card_image_le.trans_eq (by simp [Column,system])
  have hsact : (Finset.univ.image (seedActivationTile E)).card≤2 :=
    Finset.card_image_le.trans_eq (by simp)
  unfold testTiles
  have h0 := Finset.card_union_le {kernelTile E} (dependenceTiles E)
  have h1 := Finset.card_union_le ({kernelTile E}∪dependenceTiles E) (wordConstraintTiles E)
  have h2 := Finset.card_union_le ({kernelTile E}∪dependenceTiles E∪wordConstraintTiles E) (seedConstraintTiles E)
  have h3 := Finset.card_union_le ({kernelTile E}∪dependenceTiles E∪wordConstraintTiles E∪seedConstraintTiles E)
    (Finset.univ.image (ordinaryActivationTile E))
  have h4 := Finset.card_union_le
    ({kernelTile E}∪dependenceTiles E∪wordConstraintTiles E∪seedConstraintTiles E∪Finset.univ.image (ordinaryActivationTile E))
    (Finset.univ.image (seedActivationTile E))
  simp only [Finset.card_singleton] at h0
  omega

end
end TranslationTiling.FiniteCompiler.SparseSmall
