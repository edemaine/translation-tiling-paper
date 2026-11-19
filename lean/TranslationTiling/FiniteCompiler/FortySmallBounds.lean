import TranslationTiling.FiniteCompiler.PairSmallBounds
import TranslationTiling.FiniteCompiler.MassBounds
import TranslationTiling.FiniteCompiler.CompactSupport
import TranslationTiling.FiniteCompiler.FixedBounds

namespace TranslationTiling.FiniteCompiler.PairSmall
open scoped Classical BigOperators
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
variable {T : LeanWang.TileSet} {d : ℕ} (code : Code T d)
local instance fortyFamily : AlphabetFamily (system code) := family code

 theorem letter_card_forty (hd : d≤40) (n : Column (system code)) :
    Fintype.card (Letter (system code) n)≤40 := by
  change Fintype.card (Fin (arity d n))≤40
  rw [Fintype.card_fin]
  unfold arity
  split <;> first | omega | split <;> omega

 theorem testTiles_card_forty (E : EncodingParameters (system code)) (hd : d≤40)
    (W : ℕ) (hW : Fintype.card (Word (system code))=W) (hlo : 2000≤W) :
    (testTiles E).card≤3*W := by
  have hdep := FixedSize.dependence_card E
  change (dependenceTiles E).card≤(20+2)^2+20+4 at hdep
  have hword : (wordConstraintTiles E).card≤W := by
    unfold wordConstraintTiles
    apply Finset.card_biUnion_le.trans
    simp only [fixedCycleTiles,Finset.card_singleton,Finset.sum_const,smul_eq_mul,mul_one]
    exact (Finset.card_filter_le _ _).trans_eq (by simp only [Finset.card_univ,hW])
  have hseed : (seedConstraintTiles E).card≤1600 := by
    unfold seedConstraintTiles
    apply Finset.card_biUnion_le.trans
    simp only [fixedCycleTiles,Finset.card_singleton,Finset.sum_const,smul_eq_mul,mul_one]
    apply (Finset.card_filter_le _ _).trans
    simp only [Finset.card_univ,Fintype.card_prod,Fintype.card_fin]
    have hc : Fintype.card (Σ n : Column (system code), Letter (system code) n)≤800 := by
      rw [Fintype.card_sigma]
      calc
        _ ≤ ∑ _n : Column (system code), 40 := Finset.sum_le_sum (fun n _ => letter_card_forty code hd n)
        _ = 800 := by simp [Column,system]
    omega
  have hact : (Finset.univ.image (ordinaryActivationTile E)).card≤20 :=
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
end TranslationTiling.FiniteCompiler.PairSmall
