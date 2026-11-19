import TranslationTiling.FiniteCompiler.ProjectedCap
import TranslationTiling.FiniteCompiler.ProjectedSystem
import TranslationTiling.FiniteCompiler.PairSmallGeometry
import Mathlib.Algebra.BigOperators.Fin

namespace TranslationTiling.FiniteCompiler
open scoped Classical BigOperators
noncomputable section

variable {T : System} [AlphabetFamily T] (E : EncodingParameters T)

theorem projected_member {k : ℕ} [NeZero k] (emb : Fin k ↪ Column T)
    {F : Finset (Ambient E)} (hF : F∈projectedTiles E emb) :
    ∃ labels, F∈fixedCycleTiles E (projectedCycle emb) labels := by
  obtain ⟨p,_,hp⟩ := Finset.mem_biUnion.mp hF
  exact ⟨partialLabels emb p,hp⟩

theorem projectedDeck_member (C : Projections T) {F : Finset (Ambient E)}
    (hF : F∈projectedDeck E C) :
    F∈testTiles E ∨ ∃ (cy : ZMod 9 ↪ Channel T) (labels : ∀ j, Label T (cy j)),
      F∈fixedCycleTiles E cy labels := by
  simp only [projectedDeck,Finset.mem_union] at hF
  rcases hF with ((((hF|hF)|hF)|hF)|hF)
  · exact Or.inl (structural_subset E hF)
  · obtain ⟨l,h⟩ := projected_member E _ hF
    exact Or.inr ⟨_,l,h⟩
  · obtain ⟨l,h⟩ := projected_member E _ hF
    exact Or.inr ⟨_,l,h⟩
  · obtain ⟨l,h⟩ := projected_member E _ hF
    exact Or.inr ⟨_,l,h⟩
  · obtain ⟨l,h⟩ := projected_member E _ hF
    exact Or.inr ⟨_,l,h⟩

theorem projectedDeck_nonempty (C : Projections T) : (projectedDeck E C).Nonempty :=
  ⟨kernelTile E,by simp [projectedDeck,structuralTiles]⟩

theorem projectedDeck_tile_nonempty (C : Projections T)
    {F : Finset (Ambient E)} (hF : F∈projectedDeck E C) : F.Nonempty := by
  rcases projectedDeck_member E C hF with h | ⟨cy,l,h⟩
  · exact nonempty_of_mem_testTiles E h
  · exact nonempty_of_mem_fixedCycleTiles E cy l h

theorem projectedDeck_mass (C : Projections T)
    {F : Finset (Ambient E)} (hF : F∈projectedDeck E C) : F.card≤MassSize.mass E := by
  rcases projectedDeck_member E C hF with h | ⟨cy,l,h⟩
  · exact MassSize.test_card E F h
  · obtain rfl := Finset.mem_singleton.mp h
    exact MassSize.graphTile_card_le E _ 0 _ (by intro g hg; exact (mem_offsetTile E _ g).mp hg)

theorem projectedDeck_horizontal (C : Projections T) {H : ℕ} (hb : CompactSupport.Bound E H)
    (hS : ∀ n, (T.slope n).natAbs≤16) {F : Finset (Ambient E)} (hF : F∈projectedDeck E C)
    {g : Ambient E} (hg : g∈F) : g.1.1.natAbs≤H ∧ g.1.2.natAbs≤H := by
  rcases projectedDeck_member E C hF with h | ⟨cy,l,h⟩
  · exact CompactSupport.test_horizontal E hb hS h hg
  · obtain rfl := Finset.mem_singleton.mp h
    have he : g.1=0 := congrArg Prod.fst ((mem_offsetTile E _ g).mp hg)
    simp [he]

theorem projectedDeck_card (C : Projections T) :
    (projectedDeck E C).card ≤ (structuralTiles E).card+
      Fintype.card (PartialWord C.p)+Fintype.card (PartialWord C.q)+
      Fintype.card (PartialWord C.horizontal)+Fintype.card (PartialWord C.vertical) := by
  have h0 := Finset.card_union_le (structuralTiles E) (projectedTiles E C.p)
  have h1 := Finset.card_union_le (structuralTiles E ∪ projectedTiles E C.p) (projectedTiles E C.q)
  have h2 := Finset.card_union_le (structuralTiles E ∪ projectedTiles E C.p ∪ projectedTiles E C.q)
    (projectedTiles E C.horizontal)
  have h3 := Finset.card_union_le
    (structuralTiles E ∪ projectedTiles E C.p ∪ projectedTiles E C.q ∪ projectedTiles E C.horizontal)
    (projectedTiles E C.vertical)
  have := projectedTiles_card E C.p
  have := projectedTiles_card E C.q
  have := projectedTiles_card E C.horizontal
  have := projectedTiles_card E C.vertical
  unfold projectedDeck
  omega

end

namespace PairSmall
noncomputable section
set_option maxHeartbeats 4000000

variable {T : LeanWang.TileSet} {d : ℕ} (code : Code T d)
local instance projectedBoundsFamily : AlphabetFamily (system code) := family code
variable (E : EncodingParameters (system code))


private theorem structural_card (hd : 6≤d) : (structuralTiles E).card≤549+80*d := by
  have hdep := FixedSize.dependence_card E
  change (dependenceTiles E).card≤(20+2)^2+20+4 at hdep
  have hseed : (seedConstraintTiles E).card≤80*d := by
    unfold seedConstraintTiles
    apply Finset.card_biUnion_le.trans
    simp only [fixedCycleTiles,Finset.card_singleton,Finset.sum_const,smul_eq_mul,mul_one]
    apply (Finset.card_filter_le _ _).trans
    simp only [Finset.card_univ,Fintype.card_prod,Fintype.card_fin]
    have hc : Fintype.card (Σ n : Column (system code), Letter (system code) n)≤20*d := by
      rw [Fintype.card_sigma]
      calc
        _ ≤ ∑ _n : Column (system code), d := Finset.sum_le_sum (fun n _ => by
          change Fintype.card (Fin (arity d n))≤d
          rw [Fintype.card_fin]
          unfold arity
          split <;> first | omega | split <;> omega)
        _ = 20*d := by simp [Column,system]
    omega
  have ha : (Finset.univ.image (ordinaryActivationTile E)).card≤20 :=
    Finset.card_image_le.trans_eq (by simp [Column,system])
  have hb : (Finset.univ.image (seedActivationTile E)).card≤2 :=
    Finset.card_image_le.trans_eq (by simp)
  unfold structuralTiles
  have h0 := Finset.card_union_le {kernelTile E} (dependenceTiles E)
  have h1 := Finset.card_union_le ({kernelTile E}∪dependenceTiles E) (seedConstraintTiles E)
  have h2 := Finset.card_union_le ({kernelTile E}∪dependenceTiles E∪seedConstraintTiles E)
    (Finset.univ.image (ordinaryActivationTile E))
  have h3 := Finset.card_union_le
    ({kernelTile E}∪dependenceTiles E∪seedConstraintTiles E∪Finset.univ.image (ordinaryActivationTile E))
    (Finset.univ.image (seedActivationTile E))
  simp only [Finset.card_singleton] at h0
  omega

theorem projected_card (hd : 6≤d) :
    (projectedDeck E (boardProjections code)).card+1≤testLimit d := by
  have hc := projectedDeck_card E (boardProjections code)
  have ha := structural_card code E hd
  have hp : Fintype.card (PartialWord (boardProjections code).p)=4^9 := by
    unfold PartialWord
    rw [Fintype.card_pi]
    change (∏ _ : Fin 9, 4)=4^9
    simp
  have hq : Fintype.card (PartialWord (boardProjections code).q)=6^9 := by
    unfold PartialWord
    rw [Fintype.card_pi]
    change (∏ _ : Fin 9, 6)=6^9
    simp
  have hh : Fintype.card (PartialWord (boardProjections code).horizontal)=4^4*6^3*d^2 := by
    unfold PartialWord
    rw [Fintype.card_pi]
    simp only [Fin.prod_univ_succ,Fintype.card_fin,Fin.prod_univ_zero]
    change 4*(4*(4*(4*(6*(6*(6*(d*(d*1))))))))=_
    ring
  have hv : Fintype.card (PartialWord (boardProjections code).vertical)=4^3*6^4*d^2 := by
    unfold PartialWord
    rw [Fintype.card_pi]
    simp only [Fin.prod_univ_succ,Fintype.card_fin,Fin.prod_univ_zero]
    change 4*(4*(4*(6*(6*(6*(6*(d*(d*1))))))))=_
    ring
  rw [hp,hq,hh,hv] at hc
  unfold testLimit
  omega

end
end PairSmall
end TranslationTiling.FiniteCompiler
