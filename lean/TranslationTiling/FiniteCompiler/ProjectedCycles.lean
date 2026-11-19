import TranslationTiling.FiniteCompiler.Soundness
import TranslationTiling.FiniteCompiler.CommonSolution

namespace TranslationTiling.FiniteCompiler

variable [SeedFrame]
noncomputable section
open scoped Classical

variable {T : System} [AlphabetFamily T] (E : EncodingParameters T)

abbrev PartialWord {k : ℕ} (emb : Fin k ↪ Column T) := ∀ i, Letter T (emb i)

def projectedCycle {k : ℕ} [NeZero k] (emb : Fin k ↪ Column T) : ZMod k ↪ Channel T where
  toFun j := .inl (emb ((ZMod.finEquiv k).symm j))
  inj' _ _ h := (ZMod.finEquiv k).symm.injective (emb.injective (Sum.inl.inj h))

def partialLabels {k : ℕ} [NeZero k] (emb : Fin k ↪ Column T) (p : PartialWord emb) (j : ZMod k) :
    Label T (projectedCycle emb j) := p ((ZMod.finEquiv k).symm j)

def Extends {k : ℕ} (emb : Fin k ↪ Column T) (p : PartialWord emb) : Prop :=
  ∃ w : Word T, Allowed T w ∧ ∀ i, w (emb i)=p i

def projectedTiles {k : ℕ} [NeZero k] (emb : Fin k ↪ Column T) :
    Finset (Finset (Ambient E)) :=
  (Finset.univ.filter fun p => ¬ Extends emb p).biUnion fun p =>
    fixedCycleTiles E (projectedCycle emb) (partialLabels emb p)

theorem projectedTiles_iff {k : ℕ} [NeZero k] (emb : Fin k ↪ Column T)
    (o : GraphOutputs E) (hd : HasDependence E o) :
    (∀ F∈projectedTiles E emb, Tiles F (graph o)) ↔
    ∀ x p, (∀ i, Active E o (.inl (emb i)) x (p i)) → Extends emb p := by
  classical
  constructor
  · intro h x p hp
    by_contra hn
    have hc : ∀ F∈fixedCycleTiles E (projectedCycle emb) (partialLabels emb p),
        Tiles F (graph o) := by
      intro F hF
      exact h F (Finset.mem_biUnion.mpr ⟨p,by simp [hn],hF⟩)
    obtain ⟨j,hj⟩ := (fixed_cycle_exclusion_iff E _ _ o hd).mp hc x
    exact hj (hp ((ZMod.finEquiv k).symm j))
  · intro h F hF
    obtain ⟨p,hp,hF⟩ := Finset.mem_biUnion.mp hF
    apply (fixed_cycle_exclusion_iff E _ _ o hd).mpr ?_ F hF
    intro x
    by_contra hn
    push_neg at hn
    exact (Finset.mem_filter.mp hp).2 (h x p fun i => by
      have hi := hn (ZMod.finEquiv k i)
      change Active E o (.inl (emb ((ZMod.finEquiv k).symm (ZMod.finEquiv k i)))) x
        (p ((ZMod.finEquiv k).symm (ZMod.finEquiv k i))) at hi
      have he := (ZMod.finEquiv k).symm_apply_apply i
      rw [he] at hi
      exact hi)

theorem projectedTiles_card {k : ℕ} [NeZero k] (emb : Fin k ↪ Column T) :
    (projectedTiles E emb).card≤Fintype.card (PartialWord emb) := by
  unfold projectedTiles
  apply Finset.card_biUnion_le.trans
  simp only [fixedCycleTiles,Finset.card_singleton,Finset.sum_const,smul_eq_mul,mul_one]
  exact (Finset.card_filter_le _ _).trans_eq Finset.card_univ

def structuralTiles : Finset (Finset (Ambient E)) :=
  {kernelTile E} ∪ dependenceTiles E ∪ seedConstraintTiles E ∪
    Finset.univ.image (ordinaryActivationTile E) ∪ Finset.univ.image (seedActivationTile E)

theorem structural_subset : structuralTiles E ⊆ testTiles E := by
  intro F hF
  simp only [structuralTiles,Finset.mem_union,Finset.mem_singleton] at hF
  rcases hF with (((h|h)|h)|h)|h
  · exact h ▸ kernelTile_mem_testTiles E
  · exact dependenceTiles_subset_testTiles E h
  · exact seedConstraintTiles_subset_testTiles E h
  · obtain ⟨n,_,rfl⟩ := Finset.mem_image.mp h
    exact ordinaryActivationTile_mem_testTiles E n
  · obtain ⟨n,_,rfl⟩ := Finset.mem_image.mp h
    exact seedActivationTile_mem_testTiles E n

end
end TranslationTiling.FiniteCompiler

namespace TranslationTiling.FiniteCompiler
noncomputable section
open scoped Classical

variable {T : System} [AlphabetFamily T] (E : EncodingParameters T)

/-- Four projections, retaining only the coordinates used by each word test. -/
structure Projections (T : System) where
  p : Fin 9 ↪ Column T
  q : Fin 9 ↪ Column T
  horizontal : Fin 9 ↪ Column T
  vertical : Fin 9 ↪ Column T

def projectedDeck (C : Projections T) : Finset (Finset (Ambient E)) :=
  structuralTiles E ∪ projectedTiles E C.p ∪ projectedTiles E C.q ∪
    projectedTiles E C.horizontal ∪ projectedTiles E C.vertical

def ProjectedLine {k : ℕ} (emb : Fin k ↪ Column T) (W : WordArray T) : Prop :=
  ∀ x, Extends emb (fun i => W (emb i) (lineValue T (emb i) x))

def ProjectedSolves (C : Projections T) (A : Set (Ambient E)) : Prop :=
  ∀ F∈projectedDeck E C, Tiles F A

theorem structural_tile (C : Projections T) {A : Set (Ambient E)} (hA : ProjectedSolves E C A)
    {F : Finset (Ambient E)} (hF : F∈structuralTiles E) : Tiles F A :=
  hA F (by simp [projectedDeck,hF])

theorem projected_array (C : Projections T) {A : Set (Ambient E)} (hA : ProjectedSolves E C A) :
    ∃ W : WordArray T, ProjectedLine C.p W ∧ ProjectedLine C.q W ∧
      ProjectedLine C.horizontal W ∧ ProjectedLine C.vertical W ∧
      ∀ t : Fin 2, ∃ x : Plane, ∀ n, LetterSeedSet T t n (W n (lineValue T n x)) := by
  classical
  have ht : ∀ {F}, F∈structuralTiles E → Tiles F A := structural_tile E C hA
  obtain ⟨o,rfl⟩ := (kernelTile_iff_graph E A).mp (ht (by simp [structuralTiles]))
  have hdep := (dependenceTiles_iff E o).mp (fun F hF => ht (by simp [structuralTiles,hF]))
  have hseed := (seedConstraintTiles_iff E o hdep).mp (fun F hF => ht (by simp [structuralTiles,hF]))
  have hactive (n : Column T) (m : ℤ) : ∃ j, Active E o (.inl n) (0,m) j :=
    ordinary_active_of_tile E o hdep n (ht (by simp [structuralTiles])) (0,m)
  choose W hW using hactive
  have hW' (n : Column T) (x : Plane) : Active E o (.inl n) x (W n (lineValue T n x)) :=
    (active_ordinary_iff E hdep n (by simp : lineValue T n (0,lineValue T n x)=lineValue T n x) _).mp (hW n _)
  have hline (f : Fin 9 ↪ Column T) (hf : projectedTiles E f ⊆ projectedDeck E C) :
      ProjectedLine f W := by
    intro x
    exact (projectedTiles_iff E f o hdep).mp (fun F hF => hA F (hf hF)) x _ fun i => hW' (f i) x
  refine ⟨W,hline C.p (by intro F hF; simp [projectedDeck,hF]),
    hline C.q (by intro F hF; simp [projectedDeck,hF]),
    hline C.horizontal (by intro F hF; simp [projectedDeck,hF]),
    hline C.vertical (by intro F hF; simp [projectedDeck,hF]),?_⟩
  intro t
  obtain ⟨x,hx⟩ := seed_active_somewhere_of_tile E o hdep t (ht (by simp [structuralTiles]))
  exact ⟨x,fun n => hseed t n x _ hx (hW' n x)⟩

theorem projected_of_solves (C : Projections T) {A : Set (Ambient E)} (hA : Solves E A) :
    ProjectedSolves E C A := by
  classical
  obtain ⟨o,rfl⟩ := exists_graph_of_solves E hA
  obtain ⟨_,hd,hw,_,ha,_⟩ := (solves_iff E (graph o)).mp hA
  have hdep := (dependenceTiles_iff E o).mp hd
  have hword := (wordConstraintTiles_iff E o hdep).mp hw
  have ht (f : Fin 9 ↪ Column T) : ∀ F∈projectedTiles E f, Tiles F (graph o) := by
    apply (projectedTiles_iff E f o hdep).mpr
    intro x p hp
    have hj (n : Column T) : ∃ j : Letter T n, Active E o (.inl n) x j ∧
        ∀ i (he : f i=n), (congrArg (Letter T) he ▸ p i)=j := by
      by_cases hn : ∃ i, f i=n
      · obtain ⟨i,rfl⟩ := hn
        refine ⟨p i,hp i,?_⟩
        intro k he
        have hk := f.injective he
        subst k
        rfl
      · obtain ⟨j,hj⟩ := ordinary_active_of_tile E o hdep n (ha n) x
        exact ⟨j,hj,fun i hi => (hn ⟨i,hi⟩).elim⟩
    choose u hu hp' using hj
    exact ⟨u,hword x u hu,fun i => (hp' (f i) i rfl).symm⟩
  intro F hF
  simp only [projectedDeck,Finset.mem_union] at hF
  rcases hF with ((((hF|hF)|hF)|hF)|hF)
  · exact hA F (structural_subset E hF)
  · exact ht C.p F hF
  · exact ht C.q F hF
  · exact ht C.horizontal F hF
  · exact ht C.vertical F hF

end
end TranslationTiling.FiniteCompiler
