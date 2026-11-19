import TranslationTiling.FiniteCompiler.ProjectedCycles
import TranslationTiling.FiniteCompiler.CoreMassBounds
import TranslationTiling.FiniteCompiler.CoreSupport

namespace TranslationTiling.FiniteCompiler
noncomputable section
open scoped Classical

variable [SeedFrame] {T : System} [AlphabetFamily T]

/-- A partial word fixes its letters on a finite subset of columns. -/
structure PartialTest (T : System) [AlphabetFamily T] where
  columns : Finset (Column T)
  label : ∀ i : columns, Letter T i.val

/-- Keep precisely the columns where a letter is supplied. -/
def PartialTest.select (p : ∀ n : Column T, Option (Letter T n)) : PartialTest T where
  columns := Finset.univ.filter (fun i => (p i).isSome)
  label i := (p i.val).get ((Finset.mem_filter.mp i.property).2)

def PartialTest.Matches (p : PartialTest T) (w : Word T) : Prop :=
  ∀ i : p.columns, w i.val=p.label i

theorem PartialTest.matches_select (p : ∀ n : Column T, Option (Letter T n)) (w : Word T) :
    (PartialTest.select p).Matches w ↔ ∀ i v, p i=some v → w i=v := by
  constructor
  · intro hm i v hv
    have hi : i ∈ (PartialTest.select p).columns := by simp [PartialTest.select,hv]
    have hh := hm ⟨i,hi⟩
    simpa [PartialTest.select,hv] using hh
  · intro hm i
    exact hm i.val _ (Option.some_get _).symm

variable (E : EncodingParameters T)

private def testEmbedding (p : PartialTest T) : Fin p.columns.card ↪ Column T :=
  ((Fintype.equivFinOfCardEq (by simp : Fintype.card p.columns = p.columns.card)).symm.toEmbedding).trans
    (Function.Embedding.subtype _)

private def testEquiv (p : PartialTest T) : Fin p.columns.card ≃ p.columns :=
  (Fintype.equivFinOfCardEq (by simp : Fintype.card p.columns = p.columns.card)).symm

def partialTiles (p : PartialTest T) : Finset (Finset (Ambient E)) :=
  if hp : p.columns.Nonempty then
    letI : NeZero p.columns.card := ⟨(Finset.card_pos.mpr hp).ne'⟩
    fixedCycleTiles E (projectedCycle (testEmbedding p))
      (partialLabels (testEmbedding p) fun i => p.label (testEquiv p i))
  else ∅

theorem partialTiles_iff (p : PartialTest T) (hp : p.columns.Nonempty)
    (o : GraphOutputs E) (hd : HasDependence E o) :
    (∀ F∈partialTiles E p, Tiles F (graph o)) ↔
    ∀ x, ¬ ∀ i : p.columns, Active E o (.inl i.val) x (p.label i) := by
  letI : NeZero p.columns.card := ⟨(Finset.card_pos.mpr hp).ne'⟩
  simp only [partialTiles,dif_pos hp]
  rw [fixed_cycle_exclusion_iff E _ _ o hd]
  constructor
  · intro h x hc
    obtain ⟨j,hj⟩ := h x
    exact hj (hc (testEquiv p ((ZMod.finEquiv _).symm j)))
  · intro h x
    by_contra! hn
    apply h x
    intro i
    let k := (testEquiv p).symm i
    have hh := hn (ZMod.finEquiv _ k)
    change Active E o (.inl (testEquiv p ((ZMod.finEquiv _).symm (ZMod.finEquiv _ k))).val)
      x (p.label (testEquiv p ((ZMod.finEquiv _).symm (ZMod.finEquiv _ k)))) at hh
    rw [(ZMod.finEquiv _).symm_apply_apply,show testEquiv p k=i from (testEquiv p).apply_symm_apply i] at hh
    exact hh

theorem partialTiles_card (p : PartialTest T) : (partialTiles E p).card≤1 := by
  unfold partialTiles
  split <;> simp [fixedCycleTiles]

theorem partialTiles_member (p : PartialTest T) {F : Finset (Ambient E)}
    (hF : F∈partialTiles E p) :
    ∃ (k : ℕ) (hk : NeZero k) (cy : ZMod k ↪ Channel T) (lab : ∀ j, Label T (cy j)),
      F∈fixedCycleTiles E cy lab := by
  unfold partialTiles at hF
  split at hF
  · exact ⟨_,_,_,_,hF⟩
  · exact (Finset.notMem_empty F hF).elim

def partialDeck (ps : List (PartialTest T)) : Finset (Finset (Ambient E)) :=
  structuralTiles E ∪ (ps.flatMap (fun p => (partialTiles E p).toList)).toFinset

theorem partialDeck_cases (ps : List (PartialTest T)) {F : Finset (Ambient E)} :
    F∈partialDeck E ps ↔ F∈structuralTiles E ∨ ∃ p∈ps, F∈partialTiles E p := by
  simp only [partialDeck,Finset.mem_union,List.mem_toFinset,List.mem_flatMap,Finset.mem_toList]

theorem partialDeck_array (ps : List (PartialTest T)) {A : Set (Ambient E)}
    (ht : ∀ F∈partialDeck E ps, Tiles F A) :
    ∃ W : WordArray T,
      (∀ t : Fin 2, ∃ x : Plane, ∀ n, LetterSeedSet T t n (W n (lineValue T n x))) ∧
      ∀ x p, p∈ps → p.columns.Nonempty → ¬ p.Matches (fun n => W n (lineValue T n x)) := by
  have hs : ∀ {F}, F∈structuralTiles E → Tiles F A := fun h =>
    ht _ ((partialDeck_cases E ps).mpr (Or.inl h))
  obtain ⟨o,rfl⟩ := (kernelTile_iff_graph E A).mp (hs (by simp [structuralTiles]))
  have hd := (dependenceTiles_iff E o).mp (fun F hF => hs (by simp [structuralTiles,hF]))
  have hseed := (seedConstraintTiles_iff E o hd).mp (fun F hF => hs (by simp [structuralTiles,hF]))
  have ha (n : Column T) (m : ℤ) : ∃ j, Active E o (.inl n) (0,m) j :=
    ordinary_active_of_tile E o hd n (hs (by simp [structuralTiles])) (0,m)
  choose W hW using ha
  have hW' (n : Column T) (x : Plane) : Active E o (.inl n) x (W n (lineValue T n x)) :=
    (active_ordinary_iff E hd n (by simp : lineValue T n (0,lineValue T n x)=lineValue T n x) _).mp (hW n _)
  refine ⟨W,?_,?_⟩
  · intro t
    obtain ⟨x,hx⟩ := seed_active_somewhere_of_tile E o hd t (hs (by simp [structuralTiles]))
    exact ⟨x,fun n => hseed t n x _ hx (hW' n x)⟩
  · intro x p hp hn hm
    exact (partialTiles_iff E p hn o hd).mp
      (fun F hF => ht F ((partialDeck_cases E ps).mpr (Or.inr ⟨p,hp,hF⟩))) x
      (fun i => hm i ▸ hW' i x)

theorem tiles_partialDeck_of_solves (ps : List (PartialTest T)) {A : Set (Ambient E)} (hA : Solves E A)
    (hs : ∀ p∈ps, ∀ w : Word T, Allowed T w → ¬p.Matches w) :
    ∀ F∈partialDeck E ps, Tiles F A := by
  obtain ⟨o,rfl⟩ := exists_graph_of_solves E hA
  obtain ⟨_,hd,hw,_,ha,_⟩ := (solves_iff E (graph o)).mp hA
  have hdep := (dependenceTiles_iff E o).mp hd
  have hword := (wordConstraintTiles_iff E o hdep).mp hw
  intro F hF
  rcases (partialDeck_cases E ps).mp hF with hF|⟨p,hp,hF⟩
  · exact hA F (structural_subset E hF)
  have hn : p.columns.Nonempty := by
    by_contra hh
    simpa [partialTiles,hh] using hF
  apply (partialTiles_iff E p hn o hdep).mpr ?_ F hF
  intro x hx
  have hj (n : Column T) : ∃ j : Letter T n, Active E o (.inl n) x j ∧
      ∀ hi : n ∈ p.columns, p.label ⟨n,hi⟩=j := by
    by_cases hi : n∈p.columns
    · exact ⟨p.label ⟨n,hi⟩,hx ⟨n,hi⟩,fun _ => rfl⟩
    · obtain ⟨j,hj⟩ := ordinary_active_of_tile E o hdep n (ha n) x
      exact ⟨j,hj,fun h => (hi h).elim⟩
  choose u ha' he using hj
  exact hs p hp u (hword x u ha') (fun i => (he i.val i.property).symm)

end
end TranslationTiling.FiniteCompiler
