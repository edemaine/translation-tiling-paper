import TranslationTiling.FiniteCompiler.SparseTernaryArray
import TranslationTiling.FiniteCompiler.JointSystem

namespace TranslationTiling.FiniteCompiler.SparseTernary
open scoped Classical
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
variable {T : LeanWang.TileSet}

def seedSlots (t : Fin 2) (i : Sudoku.Column) (b : Fin 3) : Fin 2 ↪ Channel (system T) where
  toFun := fun j => if j=0 then .inr t else .inl (arithSlot T.length i b)
  inj' := by intro j k h; fin_cases j <;> fin_cases k <;> simp_all

def seedCycle (t : Fin 2) (i : Sudoku.Column) (b : Fin 3) : ZMod 2 ↪ Channel (system T) :=
  seedSlots t i b

def seedLabels (t : Fin 2) (i : Sudoku.Column) (b v : Fin 3) (j : ZMod 2) :
    Label (system T) (seedCycle t i b j) :=
  by
    change Label (system T) (if (j:Fin 2)=0 then .inr t else .inl (arithSlot T.length i b))
    split_ifs
    · exact ()
    · exact v

variable (E : EncodingParameters (system T))

theorem seed_cycle_iff (t : Fin 2) (i : Sudoku.Column) (b v : Fin 3)
    (o : GraphOutputs E) (hd : HasDependence E o) :
    (∀ F∈fixedCycleTiles E (seedCycle t i b) (seedLabels t i b v), Tiles F (graph o)) ↔
      ∀ x, ¬(Active E o (.inr t) x () ∧ Active E o (.inl (arithSlot T.length i b)) x v) := by
  rw [fixed_cycle_exclusion_iff E _ _ o hd]
  constructor
  · intro h x hx
    obtain ⟨j,hj⟩ := h x
    fin_cases j
    · exact hj hx.1
    · exact hj hx.2
  · intro h x
    by_cases hs : Active E o (.inr t) x ()
    · exact ⟨1,fun hv => h x ⟨hs,hv⟩⟩
    · exact ⟨0,hs⟩

def seedTiles : Finset (Finset (Ambient E)) :=
  (Finset.univ.filter (fun q : Fin 2 × Sudoku.Column × Fin 3 × Fin 3 =>
    q.2.2.2≠arithWord (seedArithmetic q.1) q.2.2.1)).biUnion fun q =>
      fixedCycleTiles E (seedCycle q.1 q.2.1 q.2.2.1) (seedLabels q.1 q.2.1 q.2.2.1 q.2.2.2)

def testFamily : Finset (Finset (Ambient E)) := testTiles E ∪ seedTiles E

def Solves (A : Set (Ambient E)) : Prop := ∀ F∈testFamily E, Tiles F A

theorem seedTiles_iff (o : GraphOutputs E) (hd : HasDependence E o) :
    (∀ F∈seedTiles E, Tiles F (graph o)) ↔
      ∀ t i b x (v : Fin 3), Active E o (.inr t) x () →
        Active E o (.inl (arithSlot T.length i b)) x v → v=arithWord (seedArithmetic t) b := by
  constructor
  · intro h t i b x v hs hv
    by_contra hn
    have hh : ∀ F∈fixedCycleTiles E (seedCycle t i b) (seedLabels t i b v), Tiles F (graph o) := by
      intro F hF
      exact h F (Finset.mem_biUnion.mpr ⟨(t,i,b,v),Finset.mem_filter.mpr ⟨Finset.mem_univ _,hn⟩,hF⟩)
    exact (seed_cycle_iff E t i b v o hd).mp hh x ⟨hs,hv⟩
  · intro h F hF
    obtain ⟨⟨t,i,b,v⟩,hq,hF⟩ := Finset.mem_biUnion.mp hF
    apply (seed_cycle_iff E t i b v o hd).mpr ?_ F hF
    intro x ⟨hs,hv⟩
    exact (Finset.mem_filter.mp hq).2 (h t i b x v hs hv)

theorem wang_of_solves {A : Set (Ambient E)} (hA : Solves E A) : LeanWang.TilesPlane T := by
  have hb : FiniteCompiler.Solves E A := fun F hF => hA F (Finset.mem_union_left _ hF)
  obtain ⟨o,rfl⟩ := exists_graph_of_solves E hb
  obtain ⟨_,hd,hw,_,ha,hact⟩ := (solves_iff E (graph o)).mp hb
  have hdep := (dependenceTiles_iff E o).mp hd
  have hword := (wordConstraintTiles_iff E o hdep).mp hw
  have hseed := (seedTiles_iff E o hdep).mp (fun F hF => hA F (Finset.mem_union_right _ hF))
  have hex (n : Column (system T)) (m : ℤ) : ∃ j, Active E o (.inl n) (0,m) j :=
    ordinary_active_of_tile E o hdep n (ha n) (0,m)
  choose W hW using hex
  have hW' (n : Column (system T)) (x : Plane) :
      Active E o (.inl n) x (W n (lineValue (system T) n x)) :=
    (active_ordinary_iff E hdep n (by simp) _).mp (hW n _)
  have hr : LineRule (system T) W := fun x => hword x _ (fun n => hW' n x)
  have hs : SeedRule W := by
    intro t
    obtain ⟨x,hx⟩ := seed_active_somewhere_of_tile E o hdep t (hact t)
    refine ⟨x,fun i b => ?_⟩
    simpa only [lineValue_arith,Label] using
      hseed t i b x _ hx (hW' (arithSlot T.length i b) x)
  exact Sudoku.Sparse.soundness T (board W hr) (board_lineRule W hr) (board_nonconstant W hr hs)

end
end TranslationTiling.FiniteCompiler.SparseTernary
