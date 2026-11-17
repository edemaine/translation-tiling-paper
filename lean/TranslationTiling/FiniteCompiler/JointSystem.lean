import TranslationTiling.FiniteCompiler.TaggedSystem

/-! Injective ternary codes with seed predicates tested on whole codewords. -/
namespace TranslationTiling.FiniteCompiler.JointSystem
open scoped Classical
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

structure Code (T : LeanWang.TileSet) (m : ℕ) where
  pos : 0 < m
  word : Sudoku.Symbol T → Fin m → Fin 3
  injective : Function.Injective word

abbrev flat := @TaggedSystem.flat

def system {T : LeanWang.TileSet} {m : ℕ} (code : Code T m) : System where
  width := Sudoku.Width * m
  width_pos := Nat.mul_pos (by decide) code.pos
  alphabet := 3
  slope n := ((finProdFinEquiv.symm n : Sudoku.Column × Fin m).1.val : ℤ)
  allowed v := ∃ w : Sudoku.Column → Sudoku.Symbol T, Sudoku.Allowed T w ∧
    ∀ i b, v (flat i b) = code.word (w i) b
  seed _ _ := True

@[simp] theorem lineValue_flat {T : LeanWang.TileSet} {m : ℕ}
    (code : Code T m) (i : Sudoku.Column) (b : Fin m) (x : Plane) :
    lineValue (system code) (flat i b) x = Compiler.lineValue i x := by
  simp [lineValue, system, flat, TaggedSystem.flat, Compiler.lineValue]

def seedWords {T : LeanWang.TileSet} {m : ℕ} (code : Code T m) (t : Fin 2) :
    Set (Fin m → Fin 3) := {v | ∃ s, Compiler.SeedSet t s ∧ code.word s = v}

def slots {T : LeanWang.TileSet} {m : ℕ} (code : Code T m)
    (t : Fin 2) (i : Sudoku.Column) : Fin (m+1) ↪ Channel (system code) where
  toFun := Fin.cases (.inr t) (fun b => .inl (flat i b))
  inj' := by
    intro a b
    refine Fin.cases ?_ (fun a => ?_) a <;> refine Fin.cases ?_ (fun b => ?_) b
    · intro _; rfl
    · intro h; cases h
    · intro h; cases h
    · intro h
      have he := finProdFinEquiv.injective (Sum.inl.inj h)
      exact congrArg Fin.succ (congrArg Prod.snd he)

def cycle {T : LeanWang.TileSet} {m : ℕ} (code : Code T m)
    (t : Fin 2) (i : Sudoku.Column) : ZMod (m+1) ↪ Channel (system code) :=
  slots code t i

def labels {T : LeanWang.TileSet} {m : ℕ} (code : Code T m)
    (t : Fin 2) (i : Sudoku.Column) (v : Fin m → Fin 3) (j : ZMod (m+1)) :
    Label (system code) (cycle code t i j) :=
  Fin.cases (motive := fun a => Label (system code) (slots code t i a))
    () (fun b => v b) j

variable {T : LeanWang.TileSet} {m : ℕ} (code : Code T m)
    (E : EncodingParameters (system code))

theorem cycle_exclusion_iff (t : Fin 2) (i : Sudoku.Column) (v : Fin m → Fin 3)
    (o : GraphOutputs E) (hdep : HasDependence E o) :
    (∀ F ∈ fixedCycleTiles E (cycle code t i) (labels code t i v), Tiles F (graph o)) ↔
      ∀ x, ¬ (Active E o (.inr t) x () ∧
        ∀ b, Active E o (.inl (flat i b)) x (v b)) := by
  rw [fixed_cycle_exclusion_iff E _ _ o hdep]
  constructor
  · intro h x hx
    obtain ⟨j,hj⟩ := h x
    have hall : ∀ a : Fin (m+1), Active E o (slots code t i a) x
        (Fin.cases (motive := fun a => Label (system code) (slots code t i a)) () (fun b => v b) a) := by
      intro a
      exact Fin.cases hx.1 (fun b => hx.2 b) a
    exact hj (hall j)
  · intro h x
    by_cases hs : Active E o (.inr t) x ()
    · obtain ⟨b,hb⟩ := not_forall.mp (fun hb => h x ⟨hs,hb⟩)
      refine ⟨b.succ,?_⟩
      exact hb
    · refine ⟨0,?_⟩
      exact hs

def seedTiles : Finset (Finset (Ambient E)) :=
  (Finset.univ.filter (fun q : Fin 2 × Sudoku.Column × Sudoku.Symbol T =>
    ¬ Compiler.SeedSet q.1 q.2.2)).biUnion fun q =>
      fixedCycleTiles E (cycle code q.1 q.2.1) (labels code q.1 q.2.1 (code.word q.2.2))

def testTiles : Finset (Finset (Ambient E)) :=
  FiniteCompiler.testTiles E ∪ seedTiles code E

def Solves (A : Set (Ambient E)) : Prop := ∀ F ∈ testTiles code E, Tiles F A

theorem seedTiles_iff (o : GraphOutputs E) (hdep : HasDependence E o) :
    (∀ F ∈ seedTiles code E, Tiles F (graph o)) ↔
      ∀ t i x s, Active E o (.inr t) x () →
        (∀ b, Active E o (.inl (flat i b)) x (code.word s b)) → Compiler.SeedSet t s := by
  constructor
  · intro h t i x s hs hv
    by_contra hn
    have hh : ∀ F ∈ fixedCycleTiles E (cycle code t i) (labels code t i (code.word s)), Tiles F (graph o) := by
      intro F hF
      exact h F (Finset.mem_biUnion.mpr ⟨(t,i,s),by simp [hn],hF⟩)
    exact (cycle_exclusion_iff code E t i (code.word s) o hdep).mp hh x ⟨hs,hv⟩
  · intro h F hF
    obtain ⟨⟨t,i,s⟩,hq,hF⟩ := Finset.mem_biUnion.mp hF
    apply (cycle_exclusion_iff code E t i (code.word s) o hdep).mpr ?_ F hF
    intro x ⟨hs,hv⟩
    exact (Finset.mem_filter.mp hq).2 (h t i x s hs hv)

theorem wang_of_array (W : WordArray (system code)) (hrule : LineRule (system code) W)
    (hseed : ∀ t : Fin 2, ∃ x : Plane, ∀ i,
      (fun b => W (flat i b) (Compiler.lineValue i x)) ∈ seedWords code t) :
    LeanWang.TilesPlane T := by
  let v : Sudoku.Column × Fin m → ℤ → Fin 3 := fun j y => W (flat j.1 j.2) y
  have hv : ∀ x : Plane, Compiler.BitChannels.EncodedAllowed code.word
      {w | Sudoku.Allowed T w} (fun j => v j (Compiler.lineValue j.1 x)) := by
    intro x
    obtain ⟨w,hw,hbits⟩ := hrule x
    refine ⟨w,hw,?_⟩
    funext j
    simpa only [Compiler.BitChannels.encodeWord,v,lineValue_flat] using (hbits j.1 j.2).symm
  obtain ⟨w,hbits,hw⟩ := Compiler.BitChannels.array_of_encoded_line_rule
    code.word code.injective {w | Sudoku.Allowed T w}
    Compiler.lineValue (fun y => (0,y)) (by intro i y; simp [Compiler.lineValue]) v hv
  have hseeds : ∀ t : Fin 2, ∃ x : Plane, ∀ i,
      Compiler.SeedSet t (w i (Compiler.lineValue i x)) := by
    intro t
    obtain ⟨x,hx⟩ := hseed t
    refine ⟨x,fun i => ?_⟩
    obtain ⟨s,hs,he⟩ := hx i
    have he' : code.word (w i (Compiler.lineValue i x)) = code.word s := by
      funext b
      rw [hbits]
      exact (congrFun he b).symm
    rw [code.injective he']
    exact hs
  have hrule' : Sudoku.LineRule w := by
    intro d e
    simpa only [Compiler.lineValue,mul_comm,add_comm] using (show Sudoku.Allowed T (fun i => w i (Compiler.lineValue i (d,e))) from hw (d,e))
  obtain ⟨x₁,hx₁⟩ := hseeds 0
  obtain ⟨x₂,hx₂⟩ := hseeds 1
  have hnonconstant : Sudoku.NonconstantColumns w := by
    constructor
    · intro i
      refine ⟨Compiler.lineValue i x₁,Compiler.lineValue i x₂,?_⟩
      intro h
      have he := congrArg (fun z : (ZMod Sudoku.p)ˣ => z.val) h
      rw [(hx₁ i).1,(hx₂ i).1] at he
      exact (by decide : (1 : ZMod Sudoku.p) ≠ 2) he
    · intro i
      refine ⟨Compiler.lineValue i x₁,Compiler.lineValue i x₂,?_⟩
      intro h
      have he := congrArg (fun z : (ZMod Sudoku.q)ˣ => z.val) h
      rw [(hx₁ i).2,(hx₂ i).2] at he
      exact (by decide : (1 : ZMod Sudoku.q) ≠ 2) he
  exact (wang_plane_iff_quadrant T).mpr (Sudoku.soundness T w hrule' hnonconstant)

theorem wang_of_solves {A : Set (Ambient E)} (hA : Solves code E A) :
    LeanWang.TilesPlane T := by
  have hbase : FiniteCompiler.Solves E A := fun F hF => hA F (Finset.mem_union_left _ hF)
  obtain ⟨o,rfl⟩ := exists_graph_of_solves E hbase
  obtain ⟨_,hd,hw,_,ha,hb⟩ := (solves_iff E (graph o)).mp hbase
  have hdep := (dependenceTiles_iff E o).mp hd
  have hword := (wordConstraintTiles_iff E o hdep).mp hw
  have hseed := (seedTiles_iff code E o hdep).mp
    (fun F hF => hA F (Finset.mem_union_right _ hF))
  have hactive (n : Column (system code)) (y : ℤ) : ∃ j, Active E o (.inl n) (0,y) j :=
    ordinary_active_of_tile E o hdep n (ha n) (0,y)
  choose W hW using hactive
  have hW' (n : Column (system code)) (x : Plane) :
      Active E o (.inl n) x (W n (lineValue (system code) n x)) :=
    (FiniteCompiler.active_ordinary_iff E hdep n (by simp) _).mp (hW n _)
  apply wang_of_array code W (fun x => hword x _ (fun n => hW' n x))
  intro t
  obtain ⟨x,hx⟩ := seed_active_somewhere_of_tile E o hdep t (hb t)
  obtain ⟨w,_,hbits⟩ := hword x _ (fun n => hW' n x)
  refine ⟨x,fun i => ⟨w i,?_,?_⟩⟩
  · apply hseed t i x (w i) hx
    intro b
    have hb' := hW' (flat i b) x
    have he := hbits i b
    change W (flat i b) (lineValue (system code) (flat i b) x) = code.word (w i) b at he
    rw [he] at hb'
    exact hb'
  · funext b
    simpa only [lineValue_flat] using (hbits i b).symm

theorem exists_solution_of_wang (hT : LeanWang.TilesPlane T) :
    ∃ A : Set (Ambient E), Solves code E A := by
  obtain ⟨τ,hτ⟩ := (wang_plane_iff_quadrant T).mp hT
  let W₀ := Sudoku.canonical τ
  let W : WordArray (system code) := fun n y =>
    code.word (W₀ (finProdFinEquiv.symm n : Sudoku.Column × Fin m).1 y)
      (finProdFinEquiv.symm n : Sudoku.Column × Fin m).2
  have hW (i : Sudoku.Column) (b : Fin m) (y : ℤ) :
      W (flat i b) y = code.word (W₀ i y) b := by
    simp only [W,flat,TaggedSystem.flat,Equiv.symm_apply_apply]
    rfl
  have hrule : LineRule (system code) W := by
    intro x
    change ∃ w : Sudoku.Column → Sudoku.Symbol T, Sudoku.Allowed T w ∧
      ∀ i b, W (flat i b) (lineValue (system code) (flat i b) x) = code.word (w i) b
    refine ⟨fun i => W₀ i (Compiler.lineValue i x),?_,?_⟩
    · simpa only [W₀,Compiler.lineValue,mul_comm,add_comm] using
        Sudoku.canonical_lineRule τ hτ (τ (0,0)) x.1 x.2
    · intro i b
      rw [lineValue_flat,hW]
  have hbase := CommonModel.common_solution E W hrule (fun _ _ _ _ => trivial)
  refine ⟨CommonModel.commonGraph E W,fun F hF => ?_⟩
  rcases Finset.mem_union.mp hF with hF | hF
  · exact hbase F hF
  · apply (seedTiles_iff code E (CommonModel.outputs E W)
      (CommonModel.outputs_hasDependence E W)).mpr ?_ F hF
    intro t i x s hs hv
    have hv' : code.word (W₀ i (Compiler.lineValue i x)) = code.word s := by
      funext b
      have hb := (CommonModel.active_ordinary_iff E W (flat i b) x (code.word s b)).mp (hv b)
      change code.word s b = W (flat i b) (lineValue (system code) (flat i b) x) at hb
      rw [lineValue_flat,hW] at hb
      exact hb.symm
    rw [←code.injective hv']
    exact Compiler.canonical_seed_regions τ t i x
      ((CommonModel.active_seed_iff E W t x).mp hs)

theorem finite_system_iff_wang :
    LeanWang.TilesPlane T ↔ ∃ A : Set (Ambient E), Solves code E A :=
  ⟨exists_solution_of_wang code E,fun ⟨_,hA⟩ => wang_of_solves code E hA⟩

end
end TranslationTiling.FiniteCompiler.JointSystem
