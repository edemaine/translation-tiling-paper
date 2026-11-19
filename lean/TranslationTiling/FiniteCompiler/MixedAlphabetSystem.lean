import TranslationTiling.FiniteCompiler.CommonSolution
import TranslationTiling.FiniteCompiler.Soundness
import TranslationTiling.Compiler.Completeness

/-! Whole-codeword simulation with three independently sized alphabets. -/
namespace TranslationTiling.FiniteCompiler.MixedAlphabetSystem
open scoped Classical
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

structure Code (T : LeanWang.TileSet) where
  radix : Fin 3 → ℕ
  word : Sudoku.Symbol T → (b : Fin 3) → Fin (radix b)
  injective : Function.Injective word

def flat (i : Sudoku.Column) (b : Fin 3) : Fin (Sudoku.Width*3) :=
  finProdFinEquiv (i,b)

def system {T : LeanWang.TileSet} (_ : Code T) : System where
  width := Sudoku.Width*3
  width_pos := by decide
  alphabet := 0
  slope n := ((finProdFinEquiv.symm n : Sudoku.Column × Fin 3).1.val : ℤ)
  allowed := ∅
  seed _ _ := True

@[instance_reducible] def family {T : LeanWang.TileSet} (code : Code T) : AlphabetFamily (system code) where
  size n := code.radix (finProdFinEquiv.symm n : Sudoku.Column × Fin 3).2
  allowed v := ∃ w : Sudoku.Column → Sudoku.Symbol T, Sudoku.Allowed T w ∧
    ∀ i b, (v (flat i b)).val=(code.word (w i) b).val
  seed _ _ _ := True

local instance codeFamily {T : LeanWang.TileSet} (code : Code T) :
    AlphabetFamily (system code) := family code

abbrev Parameters {T : LeanWang.TileSet} (code : Code T) :=
  @EncodingParameters regularSeedFrame (system code) (family code)

def letter {T : LeanWang.TileSet} (code : Code T) (i : Sudoku.Column) (b : Fin 3)
    (v : Fin (code.radix b)) : Letter (system code) (flat i b) :=
  ⟨v.val,by
    change v.val < code.radix (finProdFinEquiv.symm (finProdFinEquiv (i,b)) : Sudoku.Column × Fin 3).2
    simpa only [Equiv.symm_apply_apply] using v.isLt⟩

@[simp] theorem letter_val {T : LeanWang.TileSet} (code : Code T)
    (i : Sudoku.Column) (b : Fin 3) (v : Fin (code.radix b)) :
    (letter code i b v).val=v.val := rfl

@[simp] theorem lineValue_flat {T : LeanWang.TileSet} (code : Code T)
    (i : Sudoku.Column) (b : Fin 3) (x : Plane) :
    lineValue (system code) (flat i b) x=Compiler.lineValue i x := by
  simp [lineValue,system,flat,Compiler.lineValue]

variable {T : LeanWang.TileSet} (code : Code T)

def slots (t : Fin 2) (i : Sudoku.Column) : Fin 4 ↪ Channel (system code) where
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

def cycle (t : Fin 2) (i : Sudoku.Column) : ZMod 4 ↪ Channel (system code) := slots code t i

def labels (t : Fin 2) (i : Sudoku.Column) (v : (b : Fin 3) → Fin (code.radix b))
    (j : ZMod 4) : Label (system code) (cycle code t i j) :=
  Fin.cases (motive := fun a => Label (system code) (slots code t i a))
    () (fun b => letter code i b (v b)) j

variable (E : Parameters code)

theorem cycle_exclusion_iff (t : Fin 2) (i : Sudoku.Column)
    (v : (b : Fin 3) → Fin (code.radix b)) (o : GraphOutputs E) (hdep : HasDependence E o) :
    (∀ F∈fixedCycleTiles E (cycle code t i) (labels code t i v), Tiles F (graph o)) ↔
      ∀ x, ¬ (Active E o (.inr t) x () ∧
        ∀ b, Active E o (.inl (flat i b)) x (letter code i b (v b))) := by
  rw [fixed_cycle_exclusion_iff E _ _ o hdep]
  constructor
  · intro h x hx
    obtain ⟨j,hj⟩ := h x
    have hall : ∀ a : Fin 4, Active E o (slots code t i a) x
        (Fin.cases (motive := fun a => Label (system code) (slots code t i a))
          () (fun b => letter code i b (v b)) a) := by
      intro a
      exact Fin.cases hx.1 (fun b => hx.2 b) a
    exact hj (hall j)
  · intro h x
    by_cases hs : Active E o (.inr t) x ()
    · obtain ⟨b,hb⟩ := not_forall.mp (fun hb => h x ⟨hs,hb⟩)
      exact ⟨b.succ,hb⟩
    · exact ⟨0,hs⟩

def seedTiles : Finset (Finset (Ambient E)) :=
  (Finset.univ.filter (fun q : Fin 2 × Sudoku.Column × Sudoku.Symbol T =>
    ¬ Compiler.SeedSet q.1 q.2.2)).biUnion fun q =>
      fixedCycleTiles E (cycle code q.1 q.2.1) (labels code q.1 q.2.1 (code.word q.2.2))

def testTiles : Finset (Finset (Ambient E)) := FiniteCompiler.testTiles E ∪ seedTiles code E

def Solves (A : Set (Ambient E)) : Prop := ∀ F∈testTiles code E, Tiles F A

theorem seedTiles_iff (o : GraphOutputs E) (hdep : HasDependence E o) :
    (∀ F∈seedTiles code E, Tiles F (graph o)) ↔
      ∀ t i x s, Active E o (.inr t) x () →
        (∀ b, Active E o (.inl (flat i b)) x (letter code i b (code.word s b))) →
          Compiler.SeedSet t s := by
  constructor
  · intro h t i x s hs hv
    by_contra hn
    have hh : ∀ F∈fixedCycleTiles E (cycle code t i) (labels code t i (code.word s)), Tiles F (graph o) := by
      intro F hF
      exact h F (Finset.mem_biUnion.mpr ⟨(t,i,s),by simp [hn],hF⟩)
    exact (cycle_exclusion_iff code E t i (code.word s) o hdep).mp hh x ⟨hs,hv⟩
  · intro h F hF
    obtain ⟨⟨t,i,s⟩,hq,hF⟩ := Finset.mem_biUnion.mp hF
    apply (cycle_exclusion_iff code E t i (code.word s) o hdep).mpr ?_ F hF
    intro x ⟨hs,hv⟩
    exact (Finset.mem_filter.mp hq).2 (h t i x s hs hv)


theorem wang_of_array (W : WordArray (system code)) (hrule : LineRule (system code) W)
    (hseed : ∀ t : Fin 2, ∃ x : Plane, ∀ i, ∃ s, Compiler.SeedSet t s ∧
      ∀ b, (W (flat i b) (Compiler.lineValue i x)).val=(code.word s b).val) :
    LeanWang.TilesPlane T := by
  have hrows (y : ℤ) : ∃ w : Sudoku.Column → Sudoku.Symbol T,
      Sudoku.Allowed T w ∧ ∀ i b, (W (flat i b) y).val=(code.word (w i) b).val := by
    have hh := hrule (0,y)
    change ∃ w, Sudoku.Allowed T w ∧ ∀ i b,
      (W (flat i b) (lineValue (system code) (flat i b) (0,y))).val=(code.word (w i) b).val at hh
    simpa only [lineValue, mul_zero,add_zero] using hh
  choose rows hallowed hbits using hrows
  let w : Sudoku.Column → ℤ → Sudoku.Symbol T := fun i y => rows y i
  have hw : ∀ x : Plane, Sudoku.Allowed T (fun i => w i (Compiler.lineValue i x)) := by
    intro x
    obtain ⟨v,hv,hcode⟩ := hrule x
    have he (i : Sudoku.Column) : w i (Compiler.lineValue i x)=v i := by
      apply code.injective
      funext b
      apply Fin.ext
      exact (hbits (Compiler.lineValue i x) i b).symm.trans
        (by simpa only [lineValue_flat] using hcode i b)
    simpa only [he] using hv
  have hseeds : ∀ t : Fin 2, ∃ x : Plane, ∀ i,
      Compiler.SeedSet t (w i (Compiler.lineValue i x)) := by
    intro t
    obtain ⟨x,hx⟩ := hseed t
    refine ⟨x,fun i => ?_⟩
    obtain ⟨s,hs,he⟩ := hx i
    have he' : code.word (w i (Compiler.lineValue i x))=code.word s := by
      funext b
      apply Fin.ext
      exact (hbits (Compiler.lineValue i x) i b).symm.trans (he b)
    rw [code.injective he']
    exact hs
  have hrule' : Sudoku.LineRule w := by
    intro d e
    simpa only [Compiler.lineValue,mul_comm,add_comm] using hw (d,e)
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
  obtain ⟨v,_,hbits⟩ := hword x _ (fun n => hW' n x)
  refine ⟨x,fun i => ⟨v i,?_,?_⟩⟩
  · apply hseed t i x (v i) hx
    intro b
    have he : W (flat i b) (lineValue (system code) (flat i b) x)=
        letter code i b (code.word (v i) b) := Fin.ext (hbits i b)
    rw [←he]
    exact hW' _ _
  · intro b
    simpa only [lineValue_flat] using hbits i b

theorem exists_solution_of_wang (hT : LeanWang.TilesPlane T) :
    ∃ A : Set (Ambient E), Solves code E A := by
  obtain ⟨τ,hτ⟩ := (wang_plane_iff_quadrant T).mp hT
  let W₀ := Sudoku.canonical τ
  let W : WordArray (system code) := fun n y =>
    code.word (W₀ (finProdFinEquiv.symm n : Sudoku.Column × Fin 3).1 y)
      (finProdFinEquiv.symm n : Sudoku.Column × Fin 3).2
  have hW (i : Sudoku.Column) (b : Fin 3) (y : ℤ) :
      (W (flat i b) y).val=(code.word (W₀ i y) b).val := by
    have he : (finProdFinEquiv.symm (flat i b) : Sudoku.Column × Fin 3)=(i,b) :=
      Equiv.symm_apply_apply finProdFinEquiv (i,b)
    change (code.word (W₀ (finProdFinEquiv.symm (flat i b) : Sudoku.Column × Fin 3).1 y)
      (finProdFinEquiv.symm (flat i b) : Sudoku.Column × Fin 3).2).val=_
    rw [he]

  have hrule : LineRule (system code) W := by
    intro x
    change ∃ w : Sudoku.Column → Sudoku.Symbol T, Sudoku.Allowed T w ∧
      ∀ i b, (W (flat i b) (lineValue (system code) (flat i b) x)).val=(code.word (w i) b).val
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
    have hv' : code.word (W₀ i (Compiler.lineValue i x))=code.word s := by
      funext b
      apply Fin.ext
      have hb := (CommonModel.active_ordinary_iff E W (flat i b) x
        (letter code i b (code.word s b))).mp (hv b)
      have hb' := congrArg Fin.val hb
      change (code.word s b).val=(W (flat i b) (lineValue (system code) (flat i b) x)).val at hb'
      simpa only [lineValue_flat,hW] using hb'.symm
    rw [←code.injective hv']
    exact Compiler.canonical_seed_regions τ t i x
      ((CommonModel.active_seed_iff E W t x).mp hs)

theorem finite_system_iff_wang :
    LeanWang.TilesPlane T ↔ ∃ A : Set (Ambient E), Solves code E A :=
  ⟨exists_solution_of_wang code E,fun ⟨_,hA⟩ => wang_of_solves code E hA⟩

end
end TranslationTiling.FiniteCompiler.MixedAlphabetSystem
