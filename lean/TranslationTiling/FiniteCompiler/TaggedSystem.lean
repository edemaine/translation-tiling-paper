import TranslationTiling.FiniteCompiler.TernarySystem

/-! A seed-preserving injective code can use arbitrary ternary payloads. -/
namespace TranslationTiling.FiniteCompiler.TaggedSystem
open scoped Classical
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

structure Code (T : LeanWang.TileSet) (m : ℕ) where
  pos : 0 < m
  word : Sudoku.Symbol T → Fin m → Fin 3
  injective : Function.Injective word
  seed : ∀ t s, (∀ b, word s b = TernarySystem.seedTag t ∨ word s b = 2) ↔
    Compiler.SeedSet t s

def flat {m : ℕ} (i : Sudoku.Column) (b : Fin m) : Fin (Sudoku.Width * m) :=
  finProdFinEquiv (i, b)

def system {T : LeanWang.TileSet} {m : ℕ} (code : Code T m) : System where
  width := Sudoku.Width * m
  width_pos := Nat.mul_pos (by decide) code.pos
  alphabet := 3
  slope n := ((finProdFinEquiv.symm n : Sudoku.Column × Fin m).1.val : ℤ)
  allowed v := ∃ w : Sudoku.Column → Sudoku.Symbol T, Sudoku.Allowed T w ∧
    ∀ i b, v (flat i b) = code.word (w i) b
  seed t j := j = TernarySystem.seedTag t ∨ j = 2

@[simp] theorem lineValue_flat {T : LeanWang.TileSet} {m : ℕ}
    (code : Code T m) (i : Sudoku.Column) (b : Fin m) (x : Plane) :
    lineValue (system code) (flat i b) x = Compiler.lineValue i x := by
  simp [lineValue, system, flat, Compiler.lineValue]

@[simp] theorem seed_symbolBit {T : LeanWang.TileSet} {m : ℕ}
    (code : Code T m) (t : Fin 2) (s : Sudoku.Symbol T) :
    (∀ b, SeedSet (system code) t (code.word s b)) ↔ Compiler.SeedSet t s := by
  exact code.seed t s

theorem slope_bound {T : LeanWang.TileSet} {m : ℕ}
    (code : Code T m) (n : Column (system code)) :
    ((system code).slope n).natAbs ≤ Sudoku.Width := by
  change (((finProdFinEquiv.symm n : Sudoku.Column × Fin m).1.val : ℤ)).natAbs ≤ _
  rw [Int.natAbs_natCast]
  exact (finProdFinEquiv.symm n : Sudoku.Column × Fin m).1.isLt.le

theorem wang_of_array {T : LeanWang.TileSet} {m : ℕ} (code : Code T m)
    (W : WordArray (system code)) (hrule : LineRule (system code) W)
    (hseed : ∀ t : Fin 2, ∃ x : Plane, ∀ n,
      SeedSet (system code) t (W n (lineValue (system code) n x))) :
    LeanWang.TilesPlane T := by
  let v : Sudoku.Column × Fin m → ℤ → Fin 3 := fun j m => W (flat j.1 j.2) m
  have hv : ∀ x : Plane, Compiler.BitChannels.EncodedAllowed code.word
      {w | Sudoku.Allowed T w} (fun j => v j (Compiler.lineValue j.1 x)) := by
    intro x
    obtain ⟨w, hw, hbits⟩ := hrule x
    refine ⟨w, hw, ?_⟩
    funext j
    rcases j with ⟨i, b⟩
    simpa only [Compiler.BitChannels.encodeWord, v, lineValue_flat] using (hbits i b).symm
  obtain ⟨w, hbits, hw⟩ := Compiler.BitChannels.array_of_encoded_line_rule
    code.word code.injective {w | Sudoku.Allowed T w}
    Compiler.lineValue (fun m => (0, m)) (by intro i m; simp [Compiler.lineValue]) v hv
  have hseeds : ∀ t : Fin 2, ∃ x : Plane, ∀ i,
      Compiler.SeedSet t (w i (Compiler.lineValue i x)) := by
    intro t
    obtain ⟨x, hx⟩ := hseed t
    refine ⟨x, fun i => ?_⟩
    apply (seed_symbolBit code t _).mp
    intro b
    rw [hbits]
    simpa only [v, lineValue_flat] using hx (flat i b)
  have hrule' : Sudoku.LineRule w := by
    intro d e
    have h : Sudoku.Allowed T (fun i => w i (Compiler.lineValue i (d, e))) := hw (d, e)
    simpa only [Compiler.lineValue, mul_comm, add_comm] using h
  obtain ⟨x₁, hx₁⟩ := hseeds 0
  obtain ⟨x₂, hx₂⟩ := hseeds 1
  have hnonconstant : Sudoku.NonconstantColumns w := by
    constructor
    · intro i
      refine ⟨Compiler.lineValue i x₁, Compiler.lineValue i x₂, ?_⟩
      intro h
      have he := congrArg (fun z : (ZMod Sudoku.p)ˣ => z.val) h
      rw [(hx₁ i).1, (hx₂ i).1] at he
      exact (by decide : (1 : ZMod Sudoku.p) ≠ 2) he
    · intro i
      refine ⟨Compiler.lineValue i x₁, Compiler.lineValue i x₂, ?_⟩
      intro h
      have he := congrArg (fun z : (ZMod Sudoku.q)ˣ => z.val) h
      rw [(hx₁ i).2, (hx₂ i).2] at he
      exact (by decide : (1 : ZMod Sudoku.q) ≠ 2) he
  exact (wang_plane_iff_quadrant T).mpr (Sudoku.soundness T w hrule' hnonconstant)

theorem exists_solution_of_wang {T : LeanWang.TileSet} {m : ℕ} (code : Code T m)
    (E : EncodingParameters (system code))
    (hT : LeanWang.TilesPlane T) : ∃ A : Set (Ambient E), Solves E A := by
  obtain ⟨τ, hτ⟩ := (wang_plane_iff_quadrant T).mp hT
  let W₀ := Sudoku.canonical τ
  let W : WordArray (system code) := fun n y =>
    code.word (W₀ (finProdFinEquiv.symm n : Sudoku.Column × Fin m).1 y)
      (finProdFinEquiv.symm n : Sudoku.Column × Fin m).2
  have hW (i : Sudoku.Column) (b : Fin m) (m : ℤ) :
      W (flat i b) m = code.word (W₀ i m) b := by
    simp only [W, flat, Equiv.symm_apply_apply]
    rfl
  have hrule : LineRule (system code) W := by
    intro x
    change ∃ w : Sudoku.Column → Sudoku.Symbol T, Sudoku.Allowed T w ∧
      ∀ i b, W (flat i b) (lineValue (system code) (flat i b) x) = code.word (w i) b
    refine ⟨fun i => W₀ i (Compiler.lineValue i x), ?_, ?_⟩
    · have h := Sudoku.canonical_lineRule τ hτ (τ (0, 0)) x.1 x.2
      simpa only [W₀, Compiler.lineValue, mul_comm, add_comm] using h
    · intro i b
      rw [lineValue_flat, hW]
  have hseedW : ∀ t n x, SharedSeed.residue (system code) x ∈
      seedActiveRegion (system code) t →
      SeedSet (system code) t (W n (lineValue (system code) n x)) := by
    intro t n x hx
    obtain ⟨⟨i, b⟩, rfl⟩ := finProdFinEquiv.surjective n
    change SeedSet (system code) t (W (flat i b) (lineValue (system code) (flat i b) x))
    rw [lineValue_flat, hW]
    change Compiler.SharedSeed.residue T x ∈ Compiler.seedActiveRegion T t at hx
    exact (seed_symbolBit code t _).mpr (Compiler.canonical_seed_regions τ t i x hx) b
  exact ⟨CommonModel.commonGraph E W, CommonModel.common_solution E W hrule hseedW⟩

theorem finite_system_iff_wang {T : LeanWang.TileSet} {m : ℕ} (code : Code T m)
    (E : EncodingParameters (system code)) :
    LeanWang.TilesPlane T ↔ ∃ A : Set (Ambient E), Solves E A := by
  refine ⟨exists_solution_of_wang code E, ?_⟩
  rintro ⟨A, hA⟩
  obtain ⟨W, hw, hs⟩ := array_of_solves E hA
  exact wang_of_array code W hw hs

end
end TranslationTiling.FiniteCompiler.TaggedSystem
