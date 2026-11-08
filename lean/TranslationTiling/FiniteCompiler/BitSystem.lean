import TranslationTiling.FiniteCompiler.CommonSolution
import TranslationTiling.FiniteCompiler.Soundness
import TranslationTiling.Compiler.BitChannels
import TranslationTiling.Compiler.Completeness
import Mathlib.Logic.Equiv.Fin.Basic

set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

namespace TranslationTiling.FiniteCompiler.BitSystem

open scoped Classical
noncomputable section

abbrev Gamma := (ZMod Sudoku.p)ˣ × ((ZMod Sudoku.q)ˣ × Bool)
noncomputable instance (priority := 2000) gammaFintype : Fintype Gamma := Fintype.ofFinite _
def alphabet : ℕ := Classical.choose (show ∃ n : ℕ, n = Fintype.card Gamma from ⟨_, rfl⟩)
theorem alphabet_eq : alphabet = Fintype.card Gamma :=
  Classical.choose_spec (show ∃ n : ℕ, n = Fintype.card Gamma from ⟨_, rfl⟩)
def gammaEquiv : Gamma ≃ Fin alphabet := (Fintype.equivFin Gamma).trans (finCongr alphabet_eq.symm)

variable {T : LeanWang.TileSet} {l : ℕ}

def flat (i : Sudoku.Column) (b : Fin l) : Fin (Sudoku.Width * l) := finProdFinEquiv (i, b)

def symbolBit (code : LeanWang.TileIn T → Fin l → Bool) (s : Sudoku.Symbol T)
    (b : Fin l) : Fin alphabet := gammaEquiv (s.1, s.2.1, code s.2.2 b)

theorem symbolBit_injective (code : LeanWang.TileIn T → Fin l → Bool)
    (hc : Function.Injective code) (hl : 0 < l) : Function.Injective (symbolBit code) := by
  intro s t h
  let b : Fin l := ⟨0, hl⟩
  have h₀ := gammaEquiv.injective (congrFun h b)
  refine Prod.ext (congrArg (fun z : Gamma => z.1) h₀)
    (Prod.ext (congrArg (fun z : Gamma => z.2.1) h₀) ?_)
  apply hc
  funext j
  exact congrArg (fun z : Gamma => z.2.2) (gammaEquiv.injective (congrFun h j))

def system (code : LeanWang.TileIn T → Fin l → Bool) (hl : 0 < l) : System where
  width := Sudoku.Width * l
  width_pos := Nat.mul_pos (by decide) hl
  alphabet := alphabet
  slope n := ((finProdFinEquiv.symm n : Sudoku.Column × Fin l).1.val : ℤ)
  allowed v := ∃ w : Sudoku.Column → Sudoku.Symbol T, Sudoku.Allowed T w ∧
    ∀ i b, v (flat i b) = symbolBit code (w i) b
  seed t j := (gammaEquiv.symm j).1.val = (t.val + 1 : ℕ) ∧
    (gammaEquiv.symm j).2.1.val = (t.val + 1 : ℕ)

@[simp] theorem lineValue_flat (code : LeanWang.TileIn T → Fin l → Bool)
    (hl : 0 < l) (i : Sudoku.Column) (b : Fin l) (x : Plane) :
    lineValue (system code hl) (flat i b) x = Compiler.lineValue i x := by
  simp [lineValue, system, flat, Compiler.lineValue]

@[simp] theorem seed_symbolBit (code : LeanWang.TileIn T → Fin l → Bool)
    (hl : 0 < l) (t : Fin 2) (s : Sudoku.Symbol T) (b : Fin l) :
    SeedSet (system code hl) t (symbolBit code s b) ↔ Compiler.SeedSet t s := by
  simp [SeedSet, system, symbolBit, Compiler.SeedSet]

theorem slope_bound (code : LeanWang.TileIn T → Fin l → Bool) (hl : 0 < l)
    (n : Column (system code hl)) : ((system code hl).slope n).natAbs ≤ Sudoku.Width := by
  change (((finProdFinEquiv.symm n : Sudoku.Column × Fin l).1.val : ℤ)).natAbs ≤ _
  rw [Int.natAbs_natCast]
  exact (finProdFinEquiv.symm n : Sudoku.Column × Fin l).1.isLt.le

theorem wang_of_array (code : LeanWang.TileIn T → Fin l → Bool)
    (hc : Function.Injective code) (hl : 0 < l)
    (W : WordArray (system code hl)) (hrule : LineRule (system code hl) W)
    (hseed : ∀ t : Fin 2, ∃ x : Plane, ∀ n,
      SeedSet (system code hl) t (W n (lineValue (system code hl) n x))) :
    LeanWang.TilesPlane T := by
  let v : Sudoku.Column × Fin l → ℤ → Fin alphabet := fun j m => W (flat j.1 j.2) m
  have hv : ∀ x : Plane, Compiler.BitChannels.EncodedAllowed (symbolBit code)
      {w | Sudoku.Allowed T w} (fun j => v j (Compiler.lineValue j.1 x)) := by
    intro x
    obtain ⟨w, hw, hbits⟩ := hrule x
    refine ⟨w, hw, ?_⟩
    funext j
    rcases j with ⟨i, b⟩
    simpa only [Compiler.BitChannels.encodeWord, v, lineValue_flat] using (hbits i b).symm
  obtain ⟨w, hbits, hw⟩ := Compiler.BitChannels.array_of_encoded_line_rule
    (symbolBit code) (symbolBit_injective code hc hl) {w | Sudoku.Allowed T w}
    Compiler.lineValue (fun m => (0, m)) (by intro i m; simp [Compiler.lineValue]) v hv
  have hseeds : ∀ t : Fin 2, ∃ x : Plane, ∀ i,
      Compiler.SeedSet t (w i (Compiler.lineValue i x)) := by
    intro t
    obtain ⟨x, hx⟩ := hseed t
    refine ⟨x, fun i => ?_⟩
    let b : Fin l := ⟨0, hl⟩
    apply (seed_symbolBit code hl t _ b).mp
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

theorem exists_solution_of_wang (code : LeanWang.TileIn T → Fin l → Bool)
    (hl : 0 < l) (E : EncodingParameters (system code hl))
    (hT : LeanWang.TilesPlane T) : ∃ A : Set (Ambient E), Solves E A := by
  obtain ⟨τ, hτ⟩ := (wang_plane_iff_quadrant T).mp hT
  let W₀ := Sudoku.canonical τ
  let W : WordArray (system code hl) := fun n m =>
    symbolBit code (W₀ (finProdFinEquiv.symm n : Sudoku.Column × Fin l).1 m)
      (finProdFinEquiv.symm n : Sudoku.Column × Fin l).2
  have hW (i : Sudoku.Column) (b : Fin l) (m : ℤ) :
      W (flat i b) m = symbolBit code (W₀ i m) b := by
    simp only [W, flat, Equiv.symm_apply_apply]
    rfl
  have hrule : LineRule (system code hl) W := by
    intro x
    change ∃ w : Sudoku.Column → Sudoku.Symbol T, Sudoku.Allowed T w ∧
      ∀ i b, W (flat i b) (lineValue (system code hl) (flat i b) x) = symbolBit code (w i) b
    refine ⟨fun i => W₀ i (Compiler.lineValue i x), ?_, ?_⟩
    · have h := Sudoku.canonical_lineRule τ hτ (τ (0, 0)) x.1 x.2
      simpa only [W₀, Compiler.lineValue, mul_comm, add_comm] using h
    · intro i b
      rw [lineValue_flat, hW]
  have hseedW : ∀ t n x, SharedSeed.residue (system code hl) x ∈
      seedActiveRegion (system code hl) t →
      SeedSet (system code hl) t (W n (lineValue (system code hl) n x)) := by
    intro t n x hx
    obtain ⟨⟨i, b⟩, rfl⟩ := finProdFinEquiv.surjective n
    change SeedSet (system code hl) t (W (flat i b) (lineValue (system code hl) (flat i b) x))
    rw [lineValue_flat, hW, seed_symbolBit]
    change Compiler.SharedSeed.residue T x ∈ Compiler.seedActiveRegion T t at hx
    exact Compiler.canonical_seed_regions τ t i x hx
  exact ⟨CommonModel.commonGraph E W, CommonModel.common_solution E W hrule hseedW⟩

theorem finite_system_iff_wang (code : LeanWang.TileIn T → Fin l → Bool)
    (hc : Function.Injective code) (hl : 0 < l) (E : EncodingParameters (system code hl)) :
    LeanWang.TilesPlane T ↔ ∃ A : Set (Ambient E), Solves E A := by
  refine ⟨exists_solution_of_wang code hl E, ?_⟩
  rintro ⟨A, hA⟩
  obtain ⟨W, hw, hs⟩ := array_of_solves E hA
  exact wang_of_array code hc hl W hw hs

end
end TranslationTiling.FiniteCompiler.BitSystem
