import TranslationTiling.FiniteCompiler.BitSystem

/-! Encode both arithmetic decorations and tile labels over three symbols.
The prefix preserves the two seed predicates without a position-dependent seed. -/

namespace TranslationTiling.FiniteCompiler.TernarySystem
open scoped Classical
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def seedTag (t : Fin 2) : Fin 3 := ⟨t.val, by omega⟩

/-- Classes zero and one are the two arithmetic seed classes. -/
def tag {T : LeanWang.TileSet} (s : Sudoku.Symbol T) : Fin 3 :=
  if Compiler.SeedSet 0 s then 0 else if Compiler.SeedSet 1 s then 1 else 2

theorem seed_disjoint {T : LeanWang.TileSet} (s : Sudoku.Symbol T) :
    ¬ (Compiler.SeedSet 0 s ∧ Compiler.SeedSet 1 s) := by
  rintro ⟨h0,h1⟩
  have h := h0.1.symm.trans h1.1
  exact (by decide : (1 : ZMod Sudoku.p) ≠ 2) h

theorem tag_seed {T : LeanWang.TileSet} (t : Fin 2) (s : Sudoku.Symbol T) :
    tag s = seedTag t ↔ Compiler.SeedSet t s := by
  have hd := seed_disjoint s
  fin_cases t <;> simp only [tag, Fin.val_zero, Fin.val_one, seedTag]
  all_goals split_ifs <;> simp_all

/-- Prefixes are 00, 11, and 01. Payload ones become 2; payload zeros
become 1 in class one and 0 otherwise. -/
def encode {m : ℕ} (c : Fin 3) (bits : Fin m → Bool) (k : Fin (m + 2)) : Fin 3 :=
  if h : k.val < 2 then
    if c = 2 then ⟨k.val, by omega⟩ else c
  else if bits ⟨k.val - 2, by omega⟩ then 2 else if c = 1 then 1 else 0

@[simp] theorem encode_payload {m : ℕ} (c : Fin 3) (bits : Fin m → Bool) (j : Fin m) :
    encode c bits ⟨j.val + 2, by omega⟩ = 2 ↔ bits j = true := by
  simp only [encode, show ¬ j.val + 2 < 2 by omega, ↓reduceDIte,
    Nat.add_sub_cancel, Fin.eta]
  cases bits j <;> fin_cases c <;> decide

theorem encode_seed {m : ℕ} (c : Fin 3) (bits : Fin m → Bool) (t : Fin 2) :
    (∀ k, encode c bits k = seedTag t ∨ encode c bits k = 2) ↔ c = seedTag t := by
  constructor
  · intro h
    have h0 := h ⟨0, by omega⟩
    have h1 := h ⟨1, by omega⟩
    fin_cases c <;> fin_cases t <;> simp_all [encode, seedTag]
  · intro h k
    subst c
    fin_cases t <;> simp only [seedTag]
    all_goals unfold encode; split_ifs <;> simp_all


def symbolBit {T : LeanWang.TileSet} {m : ℕ}
    (code : Sudoku.Symbol T → Fin m → Bool) (s : Sudoku.Symbol T) : Fin (m + 2) → Fin 3 :=
  encode (tag s) (code s)

theorem symbolBit_injective {T : LeanWang.TileSet} {m : ℕ}
    (code : Sudoku.Symbol T → Fin m → Bool) (hc : Function.Injective code) :
    Function.Injective (symbolBit code) := by
  intro s u h
  apply hc
  funext j
  apply Bool.eq_iff_iff.mpr
  have he := congrArg (fun z => z = (2 : Fin 3)) (congrFun h ⟨j.val + 2, by omega⟩)
  exact Iff.of_eq (by simpa only [symbolBit, encode_payload] using he)

def flat {m : ℕ} (i : Sudoku.Column) (b : Fin (m + 2)) : Fin (Sudoku.Width * (m + 2)) :=
  finProdFinEquiv (i, b)

def system {T : LeanWang.TileSet} {m : ℕ} (code : Sudoku.Symbol T → Fin m → Bool) : System where
  width := Sudoku.Width * (m + 2)
  width_pos := Nat.mul_pos (by decide) (by omega)
  alphabet := 3
  slope n := ((finProdFinEquiv.symm n : Sudoku.Column × Fin (m + 2)).1.val : ℤ)
  allowed v := ∃ w : Sudoku.Column → Sudoku.Symbol T, Sudoku.Allowed T w ∧
    ∀ i b, v (flat i b) = symbolBit code (w i) b
  seed t j := j = seedTag t ∨ j = 2

@[simp] theorem lineValue_flat {T : LeanWang.TileSet} {m : ℕ}
    (code : Sudoku.Symbol T → Fin m → Bool) (i : Sudoku.Column) (b : Fin (m + 2)) (x : Plane) :
    lineValue (system code) (flat i b) x = Compiler.lineValue i x := by
  simp [lineValue, system, flat, Compiler.lineValue]

@[simp] theorem seed_symbolBit {T : LeanWang.TileSet} {m : ℕ}
    (code : Sudoku.Symbol T → Fin m → Bool) (t : Fin 2) (s : Sudoku.Symbol T) :
    (∀ b, SeedSet (system code) t (symbolBit code s b)) ↔ Compiler.SeedSet t s := by
  exact (encode_seed (tag s) (code s) t).trans (tag_seed t s)

theorem slope_bound {T : LeanWang.TileSet} {m : ℕ}
    (code : Sudoku.Symbol T → Fin m → Bool) (n : Column (system code)) :
    ((system code).slope n).natAbs ≤ Sudoku.Width := by
  change (((finProdFinEquiv.symm n : Sudoku.Column × Fin (m + 2)).1.val : ℤ)).natAbs ≤ _
  rw [Int.natAbs_natCast]
  exact (finProdFinEquiv.symm n : Sudoku.Column × Fin (m + 2)).1.isLt.le

theorem wang_of_array {T : LeanWang.TileSet} {m : ℕ} (code : Sudoku.Symbol T → Fin m → Bool)
    (hc : Function.Injective code)
    (W : WordArray (system code)) (hrule : LineRule (system code) W)
    (hseed : ∀ t : Fin 2, ∃ x : Plane, ∀ n,
      SeedSet (system code) t (W n (lineValue (system code) n x))) :
    LeanWang.TilesPlane T := by
  let v : Sudoku.Column × Fin (m + 2) → ℤ → Fin 3 := fun j m => W (flat j.1 j.2) m
  have hv : ∀ x : Plane, Compiler.BitChannels.EncodedAllowed (symbolBit code)
      {w | Sudoku.Allowed T w} (fun j => v j (Compiler.lineValue j.1 x)) := by
    intro x
    obtain ⟨w, hw, hbits⟩ := hrule x
    refine ⟨w, hw, ?_⟩
    funext j
    rcases j with ⟨i, b⟩
    simpa only [Compiler.BitChannels.encodeWord, v, lineValue_flat] using (hbits i b).symm
  obtain ⟨w, hbits, hw⟩ := Compiler.BitChannels.array_of_encoded_line_rule
    (symbolBit code) (symbolBit_injective code hc) {w | Sudoku.Allowed T w}
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

theorem exists_solution_of_wang {T : LeanWang.TileSet} {m : ℕ} (code : Sudoku.Symbol T → Fin m → Bool)
    (E : EncodingParameters (system code))
    (hT : LeanWang.TilesPlane T) : ∃ A : Set (Ambient E), Solves E A := by
  obtain ⟨τ, hτ⟩ := (wang_plane_iff_quadrant T).mp hT
  let W₀ := Sudoku.canonical τ
  let W : WordArray (system code) := fun n y =>
    symbolBit code (W₀ (finProdFinEquiv.symm n : Sudoku.Column × Fin (m + 2)).1 y)
      (finProdFinEquiv.symm n : Sudoku.Column × Fin (m + 2)).2
  have hW (i : Sudoku.Column) (b : Fin (m + 2)) (m : ℤ) :
      W (flat i b) m = symbolBit code (W₀ i m) b := by
    simp only [W, flat, Equiv.symm_apply_apply]
    rfl
  have hrule : LineRule (system code) W := by
    intro x
    change ∃ w : Sudoku.Column → Sudoku.Symbol T, Sudoku.Allowed T w ∧
      ∀ i b, W (flat i b) (lineValue (system code) (flat i b) x) = symbolBit code (w i) b
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

theorem finite_system_iff_wang {T : LeanWang.TileSet} {m : ℕ} (code : Sudoku.Symbol T → Fin m → Bool)
    (hc : Function.Injective code) (E : EncodingParameters (system code)) :
    LeanWang.TilesPlane T ↔ ∃ A : Set (Ambient E), Solves E A := by
  refine ⟨exists_solution_of_wang code E, ?_⟩
  rintro ⟨A, hA⟩
  obtain ⟨W, hw, hs⟩ := array_of_solves E hA
  exact wang_of_array code hc W hw hs

end
end TranslationTiling.FiniteCompiler.TernarySystem
