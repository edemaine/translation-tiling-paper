import TranslationTiling.Compiler.EffectiveArithmetic
import TranslationTiling.Proofs.FiniteWordRule

set_option maxRecDepth 1000

namespace TranslationTiling.Compiler.Effective

attribute [fun_prop] LeanWang.WangTile.n_primrec LeanWang.WangTile.s_primrec
attribute [fun_prop] LeanWang.WangTile.e_primrec LeanWang.WangTile.w_primrec

abbrev RawSymbol := ℕ × ℕ × LeanWang.WangTile
abbrev RawWord := Sudoku.Column → RawSymbol
abbrev RawRectangle := Fin 2 → Fin 2 → LeanWang.WangTile

def rawSymbol {T : LeanWang.TileSet} (j : Sudoku.Symbol T) : RawSymbol :=
  (j.1.val.val, j.2.1.val.val, j.2.2.val)

def rawWord {T : LeanWang.TileSet} (w : Sudoku.Column → Sudoku.Symbol T) : RawWord :=
  fun n => rawSymbol (w n)

def thresholdNat (r a : ℕ) : ℕ := if a % r = 0 then 0 else 1

def valuationNat (r z : ℕ) : Option ℕ :=
  if z % r ≠ 0 then some 0 else if z % (r * r) ≠ 0 then some 1 else none

def digitNat (r z : ℕ) : ℕ := if z % r = 0 then (z / r) % r else z % r

theorem thresholdNat_eq (r a : ℕ) : thresholdNat r a = Sudoku.threshold r (a : ℤ) := by
  simp only [thresholdNat, Sudoku.threshold, Int.natCast_dvd_natCast, Nat.dvd_iff_mod_eq_zero]

theorem valuationNat_eq (r z : ℕ) : valuationNat r z = Sudoku.lowValuation r (z : ℤ) := by
  simp only [valuationNat, Sudoku.lowValuation, pow_two, ← Nat.cast_mul,
    Int.natCast_dvd_natCast, Nat.dvd_iff_mod_eq_zero]

theorem digitNat_eq (r z : ℕ) [NeZero r] : digitNat r z =
    (Sudoku.lowDigit r (z : ℤ)).val := by
  unfold digitNat Sudoku.lowDigit
  simp only [Int.natCast_dvd_natCast, Nat.dvd_iff_mod_eq_zero]
  split
  · rw [← Int.natCast_ediv, Int.cast_natCast, ZMod.val_natCast]
  · rw [Int.cast_natCast, ZMod.val_natCast]

@[fun_prop] theorem thresholdNat_rule {α : Type*} [Primcodable α] {r a : α → ℕ}
    (hr : Primrec r) (ha : Primrec a) : Primrec (fun x => thresholdNat (r x) (a x)) := by
  unfold thresholdNat
  fun_prop

@[fun_prop] theorem valuationNat_rule {α : Type*} [Primcodable α] {r z : α → ℕ}
    (hr : Primrec r) (hz : Primrec z) : Primrec (fun x => valuationNat (r x) (z x)) := by
  unfold valuationNat
  fun_prop

@[fun_prop] theorem digitNat_rule {α : Type*} [Primcodable α] {r z : α → ℕ}
    (hr : Primrec r) (hz : Primrec z) : Primrec (fun x => digitNat (r x) (z x)) := by
  unfold digitNat
  fun_prop

/-- Enumerate all four decorations; unused cells may repeat a decoration. -/
def rectangles (T : LeanWang.TileSet) : List RawRectangle :=
  T.flatMap fun a => T.flatMap fun b => T.flatMap fun c =>
    T.map fun d => ![![a, b], ![c, d]]

@[fun_prop] theorem rectangles_primrec : Primrec rectangles := by unfold rectangles; fun_prop

theorem mem_rectangles (T : LeanWang.TileSet) (σ : RawRectangle) :
    σ ∈ rectangles T ↔ ∀ u v, σ u v ∈ T := by
  constructor
  · intro h
    obtain ⟨a, ha, b, hb, c, hc, d, hd, he⟩ :=
      (by simpa only [rectangles, List.mem_flatMap, List.mem_map] using h :
        ∃ a ∈ T, ∃ b ∈ T, ∃ c ∈ T, ∃ d ∈ T, ![![a, b], ![c, d]] = σ)
    subst σ
    intro u v
    fin_cases u <;> fin_cases v <;> simpa using (by assumption)
  · intro h
    simp only [rectangles, List.mem_flatMap, List.mem_map]
    refine ⟨σ 0 0, h 0 0, σ 0 1, h 0 1, σ 1 0, h 1 0, σ 1 1, h 1 1, ?_⟩
    funext u v
    fin_cases u <;> fin_cases v <;> rfl

def rectangleAt (σ : RawRectangle) (u v : Fin 2) : LeanWang.WangTile :=
  indexed (indexed σ u) v

@[fun_prop] theorem rectangleAt_rule {α : Type*} [Primcodable α]
    {σ : α → RawRectangle} {u v : α → Fin 2}
    (hσ : Primrec σ) (hu : Primrec u) (hv : Primrec v) :
    Primrec (fun a => rectangleAt (σ a) (u a) (v a)) := by unfold rectangleAt; fun_prop

def RectangleTest (s t : ℕ) (σ : RawRectangle) : Prop :=
  (s ≠ 1 ∨ ∀ v : Fin 2, v.val > t ∨
    (rectangleAt σ 0 v).e = (rectangleAt σ 1 v).w) ∧
  (t ≠ 1 ∨ ∀ u : Fin 2, u.val > s ∨
    (rectangleAt σ u 0).n = (rectangleAt σ u 1).s)

instance (s t : ℕ) (σ : RawRectangle) : Decidable (RectangleTest s t σ) := by
  unfold RectangleTest
  infer_instance

@[fun_prop] theorem rectangleTest_rule {α : Type*} [Primcodable α]
    {s t : α → ℕ} {σ : α → RawRectangle}
    (hs : Primrec s) (ht : Primrec t) (hσ : Primrec σ) :
    PrimrecPred (fun a => RectangleTest (s a) (t a) (σ a)) := by unfold RectangleTest; fun_prop

def ColumnTest (w : RawWord) (σ : RawRectangle) (a b : ℕ) (n : Sudoku.Column) : Prop :=
  let z := a * n.val + b
  let s := thresholdNat Sudoku.p a
  let t := thresholdNat Sudoku.q a
  (∀ u : Fin 2, valuationNat Sudoku.p z ≠ some u.val ∨ u.val > s ∨
    (indexed w n).1 = digitNat Sudoku.p z) ∧
  (∀ v : Fin 2, valuationNat Sudoku.q z ≠ some v.val ∨ v.val > t ∨
    (indexed w n).2.1 = digitNat Sudoku.q z) ∧
  (∀ u v : Fin 2, valuationNat Sudoku.p z ≠ some u.val ∨
    valuationNat Sudoku.q z ≠ some v.val ∨ u.val > s ∨ v.val > t ∨
    (indexed w n).2.2 = rectangleAt σ u v)

instance (w : RawWord) (σ : RawRectangle) (a b : ℕ) (n : Sudoku.Column) :
    Decidable (ColumnTest w σ a b n) := by unfold ColumnTest; infer_instance

@[fun_prop] theorem columnTest_rule {α : Type*} [Primcodable α]
    {w : α → RawWord} {σ : α → RawRectangle} {a b : α → ℕ} {n : α → Sudoku.Column}
    (hw : Primrec w) (hσ : Primrec σ) (ha : Primrec a) (hb : Primrec b) (hn : Primrec n) :
    PrimrecPred (fun x => ColumnTest (w x) (σ x) (a x) (b x) (n x)) := by
  dsimp only [ColumnTest]
  fun_prop

def CoefficientTest (T : LeanWang.TileSet) (w : RawWord) (a b : ℕ) : Prop :=
  (a % Sudoku.p ≠ 0 ∨ b % Sudoku.p ≠ 0) ∧
  (a % Sudoku.q ≠ 0 ∨ b % Sudoku.q ≠ 0) ∧
  ∃ σ ∈ rectangles T,
    RectangleTest (thresholdNat Sudoku.p a) (thresholdNat Sudoku.q a) σ ∧
      ∀ n, ColumnTest w σ a b n

instance (T : LeanWang.TileSet) (w : RawWord) (a b : ℕ) :
    Decidable (CoefficientTest T w a b) := by unfold CoefficientTest; infer_instance

@[fun_prop] theorem coefficientTest_rule {α : Type*} [Primcodable α]
    {T : α → LeanWang.TileSet} {w : α → RawWord} {a b : α → ℕ}
    (hT : Primrec T) (hw : Primrec w) (ha : Primrec a) (hb : Primrec b) :
    PrimrecPred (fun x => CoefficientTest (T x) (w x) (a x) (b x)) := by
  unfold CoefficientTest
  fun_prop

def WordTest (T : LeanWang.TileSet) (w : RawWord) : Prop :=
  ∃ a ∈ List.range Sudoku.Width, ∃ b ∈ List.range Sudoku.Width, CoefficientTest T w a b

instance (T : LeanWang.TileSet) (w : RawWord) : Decidable (WordTest T w) := by
  unfold WordTest
  infer_instance

/-- The entire decorated word-rule search has a uniform primitive-recursive checker. -/
theorem wordTest_primrec : PrimrecPred (fun z : LeanWang.TileSet × RawWord => WordTest z.1 z.2) := by
  unfold WordTest
  fun_prop

end TranslationTiling.Compiler.Effective
