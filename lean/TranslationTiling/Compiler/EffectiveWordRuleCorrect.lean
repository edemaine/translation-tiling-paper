import TranslationTiling.Compiler.EffectiveWordRule

namespace TranslationTiling.Compiler.Effective

def extendRectangle {T : LeanWang.TileSet} {s t : ℕ}
    (σ : Fin (s + 1) → Fin (t + 1) → LeanWang.TileIn T) : RawRectangle :=
  fun u v => (σ ⟨min u.val s, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩
    ⟨min v.val t, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩).val

theorem extendRectangle_mem {T : LeanWang.TileSet} {s t : ℕ}
    (σ : Fin (s + 1) → Fin (t + 1) → LeanWang.TileIn T) :
    extendRectangle σ ∈ rectangles T :=
  (mem_rectangles _ _).mpr (fun _ _ => (σ _ _).property)

def restrictRectangle {T : LeanWang.TileSet} {s t : ℕ} (hs : s ≤ 1) (ht : t ≤ 1)
    (σ : RawRectangle) (hσ : ∀ u v, σ u v ∈ T) :
    Fin (s + 1) → Fin (t + 1) → LeanWang.TileIn T :=
  fun u v => ⟨σ ⟨u.val, by omega⟩ ⟨v.val, by omega⟩, hσ _ _⟩

theorem restrict_extend {T : LeanWang.TileSet} {s t : ℕ} (hs : s ≤ 1) (ht : t ≤ 1)
    (σ : Fin (s + 1) → Fin (t + 1) → LeanWang.TileIn T) :
    restrictRectangle hs ht (extendRectangle σ)
      ((mem_rectangles _ _).mp (extendRectangle_mem σ)) = σ := by
  funext u v
  apply Subtype.ext
  simp only [restrictRectangle, extendRectangle]
  have hu : min u.val s = u.val := Nat.min_eq_left (Nat.le_of_lt_succ u.isLt)
  have hv : min v.val t = v.val := Nat.min_eq_left (Nat.le_of_lt_succ v.isLt)
  congr 2 <;> exact Fin.ext (by assumption)

theorem rectangleTest_iff {T : LeanWang.TileSet} {s t : ℕ}
    (hs : s ≤ 1) (ht : t ≤ 1) (σ : RawRectangle) (hσ : ∀ u v, σ u v ∈ T) :
    RectangleTest s t σ ↔ Sudoku.ValidRectangle T (s + 1) (t + 1)
      (restrictRectangle hs ht σ hσ) := by
  unfold RectangleTest Sudoku.ValidRectangle
  constructor
  · rintro ⟨hh, hv⟩
    constructor
    · intro u v hu
      have hs1 : s = 1 := by omega
      have hu0 : u.val = 0 := by omega
      have hv' : v.val < 2 := by omega
      have h := hh.resolve_left (fun h => h hs1)
      have he := (h ⟨v.val, hv'⟩).resolve_left (by change ¬ v.val > t; have := v.isLt; omega)
      simpa [restrictRectangle, rectangleAt, indexed, LeanWang.WangTile.HMatches,
        hu0, zero_add] using he
    · intro u v hv'
      have ht1 : t = 1 := by omega
      have hv0 : v.val = 0 := by omega
      have hu' : u.val < 2 := by omega
      have h := hv.resolve_left (fun h => h ht1)
      have he := (h ⟨u.val, hu'⟩).resolve_left (by change ¬ u.val > s; have := u.isLt; omega)
      simpa [restrictRectangle, rectangleAt, indexed, LeanWang.WangTile.VMatches,
        hv0, zero_add] using he
  · rintro ⟨hh, hv⟩
    constructor
    · by_cases hs1 : s = 1
      · right
        intro v
        by_cases hvt : v.val > t
        · exact Or.inl hvt
        · right
          have hv' : v.val < t + 1 := by omega
          have hu0 : 0 < s + 1 := by omega
          have hu1 : 0 + 1 < s + 1 := by omega
          have he := hh ⟨0, hu0⟩ ⟨v.val, hv'⟩ hu1
          simpa [restrictRectangle, rectangleAt, indexed, LeanWang.WangTile.HMatches,
            zero_add] using he
      · exact Or.inl hs1
    · by_cases ht1 : t = 1
      · right
        intro u
        by_cases hus : u.val > s
        · exact Or.inl hus
        · right
          have hu' : u.val < s + 1 := by omega
          have hv0 : 0 < t + 1 := by omega
          have hv1 : 0 + 1 < t + 1 := by omega
          have he := hv ⟨u.val, hu'⟩ ⟨0, hv0⟩ hv1
          simpa [restrictRectangle, rectangleAt, indexed, LeanWang.WangTile.VMatches,
            zero_add] using he
      · exact Or.inl ht1

theorem thresholdNat_le_one (r a : ℕ) : thresholdNat r a ≤ 1 := by
  unfold thresholdNat
  split <;> omega

private theorem finiteDigitTest_iff (r s a b n : ℕ) [NeZero r] (hs : s ≤ 1)
    (v : ZMod r) :
    (∀ u : Fin 2, valuationNat r (a * n + b) ≠ some u.val ∨ u.val > s ∨
      v.val = digitNat r (a * n + b)) ↔
    ∀ u : Fin (s + 1), Sudoku.lowValuation r ((a : ℤ) * n + b) = some u.val →
      v = Sudoku.lowDigit r ((a : ℤ) * n + b) := by
  have hval : valuationNat r (a * n + b) = Sudoku.lowValuation r ((a : ℤ) * n + b) := by
    simpa only [Nat.cast_add, Nat.cast_mul] using valuationNat_eq r (a * n + b)
  have hdig : digitNat r (a * n + b) = (Sudoku.lowDigit r ((a : ℤ) * n + b)).val := by
    simpa only [Nat.cast_add, Nat.cast_mul] using digitNat_eq r (a * n + b)
  constructor
  · intro h u hu
    have huf : u.val < 2 := by omega
    have he := ((h ⟨u.val, huf⟩).resolve_left
      (by rw [hval]; exact fun h => h hu)).resolve_left
      (by change ¬ u.val > s; have := u.isLt; omega)
    exact ZMod.val_injective r (he.trans hdig)
  · intro h u
    by_cases hv : valuationNat r (a * n + b) = some u.val
    · by_cases hu : u.val ≤ s
      · right; right
        have he := congrArg ZMod.val (h ⟨u.val, by omega⟩ (hval ▸ hv))
        exact he.trans hdig.symm
      · exact Or.inr (Or.inl (by omega))
    · exact Or.inl hv

private theorem finiteDecorationTest_iff {T : LeanWang.TileSet} (s t a b n : ℕ)
    (hs : s ≤ 1) (ht : t ≤ 1) (σ : RawRectangle) (hσ : ∀ u v, σ u v ∈ T)
    (f : LeanWang.TileIn T) :
    (∀ u v : Fin 2, valuationNat Sudoku.p (a * n + b) ≠ some u.val ∨
      valuationNat Sudoku.q (a * n + b) ≠ some v.val ∨ u.val > s ∨ v.val > t ∨
        f.val = rectangleAt σ u v) ↔
    ∀ (u : Fin (s + 1)) (v : Fin (t + 1)),
      Sudoku.lowValuation Sudoku.p ((a : ℤ) * n + b) = some u.val →
      Sudoku.lowValuation Sudoku.q ((a : ℤ) * n + b) = some v.val →
        f = restrictRectangle hs ht σ hσ u v := by
  have hp : valuationNat Sudoku.p (a * n + b) =
      Sudoku.lowValuation Sudoku.p ((a : ℤ) * n + b) := by
    simpa only [Nat.cast_add, Nat.cast_mul] using valuationNat_eq Sudoku.p (a * n + b)
  have hq : valuationNat Sudoku.q (a * n + b) =
      Sudoku.lowValuation Sudoku.q ((a : ℤ) * n + b) := by
    simpa only [Nat.cast_add, Nat.cast_mul] using valuationNat_eq Sudoku.q (a * n + b)
  constructor
  · intro h u v hu hv
    have hu2 : u.val < 2 := by omega
    have hv2 : v.val < 2 := by omega
    have he := ((((h ⟨u.val, hu2⟩ ⟨v.val, hv2⟩).resolve_left
      (by rw [hp]; exact fun h => h hu)).resolve_left
      (by rw [hq]; exact fun h => h hv)).resolve_left
      (by change ¬ u.val > s; have := u.isLt; omega)).resolve_left
      (by change ¬ v.val > t; have := v.isLt; omega)
    exact Subtype.ext he
  · intro h u v
    by_cases huval : valuationNat Sudoku.p (a * n + b) = some u.val
    · right
      by_cases hvval : valuationNat Sudoku.q (a * n + b) = some v.val
      · right
        by_cases hu : u.val ≤ s
        · right
          by_cases hv : v.val ≤ t
          · right
            have he := congrArg Subtype.val
              (h ⟨u.val, by omega⟩ ⟨v.val, by omega⟩ (hp ▸ huval) (hq ▸ hvval))
            simpa only [restrictRectangle, rectangleAt, indexed] using he
          · exact Or.inl (by omega)
        · exact Or.inl (by omega)
      · exact Or.inl hvval
    · exact Or.inl huval

theorem columnTest_iff {T : LeanWang.TileSet} (w : Sudoku.Column → Sudoku.Symbol T)
    (σ : RawRectangle) (hσ : ∀ u v, σ u v ∈ T) (a b : ℕ) (n : Sudoku.Column) :
    ColumnTest (rawWord w) σ a b n ↔
    (∀ u : Fin (thresholdNat Sudoku.p a + 1),
      Sudoku.lowValuation Sudoku.p ((a : ℤ) * n.val + b) = some u.val →
        (w n).1.val = Sudoku.lowDigit Sudoku.p ((a : ℤ) * n.val + b)) ∧
    (∀ v : Fin (thresholdNat Sudoku.q a + 1),
      Sudoku.lowValuation Sudoku.q ((a : ℤ) * n.val + b) = some v.val →
        (w n).2.1.val = Sudoku.lowDigit Sudoku.q ((a : ℤ) * n.val + b)) ∧
    (∀ (u : Fin (thresholdNat Sudoku.p a + 1)) (v : Fin (thresholdNat Sudoku.q a + 1)),
      Sudoku.lowValuation Sudoku.p ((a : ℤ) * n.val + b) = some u.val →
      Sudoku.lowValuation Sudoku.q ((a : ℤ) * n.val + b) = some v.val →
        (w n).2.2 = restrictRectangle (thresholdNat_le_one Sudoku.p a)
          (thresholdNat_le_one Sudoku.q a) σ hσ u v) := by
  dsimp only [ColumnTest, indexed, rawWord, rawSymbol]
  exact (finiteDigitTest_iff Sudoku.p _ a b n.val (thresholdNat_le_one _ _) (w n).1.val).and
    ((finiteDigitTest_iff Sudoku.q _ a b n.val (thresholdNat_le_one _ _) (w n).2.1.val).and
      (finiteDecorationTest_iff _ _ a b n.val (thresholdNat_le_one _ _)
        (thresholdNat_le_one _ _) σ hσ (w n).2.2))

theorem coefficientTest_iff {T : LeanWang.TileSet} (w : Sudoku.Column → Sudoku.Symbol T)
    (a b : ℕ) : CoefficientTest T (rawWord w) a b ↔
      Sudoku.AllowedCoefficients T w (a : ℤ) (b : ℤ) := by
  rw [Sudoku.allowedCoefficients_iff_finite]
  unfold CoefficientTest Sudoku.FiniteCoefficients
  rw [← thresholdNat_eq Sudoku.p a, ← thresholdNat_eq Sudoku.q a]
  simp only [Int.natCast_dvd_natCast, Nat.dvd_iff_mod_eq_zero]
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  constructor
  · rintro ⟨σ, hσ, hr, hn⟩
    let hmem := (mem_rectangles T σ).mp hσ
    refine ⟨restrictRectangle (thresholdNat_le_one _ _) (thresholdNat_le_one _ _) σ hmem,
      (rectangleTest_iff _ _ σ hmem).mp hr, ?_⟩
    intro n
    exact (columnTest_iff w σ hmem a b n).mp (hn n)
  · rintro ⟨σ, hr, hn⟩
    let τ := extendRectangle σ
    have hτ : τ ∈ rectangles T := extendRectangle_mem σ
    let hmem := (mem_rectangles T τ).mp hτ
    have he : restrictRectangle (thresholdNat_le_one _ _) (thresholdNat_le_one _ _) τ hmem = σ :=
      restrict_extend _ _ σ
    refine ⟨τ, hτ, (rectangleTest_iff _ _ τ hmem).mpr (he.symm ▸ hr), ?_⟩
    intro n
    apply (columnTest_iff w τ hmem a b n).mpr
    rw [he]
    exact hn n

/-- The uniform numerical checker is exactly the paper's decorated word rule. -/
theorem wordTest_iff {T : LeanWang.TileSet} (w : Sudoku.Column → Sudoku.Symbol T) :
    WordTest T (rawWord w) ↔ Sudoku.Allowed T w := by
  rw [Sudoku.allowed_iff_bounded]
  unfold WordTest
  constructor
  · rintro ⟨a, ha, b, hb, htest⟩
    exact ⟨⟨a, List.mem_range.mp ha⟩, ⟨b, List.mem_range.mp hb⟩,
      (coefficientTest_iff w a b).mp htest⟩
  · rintro ⟨a, b, htest⟩
    exact ⟨a.val, List.mem_range.mpr a.isLt, b.val, List.mem_range.mpr b.isLt,
      (coefficientTest_iff w a.val b.val).mpr htest⟩

end TranslationTiling.Compiler.Effective
