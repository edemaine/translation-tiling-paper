import TranslationTiling.Proofs.WordResidues
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.GroupWithZero.Units.Fintype

namespace TranslationTiling.Sudoku

/-- Every test in the word rule depends only on the coefficients modulo each
prime square, including the dimensions of the decorated rectangle. -/
theorem allowedCoefficients_congr {T : LeanWang.TileSet} (w : Column → Symbol T)
    {a b c d : ℤ} (haP : SqCongr p a c) (hbP : SqCongr p b d)
    (haQ : SqCongr q a c) (hbQ : SqCongr q b d) :
    AllowedCoefficients T w a b ↔ AllowedCoefficients T w c d := by
  unfold AllowedCoefficients
  rw [haP.threshold_eq, haQ.threshold_eq]
  unfold WordRectangle
  simp only [haP.dvd_iff, hbP.dvd_iff, haQ.dvd_iff, hbQ.dvd_iff,
    fun n : ℤ => (haP.affine hbP n).lowValuation_eq,
    fun n : ℤ => (haQ.affine hbQ n).lowValuation_eq,
    fun n : ℤ => (haP.affine hbP n).lowDigit_eq (by decide),
    fun n : ℤ => (haQ.affine hbQ n).lowDigit_eq (by decide)]

/-- Nonnegative representatives of the coefficients suffice. -/
theorem exists_bounded_coefficient (a : ℤ) :
    ∃ c : Column, SqCongr p a c.val ∧ SqCongr q a c.val := by
  have hm : (0 : ℤ) < Width := by decide
  have hnonneg := Int.emod_nonneg a (ne_of_gt hm)
  have hlt := Int.emod_lt_of_pos a hm
  let c : Column := ⟨(a % Width).toNat, by omega⟩
  have hc : (c.val : ℤ) = a % Width := Int.toNat_of_nonneg hnonneg
  have hmod : (Width : ℤ) ∣ a - c.val := by
    rw [hc]
    refine ⟨a / Width, ?_⟩
    have h := Int.emod_add_ediv_mul a (Width : ℤ)
    linarith
  refine ⟨c, ?_, ?_⟩
  · exact (show (p : ℤ) ^ 2 ∣ (Width : ℤ) from ⟨(q : ℤ) ^ 2, by decide⟩).trans hmod
  · exact (show (q : ℤ) ^ 2 ∣ (Width : ℤ) from ⟨(p : ℤ) ^ 2, by decide⟩).trans hmod

/-- The unbounded integer-coefficient rule is equivalent to a finite search. -/
theorem allowed_iff_bounded (T : LeanWang.TileSet) (w : Column → Symbol T) :
    Allowed T w ↔ ∃ a b : Column, AllowedCoefficients T w a.val b.val := by
  constructor
  · rintro ⟨a, b, hab⟩
    obtain ⟨c, hcP, hcQ⟩ := exists_bounded_coefficient a
    obtain ⟨d, hdP, hdQ⟩ := exists_bounded_coefficient b
    exact ⟨c, d, (allowedCoefficients_congr w hcP hdP hcQ hdQ).mp hab⟩
  · rintro ⟨a, b, hab⟩
    exact ⟨a.val, b.val, hab⟩

/-- Enumerate the finite tileset directly, without a choice-based instance. -/
instance tileInFintype (T : LeanWang.TileSet) : Fintype (LeanWang.TileIn T) :=
  Fintype.ofFinset T.toFinset (by intro t; exact List.mem_toFinset)

instance validRectangleDecidable (T : LeanWang.TileSet) (w h : ℕ)
    (σ : Fin w → Fin h → LeanWang.TileIn T) : Decidable (ValidRectangle T w h σ) := by
  unfold ValidRectangle
  infer_instance

/-- The same coefficient tests, with every quantifier over a finite type. -/
def FiniteCoefficients (T : LeanWang.TileSet) (w : Column → Symbol T) (a b : ℤ) : Prop :=
  (¬ (p : ℤ) ∣ a ∨ ¬ (p : ℤ) ∣ b) ∧
  (¬ (q : ℤ) ∣ a ∨ ¬ (q : ℤ) ∣ b) ∧
  ∃ σ : Fin (threshold p a + 1) → Fin (threshold q a + 1) → LeanWang.TileIn T,
    ValidRectangle T _ _ σ ∧ ∀ n,
      (∀ u : Fin (threshold p a + 1), lowValuation p (a * n.val + b) = some u.val →
        (w n).1.val = lowDigit p (a * n.val + b)) ∧
      (∀ v : Fin (threshold q a + 1), lowValuation q (a * n.val + b) = some v.val →
        (w n).2.1.val = lowDigit q (a * n.val + b)) ∧
      (∀ (u : Fin (threshold p a + 1)) (v : Fin (threshold q a + 1)),
        lowValuation p (a * n.val + b) = some u.val →
        lowValuation q (a * n.val + b) = some v.val → (w n).2.2 = σ u v)

theorem allowedCoefficients_iff_finite (T : LeanWang.TileSet) (w : Column → Symbol T)
    (a b : ℤ) : AllowedCoefficients T w a b ↔ FiniteCoefficients T w a b := by
  constructor
  · rintro ⟨hp, hq, σ, hσ, hn⟩
    refine ⟨hp, hq, σ, hσ, fun n => ⟨?_, ?_, ?_⟩⟩
    · intro u hu
      exact (hn n).1 u.val hu (Nat.lt_succ_iff.mp u.isLt)
    · intro v hv
      exact (hn n).2.1 v.val hv (Nat.lt_succ_iff.mp v.isLt)
    · intro u v hu hv
      exact (hn n).2.2 u.val v.val hu hv
        (Nat.lt_succ_iff.mp u.isLt) (Nat.lt_succ_iff.mp v.isLt)
  · rintro ⟨hp, hq, σ, hσ, hn⟩
    refine ⟨hp, hq, σ, hσ, fun n => ⟨?_, ?_, ?_⟩⟩
    · intro u hu hbound
      exact (hn n).1 ⟨u, Nat.lt_succ_iff.mpr hbound⟩ hu
    · intro v hv hbound
      exact (hn n).2.1 ⟨v, Nat.lt_succ_iff.mpr hbound⟩ hv
    · intro u v hu hv hboundU hboundV
      exact (hn n).2.2 ⟨u, Nat.lt_succ_iff.mpr hboundU⟩
        ⟨v, Nat.lt_succ_iff.mpr hboundV⟩ hu hv

instance finiteCoefficientsDecidable (T : LeanWang.TileSet) (w : Column → Symbol T)
    (a b : ℤ) : Decidable (FiniteCoefficients T w a b) := by
  unfold FiniteCoefficients
  infer_instance

instance allowedCoefficientsDecidable (T : LeanWang.TileSet) (w : Column → Symbol T)
    (a b : ℤ) : Decidable (AllowedCoefficients T w a b) :=
  decidable_of_iff _ (allowedCoefficients_iff_finite T w a b).symm

instance allowedDecidable (T : LeanWang.TileSet) (w : Column → Symbol T) :
    Decidable (Allowed T w) := decidable_of_iff _ (allowed_iff_bounded T w).symm

/-- Exhaustive finite decision procedure; no unbounded coefficient search. -/
def allowedBool (T : LeanWang.TileSet) (w : Column → Symbol T) : Bool := decide (Allowed T w)

@[simp] theorem allowedBool_eq_true (T : LeanWang.TileSet) (w : Column → Symbol T) :
    allowedBool T w = true ↔ Allowed T w := by simp [allowedBool]

/-- An executable finite collection of all allowed words over the decorated alphabet.
It is intended as construction data, not as a practical enumeration. -/
def allowedWords (T : LeanWang.TileSet) : Finset (Column → Symbol T) :=
  Finset.univ.filter fun w => Allowed T w

@[simp] theorem mem_allowedWords (T : LeanWang.TileSet) (w : Column → Symbol T) :
    w ∈ allowedWords T ↔ Allowed T w := by simp [allowedWords]

end TranslationTiling.Sudoku
