import TranslationTiling.SudokuArithmetic.AdjacentRows
import TranslationTiling.Proofs.Wang

/-! Decorated Sudoku soundness, using finite-depth arithmetic and Wang compactness. -/

namespace TranslationTiling.Sudoku

def height (u v : ℕ) : ℤ := (p : ℤ) ^ u * (q : ℤ) ^ v

theorem height_ne_zero (u v : ℕ) : height u v ≠ 0 :=
  mul_ne_zero (pow_ne_zero _ (by decide)) (pow_ne_zero _ (by decide))

theorem valuation_prime_powers (r : ℕ) (hp : r.Prime) (s : ℕ)
    (hs : (s : ZMod r) ≠ 0) (u v : ℕ) :
    padicValInt r ((r : ℤ) ^ u * (s : ℤ) ^ v) = u := by
  let : Fact r.Prime := ⟨hp⟩
  have hs0 : (s : ℤ) ≠ 0 := by
    intro he
    apply hs
    have hsNat : s = 0 := Int.natCast_eq_zero.mp he
    simp only [hsNat, Nat.cast_zero]
  have hsn : ¬ (r : ℤ) ∣ (s : ℤ) ^ v := by
    intro hd
    apply pow_ne_zero v hs
    simpa only [Int.cast_pow, Int.cast_natCast] using
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ r).mpr hd
  rw [padicValInt.mul (pow_ne_zero _ (Int.natCast_ne_zero.mpr hp.ne_zero))
    (pow_ne_zero _ hs0), padicValInt.eq_zero_of_not_dvd hsn, add_zero,
    ← Int.natCast_pow, padicValInt.of_nat, padicValNat.prime_pow]

theorem height_valuation_p (u v : ℕ) : padicValInt p (height u v) = u :=
  valuation_prime_powers p (by decide) q (by decide) u v

theorem height_valuation_q (u v : ℕ) : padicValInt q (height u v) = v := by
  rw [height, mul_comm]
  exact valuation_prime_powers q (by decide) p (by decide) v u

theorem height_horizontal (u v : ℕ) : height (u + 1) v = height u v * p := by
  unfold height
  rw [pow_succ]
  ring

theorem height_vertical (u v : ℕ) : height u (v + 1) = height u v * q := by
  unfold height
  rw [pow_succ, mul_assoc]

theorem canonical_rectangle {T : LeanWang.TileSet} {W : Array T} (hW : LineRule W)
    (w h : ℕ) {Bₚ : ZMod p} {Bᵩ : ZMod q}
    (hₚ : CanonicalArithmetic p (by decide) (fun n m => (W n m).1) Bₚ w)
    (hᵩ : CanonicalArithmetic q (by decide) (fun n m => (W n m).2.1) Bᵩ h) :
    ValidRectangle T w h (fun u v => (W oneColumn (height u.val v.val)).2.2) := by
  constructor
  · intro u v hu
    have hh := canonical_adjacent_rows hW hₚ hᵩ (height u.val v.val)
      (height_ne_zero _ _) (by rw [height_valuation_p]; omega)
      (by rw [height_valuation_q]; exact v.isLt)
    simpa only [height_horizontal] using hh.1
  · intro u v hv
    have hh := canonical_adjacent_rows hW hₚ hᵩ (height u.val v.val)
      (height_ne_zero _ _) (by rw [height_valuation_p]; exact u.isLt)
      (by rw [height_valuation_q]; omega)
    simpa only [height_vertical] using hh.2

theorem exists_valid_rectangle {T : LeanWang.TileSet} {W : Array T}
    (hW : LineRule W) (hcols : NonconstantColumns W) (w h : ℕ) :
    ∃ σ : Fin w → Fin h → LeanWang.TileIn T, ValidRectangle T w h σ := by
  obtain ⟨D, E, Bₚ, Bᵩ, hp, hq, hₚ, hᵩ⟩ := decorated_finite_structure hW hcols w h
  exact ⟨_, canonical_rectangle (reparametrize_lineRule hW 1 D E) w h ⟨hp, hₚ⟩ ⟨hq, hᵩ⟩⟩

/-- Greenfeld–Tao's decorated Sudoku soundness for the concrete finite word rule. -/
theorem soundness : Soundness := by
  intro T W hW hcols
  apply (wang_plane_iff_quadrant T).mp
  apply LeanWang.tilesPlane_of_cofinal_tileableSquares
  intro n
  obtain ⟨σ, hσ⟩ := exists_valid_rectangle hW hcols n n
  refine ⟨n, le_rfl, fun i j => (σ i j).val, ?_⟩
  exact ⟨fun i j => (σ i j).property, hσ.1, hσ.2⟩

end TranslationTiling.Sudoku
