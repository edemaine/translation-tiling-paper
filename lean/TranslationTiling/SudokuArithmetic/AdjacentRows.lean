import TranslationTiling.SudokuArithmetic.CanonicalSamples

/-! The tested columns `1`, `p`, and `q` read two Wang adjacencies. -/

set_option maxRecDepth 2000

namespace TranslationTiling.Sudoku

def oneColumn : Column := ⟨1, by decide⟩
def pColumn : Column := ⟨p, by decide⟩
def qColumn : Column := ⟨q, by decide⟩

theorem lowValuation_prime_mul (r : ℕ) (hr : r ≠ 0) (a : ℤ)
    (ha : (a : ZMod r) ≠ 0) : lowValuation r ((r : ℤ) * a) = some 1 := by
  have hnd : ¬ (r : ℤ) ∣ a := by
    simpa only [ne_eq, ZMod.intCast_zmod_eq_zero_iff_dvd] using ha
  have hnd2 : ¬ (r : ℤ) ^ 2 ∣ (r : ℤ) * a := by
    intro hd
    apply hnd
    apply (Int.mul_dvd_mul_iff_left (Int.natCast_ne_zero.mpr hr)).mp
    simpa only [pow_two] using hd
  simp [lowValuation, hnd2]

theorem lowValuation_affine_zero (r : ℕ) (a b : ℤ) (n : Column)
    (ha : (a : ZMod r) ≠ 0) (hb : (r : ℤ) ^ 2 ∣ b)
    (hn : ((n.val : ℤ) : ZMod r) ≠ 0) [Fact r.Prime] :
    lowValuation r (a * n.val + b) = some 0 := by
  have hcong : SqCongr r (a * n.val + b) (a * n.val) := by
    simpa only [SqCongr, add_sub_cancel_left] using hb
  rw [hcong.lowValuation_eq]
  apply lowValuation_zero_of_cast_ne
  simpa only [Int.cast_mul] using mul_ne_zero ha hn

theorem lowValuation_affine_one (r : ℕ) (hr : r ≠ 0) (a b : ℤ)
    (ha : (a : ZMod r) ≠ 0) (hb : (r : ℤ) ^ 2 ∣ b) :
    lowValuation r (a * r + b) = some 1 := by
  have hcong : SqCongr r (a * r + b) ((r : ℤ) * a) := by
    simpa only [SqCongr, mul_comm a (r : ℤ), add_sub_cancel_left] using hb
  rw [hcong.lowValuation_eq]
  exact lowValuation_prime_mul r hr a ha

theorem canonical_adjacent_rows {T : LeanWang.TileSet} {W : Array T}
    (hW : LineRule W) {Bₚ : ZMod p} {Bᵩ : ZMod q} {k l : ℕ}
    (hₚ : CanonicalArithmetic p (by decide) (fun n m => (W n m).1) Bₚ k)
    (hᵩ : CanonicalArithmetic q (by decide) (fun n m => (W n m).2.1) Bᵩ l)
    (M : ℤ) (hM : M ≠ 0) (hp : padicValInt p M + 1 ≤ k) (hq : padicValInt q M + 1 ≤ l) :
    LeanWang.WangTile.HMatches (W oneColumn M).2.2.val (W oneColumn (M * p)).2.2.val ∧
    LeanWang.WangTile.VMatches (W oneColumn M).2.2.val (W oneColumn (M * q)).2.2.val := by
  let : Fact p.Prime := ⟨by decide⟩
  let : Fact q.Prime := ⟨by decide⟩
  obtain ⟨a, b, hap, haq, σ, hσ, ht⟩ := hW M 0
  obtain ⟨haₚ, hbₚ⟩ := canonical_scaled_coefficients p (by decide) (by decide) (by decide)
    hₚ M hM hp a b hap (fun n u hn hs => by
      simpa only [add_zero] using (ht n).1 u hn hs)
  obtain ⟨haᵩ, hbᵩ⟩ := canonical_scaled_coefficients q (by decide) (by decide) (by decide)
    hᵩ M hM hq a b haq (fun n u hn hs => by
      simpa only [add_zero] using (ht n).2.1 u hn hs)
  have haₚ0 : (a : ZMod p) ≠ 0 := by rw [haₚ]; exact mul_ne_zero hₚ.1 (Units.ne_zero _)
  have haᵩ0 : (a : ZMod q) ≠ 0 := by rw [haᵩ]; exact mul_ne_zero hᵩ.1 (Units.ne_zero _)
  have htp : threshold p a = 1 := by
    have hn : ¬ (p : ℤ) ∣ a := by
      simpa only [ne_eq, ZMod.intCast_zmod_eq_zero_iff_dvd] using haₚ0
    simp only [threshold, if_neg hn]
  have htq : threshold q a = 1 := by
    have hn : ¬ (q : ℤ) ∣ a := by
      simpa only [ne_eq, ZMod.intCast_zmod_eq_zero_iff_dvd] using haᵩ0
    simp only [threshold, if_neg hn]
  let zₚ : Fin (threshold p a + 1) := ⟨0, Nat.zero_lt_succ _⟩
  let zᵩ : Fin (threshold q a + 1) := ⟨0, Nat.zero_lt_succ _⟩
  let oₚ : Fin (threshold p a + 1) := ⟨1, by rw [htp]; decide⟩
  let oᵩ : Fin (threshold q a + 1) := ⟨1, by rw [htq]; decide⟩
  have h00 : (W oneColumn M).2.2 = σ zₚ zᵩ := by
    simpa only [oneColumn, Nat.cast_one, mul_one, add_zero, zₚ, zᵩ] using
      (ht oneColumn).2.2 0 0
        (lowValuation_affine_zero p a b oneColumn haₚ0 hbₚ (by simp [oneColumn]))
        (lowValuation_affine_zero q a b oneColumn haᵩ0 hbᵩ (by simp [oneColumn]))
        (Nat.zero_le _) (Nat.zero_le _)
  have h10 : (W pColumn (M * p)).2.2 = σ oₚ zᵩ := by
    simpa only [pColumn, add_zero, oₚ, zᵩ] using (ht pColumn).2.2 1 0
      (lowValuation_affine_one p (by decide) a b haₚ0 hbₚ)
      (lowValuation_affine_zero q a b pColumn haᵩ0 hbᵩ (by decide))
      (by rw [htp]) (Nat.zero_le _)
  have h01 : (W qColumn (M * q)).2.2 = σ zₚ oᵩ := by
    simpa only [qColumn, add_zero, zₚ, oᵩ] using (ht qColumn).2.2 0 1
      (lowValuation_affine_zero p a b qColumn haₚ0 hbₚ (by decide))
      (lowValuation_affine_one q (by decide) a b haᵩ0 hbᵩ)
      (Nat.zero_le _) (by rw [htq])
  have hpM : M * (p : ℤ) ≠ 0 := mul_ne_zero hM (by decide)
  have hqM : M * (q : ℤ) ≠ 0 := mul_ne_zero hM (by decide)
  have hpp : padicValInt p (M * p) = padicValInt p M + 1 := by
    rw [padicValInt.mul hM (by decide), padicValInt_self]
  have hqq : padicValInt q (M * q) = padicValInt q M + 1 := by
    rw [padicValInt.mul hM (by decide), padicValInt_self]
  have hpq : padicValInt q (M * p) = padicValInt q M :=
    (digit_mul_unit q (by decide) hM (by decide)).2.1
  have hqp : padicValInt p (M * q) = padicValInt p M :=
    (digit_mul_unit p (by decide) hM (by decide)).2.1
  have hrowp := canonical_row_decoration hW hₚ hᵩ (M * p) hpM
    (by rwa [hpp]) (by rw [hpq]; omega) pColumn oneColumn
  have hrowq := canonical_row_decoration hW hₚ hᵩ (M * q) hqM
    (by rw [hqp]; omega) (by rwa [hqq]) qColumn oneColumn
  constructor
  · have hh := hσ.1 zₚ zᵩ (by change 0 + 1 < threshold p a + 1; rw [htp]; decide)
    change LeanWang.WangTile.HMatches (σ zₚ zᵩ).val (σ oₚ zᵩ).val at hh
    rwa [← h00, ← h10, hrowp] at hh
  · have hh := hσ.2 zₚ zᵩ (by change 0 + 1 < threshold q a + 1; rw [htq]; decide)
    change LeanWang.WangTile.VMatches (σ zₚ zᵩ).val (σ zₚ oᵩ).val at hh
    rwa [← h00, ← h01, hrowq] at hh

end TranslationTiling.Sudoku
