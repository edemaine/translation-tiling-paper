import TranslationTiling.SudokuArithmetic.SparseRule
import TranslationTiling.SudokuArithmetic.SparseSamples

namespace TranslationTiling.Sudoku.Sparse
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

abbrev CanonicalP {T : LeanWang.TileSet} (W : Board T) :=
  SparseArithmetic.Canonical 5 (by decide) W.p
abbrev CanonicalQ {T : LeanWang.TileSet} (W : Board T) :=
  SparseArithmetic.Canonical 7 (by decide) W.q

theorem canonical_row {T : LeanWang.TileSet} {W : Board T}
    (hW : LineRule W) {Bp : ZMod 5} {Bq : ZMod 7} {k l : ℕ}
    (hP : CanonicalP W Bp k) (hQ : CanonicalQ W Bq l)
    (m : ℤ) (hm : m≠0) (hp : padicValInt 5 m≤k) (hq : padicValInt 7 m≤l) :
    ∀ i j, W.tile i m=W.tile j m := by
  obtain ⟨a,b,hap,haq,σ,hσ,htP,htQ,htC⟩ := hW 0 m
  have hP0 : ∀ n, (W.p n m).val=Bp*(lastDigit 5 (by decide) m).val :=
    fun n => hP.2 n m hm hp
  have hQ0 : ∀ n, (W.q n m).val=Bq*(lastDigit 7 (by decide) m).val :=
    fun n => hQ.2 n m hm hq
  have hp0 : Bp*(lastDigit 5 (by decide) m).val≠0 := by
    letI : Fact (Nat.Prime 5) := ⟨by decide⟩
    exact mul_ne_zero hP.1 (Units.ne_zero _)
  have hq0 : Bq*(lastDigit 7 (by decide) m).val≠0 := by
    letI : Fact (Nat.Prime 7) := ⟨by decide⟩
    exact mul_ne_zero hQ.1 (Units.ne_zero _)
  obtain ⟨ha5,hb5⟩ := SparseArithmetic.constant_word_coefficients 5
    (by decide) (by decide) (by decide) (fun n => W.p n m) a b hap
    (fun n u hu hs => by simpa using htP n u hu hs) _ hp0 hP0
  obtain ⟨ha7,hb7⟩ := SparseArithmetic.constant_word_coefficients 7
    (by decide) (by decide) (by decide) (fun n => W.q n m) a b haq
    (fun n v hv hs => by simpa using htQ n v hv hs) _ hq0 hQ0
  have hzero (r : ℕ) [Fact r.Prime] (c : ZMod r) (hc : c≠0)
      (hA : (a:ZMod r)=0) (hB : (b:ZMod r)=c) (n : ℕ) :
      lowValuation r (a*n+b)=some 0 := by
    apply lowValuation_zero_of_cast_ne
    simpa [hA,hB] using hc
  letI : Fact (Nat.Prime 5) := ⟨by decide⟩
  letI : Fact (Nat.Prime 7) := ⟨by decide⟩
  have ht (n : TileColumn) := htC n 0 0
    (hzero 5 _ hp0 ha5 hb5 (position n))
    (hzero 7 _ hq0 ha7 hb7 (position n)) (Nat.zero_le _) (Nat.zero_le _)
  intro i j
  simpa using (ht i).trans (ht j).symm

theorem canonical_adjacent_rows {T : LeanWang.TileSet} {W : Board T}
    (hW : LineRule W) {Bₚ : ZMod p} {Bᵩ : ZMod q} {k l : ℕ}
    (hₚ : CanonicalP W Bₚ k)
    (hᵩ : CanonicalQ W Bᵩ l)
    (M : ℤ) (hM : M ≠ 0) (hp : padicValInt p M + 1 ≤ k) (hq : padicValInt q M + 1 ≤ l) :
    LeanWang.WangTile.HMatches (W.tile 0 M).val (W.tile 0 (M * p)).val ∧
    LeanWang.WangTile.VMatches (W.tile 0 M).val (W.tile 0 (M * q)).val := by
  let : Fact p.Prime := ⟨by decide⟩
  let : Fact q.Prime := ⟨by decide⟩
  obtain ⟨a, b, hap, haq, σ, hσ, htP, htQ, htC⟩ := hW M 0
  obtain ⟨haₚ, hbₚ⟩ := SparseArithmetic.canonical_scaled_coefficients p (by decide) (by decide) (by decide)
    hₚ M hM hp a b hap (fun n u hn hs => by
      simpa only [add_zero] using htP n u hn hs)
  obtain ⟨haᵩ, hbᵩ⟩ := SparseArithmetic.canonical_scaled_coefficients q (by decide) (by decide) (by decide)
    hᵩ M hM hq a b haq (fun n u hn hs => by
      simpa only [add_zero] using htQ n u hn hs)
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
  have h00 : W.tile 0 M = σ zₚ zᵩ := by
    simpa [oneColumn,position,Nat.cast_one,mul_one,add_zero,zₚ,zᵩ] using
      htC 0 0 0
        (lowValuation_affine_zero p a b oneColumn haₚ0 hbₚ (by simp [oneColumn]))
        (lowValuation_affine_zero q a b oneColumn haᵩ0 hbᵩ (by simp [oneColumn]))
        (Nat.zero_le _) (Nat.zero_le _)
  have h10 : W.tile 1 (M * p) = σ oₚ zᵩ := by
    simpa [pColumn,position,p,add_zero,oₚ,zᵩ] using htC 1 1 0
      (lowValuation_affine_one p (by decide) a b haₚ0 hbₚ)
      (lowValuation_affine_zero q a b pColumn haᵩ0 hbᵩ (by decide))
      (by rw [htp]) (Nat.zero_le _)
  have h01 : W.tile 2 (M * q) = σ zₚ oᵩ := by
    simpa [qColumn,position,q,add_zero,zₚ,oᵩ] using htC 2 0 1
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
  have hrowp := canonical_row hW hₚ hᵩ (M * p) hpM
    (by rwa [hpp]) (by rw [hpq]; omega) 1 0
  have hrowq := canonical_row hW hₚ hᵩ (M * q) hqM
    (by rw [hqp]; omega) (by rwa [hqq]) 2 0
  constructor
  · have hh := hσ.1 zₚ zᵩ (by change 0 + 1 < threshold p a + 1; rw [htp]; decide)
    change LeanWang.WangTile.HMatches (σ zₚ zᵩ).val (σ oₚ zᵩ).val at hh
    rwa [← h00, ← h10, hrowp] at hh
  · have hh := hσ.2 zₚ zᵩ (by change 0 + 1 < threshold q a + 1; rw [htq]; decide)
    change LeanWang.WangTile.VMatches (σ zₚ zᵩ).val (σ zₚ oᵩ).val at hh
    rwa [← h00, ← h01, hrowq] at hh


end
end TranslationTiling.Sudoku.Sparse
