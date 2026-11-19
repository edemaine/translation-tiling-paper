import TranslationTiling.SudokuArithmetic.PairBoardRule
import TranslationTiling.SudokuArithmetic.PairSamples

namespace TranslationTiling.Sudoku.PairBoard
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

abbrev CanonicalP {T : LeanWang.TileSet} (W : Board T) :=
  NineArithmetic.Canonical 5 (by decide) W.p
abbrev CanonicalQ {T : LeanWang.TileSet} (W : Board T) :=
  NineArithmetic.Canonical 7 (by decide) W.q

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
  obtain ⟨ha5,hb5⟩ := NineArithmetic.constant_word_coefficients 5
    (by decide) (by decide) (fun n => W.p n m) a b hap
    (fun n u hu hs => by simpa using htP n u hu hs) _ hp0 hP0
  obtain ⟨ha7,hb7⟩ := NineArithmetic.constant_word_coefficients 7
    (by decide) (by decide) (fun n => W.q n m) a b haq
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

theorem canonical_horizontal_rows {T : LeanWang.TileSet} {W : Board T}
    (hW : LineRule W) {Bp : ZMod 5} {Bq : ZMod 7} {k l : ℕ}
    (hP : CanonicalP W Bp k) (hQ : CanonicalQ W Bq l)
    (M : ℤ) (hM : M≠0) (hp : padicValInt 5 M+1≤k) (hq : padicValInt 7 M+1≤l) :
    LeanWang.WangTile.HMatches (W.tile 0 M).val (W.tile 0 (M*5)).val := by
  letI : Fact (Nat.Prime 5) := ⟨by decide⟩
  letI : Fact (Nat.Prime 7) := ⟨by decide⟩
  obtain ⟨a,b,hap,haq,σ,hσ,htP,htQ,htC⟩ := hW (2*M) M
  have htime (x : ℤ) : M*(2*x+1)=(2*M)*x+M := by ring
  have tp : ∀ n u, lowValuation 5 (a*NineArithmetic.position 5 n+b)=some u → u≤threshold 5 a →
      (W.p n (M*(2*NineArithmetic.position 5 n+1))).val=lowDigit 5 (a*NineArithmetic.position 5 n+b) := by
    intro n u hu hs
    rw [htime]
    exact htP n u hu hs
  have tq : ∀ n u, lowValuation 7 (a*NineArithmetic.position 7 n+b)=some u → u≤threshold 7 a →
      (W.q n (M*(2*NineArithmetic.position 7 n+1))).val=lowDigit 7 (a*NineArithmetic.position 7 n+b) := by
    intro n u hu hs
    rw [htime]
    exact htQ n u hu hs
  obtain ⟨ha5,hb5⟩ := NineArithmetic.canonical_shifted_coefficients 5 (by decide) (by decide)
    hP M 2 hM (by omega) a b hap tp
  obtain ⟨ha7,hb7⟩ := NineArithmetic.canonical_shifted_coefficients 7 (by decide) (by decide)
    hQ M 2 hM (by omega) a b haq tq
  have cp : Bp*(lastDigit 5 (by decide) M).val≠0 := mul_ne_zero hP.1 (Units.ne_zero _)
  have cq : Bq*(lastDigit 7 (by decide) M).val≠0 := mul_ne_zero hQ.1 (Units.ne_zero _)
  have ha50 : (a:ZMod 5)≠0 := by rw [ha5]; exact mul_ne_zero cp (by decide)
  have ha70 : (a:ZMod 7)≠0 := by rw [ha7]; exact mul_ne_zero cq (by decide)
  have htp : threshold 5 a=1 := by
    have hn : ¬(5:ℤ)∣a := by simpa [ZMod.intCast_zmod_eq_zero_iff_dvd] using ha50
    simp [threshold,hn]
  have htq : threshold 7 a=1 := by
    have hn : ¬(7:ℤ)∣a := by simpa [ZMod.intCast_zmod_eq_zero_iff_dvd] using ha70
    simp [threshold,hn]
  have h05 : lowValuation 5 b=some 0 := lowValuation_zero_of_cast_ne _ _ (hb5 ▸ cp)
  have h07 : lowValuation 7 b=some 0 := lowValuation_zero_of_cast_ne _ _ (hb7 ▸ cq)
  have h25 : lowValuation 5 (2*a+b)=some 1 :=
    NineArithmetic.shifted_root_one 5 (by decide) (by decide) hP M 2 hM hp
      (by norm_num) (by decide) (by decide) a b hap tp
  have h27 : lowValuation 7 (2*a+b)=some 0 := by
    apply lowValuation_zero_of_cast_ne
    have he : ((2*a+b:ℤ):ZMod 7)=
        (Bq*(lastDigit 7 (by decide) M).val)*5 := by
      push_cast
      rw [ha7,hb7]
      norm_num
      ring
    rw [he]
    exact mul_ne_zero cq (by decide)
  let zp : Fin (threshold 5 a+1) := ⟨0,Nat.zero_lt_succ _⟩
  let zq : Fin (threshold 7 a+1) := ⟨0,Nat.zero_lt_succ _⟩
  let op : Fin (threshold 5 a+1) := ⟨1,by rw [htp]; decide⟩
  let oq : Fin (threshold 7 a+1) := ⟨1,by rw [htq]; decide⟩
  have h00 : W.tile 0 M=σ zp zq := by
    simpa [position,zp,zq] using htC 0 0 0 (by simpa [position] using h05)
      (by simpa [position] using h07) (Nat.zero_le _) (Nat.zero_le _)
  have htarget : W.tile 1 (M*5)=σ op zq := by
    have hh := htC 1 1 0 (by simpa [position,mul_comm] using h25)
      (by simpa [position,mul_comm] using h27) (by simp [htp]) (by simp [htq])
    have he : (2*M)*(position 1:ℤ)+M=M*5 := by norm_num [position]; ring
    dsimp only at hh
    rw [he] at hh
    simpa only [op,zq] using hh
  have hrow := canonical_row hW hP hQ (M*5) (mul_ne_zero hM (by norm_num))
    (by rw [padicValInt.mul hM (by norm_num),show padicValInt 5 (5:ℤ)=1 from padicValInt_self]; exact hp)
    (by rw [(digit_mul_unit 7 (by decide) hM (by decide : ¬(7:ℤ)∣5)).2.1]; omega) 1 0
  have hh := hσ.1 zp zq (by change 0+1<threshold 5 a+1; rw [htp]; decide)
  change LeanWang.WangTile.HMatches (σ zp zq).val (σ op zq).val at hh
  rwa [←h00,←htarget,hrow] at hh

theorem canonical_vertical_rows {T : LeanWang.TileSet} {W : Board T}
    (hW : LineRule W) {Bp : ZMod 5} {Bq : ZMod 7} {k l : ℕ}
    (hP : CanonicalP W Bp k) (hQ : CanonicalQ W Bq l)
    (M : ℤ) (hM : M≠0) (hp : padicValInt 5 M+1≤k) (hq : padicValInt 7 M+1≤l) :
    LeanWang.WangTile.VMatches (W.tile 0 M).val (W.tile 0 (M*7)).val := by
  letI : Fact (Nat.Prime 5) := ⟨by decide⟩
  letI : Fact (Nat.Prime 7) := ⟨by decide⟩
  obtain ⟨a,b,hap,haq,σ,hσ,htP,htQ,htC⟩ := hW (3*M) M
  have htime (x : ℤ) : M*(3*x+1)=(3*M)*x+M := by ring
  have tp : ∀ n u, lowValuation 5 (a*NineArithmetic.position 5 n+b)=some u → u≤threshold 5 a →
      (W.p n (M*(3*NineArithmetic.position 5 n+1))).val=lowDigit 5 (a*NineArithmetic.position 5 n+b) := by
    intro n u hu hs
    rw [htime]
    exact htP n u hu hs
  have tq : ∀ n u, lowValuation 7 (a*NineArithmetic.position 7 n+b)=some u → u≤threshold 7 a →
      (W.q n (M*(3*NineArithmetic.position 7 n+1))).val=lowDigit 7 (a*NineArithmetic.position 7 n+b) := by
    intro n u hu hs
    rw [htime]
    exact htQ n u hu hs
  obtain ⟨ha5,hb5⟩ := NineArithmetic.canonical_shifted_coefficients 5 (by decide) (by decide)
    hP M 3 hM (by omega) a b hap tp
  obtain ⟨ha7,hb7⟩ := NineArithmetic.canonical_shifted_coefficients 7 (by decide) (by decide)
    hQ M 3 hM (by omega) a b haq tq
  have cp : Bp*(lastDigit 5 (by decide) M).val≠0 := mul_ne_zero hP.1 (Units.ne_zero _)
  have cq : Bq*(lastDigit 7 (by decide) M).val≠0 := mul_ne_zero hQ.1 (Units.ne_zero _)
  have ha50 : (a:ZMod 5)≠0 := by rw [ha5]; exact mul_ne_zero cp (by decide)
  have ha70 : (a:ZMod 7)≠0 := by rw [ha7]; exact mul_ne_zero cq (by decide)
  have htp : threshold 5 a=1 := by
    have hn : ¬(5:ℤ)∣a := by simpa [ZMod.intCast_zmod_eq_zero_iff_dvd] using ha50
    simp [threshold,hn]
  have htq : threshold 7 a=1 := by
    have hn : ¬(7:ℤ)∣a := by simpa [ZMod.intCast_zmod_eq_zero_iff_dvd] using ha70
    simp [threshold,hn]
  have h05 : lowValuation 5 b=some 0 := lowValuation_zero_of_cast_ne _ _ (hb5 ▸ cp)
  have h07 : lowValuation 7 b=some 0 := lowValuation_zero_of_cast_ne _ _ (hb7 ▸ cq)
  have h25 : lowValuation 5 (2*a+b)=some 0 := by
    apply lowValuation_zero_of_cast_ne
    have he : ((2*a+b:ℤ):ZMod 5)=
        (Bp*(lastDigit 5 (by decide) M).val)*7 := by
      push_cast
      rw [ha5,hb5]
      norm_num
      ring
    rw [he]
    exact mul_ne_zero cp (by decide)
  have h27 : lowValuation 7 (2*a+b)=some 1 :=
    NineArithmetic.shifted_root_one 7 (by decide) (by decide) hQ M 3 hM hq
      (by norm_num) (by decide) (by decide) a b haq tq
  let zp : Fin (threshold 5 a+1) := ⟨0,Nat.zero_lt_succ _⟩
  let zq : Fin (threshold 7 a+1) := ⟨0,Nat.zero_lt_succ _⟩
  let op : Fin (threshold 5 a+1) := ⟨1,by rw [htp]; decide⟩
  let oq : Fin (threshold 7 a+1) := ⟨1,by rw [htq]; decide⟩
  have h00 : W.tile 0 M=σ zp zq := by
    simpa [position,zp,zq] using htC 0 0 0 (by simpa [position] using h05)
      (by simpa [position] using h07) (Nat.zero_le _) (Nat.zero_le _)
  have htarget : W.tile 1 (M*7)=σ zp oq := by
    have hh := htC 1 0 1 (by simpa [position,mul_comm] using h25)
      (by simpa [position,mul_comm] using h27) (by simp [htp]) (by simp [htq])
    have he : (3*M)*(position 1:ℤ)+M=M*7 := by norm_num [position]; ring
    dsimp only at hh
    rw [he] at hh
    simpa only [zp,oq] using hh
  have hrow := canonical_row hW hP hQ (M*7) (mul_ne_zero hM (by norm_num))
    (by rw [(digit_mul_unit 5 (by decide) hM (by decide : ¬(5:ℤ)∣7)).2.1]; omega)
    (by rw [padicValInt.mul hM (by norm_num),show padicValInt 7 (7:ℤ)=1 from padicValInt_self]; exact hq) 1 0
  have hh := hσ.2 zp zq (by change 0+1<threshold 7 a+1; rw [htq]; decide)
  change LeanWang.WangTile.VMatches (σ zp zq).val (σ zp oq).val at hh
  rwa [←h00,←htarget,hrow] at hh

theorem canonical_adjacent_rows {T : LeanWang.TileSet} {W : Board T}
    (hW : LineRule W) {Bp : ZMod p} {Bq : ZMod q} {k l : ℕ}
    (hP : CanonicalP W Bp k) (hQ : CanonicalQ W Bq l)
    (M : ℤ) (hM : M≠0) (hp : padicValInt p M+1≤k) (hq : padicValInt q M+1≤l) :
    LeanWang.WangTile.HMatches (W.tile 0 M).val (W.tile 0 (M*p)).val ∧
    LeanWang.WangTile.VMatches (W.tile 0 M).val (W.tile 0 (M*q)).val :=
  ⟨canonical_horizontal_rows hW hP hQ M hM hp hq,
   canonical_vertical_rows hW hP hQ M hM hp hq⟩

end
end TranslationTiling.Sudoku.PairBoard
