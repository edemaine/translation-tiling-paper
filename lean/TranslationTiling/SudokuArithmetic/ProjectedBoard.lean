import TranslationTiling.SudokuArithmetic.PairBoardSoundness
import TranslationTiling.SudokuArithmetic.ProjectedSamples

namespace TranslationTiling.Sudoku.PairBoard
open NineArithmetic
noncomputable section
set_option maxHeartbeats 4000000

def Selected (r : ℕ) (root : Bool) (n : NineArithmetic.Column r) : Prop :=
  (∃ i, baseSample r i=n) ∨ (root=true ∧ n=atColumn r (2+r))

theorem base_selected (r : ℕ) (root : Bool) (i : Fin 3) :
    Selected r root (baseSample r i) := Or.inl ⟨i,rfl⟩

theorem root_selected (r : ℕ) : Selected r true (atColumn r (2+r)) :=
  Or.inr ⟨rfl,rfl⟩

def ProjectedAllowed (T : LeanWang.TileSet) (side : Bool)
    (P : PColumn → (ZMod 5)ˣ) (Q : QColumn → (ZMod 7)ˣ)
    (C : TileColumn → LeanWang.TileIn T) : Prop :=
  ∃ a b : ℤ, (¬ (5:ℤ) ∣ a ∨ ¬ (5:ℤ) ∣ b) ∧
    (¬ (7:ℤ) ∣ a ∨ ¬ (7:ℤ) ∣ b) ∧
    ∃ σ : Fin (threshold 5 a+1) → Fin (threshold 7 a+1) → LeanWang.TileIn T,
      ValidRectangle T _ _ σ ∧
      SelectedAgreement 5 (Selected 5 side) P a b ∧
      SelectedAgreement 7 (Selected 7 (!side)) Q a b ∧
      ∀ n u v, lowValuation 5 (a*position n+b)=some u →
        lowValuation 7 (a*position n+b)=some v →
        ∀ (hu : u≤threshold 5 a) (hv : v≤threshold 7 a),
          C n=σ ⟨u,Nat.lt_succ_iff.mpr hu⟩ ⟨v,Nat.lt_succ_iff.mpr hv⟩

def ProjectedLineRule {T : LeanWang.TileSet} (W : Board T) : Prop :=
  ∀ (side : Bool) (d e : ℤ), ProjectedAllowed T side
    (fun n => W.p n (d*NineArithmetic.position 5 n+e))
    (fun n => W.q n (d*NineArithmetic.position 7 n+e))
    (fun n => W.tile n (d*position n+e))

theorem projected_reparametrize {T : LeanWang.TileSet} {W : Board T}
    (hW : ProjectedLineRule W) (a D E : ℤ) : ProjectedLineRule (reparametrize W a D E) := by
  intro side d e
  convert hW side (a*d+D) (a*e+E) using 1 <;>
    first | (funext n; dsimp [reparametrize]; congr 1; ring) | rfl

theorem projected_finite_structure {T : LeanWang.TileSet} {W : Board T}
    (hP : NineArithmetic.ArithmeticLineRule 5 W.p) (hQ : NineArithmetic.ArithmeticLineRule 7 W.q) (hc : Nonconstant W) (k l : ℕ) :
    ∃ (D E : ℤ) (Bp : ZMod 5) (Bq : ZMod 7), Bp≠0 ∧ Bq≠0 ∧
      (∀ n m, m≠0 → padicValInt 5 m≤k →
        ((reparametrize W 1 D E).p n m).val=Bp*(lastDigit 5 (by decide) m).val) ∧
      (∀ n m, m≠0 → padicValInt 7 m≤l →
        ((reparametrize W 1 D E).q n m).val=Bq*(lastDigit 7 (by decide) m).val) := by
  obtain ⟨Dp,Ep,Bp,hBp,hp⟩ := NineArithmetic.arithmetic_finite_structure
    (by decide : Nat.Prime 5) (by decide) (by decide) _ hP hc.1 k
  obtain ⟨Dq,Eq,Bq,hBq,hq⟩ := NineArithmetic.arithmetic_finite_structure
    (by decide : Nat.Prime 7) (by decide) (by decide) _ hQ hc.2 l
  obtain ⟨D,hDp,hDq⟩ := exists_twoPrime_power_residue (k+1) (l+1) Dp Dq
  obtain ⟨E,hEp,hEq⟩ := exists_twoPrime_power_residue (k+1) (l+1) Ep Eq
  have affine_congr (r K : ℕ) (Dr Er : ℤ)
      (hD : (r:ℤ)^K ∣ D-Dr) (hE : (r:ℤ)^K ∣ E-Er) (n m : ℤ) :
      (r:ℤ)^K ∣ (m+D*n+E-Dr*n-Er)-m := by
    rw [show (m+D*n+E-Dr*n-Er)-m=(D-Dr)*n+(E-Er) by ring]
    exact dvd_add (dvd_mul_of_dvd_left hD n) hE
  refine ⟨D,E,Bp,Bq,hBp,hBq,?_,?_⟩
  · intro n m hm hv
    obtain ⟨hnz,hval,hdigit⟩ := digit_congr_bounded 5 (by decide) k hm hv
      (affine_congr 5 (k+1) Dp Ep hDp hEp (NineArithmetic.position 5 n) m)
    have hh := hp n (m+D*NineArithmetic.position 5 n+E) hnz (by rwa [hval])
    simpa only [reparametrize,one_mul,hdigit] using hh
  · intro n m hm hv
    obtain ⟨hnz,hval,hdigit⟩ := digit_congr_bounded 7 (by decide) l hm hv
      (affine_congr 7 (l+1) Dq Eq hDq hEq (NineArithmetic.position 7 n) m)
    have hh := hq n (m+D*NineArithmetic.position 7 n+E) hnz (by rwa [hval])
    simpa only [reparametrize,one_mul,hdigit] using hh

theorem projected_row {T : LeanWang.TileSet} {W : Board T}
    (hW : ProjectedLineRule W) {Bp : ZMod 5} {Bq : ZMod 7} {k l : ℕ}
    (hP : CanonicalP W Bp k) (hQ : CanonicalQ W Bq l)
    (m : ℤ) (hm : m≠0) (hp : padicValInt 5 m≤k) (hq : padicValInt 7 m≤l) :
    ∀ i j, W.tile i m=W.tile j m := by
  obtain ⟨a,b,hap,haq,σ,hσ,htP,htQ,htC⟩ := hW true 0 m
  have hp0 : Bp*(lastDigit 5 (by decide) m).val≠0 := by
    letI : Fact (Nat.Prime 5) := ⟨by decide⟩
    exact mul_ne_zero hP.1 (Units.ne_zero _)
  have hq0 : Bq*(lastDigit 7 (by decide) m).val≠0 := by
    letI : Fact (Nat.Prime 7) := ⟨by decide⟩
    exact mul_ne_zero hQ.1 (Units.ne_zero _)
  obtain ⟨ha5,hb5⟩ := selected_coefficients 5 (by decide) (by decide)
    hP m 0 hm (by decide) hp a b hap (base_selected 5 true)
    (by simpa [SelectedAgreement] using htP)
  obtain ⟨ha7,hb7⟩ := selected_coefficients 7 (by decide) (by decide)
    hQ m 0 hm (by decide) hq a b haq (base_selected 7 false)
    (by simpa [SelectedAgreement] using htQ)
  simp only [Int.cast_zero,mul_zero] at ha5 ha7
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

theorem projected_horizontal_rows {T : LeanWang.TileSet} {W : Board T}
    (hW : ProjectedLineRule W) {Bp : ZMod 5} {Bq : ZMod 7} {k l : ℕ}
    (hP : CanonicalP W Bp k) (hQ : CanonicalQ W Bq l)
    (M : ℤ) (hM : M≠0) (hp : padicValInt 5 M+1≤k) (hq : padicValInt 7 M+1≤l) :
    LeanWang.WangTile.HMatches (W.tile 0 M).val (W.tile 0 (M*5)).val := by
  letI : Fact (Nat.Prime 5) := ⟨by decide⟩
  letI : Fact (Nat.Prime 7) := ⟨by decide⟩
  obtain ⟨a,b,hap,haq,σ,hσ,htP,htQ,htC⟩ := hW true (2*M) M
  have htime (x : ℤ) : M*(2*x+1)=(2*M)*x+M := by ring
  have tp : SelectedAgreement 5 (Selected 5 true)
      (fun n => W.p n (M*(2*NineArithmetic.position 5 n+1))) a b := by
    intro n hn u hu hs
    dsimp only
    rw [htime]
    exact htP n hn u hu hs
  have tq : SelectedAgreement 7 (Selected 7 false)
      (fun n => W.q n (M*(2*NineArithmetic.position 7 n+1))) a b := by
    intro n hn u hu hs
    dsimp only
    rw [htime]
    exact htQ n hn u hu hs
  obtain ⟨ha5,hb5⟩ := selected_coefficients 5 (by decide) (by decide)
    hP M 2 hM (by decide) (by omega) a b hap (base_selected 5 true) tp
  obtain ⟨ha7,hb7⟩ := selected_coefficients 7 (by decide) (by decide)
    hQ M 2 hM (by decide) (by omega) a b haq (base_selected 7 false) tq
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
    selected_root_one 5 (by decide) (by decide) hP M 2 hM hp
      (by norm_num) (by decide) (by decide) a b hap (base_selected 5 true) (root_selected 5) (by decide) tp
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
  have hrow := projected_row hW hP hQ (M*5) (mul_ne_zero hM (by norm_num))
    (by rw [padicValInt.mul hM (by norm_num),show padicValInt 5 (5:ℤ)=1 from padicValInt_self]; exact hp)
    (by rw [(digit_mul_unit 7 (by decide) hM (by decide : ¬(7:ℤ)∣5)).2.1]; omega) 1 0
  have hh := hσ.1 zp zq (by change 0+1<threshold 5 a+1; rw [htp]; decide)
  change LeanWang.WangTile.HMatches (σ zp zq).val (σ op zq).val at hh
  rwa [←h00,←htarget,hrow] at hh

theorem projected_vertical_rows {T : LeanWang.TileSet} {W : Board T}
    (hW : ProjectedLineRule W) {Bp : ZMod 5} {Bq : ZMod 7} {k l : ℕ}
    (hP : CanonicalP W Bp k) (hQ : CanonicalQ W Bq l)
    (M : ℤ) (hM : M≠0) (hp : padicValInt 5 M+1≤k) (hq : padicValInt 7 M+1≤l) :
    LeanWang.WangTile.VMatches (W.tile 0 M).val (W.tile 0 (M*7)).val := by
  letI : Fact (Nat.Prime 5) := ⟨by decide⟩
  letI : Fact (Nat.Prime 7) := ⟨by decide⟩
  obtain ⟨a,b,hap,haq,σ,hσ,htP,htQ,htC⟩ := hW false (3*M) M
  have htime (x : ℤ) : M*(3*x+1)=(3*M)*x+M := by ring
  have tp : SelectedAgreement 5 (Selected 5 false)
      (fun n => W.p n (M*(3*NineArithmetic.position 5 n+1))) a b := by
    intro n hn u hu hs
    dsimp only
    rw [htime]
    exact htP n hn u hu hs
  have tq : SelectedAgreement 7 (Selected 7 true)
      (fun n => W.q n (M*(3*NineArithmetic.position 7 n+1))) a b := by
    intro n hn u hu hs
    dsimp only
    rw [htime]
    exact htQ n hn u hu hs
  obtain ⟨ha5,hb5⟩ := selected_coefficients 5 (by decide) (by decide)
    hP M 3 hM (by decide) (by omega) a b hap (base_selected 5 false) tp
  obtain ⟨ha7,hb7⟩ := selected_coefficients 7 (by decide) (by decide)
    hQ M 3 hM (by decide) (by omega) a b haq (base_selected 7 true) tq
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
    selected_root_one 7 (by decide) (by decide) hQ M 3 hM hq
      (by norm_num) (by decide) (by decide) a b haq (base_selected 7 true) (root_selected 7) (by decide) tq
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
  have hrow := projected_row hW hP hQ (M*7) (mul_ne_zero hM (by norm_num))
    (by rw [(digit_mul_unit 5 (by decide) hM (by decide : ¬(5:ℤ)∣7)).2.1]; omega)
    (by rw [padicValInt.mul hM (by norm_num),show padicValInt 7 (7:ℤ)=1 from padicValInt_self]; exact hq) 1 0
  have hh := hσ.2 zp zq (by change 0+1<threshold 7 a+1; rw [htq]; decide)
  change LeanWang.WangTile.VMatches (σ zp zq).val (σ zp oq).val at hh
  rwa [←h00,←htarget,hrow] at hh

theorem projected_adjacent_rows {T : LeanWang.TileSet} {W : Board T}
    (hW : ProjectedLineRule W) {Bp : ZMod p} {Bq : ZMod q} {k l : ℕ}
    (hP : CanonicalP W Bp k) (hQ : CanonicalQ W Bq l)
    (M : ℤ) (hM : M≠0) (hp : padicValInt p M+1≤k) (hq : padicValInt q M+1≤l) :
    LeanWang.WangTile.HMatches (W.tile 0 M).val (W.tile 0 (M*p)).val ∧
    LeanWang.WangTile.VMatches (W.tile 0 M).val (W.tile 0 (M*q)).val :=
  ⟨projected_horizontal_rows hW hP hQ M hM hp hq,
   projected_vertical_rows hW hP hQ M hM hp hq⟩
theorem projected_rectangle {T : LeanWang.TileSet} {W : Board T} (hW : ProjectedLineRule W)
    (w h : ℕ) {Bₚ : ZMod p} {Bᵩ : ZMod q}
    (hₚ : CanonicalP W Bₚ w)
    (hᵩ : CanonicalQ W Bᵩ h) :
    ValidRectangle T w h (fun u v => W.tile 0 (height u.val v.val)) := by
  constructor
  · intro u v hu
    have hh := projected_adjacent_rows hW hₚ hᵩ (height u.val v.val)
      (height_ne_zero _ _) (by rw [height_valuation_p]; omega)
      (by rw [height_valuation_q]; exact v.isLt)
    simpa only [height_horizontal] using hh.1
  · intro u v hv
    have hh := projected_adjacent_rows hW hₚ hᵩ (height u.val v.val)
      (height_ne_zero _ _) (by rw [height_valuation_p]; exact u.isLt)
      (by rw [height_valuation_q]; omega)
    simpa only [height_vertical] using hh.2

theorem projected_exists_valid_rectangle {T : LeanWang.TileSet} {W : Board T}
    (hW : ProjectedLineRule W)
    (hP : NineArithmetic.ArithmeticLineRule 5 W.p) (hQ : NineArithmetic.ArithmeticLineRule 7 W.q) (hcols : Nonconstant W) (w h : ℕ) :
    ∃ σ : Fin w → Fin h → LeanWang.TileIn T, ValidRectangle T w h σ := by
  obtain ⟨D, E, Bₚ, Bᵩ, hp, hq, hₚ, hᵩ⟩ := projected_finite_structure hP hQ hcols w h
  exact ⟨_, projected_rectangle (projected_reparametrize hW 1 D E) w h ⟨hp, hₚ⟩ ⟨hq, hᵩ⟩⟩

/-- Soundness after retaining only the two Wang-decoration columns. -/
theorem projected_soundness (T : LeanWang.TileSet) (W : Board T)
    (hW : ProjectedLineRule W)
    (hP : NineArithmetic.ArithmeticLineRule 5 W.p) (hQ : NineArithmetic.ArithmeticLineRule 7 W.q) (hcols : Nonconstant W) : LeanWang.TilesPlane T := by
  apply LeanWang.tilesPlane_of_cofinal_tileableSquares
  intro n
  obtain ⟨σ, hσ⟩ := projected_exists_valid_rectangle hW hP hQ hcols n n
  refine ⟨n, le_rfl, fun i j => (σ i j).val, ?_⟩
  exact ⟨fun i j => (σ i j).property, hσ.1, hσ.2⟩



end
end TranslationTiling.Sudoku.PairBoard
