import TranslationTiling.SudokuArithmetic.ProjectedBoard

namespace TranslationTiling.Sudoku.PairBoard
open NineArithmetic
noncomputable section
set_option maxHeartbeats 2000000

def querySlope (j : Fin 3) : ℤ := ![0,2,3] j

theorem querySlope_cases (j : Fin 3) : querySlope j=0 ∨ querySlope j=2 ∨ querySlope j=3 := by
  fin_cases j <;> decide

def Guard (r : ℕ) (j : Fin 3) (c : (ZMod r)ˣ) (V : NineArithmetic.Column r → (ZMod r)ˣ) : Prop :=
  (∀ i : Fin 3, (V (baseSample r i)).val =
    c.val * ((querySlope j : ZMod r)*NineArithmetic.position r (baseSample r i)+1)) ∧
  (2*querySlope j+1=(r:ℤ) →
    (V (atColumn r (2+r))).val=c.val*((querySlope j:ZMod r)+1))

def QueryMatch {T : LeanWang.TileSet} (j : Fin 3) (a b : LeanWang.TileIn T) : Prop :=
  if j=0 then a=b else if j=1 then a.val.HMatches b.val else a.val.VMatches b.val

def GuardedRule {T : LeanWang.TileSet} (W : Board T) : Prop :=
  ∀ (j : Fin 3) (c : (ZMod 5)ˣ) (c' : (ZMod 7)ˣ) (d e : ℤ),
    Guard 5 j c (fun n => W.p n (d*NineArithmetic.position 5 n+e)) →
    Guard 7 j c' (fun n => W.q n (d*NineArithmetic.position 7 n+e)) →
    QueryMatch j (W.tile 0 e) (W.tile 1 (2*d+e))

theorem guarded_reparametrize {T : LeanWang.TileSet} {W : Board T}
    (hW : GuardedRule W) (D E : ℤ) : GuardedRule (reparametrize W 1 D E) := by
  intro j c c' d e hp hq
  have h (x : ℕ) : 1*(d*x+e)+D*x+E=(d+D)*x+(e+E) := by ring
  have hp' : Guard 5 j c (fun n => W.p n ((d+D)*NineArithmetic.position 5 n+(e+E))) := by
    simpa only [reparametrize,h] using hp
  have hq' : Guard 7 j c' (fun n => W.q n ((d+D)*NineArithmetic.position 7 n+(e+E))) := by
    simpa only [reparametrize,h] using hq
  have h0 : (1:ℤ)*e+D*position 0+E=e+E := by norm_num [position]
  have h1 : 1*(2*d+e)+D*position 1+E=2*(d+D)+(e+E) := by norm_num [position]; ring
  simpa only [reparametrize,h0,h1] using hW j c c' (d+D) (e+E) hp' hq'

def phase (r : ℕ) (hr : r.Prime) (B : ZMod r) (hB : B≠0) (M : ℤ) : (ZMod r)ˣ :=
  letI : Fact r.Prime := ⟨hr⟩
  Units.mk0 (B*(lastDigit r hr M).val) (mul_ne_zero hB (Units.ne_zero _))

theorem canonical_guard (r : ℕ) (hr : r.Prime) (hrs : r=5 ∨ r=7)
    {V : NineArithmetic.Column r → ℤ → (ZMod r)ˣ} {B : ZMod r} {K : ℕ}
    (hV : Canonical r hr V B K) (M : ℤ) (hM : M≠0)
    (j : Fin 3) (h0 : padicValInt r M≤K)
    (h1 : 2*querySlope j+1=(r:ℤ) → padicValInt r M+1≤K) :
    Guard r j (phase r hr B hV.1 M) (fun n => V n ((M*querySlope j)*NineArithmetic.position r n+M)) := by
  have he (n : NineArithmetic.Column r) :
      (M*querySlope j)*NineArithmetic.position r n+M=M*(querySlope j*NineArithmetic.position r n+1) := by ring
  constructor
  · intro i
    dsimp only
    rw [he]
    obtain ⟨hz,hval,hdig⟩ := digit_mul_unit r hr hM (sample_units r _ hrs (querySlope_cases j) i)
    rw [hV.2 _ _ hz (hval ▸ h0),hdig]
    simp only [phase,Units.val_mk0,Int.cast_add,Int.cast_mul,Int.cast_natCast,Int.cast_one,mul_assoc]
  · intro hrel
    dsimp only
    rw [he]
    have hh := canonical_root_value r hr hV M (querySlope j) (querySlope j+1) hM (h1 hrel) (atColumn r (2+r)) (by
      rw [position_at hrs (2+r) (Or.inr (Or.inr (Or.inr (Or.inl (by omega))))) ]
      push_cast
      linear_combination hrel) (by
        rcases hrs with rfl|rfl <;> fin_cases j <;> first | contradiction | (norm_num [querySlope] at *; done) | decide +revert)
    simpa only [phase,Units.val_mk0,Int.cast_add,Int.cast_one] using hh

theorem guarded_row {T : LeanWang.TileSet} {W : Board T} (hg : GuardedRule W)
    {Bp : ZMod 5} {Bq : ZMod 7} {k l : ℕ}
    (hp : CanonicalP W Bp k) (hq : CanonicalQ W Bq l) (M : ℤ) (hM : M≠0)
    (hk : padicValInt 5 M≤k) (hl : padicValInt 7 M≤l) :
    W.tile 0 M=W.tile 1 M := by
  have h := hg 0 _ _ (M*querySlope 0) M
    (canonical_guard 5 (by decide) (by decide) hp M hM 0 hk (fun h => (by decide : 2*querySlope 0+1≠5) h |>.elim))
    (canonical_guard 7 (by decide) (by decide) hq M hM 0 hl (fun h => (by decide : 2*querySlope 0+1≠7) h |>.elim))
  simpa [QueryMatch,show querySlope 0=0 by decide] using h

theorem guarded_adjacent {T : LeanWang.TileSet} {W : Board T} (hg : GuardedRule W)
    {Bp : ZMod 5} {Bq : ZMod 7} {k l : ℕ}
    (hp : CanonicalP W Bp k) (hq : CanonicalQ W Bq l) (M : ℤ) (hM : M≠0)
    (hk : padicValInt 5 M+1≤k) (hl : padicValInt 7 M+1≤l) :
    (W.tile 0 M).val.HMatches (W.tile 0 (M*5)).val ∧
    (W.tile 0 M).val.VMatches (W.tile 0 (M*7)).val := by
  letI : Fact (Nat.Prime 5) := ⟨by decide⟩
  letI : Fact (Nat.Prime 7) := ⟨by decide⟩
  have ha := hg 1 _ _ (M*querySlope 1) M
    (canonical_guard 5 (by decide) (by decide) hp M hM 1 (by omega) (fun _ => hk))
    (canonical_guard 7 (by decide) (by decide) hq M hM 1 (by omega) (fun _ => hl))
  have hb := hg 2 _ _ (M*querySlope 2) M
    (canonical_guard 5 (by decide) (by decide) hp M hM 2 (by omega) (fun _ => hk))
    (canonical_guard 7 (by decide) (by decide) hq M hM 2 (by omega) (fun _ => hl))
  have he5 : 2*(M*querySlope 1)+M=M*5 := by rw [show querySlope 1=2 by decide]; ring
  have he7 : 2*(M*querySlope 2)+M=M*7 := by rw [show querySlope 2=3 by decide]; ring
  rw [he5,←guarded_row hg hp hq _ (mul_ne_zero hM (by norm_num))
    (by rwa [padicValInt.mul hM (by norm_num),show padicValInt 5 (5:ℤ)=1 from padicValInt_self])
    (by rw [(digit_mul_unit 7 (by decide) hM (by decide : ¬(7:ℤ)∣5)).2.1]; omega)] at ha
  rw [he7,←guarded_row hg hp hq _ (mul_ne_zero hM (by norm_num))
    (by rw [(digit_mul_unit 5 (by decide) hM (by decide : ¬(5:ℤ)∣7)).2.1]; omega)
    (by rwa [padicValInt.mul hM (by norm_num),show padicValInt 7 (7:ℤ)=1 from padicValInt_self])] at hb
  exact ⟨ha,hb⟩

theorem guarded_soundness (T : LeanWang.TileSet) (W : Board T)
    (hg : GuardedRule W) (hp : NineArithmetic.ArithmeticLineRule 5 W.p) (hq : NineArithmetic.ArithmeticLineRule 7 W.q)
    (hc : Nonconstant W) : LeanWang.TilesPlane T := by
  apply LeanWang.tilesPlane_of_cofinal_tileableSquares
  intro n
  obtain ⟨D,E,Bp,Bq,hBp,hBq,hp',hq'⟩ := projected_finite_structure hp hq hc n n
  let W' := reparametrize W 1 D E
  have hs : GuardedRule W' := guarded_reparametrize hg D E
  have hP : CanonicalP W' Bp n := ⟨hBp,hp'⟩
  have hQ : CanonicalQ W' Bq n := ⟨hBq,hq'⟩
  refine ⟨n,le_rfl,fun i j => (W'.tile 0 (height i.val j.val)).val,
    fun _ _ => (W'.tile 0 _).property,?_,?_⟩
  · intro i j hi
    have h := (guarded_adjacent hs hP hQ (height i.val j.val) (height_ne_zero _ _)
      (by rw [height_valuation_p]; omega) (by rw [height_valuation_q]; exact j.isLt)).1
    dsimp only
    rw [height_horizontal]
    exact h
  · intro i j hj
    have h := (guarded_adjacent hs hP hQ (height i.val j.val) (height_ne_zero _ _)
      (by rw [height_valuation_p]; exact i.isLt) (by rw [height_valuation_q]; omega)).2
    dsimp only
    rw [height_vertical]
    exact h

theorem guard_coefficients (r : ℕ) (hr : r.Prime) (hrs : r=5 ∨ r=7) (j : Fin 3)
    (c : (ZMod r)ˣ) (V : NineArithmetic.Column r → (ZMod r)ˣ) (hg : Guard r j c V)
    (a b : ℤ) (hab : ¬ (r:ℤ)∣a ∨ ¬ (r:ℤ)∣b) {S : NineArithmetic.Column r → Prop}
    (hs : ∀ i, S (baseSample r i)) (ht : SelectedAgreement r S V a b) :
    (a:ZMod r)=c.val*(querySlope j:ZMod r) ∧ (b:ZMod r)=c.val := by
  letI : Fact r.Prime := ⟨hr⟩
  apply sampleCheck r _ hrs (querySlope_cases j) _ _ c.val
    (by simpa only [ne_eq,ZMod.intCast_zmod_eq_zero_iff_dvd] using hab) (Units.ne_zero _)
  intro i hi
  let x := NineArithmetic.position r (baseSample r i)
  have hne : ((a*x+b:ℤ):ZMod r)≠0 := by push_cast; exact hi
  have hn : ¬ (r:ℤ)∣a*x+b := fun h => hne ((ZMod.intCast_zmod_eq_zero_iff_dvd _ r).mpr h)
  have hv := ht (baseSample r i) (hs i) 0 (lowValuation_zero_of_cast_ne _ _ hne) (Nat.zero_le _)
  rw [hg.1 i] at hv
  simpa only [x,lowDigit,if_neg hn,Int.cast_add,Int.cast_mul,Int.cast_natCast] using hv.symm

private theorem guard_root (r : ℕ) (hr : r.Prime) (hrs : r=5 ∨ r=7) (j : Fin 3)
    (c : (ZMod r)ˣ) (V : NineArithmetic.Column r → (ZMod r)ˣ) (hg : Guard r j c V)
    (hrel : 2*querySlope j+1=(r:ℤ)) (a b : ℤ)
    (ha : (a:ZMod r)=c.val*(querySlope j:ZMod r)) (hb : (b:ZMod r)=c.val)
    {S : NineArithmetic.Column r → Prop} (hx : S (atColumn r (2+r)))
    (ht : SelectedAgreement r S V a b) :
    lowValuation r (2*a+b)=some 1 := by
  letI : Fact r.Prime := ⟨hr⟩
  have hds : (querySlope j:ZMod r)≠0 := by
    rcases hrs with rfl|rfl <;> fin_cases j <;> first | contradiction | (norm_num [querySlope] at *; done) | decide +revert
  have ha0 : (a:ZMod r)≠0 := by rw [ha]; exact mul_ne_zero (Units.ne_zero _) hds
  have hdiv : (r:ℤ)∣2*a+b := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ r).mp
    have he := congrArg (fun z : ℤ => (z:ZMod r)) hrel
    push_cast at he ⊢
    simp only [ZMod.natCast_self] at he
    rw [ha,hb]
    linear_combination c.val*he
  obtain ⟨z,hz⟩ := hdiv
  let n := atColumn r (2+r)
  have hn : NineArithmetic.position r n=2+r := position_at hrs _ (by omega)
  have hr0 : (r:ℤ)≠0 := Int.natCast_ne_zero.mpr hr.ne_zero
  have he : a*NineArithmetic.position r n+b=(r:ℤ)*(z+a) := by
    rw [hn]; push_cast; linear_combination hz
  have hnot : ¬(r:ℤ)∣z := by
    intro hbad
    have hz0 : (z:ZMod r)=0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ r).mpr hbad
    have hzua : ¬(r:ℤ)∣z+a := by
      simpa only [←ZMod.intCast_zmod_eq_zero_iff_dvd,Int.cast_add,hz0,zero_add] using ha0
    have hsq : ¬(r:ℤ)^2∣a*NineArithmetic.position r n+b := by
      rw [he,pow_two,Int.mul_dvd_mul_iff_left hr0]
      exact hzua
    have hdiv : (r:ℤ)∣a*NineArithmetic.position r n+b := ⟨_,he⟩
    have hv := ht n hx 1 (by simp [lowValuation,hdiv,hsq])
      (by simp [threshold,show ¬(r:ℤ)∣a by simpa [ZMod.intCast_zmod_eq_zero_iff_dvd] using ha0])
    rw [lowDigit,if_pos hdiv,he,Int.mul_ediv_cancel_left _ hr0] at hv
    change (V (atColumn r (2+r))).val=((z+a:ℤ):ZMod r) at hv
    rw [hg.2 hrel,Int.cast_add,hz0,zero_add,ha] at hv
    apply Units.ne_zero c
    linear_combination hv
  have hsq : ¬(r:ℤ)^2∣2*a+b := by rw [hz,pow_two,Int.mul_dvd_mul_iff_left hr0]; exact hnot
  simp [lowValuation,show (r:ℤ)∣2*a+b from ⟨z,hz⟩,hsq]

def queriedValuation (r : ℕ) (j : Fin 3) := if 2*querySlope j+1=(r:ℤ) then 1 else 0

theorem guard_valuations (r : ℕ) (hr : r.Prime) (hrs : r=5 ∨ r=7) (j : Fin 3)
    (c : (ZMod r)ˣ) (V : NineArithmetic.Column r → (ZMod r)ˣ) (hg : Guard r j c V)
    (a b : ℤ) (hab : ¬ (r:ℤ)∣a ∨ ¬ (r:ℤ)∣b) {S : NineArithmetic.Column r → Prop}
    (hs : ∀ i, S (baseSample r i))
    (hx : 2*querySlope j+1=(r:ℤ) → S (atColumn r (2+r)))
    (ht : SelectedAgreement r S V a b) :
    lowValuation r b=some 0 ∧
    lowValuation r (2*a+b)=some (queriedValuation r j) ∧ queriedValuation r j≤threshold r a := by
  letI : Fact r.Prime := ⟨hr⟩
  obtain ⟨ha,hb⟩ := guard_coefficients r hr hrs j c V hg a b hab hs ht
  refine ⟨lowValuation_zero_of_cast_ne _ _ (hb ▸ Units.ne_zero c),?_⟩
  unfold queriedValuation
  split
  · rename_i ht'
    have hv := guard_root r hr hrs j c V hg ht' a b ha hb (hx ht') ht
    refine ⟨hv,?_⟩
    have hd : (r:ℤ)∣a*2+b := by
      rw [mul_comm]
      by_contra h
      simp [lowValuation,h] at hv
    simp [threshold,primitive_slope_not_dvd r a b 2 hab hd]
  · rename_i ht'
    refine ⟨lowValuation_zero_of_cast_ne _ _ ?_,Nat.zero_le _⟩
    have he : ((2*a+b:ℤ):ZMod r)=c.val*(2*(querySlope j:ZMod r)+1) := by
      push_cast; rw [ha,hb]; ring
    rw [he]
    apply mul_ne_zero (Units.ne_zero _)
    have ht (r : ℕ) (h : r=5 ∨ r=7) :
        ∀ k : Fin 3, 2*querySlope k+1≠(r:ℤ) → 2*(querySlope k:ZMod r)+1≠0 := by
      rcases h with rfl|rfl <;> decide +kernel
    exact ht r hrs j ht' 

theorem guarded_of_projected {T : LeanWang.TileSet} {W : Board T} (hW : ProjectedLineRule W) :
    GuardedRule W := by
  intro j c c' d e hp hq
  let side := decide (j≠2)
  obtain ⟨a,b,hap,haq,σ,hσ,htP,htQ,htC⟩ := hW side d e
  obtain ⟨hp0,hp1,hbp⟩ := guard_valuations 5 (by decide) (by decide) j c _ hp a b hap
    (base_selected 5 side) (by fin_cases j <;> intro h <;> first | contradiction | exact root_selected 5) htP
  obtain ⟨hq0,hq1,hbq⟩ := guard_valuations 7 (by decide) (by decide) j c' _ hq a b haq
    (base_selected 7 (!side)) (by fin_cases j <;> intro h <;> first | contradiction | exact root_selected 7) htQ
  let zp : Fin (threshold 5 a+1) := ⟨0,Nat.zero_lt_succ _⟩
  let zq : Fin (threshold 7 a+1) := ⟨0,Nat.zero_lt_succ _⟩
  let up : Fin (threshold 5 a+1) := ⟨queriedValuation 5 j,Nat.lt_succ_iff.mpr hbp⟩
  let uq : Fin (threshold 7 a+1) := ⟨queriedValuation 7 j,Nat.lt_succ_iff.mpr hbq⟩
  have hh0 : W.tile 0 e=σ zp zq := by
    simpa [position,zp,zq] using htC 0 0 0
      (by simpa [position] using hp0) (by simpa [position] using hq0) (Nat.zero_le _) (Nat.zero_le _)
  have hh1 : W.tile 1 (2*d+e)=σ up uq := by
    simpa [position,mul_comm,up,uq] using htC 1 _ _
      (by simpa [position,mul_comm] using hp1) (by simpa [position,mul_comm] using hq1) hbp hbq
  rw [hh0,hh1]
  fin_cases j
  · exact rfl
  · exact hσ.1 zp zq up.isLt
  · exact hσ.2 zp zq uq.isLt

end
end TranslationTiling.Sudoku.PairBoard
