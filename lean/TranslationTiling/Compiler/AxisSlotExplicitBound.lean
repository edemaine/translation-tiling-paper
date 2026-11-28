import TranslationTiling.Compiler.AxisSlotComputability
import TranslationTiling.Compiler.AxisSlotLogBound
import TranslationTiling.Compiler.SlotExplicitBound

namespace TranslationTiling.Compiler.Size

open FiniteCompiler.Packed FiniteCompiler.Effective Compiler.Effective

noncomputable section

def axisPublicBound (n : ℕ) : ℝ :=
  if n ≤ 1 then 2^2055 else
    (n + 2) ^ (4.986901 * (Real.logb 2 (Real.logb 2 (n + 2)) +
      Real.logb 2 (Real.logb 2 (Real.logb 2 (n + 2)))) + 172) * (2 : ℝ) ^ 1844

private def comparisonLogs (n : ℕ) : (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ) :=
  ([( (2000,1000,0),    (2584,1369,453)),
    ( (2322,1216,283),  (2807,1489,574)),
    ( (2585,1371,456),  (3000,1584,663)),
    ( (2808,1490,576),  (3169,1664,734)),
    ( (3000,1585,665),  (3321,1731,791)),
    ( (3170,1665,736),  (3459,1790,839)),
    ( (3322,1733,794),  (3584,1841,880)),
    ( (3460,1791,841),  (3700,1887,916)),
    ( (3585,1842,882),  (3807,1928,947)),
    ( (3701,1888,917),  (3906,1965,974)),
    ( (3808,1930,949),  (4000,2000,1000)),
    ( (3907,1967,976),  (4087,2031,1022)),
    ( (4000,2000,1000), (4169,2059,1041)),
    ( (4088,2032,1023), (4247,2086,1060)),
    ( (4170,2061,1044), (4321,2111,1077)),
    ( (4248,2087,1062), (4392,2134,1093)),
    ( (4322,2112,1079), (4459,2156,1108)),
    ( (4393,2136,1095), (4523,2177,1122))] :
      List ((ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ))).getD (n-2) ((0,0,0),(0,0,0))

private def comparisonLogCheck (n : ℕ) : Prop :=
  let ((a,b,c),(d,e,f)) := comparisonLogs n
  0<d ∧ 0<e ∧
  (n+2)^1000≤2^a ∧ a^1000≤1000^1000*2^b ∧ b^1000≤1000^1000*2^c ∧
  2^d≤(n+4)^1000 ∧ 1000^1000*2^e≤d^1000 ∧ 1000^1000*2^f≤e^1000 ∧
  (1844+(a:ℚ)/1000*((4986901/1000000)*((b:ℚ)+c)/1000+172) <
    (d:ℚ)/1000*((4986901/1000000)*((e:ℚ)+f)/1000+192)+
      1880*((d:ℚ)/1000/((d:ℚ)/1000+31/100)))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem comparisonLog_cert {n : ℕ} (hn : 2≤n) (hn' : n<20) :
    comparisonLogCheck n := by
  unfold comparisonLogCheck
  interval_cases n <;> decide +kernel

private theorem axisLog_lt_previous {n : ℕ} (hn : 2≤n) :
    let u := Real.logb 2 ((n:ℝ)+2)
    let v := Real.logb 2 ((n:ℝ)+4)
    let g := Real.logb 2 u
    let h := Real.logb 2 v
    1844+u*(4.986901*(g+Real.logb 2 g)+172) <
      v*(4.986901*(h+Real.logb 2 h)+192)+1880*(v/(v+0.31)) := by
  let x := (n:ℝ)+2
  let y := (n:ℝ)+4
  let u := Real.logb 2 x
  let v := Real.logb 2 y
  let g := Real.logb 2 u
  let h := Real.logb 2 v
  have hx : 0<x := by dsimp [x]; positivity
  have hy : 0<y := by dsimp [y]; positivity
  have hu : (2:ℝ)≤u := by
    have hh : (2:ℝ)^2≤x := by
      have hcast : (2:ℝ)≤n := by exact_mod_cast hn
      dsimp [x]
      linarith
    simpa only [lg_two_pow,Nat.cast_ofNat] using lg_mono (by positivity) hh
  have huv : u≤v := lg_mono hx (by dsimp [x,y]; linarith)
  have hg : (1:ℝ)≤g := by
    have hh : (2:ℝ)^1≤u := by simpa only [pow_one] using hu
    simpa only [lg_two_pow,Nat.cast_one] using lg_mono (by positivity) hh
  have hgh : g≤h := lg_mono (by linarith) huv
  have hl : Real.logb 2 g≤Real.logb 2 h := lg_mono (by linarith) hgh
  have hr {s t : ℝ} (hs : 0≤s) (hst : s≤t) : s/(s+0.31)≤t/(t+0.31) :=
    (div_le_div_iff₀ (by linarith) (by linarith)).mpr (by nlinarith only [hst])
  change 1844+u*(4.986901*(g+Real.logb 2 g)+172) <
    v*(4.986901*(h+Real.logb 2 h)+192)+1880*(v/(v+0.31))
  by_cases hn' : 20≤n
  · have hv : (9:ℝ)/2≤v := by
      apply lg_lower (by decide) _ hy
      calc
        (2:ℝ)^9 ≤ 24^2 := by norm_num
        _ ≤ y^2 := by
          have hh : (20:ℝ)≤n := by exact_mod_cast hn'
          gcongr
          dsimp [y]
          linarith
    have hmain := mul_le_mul huv
      (show 4.986901*(g+Real.logb 2 g)+172≤4.986901*(h+Real.logb 2 h)+172 from by linarith)
      (by linarith [Real.logb_nonneg (by norm_num : (1:ℝ)<2) hg]) (by linarith)
    have hrat := hr (by norm_num : (0:ℝ)≤9/2) hv
    norm_num at hrat
    nlinarith only [hv,hmain,hrat]
  have hc := comparisonLog_cert hn (by omega)
  rcases htable : comparisonLogs n with ⟨⟨a,b,c⟩,⟨d,e,f⟩⟩
  unfold comparisonLogCheck at hc
  rw [htable] at hc
  obtain ⟨hd,he,hxa,hab,hbc,hyd,hde,hef,hnumeric⟩ := hc
  let rat (a : ℕ) : ℝ := (a:ℝ)/1000
  have rp (a : ℕ) (ha : 0<a) : 0<rat a := div_pos (by exact_mod_cast ha) (by norm_num)
  have upper {a : ℕ} {z : ℝ} (hz : 0<z) (hpow : z^1000≤(2:ℝ)^a) :
      Real.logb 2 z≤rat a := by
    have hp := lg_mono (pow_pos hz 1000) hpow
    rw [Real.logb_pow,lg_two_pow] at hp
    norm_num at hp
    exact (le_div_iff₀ (by norm_num)).mpr (by linarith)
  have up {a b : ℕ} (ha : 0<rat a) (hh : a^1000≤1000^1000*2^b) :
      Real.logb 2 (rat a)≤rat b := by
    apply upper ha
    dsimp [rat]
    rw [div_pow]
    exact (div_le_iff₀ (by positivity)).mpr (by
      rw [mul_comm]; exact_mod_cast hh)
  have low {a b : ℕ} (ha : 0<rat a) (hh : 1000^1000*2^b≤a^1000) :
      rat b≤Real.logb 2 (rat a) := by
    apply lg_lower (by decide) _ ha
    dsimp [rat]
    rw [div_pow]
    exact (le_div_iff₀ (by positivity)).mpr (by
      rw [mul_comm]; exact_mod_cast hh)
  have ha : u≤rat a := upper hx (by dsimp [x]; exact_mod_cast hxa)
  have hb : g≤rat b := (lg_mono (by linarith : 0<u) ha).trans (up (by linarith) hab)
  have hc : Real.logb 2 g≤rat c := (lg_mono (by linarith : 0<g) hb).trans (up (by linarith) hbc)
  have hD : rat d≤v := lg_lower (by decide) (by dsimp [y]; exact_mod_cast hyd) hy
  have hE : rat e≤h := (low (rp d hd) hde).trans (lg_mono (rp d hd) hD)
  have hF : rat f≤Real.logb 2 h := (low (rp e he) hef).trans (lg_mono (rp e he) hE)
  have hn' : 1844+rat a*(4.986901*(rat b+rat c)+172) <
      rat d*(4.986901*(rat e+rat f)+192)+1880*(rat d/(rat d+0.31)) := by
    have hcast : (1844+(a:ℝ)/1000*((4986901/1000000)*((b:ℝ)+c)/1000+172) <
        (d:ℝ)/1000*((4986901/1000000)*((e:ℝ)+f)/1000+192)+
          1880*((d:ℝ)/1000/((d:ℝ)/1000+31/100))) := by
      have hh := (Rat.cast_lt (K:=ℝ)).mpr hnumeric
      push_cast at hh
      exact hh
    convert hcast using 1 <;> unfold rat <;> ring
  have hleft : u*(4.986901*(g+Real.logb 2 g)+172)≤rat a*(4.986901*(rat b+rat c)+172) :=
    mul_le_mul ha (by linarith only [hb,hc])
      (by linarith [Real.logb_nonneg (by norm_num : (1:ℝ)<2) hg]) (by linarith)
  have hright : rat d*(4.986901*(rat e+rat f)+192)≤v*(4.986901*(h+Real.logb 2 h)+192) :=
    mul_le_mul hD (by linarith only [hE,hF]) (by dsimp [rat]; positivity) (by linarith)
  exact (add_le_add le_rfl hleft).trans_lt
    (hn'.trans_le (add_le_add hright (mul_le_mul_of_nonneg_left (hr (rp d hd).le hD) (by norm_num))))

theorem axisPublicBound_lt_previous {n : ℕ} (hn : 2≤n) :
    axisPublicBound n <
      (n + 4) ^ (4.986901 * (Real.logb 2 (Real.logb 2 (n + 4)) +
        Real.logb 2 (Real.logb 2 (Real.logb 2 (n + 4)))) +
        192 + 1880 / (Real.logb 2 (n + 4) + 0.31)) := by
  rw [axisPublicBound,ite_eq_right (by omega)]
  have hx : 0 < (n:ℝ)+2 := by positivity
  have hy : 0 < (n:ℝ)+4 := by positivity
  apply (Real.logb_lt_logb_iff (by norm_num : (1:ℝ)<2) (by positivity) (by positivity)).mp
  rw [Real.logb_mul (Real.rpow_pos_of_pos hx _).ne' (by norm_num),lg_two_pow,
    Real.logb_rpow_eq_mul_logb_of_pos hx,Real.logb_rpow_eq_mul_logb_of_pos hy]
  have h := axisLog_lt_previous hn
  convert h using 1 <;> ring

private theorem input_large_of_axis {n : ℕ} (h : 48 ≤ axisInputLog n) : 4 ≤ n := by
  by_contra! hn
  have hh : axisInputLog n ≤ axisInputLog 3 := by
    unfold axisInputLog
    exact Nat.log_mono_right (Nat.log_mono_right (by omega))
  have ht : axisInputLog 3 = 0 := by decide
  omega

theorem axisInputLog_cutoff {n j : ℕ} (hn : 4 ≤ n) :
    j ≤ axisInputLog n ↔ (2:ℕ)^(2^j) ≤ n := by
  have ha : 1 ≤ Nat.log 2 n :=
    (Nat.le_log_iff_pow_le (by decide) (by omega : n ≠ 0)).mpr (by omega)
  unfold axisInputLog
  rw [Nat.le_log_iff_pow_le (by decide) (by omega : Nat.log 2 n ≠ 0),
    Nat.le_log_iff_pow_le (by decide) (by omega : n ≠ 0)]

theorem compileAxis_explicit (T : LeanWang.TileSet) (hb : 48 ≤ axisInputLog T.length) :
    ((compileAxis T).length:ℝ) ≤
      (T.length+4)^(4.986901*(Real.logb 2 (Real.logb 2 (T.length+4)) +
        Real.logb 2 (Real.logb 2 (Real.logb 2 (T.length+4))))+19) := by
  have hn := input_large_of_axis hb
  let x : ℝ := (T.length:ℝ)+4
  let u := Real.logb 2 x
  let g := Real.logb 2 u
  let l := Real.logb 2 g
  let U := compileAxis T
  obtain ⟨hne,_,_,hs⟩ := compileAxis_correct T (by omega)
  have hp : 0 < (U.length:ℝ) := by exact_mod_cast List.length_pos_iff.mpr hne
  have hx : 0 < x := by dsimp [x]; positivity
  change (U.length:ℝ) ≤ x^(4.986901*(g+l)+19)
  apply (Real.logb_le_logb (show (1:ℝ)<2 by norm_num) hp (Real.rpow_pos_of_pos hx _)).mp
  change Real.logb 2 (U.length:ℝ) ≤ Real.logb 2 (x^(4.986901*(g+l)+19))
  rw [Real.logb_rpow_eq_mul_logb_of_pos hx]
  have hh := (lg_mono hp (Nat.cast_le.mpr hs)).trans (axisEstimate_log hn hb)
  exact hh.trans_eq (mul_comm ..)

private theorem axisPublicBound_of_log (T : LeanWang.TileSet) (hn : 2≤T.length)
    {U : Tile 3} (hU : U ≠ [])
    (hlog : let u := Real.logb 2 ((T.length:ℝ)+2)
      let g := Real.logb 2 u
      Real.logb 2 (U.length:ℝ) ≤ 1844+u*(4.986901*(g+Real.logb 2 g)+172)) :
    (U.length:ℝ) ≤ axisPublicBound T.length := by
  let x := (T.length:ℝ)+2
  let u := Real.logb 2 x
  let g := Real.logb 2 u
  have hp : 0 < (U.length:ℝ) := by exact_mod_cast List.length_pos_iff.mpr hU
  have hx : 0 < x := by dsimp [x]; positivity
  rw [axisPublicBound,ite_eq_right (by omega)]
  change _ ≤ x^(4.986901*(g+Real.logb 2 g)+172)*(2:ℝ)^1844
  have hq : 0 < x^(4.986901*(g+Real.logb 2 g)+172)*(2:ℝ)^1844 :=
    mul_pos (Real.rpow_pos_of_pos hx _) (by positivity)
  apply (Real.logb_le_logb (by norm_num : (1:ℝ)<2) hp hq).mp
  rw [Real.logb_mul (Real.rpow_pos_of_pos hx _).ne' (by norm_num), lg_two_pow,
    Real.logb_rpow_eq_mul_logb_of_pos hx]
  exact hlog.trans_eq (by change _ = (4.986901*(g+Real.logb 2 g)+172)*u+1844; ring)

private theorem axis_small_public (T : LeanWang.TileSet) (hb : axisInputLog T.length < 48)
    (hr : ¬ (65536≤T.length ∧ T.length<(2:ℕ)^64)) :
    ((compileCompactSlot T).length:ℝ) ≤ axisPublicBound T.length := by
  by_cases hn : T.length ≤ 1
  · have h := (compileSlotTotal_facts T).2.2.2
    simpa only [compileCompactSlot,ite_eq_right (by omega : ¬ (10 ≤ T.length ∧ T.length ≤ 729)),
      axisPublicBound,slotExplicitBound,ite_eq_left hn] using h
  have hp := (compileCompactSlot_correct T).1
  apply axisPublicBound_of_log T (by omega) hp
  by_cases hlo : T.length<65536
  · exact compileCompactSlot_small_log (by omega) hlo
  have hn64 : (2:ℕ)^64≤T.length := by omega
  have hsame : compileCompactSlot T = compileSlot T := by
    simp [compileCompactSlot,compileSlotTotal,nonemptyInput,
      show ¬ (10 ≤ T.length ∧ T.length ≤ 729) by omega,
      show T.length ≠ 0 by omega]
  rw [hsame]
  have hpos : 0 < ((compileSlot T).length:ℝ) := by
    exact_mod_cast List.length_pos_iff.mpr (hsame ▸ hp)
  exact (lg_mono hpos (Nat.cast_le.mpr (compileSlot_large_sharp T (by omega)))).trans
    (slotSharpEstimate_log hn64 hb)

private theorem axis_large_public (T : LeanWang.TileSet) (hb : 48≤axisInputLog T.length)
    (hU : compileAxis T ≠ []) :
    ((compileAxis T).length:ℝ) ≤ axisPublicBound T.length := by
  have hn := input_large_of_axis hb
  let x := (T.length:ℝ)+2
  let y := (T.length:ℝ)+4
  let u := Real.logb 2 x
  let v := Real.logb 2 y
  let g := Real.logb 2 u
  let f := Real.logb 2 v
  let s := g+Real.logb 2 g
  let r := f+Real.logb 2 f
  have hx : 0 < x := by dsimp [x]; positivity
  have hy : 0 < y := by dsimp [y]; positivity
  have hu : (2:ℝ)≤u := by
    have hh : (2:ℝ)^2≤x := by
      have h : (2:ℝ)≤T.length := by exact_mod_cast (by omega : 2≤T.length)
      dsimp [x]
      linarith
    simpa only [lg_two_pow,Nat.cast_ofNat] using lg_mono (by positivity) hh
  have hvu : u≤v := lg_mono hx (by dsimp [x,y]; linarith)
  have hv : v≤u+1 := by
    have hm := lg_mono hy (show y≤2*x by dsimp [x,y]; linarith [Nat.cast_nonneg (α:=ℝ) T.length])
    rwa [Real.logb_mul (by norm_num) hx.ne',Real.logb_self_eq_one (by norm_num),add_comm (1:ℝ)] at hm
  have hg : 1≤g := by
    have hh : (2:ℝ)^1≤u := by simpa only [pow_one] using hu
    simpa only [lg_two_pow,Nat.cast_one] using lg_mono (by positivity) hh
  have hfg : g≤f := lg_mono (by linarith) hvu
  have hgf : f≤g+1 := by
    have hm := lg_mono (by linarith : 0<v) (show v≤2*u by linarith)
    rwa [Real.logb_mul (by norm_num) (by linarith : u≠0),
      Real.logb_self_eq_one (by norm_num),add_comm (1:ℝ)] at hm
  have hil : Real.logb 2 f≤Real.logb 2 g+1 := by
    have hm := lg_mono (by linarith : 0<f) (show f≤2*g by linarith)
    rwa [Real.logb_mul (by norm_num) (by linarith : g≠0),
      Real.logb_self_eq_one (by norm_num),add_comm (1:ℝ)] at hm
  have hlog_le {z : ℝ} (hz : 1≤z) : Real.logb 2 z≤2*(z-1) := by
    have he := lg_tangent (a:=1) (by norm_num) (show 0<z by linarith)
    simp only [Real.logb_one, zero_add,div_one] at he
    refine he.trans ((div_le_iff₀ (Real.log_pos (by norm_num))).mpr ?_)
    have hab := mul_le_mul_of_nonneg_left (show (1:ℝ)≤2*Real.log 2 by
      linarith [Real.log_two_gt_d9]) (show 0≤z-1 by linarith)
    nlinarith only [hab]
  have hs : s≤6*u := by
    dsimp only [s]
    linarith only [hlog_le hg, hlog_le (by linarith : 1≤u)]
  have hr : r≤s+2 := by dsimp only [r,s]; linarith
  have hr₀ : 0≤r := by
    dsimp only [r]
    linarith [Real.logb_nonneg (by norm_num : (1:ℝ)<2) (show 1≤f by linarith)]
  have hbound : v*(4.986901*r+19) ≤ 1844+u*(4.986901*s+172) := by
    have hh := mul_le_mul hv (show 4.986901*r+19≤4.986901*(s+2)+19 by linarith)
      (by linarith : 0≤4.986901*r+19) (by linarith : 0≤u+1)
    nlinarith only [hh,hs,hu]
  have hp : 0 < ((compileAxis T).length:ℝ) := by
    exact_mod_cast List.length_pos_iff.mpr hU
  apply axisPublicBound_of_log T (by omega) hU
  have he := lg_mono hp (compileAxis_explicit T hb)
  rw [Real.logb_rpow_eq_mul_logb_of_pos hy] at he
  exact (he.trans_eq (mul_comm ..)).trans hbound

/-- Both slot layouts use the guarded Sudoku construction. Large alphabets use
two CRT axes per Wang slot. -/
def compileAxisTotal (T : LeanWang.TileSet) : Tile 3 :=
  if 48 ≤ axisInputLog T.length then compileAxis T
  else if 65536≤T.length ∧ T.length<(2:ℕ)^64 then
    compileSlotWith T (ternarySlotDigits T.length) 1 1
  else compileCompactSlot T

theorem compileAxisTotal_large_bound (T : LeanWang.TileSet) {j : ℕ}
    (hj : 48 ≤ j) (hn : 2^(2^j) ≤ T.length) :
    ((compileAxisTotal T).length:ℝ) ≤
      (T.length+4)^(4.986901*(Real.logb 2 (Real.logb 2 (T.length+4)) +
        Real.logb 2 (Real.logb 2 (Real.logb 2 (T.length+4))))+19) := by
  have hpow : 2 ≤ (2:ℕ)^j := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) (show 1 ≤ j by omega)
  have hcut : (4:ℕ) ≤ 2^(2^j) :=
    (show (2:ℕ)^2 ≤ 2^(2^j) from Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) hpow)
  have hb := hj.trans ((axisInputLog_cutoff (j:=j) (hcut.trans hn)).mpr hn)
  rw [compileAxisTotal,ite_eq_left hb]
  exact compileAxis_explicit T hb

theorem compileAxisTotal_computable : Computable compileAxisTotal := by
  have hl := natLog_primrec 2 (by decide)
  have h : Primrec (fun T : LeanWang.TileSet => decide (48 ≤ axisInputLog T.length)) := by
    unfold axisInputLog
    fun_prop
  let hold (T : LeanWang.TileSet) := decide (65536≤T.length ∧ T.length<(2:ℕ)^64)
  have hguard : Primrec hold := by
    unfold hold
    have h64 : Primrec (fun _ : LeanWang.TileSet => (2:ℕ)^64) := Primrec.const _
    fun_prop
  have hd := ternarySlotDigits_primrec.comp (Primrec.list_length : Primrec (List.length : LeanWang.TileSet → ℕ))
  have hargs : Primrec (fun T : LeanWang.TileSet => (T,ternarySlotDigits T.length,(1:ℕ),(1:ℕ))) :=
    Primrec.id.pair (hd.pair (Primrec.const _))
  have ht := compileSlotWith_computable.comp hargs.to_comp
  exact (Computable.cond h.to_comp compileAxis_computable
    (Computable.cond hguard.to_comp ht compileCompactSlot_computable)).of_eq (by
      intro T
      by_cases h₁ : 48≤axisInputLog T.length
      · simp [compileAxisTotal,h₁]
      · by_cases h₂ : 65536≤T.length ∧ T.length<(2:ℕ)^64 <;> simp [compileAxisTotal,hold,h₁,h₂])

theorem compileAxisTotal_facts (T : LeanWang.TileSet) :
    compileAxisTotal T ≠ [] ∧ FaceConnected (compileAxisTotal T) ∧
      (LeanWang.TilesPlane T ↔ TranslationTiling.Tiles (compileAxisTotal T)) ∧
      ((compileAxisTotal T).length : ℝ) ≤ axisPublicBound T.length := by
  unfold compileAxisTotal
  split
  · rename_i hb
    have hn := input_large_of_axis hb
    obtain ⟨hne,hconn,hiff,_⟩ := compileAxis_correct T (by omega)
    exact ⟨hne,hconn,hiff,axis_large_public T hb hne⟩
  · rename_i hb
    split
    · rename_i hr
      obtain ⟨hne,hconn,hiff,hsize⟩ := ternarySlot_log (T:=T) hr.1 hr.2
      exact ⟨hne,hconn,hiff,axisPublicBound_of_log T (by omega) hne hsize⟩
    · rename_i hr
      obtain ⟨hne,hconn,hiff⟩ := compileCompactSlot_correct T
      exact ⟨hne,hconn,hiff,axis_small_public T (by omega) hr⟩

theorem compileAxisTotal_public_bound (T : LeanWang.TileSet) :
    ((compileAxisTotal T).length : ℝ) ≤ axisPublicBound T.length :=
  (compileAxisTotal_facts T).2.2.2

end
end TranslationTiling.Compiler.Size
