import TranslationTiling.Compiler.AxisSlotComputability
import TranslationTiling.Compiler.AxisSlotLogBound
import TranslationTiling.Compiler.SlotExplicitBound

namespace TranslationTiling.Compiler.Size

open FiniteCompiler.Packed FiniteCompiler.Effective Compiler.Effective

noncomputable section

def axisPublicBound (n : ℕ) : ℝ :=
  if n ≤ 1 then 2^2055 else
    (n + 4) ^ (4.986901 * (Real.logb 2 (Real.logb 2 (n + 4)) +
      Real.logb 2 (Real.logb 2 (Real.logb 2 (n + 4)))) +
      192 + 1880 / (Real.logb 2 (n + 4) + 0.31))

theorem axisPublicBound_lt_previous {n : ℕ} (hn : 2 ≤ n) :
    axisPublicBound n <
      (n + 4) ^ (4.986901 * (Real.logb 2 (Real.logb 2 (n + 4)) +
        Real.logb 2 (Real.logb 2 (Real.logb 2 (n + 4)))) + 247 + 1539 / Real.logb 2 (n + 4)) := by
  let x := (n:ℝ)+4
  let u := Real.logb 2 x
  have hx : 1 < x := by dsimp [x]; linarith [Nat.cast_nonneg (α := ℝ) n]
  have hu : 0 < u := Real.logb_pos (by norm_num) hx
  have hv : 0 < u+0.31 := by linarith
  rw [axisPublicBound,ite_eq_right (by omega)]
  apply Real.rpow_lt_rpow_of_exponent_lt hx
  change _ + 192 + 1880/(u+0.31) < _ + 247 + 1539/u
  have h : 1880/(u+0.31) < 55+1539/u := by
    apply (div_lt_iff₀ hv).mpr
    have hp : 1880*u < (55*u+1539)*(u+0.31) := by
      nlinarith only [sq_nonneg (110*u-323.95)]
    convert (div_lt_div_iff_of_pos_right hu).mpr hp using 1
    · field_simp
    · field_simp
  linarith only [h]

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

private theorem axis_small_log (T : LeanWang.TileSet) (hn : 65536 ≤ T.length)
    (hb : axisInputLog T.length < 48) :
    let u := Real.logb 2 ((T.length:ℝ)+4)
    let g := Real.logb 2 u
    Real.logb 2 ((compileCompactSlot T).length:ℝ) ≤
      u*(4.986901*(g+Real.logb 2 g)+192)+1880*(u/(u+0.31)) := by
  let n := T.length
  let x := (n:ℝ)+4
  let u := Real.logb 2 x
  let g := Real.logb 2 u
  let l := Real.logb 2 g
  have hU : compileCompactSlot T = compileSlot T := by
    simp [compileCompactSlot,compileSlotTotal,nonemptyInput,show n ≠ 0 by omega,
      show ¬ (10 ≤ n ∧ n ≤ 729) by omega,n]
  rw [hU]
  have ⟨hg,hg'⟩ := axis_log_comparison n (by omega)
  change (axisInputLog n:ℝ) ≤ g at hg
  change g < (axisInputLog n:ℝ)+2 at hg'
  change axisInputLog n < 48 at hb
  have hb' : (axisInputLog n:ℝ) ≤ 47 := by exact_mod_cast (Nat.le_of_lt_succ hb)
  have hb4 : 4 ≤ axisInputLog n := (axisInputLog_cutoff (by omega : 4 ≤ n)).mpr (by norm_num; exact hn)
  have hg4 : 4 ≤ g := (Nat.cast_le.mpr hb4 : (4:ℝ) ≤ axisInputLog n).trans hg
  have hlog : 0 < ((compileSlot T).length:ℝ) := by
    exact_mod_cast List.length_pos_iff.mpr (compileSlot_correct T (by omega)).1
  have hl2 : 2 ≤ l := by
    have hh := lg_mono (by norm_num : 0 < (2:ℝ)^2) (show (2:ℝ)^2 ≤ g by norm_num; exact hg4)
    rwa [lg_two_pow] at hh
  have hl6 : l ≤ 6 := by
    have hh := lg_mono (by linarith : 0 < g) (show g ≤ (2:ℝ)^6 by norm_num; linarith)
    rwa [lg_two_pow] at hh
  have hu16 : 16 ≤ u := by
    have h := lg_mono (by norm_num : 0 < (2:ℝ)^16) (show (2:ℝ)^16 ≤ x by
      have hnR : (65536:ℝ) ≤ n := by exact_mod_cast hn
      dsimp [x]; norm_num; linarith)
    rw [lg_two_pow] at h
    exact_mod_cast h
  change _ ≤ u*(4.986901*(g+l)+192)+1880*(u/(u+0.31))
  by_cases h : axisInputLog n < 6
  · have ht : wideSlotLength n = 2 := by
      have hh : axisInputLog n = 4 ∨ axisInputLog n = 5 := by omega
      change max 1 (axisInputLog n * Nat.log 2 (axisInputLog n)/4) = 2
      rcases hh with hh | hh <;> rw [hh] <;> decide
    have hn64 : n < 2^64 := by
      by_contra! hh
      have hz := (axisInputLog_cutoff (j := 6) (by omega : 4 ≤ n)).mpr
        (by norm_num; exact hh)
      omega
    let k := slotPackedDigits n 2
    have hdim : compileSlot T = compileSlotWith T k 8 6 := by
      rw [compileSlot_wide T (by omega)]
      change compileSlotWith T (slotPackedDigits n (wideSlotLength n))
        (4*wideSlotLength n) (3*wideSlotLength n) = _
      rw [ht]
    have hD : slotRadix 8 6 = 20412 := by decide
    have hkdef : k = max 1 (Nat.clog 20412 n) := by
      change max 1 (Nat.clog (slotRadix 8 6) n) = _
      rw [hD]
    have hk2 : 2 ≤ k := by
      rw [hkdef]
      by_contra! hh
      have hd := (Nat.clog_le_iff_le_pow (by decide : 1 < 20412)).mp
        (show Nat.clog 20412 n ≤ 1 by omega)
      omega
    have hk5 : k ≤ 5 := by
      rw [hkdef]
      exact max_le (by decide) ((Nat.clog_le_iff_le_pow (by decide : 1 < 20412)).mpr
        (hn64.le.trans (by decide)))
    have hkcap : n ≤ 20412^k := by
      rw [hkdef]
      exact (Nat.clog_le_iff_le_pow (by decide : 1 < 20412)).mp (le_max_right ..)
    have he : (compileSlot T).length ≤ 2^widthEightExponent k := by
      by_cases hk : k = 2
      · rw [hdim,hk]
        exact compileSlotWith_widthEight_bound T (by omega) (hk ▸ hkcap)
      · have h := compileSlot_large T (by omega : 28 ≤ T.length)
        change _ ≤ slotRefinedEstimate (slotPackedDigits n (wideSlotLength n))
          (4*wideSlotLength n) (3*wideSlotLength n) at h
        rw [ht] at h
        exact h.trans (slotRefinedEstimate_widthEight (by omega) hk5)
    have hle := lg_mono hlog (show ((compileSlot T).length:ℝ) ≤ (2:ℝ)^widthEightExponent k by
      exact_mod_cast he)
    rw [lg_two_pow] at hle
    have huK : (14*(k-1):ℕ) ≤ u := by
      have hkn : Nat.clog 20412 n = k := by
        rw [hkdef] at hk2 ⊢
        exact (max_eq_right (by omega : 1 ≤ Nat.clog 20412 n)).symm
      have hd := (Nat.pow_pred_clog_lt_self (by decide : 1 < 20412) (by omega : 1 < n)).le
      rw [hkn] at hd
      have hp : (2:ℕ)^(14*(k-1)) ≤ n := by
        rw [pow_mul]
        exact (Nat.pow_le_pow_left (by decide : 2^14 ≤ 20412) _).trans hd
      exact (Nat.cast_le.mpr ((Nat.le_log_iff_pow_le (by decide) (by omega : n ≠ 0)).mpr hp)).trans
        ((lg_natLog_le (by omega : 0 < n)).trans (lg_mono (by positivity : 0 < (n:ℝ)) (by
          dsimp [x]; linarith)))
    have hrate : 6*4.986901+192 ≤ 4.986901*(g+l)+192 := by linarith
    have compare {v : ℝ} (hv : v ≤ u) (hv0 : 0 ≤ v)
        (he' : (widthEightExponent k:ℝ) ≤ v*(6*4.986901+192)+1880*(v/(v+0.31))) :
        Real.logb 2 ((compileSlot T).length:ℝ) ≤
          u*(4.986901*(g+l)+192)+1880*(u/(u+0.31)) := by
      have hratio : v/(v+0.31) ≤ u/(u+0.31) :=
        (div_le_div_iff₀ (by linarith) (by linarith)).mpr (by nlinarith only [hv])
      exact hle.trans (he'.trans (add_le_add
        (mul_le_mul hv hrate (by norm_num) (by linarith))
        (mul_le_mul_of_nonneg_left hratio (by norm_num))))
    interval_cases k
    · exact compare hu16 (by norm_num) (by norm_num [widthEightExponent])
    · exact compare (by norm_num at huK; exact huK : 28 ≤ u) (by norm_num)
        (by norm_num [widthEightExponent])
    · exact compare (by norm_num at huK; exact huK : 42 ≤ u) (by norm_num)
        (by norm_num [widthEightExponent])
    · exact compare (by norm_num at huK; exact huK : 56 ≤ u) (by norm_num)
        (by norm_num [widthEightExponent])
  · have hc := lg_mono hlog (Nat.cast_le.mpr (compileSlot_large T (by omega : 28 ≤ T.length)))
    have he := slotRefinedEstimate_moderate_log hn (by change 6 ≤ axisInputLog n; omega) hb
    change _ ≤ 1322+u*(5*g+5*l+191) at he
    have hp : 5*g+5*l+191 ≤ 4.986901*(g+l)+192 := by linarith only [hg',hb',hl6]
    have hq : 1322 ≤ 1880*(u/(u+0.31)) := by
      rw [← mul_div_assoc]
      exact (le_div_iff₀ (by linarith)).mpr (by linarith)
    exact (hc.trans he).trans (by linarith only [hq,mul_le_mul_of_nonneg_left hp (by linarith : 0 ≤ u)])

private theorem axis_small_public (T : LeanWang.TileSet) (hb : axisInputLog T.length < 48) :
    ((compileCompactSlot T).length:ℝ) ≤ axisPublicBound T.length := by
  by_cases hn : T.length ≤ 1
  · have h := (compileSlotTotal_facts T).2.2.2
    simpa only [compileCompactSlot,ite_eq_right (by omega : ¬ (10 ≤ T.length ∧ T.length ≤ 729)),
      axisPublicBound,slotExplicitBound,ite_eq_left hn] using h
  let x := (T.length:ℝ)+4
  let u := Real.logb 2 x
  let g := Real.logb 2 u
  let l := Real.logb 2 g
  have hlog : Real.logb 2 ((compileCompactSlot T).length:ℝ) ≤
      u*(4.986901*(g+l)+192)+1880*(u/(u+0.31)) := by
    by_cases h : 65536 ≤ T.length
    · exact axis_small_log T h hb
    · exact compileCompactSlot_small_log (by omega) (by omega)
  have hU : 0 < ((compileCompactSlot T).length:ℝ) := by
    exact_mod_cast List.length_pos_iff.mpr (compileCompactSlot_correct T).1
  have hx : 0 < x := by dsimp [x]; positivity
  have hu : 0 < u := Real.logb_pos (by norm_num) (by dsimp [x]; linarith [Nat.cast_nonneg (α := ℝ) T.length])
  rw [axisPublicBound,ite_eq_right hn]
  change _ ≤ x^(4.986901*(g+l)+192+1880/(u+0.31))
  apply (Real.logb_le_logb (by norm_num : (1:ℝ) < 2) hU (Real.rpow_pos_of_pos hx _)).mp
  rw [Real.logb_rpow_eq_mul_logb_of_pos hx]
  change _ ≤ (4.986901*(g+l)+192+1880/(u+0.31))*u
  convert hlog using 1
  ring

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

/-- Both slot layouts use the guarded Sudoku construction. Large alphabets use
two CRT axes per Wang slot. -/
def compileAxisTotal (T : LeanWang.TileSet) : Tile 3 :=
  if 48 ≤ axisInputLog T.length then compileAxis T else compileCompactSlot T

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
  exact (Computable.cond h.to_comp compileAxis_computable compileCompactSlot_computable).of_eq
    (by intro T; by_cases h : 48 ≤ axisInputLog T.length <;> simp [compileAxisTotal,h])

theorem compileAxisTotal_facts (T : LeanWang.TileSet) :
    compileAxisTotal T ≠ [] ∧ FaceConnected (compileAxisTotal T) ∧
      (LeanWang.TilesPlane T ↔ TranslationTiling.Tiles (compileAxisTotal T)) ∧
      ((compileAxisTotal T).length : ℝ) ≤ axisPublicBound T.length := by
  unfold compileAxisTotal
  split
  · rename_i hb
    have hn := input_large_of_axis hb
    obtain ⟨hne,hconn,hiff,_⟩ := compileAxis_correct T (by omega)
    refine ⟨hne,hconn,hiff,(compileAxis_explicit T hb).trans ?_⟩
    rw [axisPublicBound,ite_eq_right (by omega)]
    apply Real.rpow_le_rpow_of_exponent_le
    · have h : (0:ℝ) ≤ T.length := by positivity
      linarith
    · have hx : (1:ℝ) < (T.length:ℝ)+4 := by linarith [Nat.cast_nonneg (α := ℝ) T.length]
      have h := Real.logb_pos (by norm_num : (1:ℝ)<2) hx
      linarith [div_nonneg (show (0:ℝ) ≤ 1880 by norm_num) (by linarith : 0 ≤ Real.logb 2 ((T.length:ℝ)+4)+0.31)]
  · rename_i hb
    obtain ⟨hne,hconn,hiff⟩ := compileCompactSlot_correct T
    exact ⟨hne,hconn,hiff,axis_small_public T (by omega)⟩

theorem compileAxisTotal_public_bound (T : LeanWang.TileSet) :
    ((compileAxisTotal T).length : ℝ) ≤ axisPublicBound T.length :=
  (compileAxisTotal_facts T).2.2.2

end
end TranslationTiling.Compiler.Size
