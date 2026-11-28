import TranslationTiling.Compiler.AxisSlotComputability
import TranslationTiling.Compiler.AxisSlotLogBound
import TranslationTiling.Compiler.SlotExplicitBound

namespace TranslationTiling.Compiler.Size

open FiniteCompiler.Packed FiniteCompiler.Effective Compiler.Effective

noncomputable section

def axisPublicBound (n : ℕ) : ℝ :=
  if n ≤ 1 then 2^2055 else
    (n + 4) ^ (4.986901 * (Real.logb 2 (Real.logb 2 (n + 4)) +
      Real.logb 2 (Real.logb 2 (Real.logb 2 (n + 4)))) + 247 + 1539 / Real.logb 2 (n + 4))

theorem axisPublicBound_lt_previous {n : ℕ} (hn : 2 ≤ n) :
    axisPublicBound n <
      (n + 4) ^ (4.986901 * (Real.logb 2 (Real.logb 2 (n + 4)) +
        Real.logb 2 (Real.logb 2 (Real.logb 2 (n + 4)))) + 331 + 1322 / Real.logb 2 (n + 4)) := by
  let x := (n:ℝ)+4
  let u := Real.logb 2 x
  have hx : (6:ℝ) ≤ x := by
    dsimp [x]
    linarith [show (2:ℝ) ≤ n by exact_mod_cast hn]
  have hu : (137:ℝ)/53 ≤ u :=
    (lg_lower (a := 137) (b := 53) (by decide)
      (by norm_num : (2:ℝ)^137 ≤ (6:ℝ)^53) (by norm_num)).trans (lg_mono (by norm_num) hx)
  rw [axisPublicBound,ite_eq_right (by omega)]
  apply Real.rpow_lt_rpow_of_exponent_lt (by change 1 < x; linarith)
  have h : (217:ℝ)/u < 84 := (div_lt_iff₀ (by linarith : 0 < u)).mpr (by linarith)
  rw [show (217:ℝ) = 1539-1322 by norm_num, sub_div] at h
  change _ + 247 + 1539/u < _ + 331 + 1322/u
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
      1539+u*(4.986901*(g+Real.logb 2 g)+247) := by
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
  change _ ≤ 1539+u*(4.986901*(g+l)+247)
  by_cases h : axisInputLog n = 4
  · have hq := compileSlot_widthEight T hn h
    have hrate : 6*4.986901+247 ≤ 4.986901*(g+l)+247 := by linarith
    have compare {e : ℕ} {v : ℝ} (he : (compileSlot T).length ≤ 2^e)
        (hv : v ≤ u) (he' : (e:ℝ) ≤ 1539+v*(6*4.986901+247)) :
        Real.logb 2 ((compileSlot T).length:ℝ) ≤ 1539+u*(4.986901*(g+l)+247) := by
      have hh := lg_mono hlog (show ((compileSlot T).length:ℝ) ≤ (2:ℝ)^e by exact_mod_cast he)
      rw [lg_two_pow] at hh
      have hc := mul_le_mul hv hrate (by norm_num) (show 0 ≤ u by linarith)
      linarith only [hh,he',hc]
    by_cases hk : T.length ≤ 20412^2
    · exact compare (by simpa only [ite_eq_left hk] using hq : (compileSlot T).length ≤ 2^5500)
        hu16 (by norm_num)
    · have hu28 : 28 ≤ u := by
        have hh : (2:ℝ)^28 ≤ x := by
          have hk' : (20412:ℝ)^2 ≤ (n:ℝ) := by exact_mod_cast (le_of_not_ge hk)
          have hp : (2:ℝ)^28 ≤ (20412:ℝ)^2 := by norm_num
          exact hp.trans (hk'.trans (by dsimp [x]; linarith))
        have h := lg_mono (by norm_num : 0 < (2:ℝ)^28) hh
        rwa [lg_two_pow] at h
      exact compare (by simpa only [ite_eq_right hk] using hq : (compileSlot T).length ≤ 2^7020)
        hu28 (by norm_num)
  · have hc := lg_mono hlog (Nat.cast_le.mpr (compileSlot_large T (by omega : 28 ≤ T.length)))
    have he := slotRefinedEstimate_log_at hn
    have hh : 5 ≤ Nat.log 2 (Nat.log 2 T.length) ∧ Nat.log 2 (Nat.log 2 T.length) < 48 :=
      ⟨by change 5 ≤ axisInputLog n; omega, hb⟩
    simp only [ite_eq_left hh] at he
    change _ ≤ 1322+u*(5*g+5*l+246) at he
    have hp : 5*g+5*l+246 ≤ 4.986901*(g+l)+247 := by linarith only [hg',hb',hl6]
    exact (hc.trans he).trans (by linarith only [mul_le_mul_of_nonneg_left hp (show 0 ≤ u by linarith)])

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
      1539+u*(4.986901*(g+l)+247) := by
    by_cases h : 65536 ≤ T.length
    · exact axis_small_log T h hb
    · exact compileCompactSlot_small_log (by omega) (by omega)
  have hU : 0 < ((compileCompactSlot T).length:ℝ) := by
    exact_mod_cast List.length_pos_iff.mpr (compileCompactSlot_correct T).1
  have hx : 0 < x := by dsimp [x]; positivity
  have hu : 0 < u := Real.logb_pos (by norm_num) (by dsimp [x]; linarith [Nat.cast_nonneg (α := ℝ) T.length])
  rw [axisPublicBound,ite_eq_right hn]
  change _ ≤ x^(4.986901*(g+l)+247+1539/u)
  apply (Real.logb_le_logb (by norm_num : (1:ℝ) < 2) hU (Real.rpow_pos_of_pos hx _)).mp
  rw [Real.logb_rpow_eq_mul_logb_of_pos hx]
  change _ ≤ (4.986901*(g+l)+247+1539/u)*u
  rw [add_mul,div_mul_cancel₀ _ hu.ne']
  linarith only [hlog, mul_comm (4.986901*(g+l)+247) u]

theorem compileAxis_explicit (T : LeanWang.TileSet) (hb : 48 ≤ axisInputLog T.length) :
    ((compileAxis T).length:ℝ) ≤
      (T.length+4)^(4.986901*(Real.logb 2 (Real.logb 2 (T.length+4)) +
        Real.logb 2 (Real.logb 2 (Real.logb 2 (T.length+4))))+64) := by
  have hn := input_large_of_axis hb
  let x : ℝ := (T.length:ℝ)+4
  let u := Real.logb 2 x
  let g := Real.logb 2 u
  let l := Real.logb 2 g
  let U := compileAxis T
  obtain ⟨hne,_,_,hs⟩ := compileAxis_correct T (by omega)
  have hp : 0 < (U.length:ℝ) := by exact_mod_cast List.length_pos_iff.mpr hne
  have hx : 0 < x := by dsimp [x]; positivity
  change (U.length:ℝ) ≤ x^(4.986901*(g+l)+64)
  apply (Real.logb_le_logb (show (1:ℝ)<2 by norm_num) hp (Real.rpow_pos_of_pos hx _)).mp
  change Real.logb 2 (U.length:ℝ) ≤ Real.logb 2 (x^(4.986901*(g+l)+64))
  rw [Real.logb_rpow_eq_mul_logb_of_pos hx]
  have hh := (lg_mono hp (Nat.cast_le.mpr hs)).trans (axisEstimate_log hn hb)
  exact hh.trans_eq (mul_comm ..)

/-- Both slot layouts use the guarded Sudoku construction. Large alphabets use
two CRT axes per Wang slot. -/
def compileAxisTotal (T : LeanWang.TileSet) : Tile 3 :=
  if 48 ≤ axisInputLog T.length then compileAxis T else compileCompactSlot T

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
      linarith [div_nonneg (show (0:ℝ) ≤ 1539 by norm_num) h.le]
  · rename_i hb
    obtain ⟨hne,hconn,hiff⟩ := compileCompactSlot_correct T
    exact ⟨hne,hconn,hiff,axis_small_public T (by omega)⟩

theorem compileAxisTotal_public_bound (T : LeanWang.TileSet) :
    ((compileAxisTotal T).length : ℝ) ≤ axisPublicBound T.length :=
  (compileAxisTotal_facts T).2.2.2

end
end TranslationTiling.Compiler.Size
