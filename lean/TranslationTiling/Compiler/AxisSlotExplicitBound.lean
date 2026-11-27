import TranslationTiling.Compiler.AxisSlotComputability
import TranslationTiling.Compiler.AxisSlotLogBound
import TranslationTiling.Compiler.SlotExplicitBound

namespace TranslationTiling.Compiler.Size

open FiniteCompiler.Packed FiniteCompiler.Effective Compiler.Effective

noncomputable section

def axisPublicBound (n : ℕ) : ℝ :=
  if n ≤ 1 then 2^2055 else
    (n + 4) ^ (4.986901 * (Real.logb 2 (Real.logb 2 (n + 4)) +
      Real.logb 2 (Real.logb 2 (Real.logb 2 (n + 4)))) + 331 + 1322 / Real.logb 2 (n + 4))

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

private theorem axis_small_public {n : ℕ} (h : axisInputLog n < 48) :
    slotExplicitBound n ≤ axisPublicBound n := by
  by_cases h₁ : n ≤ 1
  · simp [slotExplicitBound,axisPublicBound,h₁]
  rw [slotExplicitBound,axisPublicBound,ite_eq_right h₁,ite_eq_right h₁]
  let x : ℝ := (n:ℝ)+4
  let u := Real.logb 2 x
  let g := Real.logb 2 u
  let l := Real.logb 2 g
  have hx : 4 ≤ x := by dsimp [x]; linarith [Nat.cast_nonneg (α := ℝ) n]
  have hu : 2 ≤ u := by
    have hh := lg_mono (by norm_num : 0 < (4:ℝ)) hx
    rw [show (4:ℝ) = (2:ℝ)^2 by norm_num,lg_two_pow] at hh
    exact_mod_cast hh
  have hg : 1 ≤ g := by
    have hh := lg_mono (by norm_num : 0 < (2:ℝ)) hu
    rwa [Real.logb_self_eq_one (by norm_num)] at hh
  have hg' : g < 49 := by
    by_cases h4 : 4 ≤ n
    · have ht := (axis_log_comparison n h4).2
      change g < (axisInputLog n:ℝ)+2 at ht
      have hb : (axisInputLog n:ℝ) ≤ 47 := by exact_mod_cast (by omega : axisInputLog n ≤ 47)
      linarith
    · have hx' : x ≤ 8 := by
        have hn : (n:ℝ) ≤ 3 := by exact_mod_cast (by omega : n ≤ 3)
        dsimp [x]; linarith
      have hu' : u ≤ 3 := by
        have hh := lg_mono (by linarith : 0 < x) hx'
        rw [show (8:ℝ) = (2:ℝ)^3 by norm_num,lg_two_pow] at hh
        exact_mod_cast hh
      have hh := lg_mono (by linarith : 0 < u) (show u ≤ (2:ℝ)^2 by linarith)
      rw [lg_two_pow] at hh
      change g < 49
      norm_num at hh
      linarith
  have hl : l ≤ 6 := by
    have hh := lg_mono (by linarith : 0 < g) (show g ≤ (2:ℝ)^6 by norm_num; linarith)
    rw [lg_two_pow] at hh
    exact_mod_cast hh
  change x^(5*g+5*l+330+1322/u) ≤ x^(4.986901*(g+l)+331+1322/u)
  exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith only [hg',hl])

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

/-- Both widths use the guarded Sudoku construction. Large alphabets use
two CRT axes per Wang slot. -/
def compileAxisTotal (T : LeanWang.TileSet) : Tile 3 :=
  if 48 ≤ axisInputLog T.length then compileAxis T else compileSlotTotal T

theorem compileAxisTotal_computable : Computable compileAxisTotal := by
  have hl := natLog_primrec 2 (by decide)
  have h : Primrec (fun T : LeanWang.TileSet => decide (48 ≤ axisInputLog T.length)) := by
    unfold axisInputLog
    fun_prop
  exact (Computable.cond h.to_comp compileAxis_computable compileSlotTotal_computable).of_eq
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
      linarith [div_nonneg (show (0:ℝ) ≤ 1322 by norm_num) h.le]
  · rename_i hb
    obtain ⟨hne,hconn,hiff,hb'⟩ := compileSlotTotal_facts T
    exact ⟨hne,hconn,hiff,hb'.trans (axis_small_public (by omega))⟩

theorem compileAxisTotal_public_bound (T : LeanWang.TileSet) :
    ((compileAxisTotal T).length : ℝ) ≤ axisPublicBound T.length :=
  (compileAxisTotal_facts T).2.2.2

end
end TranslationTiling.Compiler.Size
