import TranslationTiling.Compiler.ClosedSupportBound
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Int.Interval
import Mathlib.Tactic.Positivity

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace TranslationTiling.Compiler.Size

open scoped Classical BigOperators
open Effective
noncomputable section

def lowCap (n : ℕ) : ℕ := digitPrimeBound n ^ labelsBound n
def parameterCap (n : ℕ) : ℕ := lowCap n + usefulCap + residueModulus + 2
def finiteCap (b : ℕ) : ℕ := b ^ (4 * channelCount + 2)
def supportVolume (b : ℕ) : ℕ := (2 * horizontalCap b + 1) ^ 2 * finiteCap b

theorem exists_parameterBudget (T : LeanWang.TileSet) :
    ∃ E : EncodingParameters T, ParameterBudget E (parameterCap T.length) := by
  obtain ⟨E, hu, hp⟩ := exists_bounded_parameters T
  have hQ : 1 ≤ digitPrimeBound T.length := by
    have : 0 < digitPrimeBound T.length :=
      Nat.mul_pos (pow_pos (by decide : 0 < 4) _) (Nat.succ_pos _)
    omega
  have hr (i : Channel T) : E.r i ≤ lowCap T.length := by
    rw [E.r_eq_prod]
    calc
      _ ≤ ∏ _j : Label T i, digitPrimeBound T.length := Finset.prod_le_prod (fun j _ => hp i j)
      _ = digitPrimeBound T.length ^ Fintype.card (Label T i) := by simp
      _ ≤ lowCap T.length := Nat.pow_le_pow_right hQ (label_card_le T i)
  refine ⟨E, ?_⟩
  constructor
  · unfold parameterCap; omega
  · unfold parameterCap; omega
  · intro i; have := hr i; unfold parameterCap; omega
  · intro i
    have := (hu i).1
    unfold parameterCap; omega
  · intro i
    have := (hu i).2
    unfold parameterCap; omega

theorem cyclicOrder_le {T : LeanWang.TileSet} {E : EncodingParameters T} {b : ℕ}
    (hb : ParameterBudget E b) : E.cyclicOrder ≤ finiteCap b := by
  have hblock (i : Channel T) : E.blockModulus i ≤ b ^ 4 := by
    unfold EncodingParameters.blockModulus
    calc
      _ ≤ b ^ 2 * b * b := by
        gcongr
        · exact hb.r i
        · exact hb.a i
        · exact hb.usefulB i
      _ = _ := by ring
  unfold EncodingParameters.cyclicOrder finiteCap
  calc
    _ ≤ b ^ 2 * ∏ _i : Channel T, b ^ 4 := by
      apply Nat.mul_le_mul
      · exact Nat.pow_le_pow_left hb.width _
      · exact Finset.prod_le_prod (fun i _ => hblock i)
    _ = b ^ 2 * (b ^ 4) ^ channelCount := by simp [channelCount]
    _ = _ := by rw [← pow_mul, ← pow_add]; congr 1; omega

def ambientBox {T : LeanWang.TileSet} (E : EncodingParameters T) (b : ℕ) :
    Finset (Ambient E) :=
  ((Finset.Icc (-(horizontalCap b : ℤ)) (horizontalCap b)).product
    (Finset.Icc (-(horizontalCap b : ℤ)) (horizontalCap b))).product Finset.univ

theorem int_mem_interval_of_natAbs {z : ℤ} {h : ℕ} (hz : z.natAbs ≤ h) :
    z ∈ Finset.Icc (-(h : ℤ)) h := by
  apply Finset.mem_Icc.mpr
  have hhi : ((z.natAbs : ℕ) : ℤ) ≤ h := by exact_mod_cast hz
  have hp := Int.le_natAbs (a := z)
  have hn := Int.le_natAbs (a := -z)
  simp only [Int.natAbs_neg] at hn
  omega

theorem testTile_subset_box {T : LeanWang.TileSet} {E : EncodingParameters T} {b : ℕ}
    (hb : ParameterBudget E b) {F : Finset (Ambient E)} (hF : F ∈ testTiles E) :
    F ⊆ ambientBox E b := by
  intro g hg
  obtain ⟨hx, hy⟩ := testTile_horizontal_bound hb hF hg
  simp only [ambientBox, Finset.product_eq_sprod, Finset.mem_product, Finset.mem_univ,
    and_true]
  exact ⟨int_mem_interval_of_natAbs hx, int_mem_interval_of_natAbs hy⟩

theorem ambientBox_card {T : LeanWang.TileSet} (E : EncodingParameters T) (b : ℕ) :
    (ambientBox E b).card = (2 * horizontalCap b + 1) ^ 2 * E.cyclicOrder := by
  have hV : Fintype.card (V E) = E.cyclicOrder := by
    simpa only [ZMod.card] using Fintype.card_congr (finiteFactorEquiv E).toEquiv
  have hI : (Finset.Icc (-(horizontalCap b : ℤ)) (horizontalCap b)).card =
      2 * horizontalCap b + 1 := by
    rw [Int.card_Icc]
    omega
  simp only [ambientBox, Finset.product_eq_sprod, Finset.card_product, hI,
    Finset.card_univ, hV, pow_two]

theorem testTiles_card_le {T : LeanWang.TileSet} {E : EncodingParameters T} {b : ℕ}
    (hb : ParameterBudget E b) : (testTiles E).card ≤ 2 ^ supportVolume b := by
  have hsub : testTiles E ⊆ (ambientBox E b).powerset := by
    intro F hF
    exact Finset.mem_powerset.mpr (testTile_subset_box hb hF)
  apply (Finset.card_le_card hsub).trans
  rw [Finset.card_powerset, ambientBox_card]
  apply Nat.pow_le_pow_right (by decide)
  exact Nat.mul_le_mul_left _ (cyclicOrder_le hb)

end
end TranslationTiling.Compiler.Size
