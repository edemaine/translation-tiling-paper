import TranslationTiling.Rotations.General.Real.Covers
import Mathlib.Topology.LocallyFinite
import Mathlib.Tactic

/-! Small spatial cells give a fixed countable set of slots for a Euclidean
tiling. A packing has at most one tile anchor in each slot, regardless of its
rotation. -/
namespace TranslationTiling.EuclideanMembership

open Rotations.General
open scoped BigOperators
noncomputable section
variable {d : ℕ}

theorem norm_le_sum_abs (x : EPoint d) : ‖x‖ ≤ ∑ i, |x i| := by
  have he : (∑ i : Fin d, EuclideanSpace.single i (x i))=x := by
    ext j
    simp [EuclideanSpace.single,PiLp.single_apply]
  calc
    ‖x‖ = ‖∑ i : Fin d, EuclideanSpace.single i (x i)‖ := congrArg norm he.symm
    _ ≤ ∑ i : Fin d, ‖EuclideanSpace.single i (x i)‖ := norm_sum_le _ _
    _ = _ := by simp [EuclideanSpace.single,PiLp.norm_single,Real.norm_eq_abs]

def cellScale (d : ℕ) : ℕ := 4*(d+1)

def cellCenter (z : Lattice d) (u : Fin d → ℝ) : EPoint d :=
  WithLp.toLp 2 fun i => (2*(z i : ℝ)+u i)/(cellScale d : ℝ)

def cellIndex (x : EPoint d) : Lattice d :=
  fun i => ⌊2*((d : ℝ)+1)*x i+1/2⌋

def cellParameter (x : EPoint d) : Fin d → ℝ :=
  fun i => (cellScale d : ℝ)*x i-2*(cellIndex x i : ℝ)

theorem cellScale_pos (d : ℕ) : 0 < cellScale d := by unfold cellScale; positivity

theorem cellParameter_bound (x : EPoint d) (i : Fin d) : |cellParameter x i| ≤ 1 := by
  have hl := Int.floor_le (2*((d : ℝ)+1)*x i+1/2)
  have hu := Int.lt_floor_add_one (2*((d : ℝ)+1)*x i+1/2)
  apply abs_le.mpr
  change -1 ≤ (cellScale d : ℝ)*x i-2*(⌊2*((d : ℝ)+1)*x i+1/2⌋ : ℝ) ∧
    (cellScale d : ℝ)*x i-2*(⌊2*((d : ℝ)+1)*x i+1/2⌋ : ℝ) ≤ 1
  simp only [cellScale,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_add,Nat.cast_one]
  constructor <;> linarith

theorem cellCenter_index (x : EPoint d) : cellCenter (cellIndex x) (cellParameter x)=x := by
  ext i
  change (2*(cellIndex x i : ℝ)+((cellScale d : ℝ)*x i-2*(cellIndex x i : ℝ)))/
    (cellScale d : ℝ)=x i
  have hd : (cellScale d : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (cellScale_pos d)
  field_simp
  <;> ring

theorem cellCenter_dist_lt_one (z : Lattice d) (u v : Fin d → ℝ)
    (hu : ∀ i, |u i| ≤ 1) (hv : ∀ i, |v i| ≤ 1) :
    dist (cellCenter z u) (cellCenter z v) < 1 := by
  have hd : (0 : ℝ) < cellScale d := by exact_mod_cast cellScale_pos d
  have hb (i : Fin d) : |(cellCenter z u-cellCenter z v) i| ≤ 2/(cellScale d : ℝ) := by
    change |(2*(z i : ℝ)+u i)/(cellScale d : ℝ)-
      (2*(z i : ℝ)+v i)/(cellScale d : ℝ)| ≤ _
    have he : (2*(z i : ℝ)+u i)/(cellScale d : ℝ)-
        (2*(z i : ℝ)+v i)/(cellScale d : ℝ)=(u i-v i)/(cellScale d : ℝ) := by ring
    rw [he,abs_div,abs_of_pos hd]
    exact div_le_div_of_nonneg_right ((abs_sub _ _).trans (by linarith [hu i,hv i])) hd.le
  rw [dist_eq_norm]
  calc
    _ ≤ ∑ i, |(cellCenter z u-cellCenter z v) i| := norm_le_sum_abs _
    _ ≤ ∑ _i : Fin d, 2/(cellScale d : ℝ) := Finset.sum_le_sum fun i _ => hb i
    _ = (d : ℝ)*(2/(cellScale d : ℝ)) := by simp
    _ < 1 := by
      rw [← mul_div_assoc,div_lt_one hd]
      simp only [cellScale,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_add,Nat.cast_one]
      nlinarith [(show (0 : ℝ) ≤ d from Nat.cast_nonneg d)]

theorem same_cell_dist_lt_one {x y : EPoint d} (h : cellIndex x=cellIndex y) : dist x y < 1 := by
  conv_lhs => rw [← cellCenter_index x,← cellCenter_index y,h]
  exact cellCenter_dist_lt_one _ _ _ (cellParameter_bound x) (cellParameter_bound y)

theorem cellIndex_abs_le (x : EPoint d) (i : Fin d) :
    |(cellIndex x i : ℝ)| ≤ 2*((d : ℝ)+1)*|x i|+1 := by
  have hh := cellParameter_bound x i
  have hl := Int.floor_le (2*((d : ℝ)+1)*x i+1/2)
  have hu := Int.lt_floor_add_one (2*((d : ℝ)+1)*x i+1/2)
  apply abs_le.mpr
  have hx := abs_le.mp (le_refl |x i|)
  change -(2*((d : ℝ)+1)*|x i|+1) ≤ (⌊2*((d : ℝ)+1)*x i+1/2⌋ : ℝ) ∧
    (⌊2*((d : ℝ)+1)*x i+1/2⌋ : ℝ) ≤ 2*((d : ℝ)+1)*|x i|+1
  constructor <;> nlinarith [(show (0 : ℝ) ≤ d from Nat.cast_nonneg d)]

end
end TranslationTiling.EuclideanMembership
