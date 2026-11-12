import TranslationTiling.EuclideanMembership.BodyBounds
import TranslationTiling.EuclideanMembership.RationalTests

/-! Rational probes are dense in Euclidean space. Only finitely many spatial
slots can cover any given probe; their list is computed from the input tile. -/
namespace TranslationTiling.EuclideanMembership

open Rotations.General (EPoint castPoint)
open Rotations.General.Real (Placed RigidMotion)
open scoped BigOperators
noncomputable section
variable {d : ℕ}

abbrev Probe (d : ℕ) := Lattice d × ℕ

def probe (a : Probe d) : EPoint d :=
  WithLp.toLp 2 fun i => (a.1 i : ℝ)/((a.2 : ℝ)+1)

theorem floor_rational_error (x : ℝ) (D : ℕ) (hD : 0 < D) :
    |x-(⌊x*(D : ℝ)⌋ : ℝ)/(D : ℝ)| ≤ 1/(D : ℝ) := by
  have hd : (0 : ℝ) < D := by exact_mod_cast hD
  have hl := Int.floor_le (x*(D : ℝ))
  have hu := Int.lt_floor_add_one (x*(D : ℝ))
  have hc : ((⌊x*(D : ℝ)⌋ : ℝ)/(D : ℝ))*(D : ℝ)=(⌊x*(D : ℝ)⌋ : ℝ) :=
    div_mul_cancel₀ _ hd.ne'
  have hn : 0 ≤ x-(⌊x*(D : ℝ)⌋ : ℝ)/(D : ℝ) := by
    rw [sub_nonneg,div_le_iff₀ hd]
    exact hl
  rw [abs_of_nonneg hn,le_div_iff₀ hd]
  nlinarith

theorem probe_dense : DenseRange (@probe d) := by
  rw [Metric.denseRange_iff]
  intro x r hr
  obtain ⟨n,hn⟩ := exists_nat_gt ((d : ℝ)/r)
  let a : Probe d := (fun i => ⌊x i*((n : ℝ)+1)⌋,n)
  have hd : (0 : ℝ) < (n : ℝ)+1 := by positivity
  have hb (i : Fin d) : |(x-probe a) i| ≤ 1/((n : ℝ)+1) := by
    simpa only [probe,PiLp.sub_apply,PiLp.toLp_apply,Nat.cast_add,Nat.cast_one] using
      floor_rational_error (x i) (n+1) (by omega)
  refine ⟨a,?_⟩
  rw [dist_eq_norm]
  calc
    ‖x-probe a‖ ≤ ∑ i, |(x-probe a) i| := norm_le_sum_abs _
    _ ≤ ∑ _i : Fin d, 1/((n : ℝ)+1) := Finset.sum_le_sum fun i _ => hb i
    _ = (d : ℝ)/((n : ℝ)+1) := by simp [div_eq_mul_inv]
    _ < r := by
      rw [div_lt_iff₀ hd]
      have hh := (div_lt_iff₀ hr).mp hn
      nlinarith

def coordinateSum (z : Lattice d) : ℕ := (List.ofFn fun i => (z i).natAbs).sum

theorem probe_norm_bound (a : Probe d) : ‖probe a‖ ≤ coordinateSum a.1 := by
  have hd : (1 : ℝ) ≤ (a.2 : ℝ)+1 := by
    linarith [(show (0 : ℝ) ≤ a.2 from Nat.cast_nonneg a.2)]
  have hb (i : Fin d) : |probe a i| ≤ |(a.1 i : ℝ)| := by
    change |(a.1 i : ℝ)/((a.2 : ℝ)+1)| ≤ _
    rw [abs_div,abs_of_pos (by positivity : (0 : ℝ) < (a.2 : ℝ)+1)]
    exact div_le_self (abs_nonneg _) hd
  calc
    ‖probe a‖ ≤ ∑ i, |probe a i| := norm_le_sum_abs _
    _ ≤ ∑ i, |(a.1 i : ℝ)| := Finset.sum_le_sum fun i _ => hb i
    _ = coordinateSum a.1 := by simp [coordinateSum,Fin.sum_ofFn]

/-- A finite list of every lattice point in a coordinate box. -/
def cellBox (d B : ℕ) : List (Lattice d) :=
  (Compiler.Effective.strings (integerGrid B) d).map fun z => fun i : Fin d => z.getD i.val 0

theorem mem_cellBox (B : ℕ) (z : Lattice d) :
    z ∈ cellBox d B ↔ ∀ i, |z i| ≤ B := by
  unfold cellBox
  constructor
  · intro hz
    obtain ⟨xs,hxs,rfl⟩ := List.mem_map.mp hz
    intro i
    have hm := (Compiler.Effective.mem_strings _ _ _).mp hxs
    have hi : i.val < xs.length := by rw [hm.1]; exact i.isLt
    change |xs.getD i.val 0| ≤ (B : ℤ)
    rw [List.getD_eq_getElem xs 0 hi]
    exact abs_le.mpr ((mem_integerGrid _ _).mp (hm.2 _ (List.getElem_mem hi)))
  · intro hz
    apply List.mem_map.mpr
    refine ⟨List.ofFn z,?_,?_⟩
    · apply (Compiler.Effective.mem_strings _ _ _).mpr
      refine ⟨by simp,?_⟩
      intro a ha
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ha
      exact (mem_integerGrid _ _).mpr (abs_le.mp (hz i))
    · ext i
      rw [List.getD_eq_getElem _ 0 (by simp)]
      simp

def probeRadius (P : Tile d) (a : Probe d) : ℕ :=
  2*(d+1)*(coordinateSum a.1+tileDiameter P+1)+1

def probeCells (P : Tile d) (a : Probe d) : List (Lattice d) := cellBox d (probeRadius P a)

theorem placed_probe_cell_mem (P : Tile d) {p : Lattice d} (hp : p ∈ P)
    (m : RigidMotion d) (a : Probe d) (ha : probe a ∈ Placed P.toFinset m) :
    cellIndex (m.apply (castPoint p)) ∈ probeCells P a := by
  apply (mem_cellBox _ _).mpr
  intro i
  have hb := placed_index_bound P hp m ha i
  have hn := probe_norm_bound a
  have hm := mul_le_mul_of_nonneg_left
    (add_le_add_right hn (tileDiameter P : ℝ))
    (by positivity : (0 : ℝ) ≤ 2*((d : ℝ)+1))
  have ht : |(cellIndex (m.apply (castPoint p)) i : ℝ)| ≤ probeRadius P a := by
    simp only [probeRadius,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one]
    nlinarith [(show (0 : ℝ) ≤ d from Nat.cast_nonneg d)]
  exact_mod_cast ht

end
end TranslationTiling.EuclideanMembership
