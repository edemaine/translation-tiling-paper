import TranslationTiling.EuclideanMembership.Cells

/-! Computable bounds on the size of a polycube and the spatial slots that can
contribute to coverage near a given point. -/
namespace TranslationTiling.EuclideanMembership

open Rotations.General (EPoint castPoint)
open Rotations.General.Real (solid voxel Placed RigidMotion)
open scoped BigOperators
noncomputable section
variable {d : ℕ}

/-- A coordinate bound computed directly from the list of cubes. -/
def coordinateRadius (P : Tile d) : ℕ :=
  1+(P.flatMap fun p => List.ofFn fun i : Fin d => (p i).natAbs).sum

def bodyRadius (P : Tile d) : ℕ := (d+1)*(coordinateRadius P+1)
def tileDiameter (P : Tile d) : ℕ := 2*bodyRadius P

theorem coordinate_bound {P : Tile d} {p : Lattice d} (hp : p ∈ P) (i : Fin d) :
    |(p i : ℝ)| ≤ coordinateRadius P := by
  have hm : (p i).natAbs ∈ P.flatMap (fun p => List.ofFn fun i : Fin d => (p i).natAbs) :=
    List.mem_flatMap.mpr ⟨p,hp,List.mem_ofFn.mpr ⟨i,rfl⟩⟩
  have hb := List.single_le_sum (fun _ _ => Nat.zero_le _) ((p i).natAbs) hm
  have hh : (p i).natAbs ≤ coordinateRadius P := hb.trans (by unfold coordinateRadius; omega)
  simpa using (show ((p i).natAbs : ℝ) ≤ coordinateRadius P by exact_mod_cast hh)

theorem solid_norm_bound (P : Tile d) {x : EPoint d} (hx : x ∈ solid P.toFinset) :
    ‖x‖ ≤ bodyRadius P := by
  obtain ⟨p,hp,hv⟩ := hx
  have hp' : p ∈ P := List.mem_toFinset.mp hp
  have hb (i : Fin d) : |x i| ≤ (coordinateRadius P : ℝ)+1/2 := by
    have hi := hv i
    have hh := coordinate_bound hp' i
    have he : x i=(x i-(p i : ℝ))+(p i : ℝ) := by ring
    calc
      |x i| = |(x i-(p i : ℝ))+(p i : ℝ)| := congrArg abs he
      _ ≤ |x i-(p i : ℝ)|+|(p i : ℝ)| := abs_add_le _ _
      _ ≤ _ := by linarith
  calc
    ‖x‖ ≤ ∑ i, |x i| := norm_le_sum_abs x
    _ ≤ ∑ _i : Fin d, ((coordinateRadius P : ℝ)+1/2) :=
      Finset.sum_le_sum fun i _ => hb i
    _ = (d : ℝ)*((coordinateRadius P : ℝ)+1/2) := by simp; ring
    _ ≤ bodyRadius P := by
      simp only [bodyRadius,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
      nlinarith [(show (0 : ℝ) ≤ d from Nat.cast_nonneg d),
        (show (0 : ℝ) ≤ coordinateRadius P from Nat.cast_nonneg _)]

theorem castPoint_mem_solid {P : Tile d} {p : Lattice d} (hp : p ∈ P) :
    castPoint p ∈ solid P.toFinset := by
  refine ⟨p,List.mem_toFinset.mpr hp,?_⟩
  intro i
  simp [castPoint]

theorem solid_dist_bound (P : Tile d) {p : Lattice d} (hp : p ∈ P)
    {x : EPoint d} (hx : x ∈ solid P.toFinset) :
    dist x (castPoint p) ≤ tileDiameter P := by
  have hx' := solid_norm_bound P hx
  have hp' := solid_norm_bound P (castPoint_mem_solid hp)
  rw [dist_eq_norm]
  calc
    ‖x-castPoint p‖ ≤ ‖x‖+‖castPoint p‖ := norm_sub_le _ _
    _ ≤ tileDiameter P := by simp only [tileDiameter,Nat.cast_mul,Nat.cast_ofNat]; linarith

theorem motion_dist_eq (m : RigidMotion d) (x y : EPoint d) :
    dist (m.apply x) (m.apply y)=dist x y := by
  simpa only [RigidMotion.apply,dist_add_left] using m.rotation.dist_map x y

theorem placed_anchor_dist_bound (P : Tile d) {p : Lattice d} (hp : p ∈ P)
    (m : RigidMotion d) {x : EPoint d} (hx : x ∈ Placed P.toFinset m) :
    dist (m.apply (castPoint p)) x ≤ tileDiameter P := by
  obtain ⟨y,hy,rfl⟩ := hx
  rw [motion_dist_eq,dist_comm]
  exact solid_dist_bound P hp hy

theorem placed_index_bound (P : Tile d) {p : Lattice d} (hp : p ∈ P)
    (m : RigidMotion d) {x : EPoint d} (hx : x ∈ Placed P.toFinset m) (i : Fin d) :
    |(cellIndex (m.apply (castPoint p)) i : ℝ)| ≤
      2*((d : ℝ)+1)*(‖x‖+(tileDiameter P : ℝ))+1 := by
  have hd := placed_anchor_dist_bound P hp m hx
  have ha := dist_triangle (m.apply (castPoint p)) x 0
  simp only [dist_zero_right] at ha
  have hc : |m.apply (castPoint p) i| ≤ ‖x‖+(tileDiameter P : ℝ) := by
    have hh := PiLp.norm_apply_le (p := 2) (m.apply (castPoint p)) i
    rw [Real.norm_eq_abs] at hh
    linarith
  exact (cellIndex_abs_le _ i).trans (by
    have hm := mul_le_mul_of_nonneg_left hc (by positivity : 0 ≤ 2*((d : ℝ)+1))
    linarith)

end
end TranslationTiling.EuclideanMembership
