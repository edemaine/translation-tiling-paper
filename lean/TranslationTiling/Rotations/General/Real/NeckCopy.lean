import TranslationTiling.Rotations.General.Real.GridCubes
import TranslationTiling.Rotations.General.Real.NeckWalls
import TranslationTiling.Rotations.General.Real.NeckPosition

namespace TranslationTiling.Rotations.General.Real
noncomputable section
open Set
variable {d : ℕ} [NeZero d]

/-- A cube entering the middle of a neck acquires a grid orientation, zero
transverse center, and an integral phase in every transverse coordinate. -/
theorem neck_copy_alignment {F : Finset (Lattice d)} {p : Lattice d} (hp : p ∈ F)
    (m : RigidMotion d) (f : Face d) {u : EPoint d} (hu : u ∈ openVoxel p)
    (h0 : (neckCenter d : ℝ)-1/4 < m.apply u 0 ∧ m.apply u 0 < (neckCenter d : ℝ)+1/4)
    (ht : ∀ j : Fin d, j ≠ 0 → |m.apply u j| < (1 : ℝ)/2)
    (packing : Disjoint (Placed F m) (interior (solid (localBody f)))) :
    ∃ r : Orientation d, m.rotation=gridRotation r ∧
      (∀ j : Fin d, j ≠ 0 → m.apply (castPoint p) j=0) ∧
      (∀ j : Fin d, j ≠ 0 → ∃ z : ℤ, m.offset j=(z : ℝ)) := by
  let c : RigidMotion d := ⟨m.rotation,m.apply (castPoint p)⟩
  have hc_apply (x : EPoint d) : c.apply x=m.apply (castPoint p+x) := by
    simp [c,RigidMotion.apply,map_add,add_assoc]
  have hc_sub : c.apply (u-castPoint p)=m.apply u := by rw [hc_apply]; congr 1; abel
  have huv : u-castPoint p ∈ unitCube := by
    intro j
    simpa only [PiLp.sub_apply,castPoint_apply] using (hu j).le
  have hc_mem (x : EPoint d) (hx : x ∈ unitCube) : c.apply x ∈ Placed F m := by
    rw [hc_apply]
    refine ⟨castPoint p+x,⟨p,hp,?_⟩,rfl⟩
    intro j
    simpa only [PiLp.add_apply,castPoint_apply,add_sub_cancel_left] using hx j
  have confined (x : EPoint d) (hx : x ∈ unitCube) (j : Fin d) (hj : j ≠ 0) :
      |c.apply x j| ≤ (1 : ℝ)/2 := by
    have hd0 := abs_lt.mp (c.cube_coordinate_diameter hx huv 0)
    rw [hc_sub] at hd0
    have hb0 : -(1 : ℝ)/2 < c.apply x 0 ∧ c.apply x 0 < (neckLength d : ℝ)-(1 : ℝ)/2 := by
      have hn := h0
      simp only [neckCenter,neckLength,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] at hn ⊢
      constructor <;> linarith
    have hbt (k : Fin d) (hk : k ≠ 0) : |c.apply x k| < (d : ℝ)+3/2 := by
      have hdk := abs_lt.mp (c.cube_coordinate_diameter hx huv k)
      rw [hc_sub] at hdk
      have huk := abs_lt.mp (ht k hk)
      rw [abs_lt]
      constructor <;> linarith
    by_contra hn
    have hout : ∃ k : Fin d, k ≠ 0 ∧ (1 : ℝ)/2 < |c.apply x k| := ⟨j,hj,lt_of_not_ge hn⟩
    exact Set.disjoint_left.mp packing (hc_mem x hx) (local_neck_wall f hb0 hbt hout)
  obtain ⟨r,hr⟩ := cube_alignment c.rotation c.offset 0 (fun _ => -(1 : ℝ)/2) (by
    intro j hj x hx
    have hh := abs_le.mp (confined x hx j hj)
    change -(1 : ℝ)/2 ≤ c.apply x j ∧ c.apply x j ≤ -(1 : ℝ)/2+1
    constructor <;> linarith)
  have centers (j : Fin d) (hj : j ≠ 0) : c.offset j=0 :=
    transverse_center c r hr j (fun x hx => confined x hx j hj)
  refine ⟨r,hr,centers,?_⟩
  intro j hj
  refine ⟨-r.sign j*p (r.axes j),?_⟩
  have hcj := centers j hj
  change m.apply (castPoint p) j=0 at hcj
  have hrm : m.rotation=gridRotation r := hr
  simp only [RigidMotion.apply,hrm,PiLp.add_apply,gridRotation_apply,castPoint_apply] at hcj
  push_cast
  linarith

end
end TranslationTiling.Rotations.General.Real
