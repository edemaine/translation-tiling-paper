import TranslationTiling.Rotations.Euclidean.GridCubes
import TranslationTiling.Rotations.Euclidean.LocalChambers

namespace TranslationTiling.Rotations.Euclidean

noncomputable section
open Set SixKeys

theorem local_neck_wall (i : Face) {x : EPoint}
    (h0 : -(1:ℝ)/2 < x 0 ∧ x 0 < 9/2)
    (h1 : |x 1| < (5:ℝ)/2) (h2 : |x 2| < (5:ℝ)/2)
    (hout : (1:ℝ)/2 < |x 1| ∨ (1:ℝ)/2 < |x 2|) :
    x ∈ interior (solid (localBody i)) := by
  let e := (embedMotion (frameMotion i)).homeomorph
  have hF : (localBody i).image (frameMotion i).apply = body := by
    simp [localBody,Finset.image_image,Function.comp_def]
  have hs : e '' solid (localBody i)=solid body := by
    change (embedMotion (frameMotion i)).apply '' solid (localBody i)=solid body
    rw [embedMotion_solid,hF]
  have hi : e '' interior (solid (localBody i))=interior (solid body) := by
    rw [e.image_interior,hs]
  have hx := neck_wall i h0 h1 h2 hout
  rw [← hi] at hx
  obtain ⟨y,hy,he⟩ := hx
  exact e.injective he ▸ hy

theorem neck_copy_alignment {F : Finset (Lattice 3)} {p : Lattice 3} (hp : p ∈ F)
    (m : RigidMotion) (i : Face) {u : EPoint} (hu : u ∈ openVoxel p)
    (h0 : (7:ℝ)/4 < m.apply u 0 ∧ m.apply u 0 < 9/4)
    (h1 : |m.apply u 1| < (1:ℝ)/2) (h2 : |m.apply u 2| < (1:ℝ)/2)
    (packing : Disjoint (Placed F m) (interior (solid (localBody i)))) :
    ∃ r : Orientation, m.rotation=gridRotation r ∧
      m.apply (castPoint p) 1=0 ∧ m.apply (castPoint p) 2=0 ∧
      (∃ z : ℤ, m.offset 1=(z:ℝ)) ∧ (∃ z : ℤ, m.offset 2=(z:ℝ)) := by
  let c : RigidMotion := ⟨m.rotation,m.apply (castPoint p)⟩
  have hc_apply (x : EPoint) : c.apply x=m.apply (castPoint p+x) := by
    simp [c,RigidMotion.apply,map_add,add_assoc]
  have hc_sub : c.apply (u-castPoint p)=m.apply u := by rw [hc_apply]; congr 1; abel
  have huv : u-castPoint p ∈ unitCube := by
    intro j
    simpa only [PiLp.sub_apply,castPoint_apply] using (hu j).le
  have hc_mem (x : EPoint) (hx : x ∈ unitCube) : c.apply x ∈ Placed F m := by
    rw [hc_apply]
    refine ⟨castPoint p+x,⟨p,hp,?_⟩,rfl⟩
    intro j
    simpa only [PiLp.add_apply,castPoint_apply,add_sub_cancel_left] using hx j
  have confined (x : EPoint) (hx : x ∈ unitCube) :
      |c.apply x 1| ≤ (1:ℝ)/2 ∧ |c.apply x 2| ≤ (1:ℝ)/2 := by
    have hd0 := abs_lt.mp (c.cube_coordinate_diameter hx huv 0)
    have hd1 := abs_lt.mp (c.cube_coordinate_diameter hx huv 1)
    have hd2 := abs_lt.mp (c.cube_coordinate_diameter hx huv 2)
    rw [hc_sub] at hd0 hd1 hd2
    have hu1 := abs_lt.mp h1
    have hu2 := abs_lt.mp h2
    by_contra! hn
    have hout : (1:ℝ)/2 < |c.apply x 1| ∨ (1:ℝ)/2 < |c.apply x 2| := by
      by_cases hf : |c.apply x 1| ≤ (1:ℝ)/2
      · exact Or.inr (hn hf)
      · exact Or.inl (lt_of_not_ge hf)
    exact Set.disjoint_left.mp packing (hc_mem x hx)
      (local_neck_wall i ⟨by linarith,by linarith⟩
        (abs_lt.mpr ⟨by linarith,by linarith⟩)
        (abs_lt.mpr ⟨by linarith,by linarith⟩) hout)
  obtain ⟨r,hr⟩ := cube_alignment c.rotation c.offset (-(1:ℝ)/2) (-(1:ℝ)/2)
    (fun x hx => by have hh := abs_le.mp (confined x hx).1; change -(1:ℝ)/2≤c.apply x 1 ∧ c.apply x 1≤ -(1:ℝ)/2+1; constructor <;> linarith)
    (fun x hx => by have hh := abs_le.mp (confined x hx).2; change -(1:ℝ)/2≤c.apply x 2 ∧ c.apply x 2≤ -(1:ℝ)/2+1; constructor <;> linarith)
  have hcz1 := transverse_center c r hr 1 (fun x hx => (confined x hx).1)
  have hcz2 := transverse_center c r hr 2 (fun x hx => (confined x hx).2)
  have hrm : m.rotation=gridRotation r := hr
  refine ⟨r,hrm,hcz1,hcz2,?_,?_⟩
  · refine ⟨-r.sign 1*p (r.axes 1),?_⟩
    change m.apply (castPoint p) 1=0 at hcz1
    simp only [RigidMotion.apply,hrm,PiLp.add_apply,gridRotation_apply,castPoint_apply] at hcz1
    push_cast
    linarith
  · refine ⟨-r.sign 2*p (r.axes 2),?_⟩
    change m.apply (castPoint p) 2=0 at hcz2
    simp only [RigidMotion.apply,hrm,PiLp.add_apply,gridRotation_apply,castPoint_apply] at hcz2
    push_cast
    linarith

end
end TranslationTiling.Rotations.Euclidean
