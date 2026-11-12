import TranslationTiling.Rotations.General.BodyGeometry
import TranslationTiling.Rotations.General.PuncturedBoxes

namespace TranslationTiling.Rotations.General
variable {d : ℕ} [NeZero d]

def Plane (i : Fin d) (c : ℤ) : Set (Lattice d) := {x | InCube x ∧ x i = c}

theorem plane_eq_box (i : Fin d) (c : ℤ) (hc : 0 ≤ c ∧ c < cubeSide d) : Plane i c =
    Box (Function.update 0 i c) (Function.update (fun _ => (cubeSide d : ℤ)-1) i c) := by
  ext x
  constructor
  · intro hx j
    by_cases hj : j = i
    · subst j; simp [hx.2]
    · simpa [Function.update_of_ne hj] using hx.1 j
  · intro hx
    have hi := hx i
    simp only [Function.update_self] at hi
    have he : x i = c := le_antisymm hi.2 hi.1
    refine ⟨?_,he⟩
    intro j
    by_cases hj : j = i
    · subst j
      simp only [Pi.zero_apply]
      rw [he]
      exact ⟨hc.1,by omega⟩
    · simpa [Function.update_of_ne hj] using hx j

/-- Each interior coordinate plane stays connected after deleting one voxel. -/
theorem plane_punctured (hd : 3 ≤ d) (i : Fin d) (c : ℤ)
    (hc : 0 ≤ c ∧ c < cubeSide d) (v : Lattice d) : Connected (Plane i c \ {v}) := by
  obtain ⟨j,hji⟩ := exists_other (by omega : 2 ≤ d) i
  obtain ⟨k,hki,hkj⟩ := exists_third hd i j
  rw [plane_eq_box i c hc]
  have hp := margin_pos (d := d)
  have hL := margin_five_lt_cubeSide (d := d)
  refine box_punctured _ _ v ?_ j k (Ne.symm hkj) ?_ ?_
  · intro a
    by_cases hai : a = i
    · subst a; simp
    · simp only [Function.update_of_ne hai,Pi.zero_apply]; omega
  · simp only [Function.update_of_ne hji,Pi.zero_apply]; omega
  · simp only [Function.update_of_ne hki,Pi.zero_apply]; omega

/-- The union of the intact coordinate planes stays connected after one deletion. -/
theorem skeleton_punctured (hd : 3 ≤ d) (v : Lattice d) :
    Connected {x | Skeleton x ∧ x ≠ v} := by
  have hp := margin_pos (d := d)
  have hL := margin_five_lt_cubeSide (d := d)
  let q : Lattice d := fun i => if v i = (margin d : ℤ)
    then (cubeSide d : ℤ)-(margin d : ℤ) else margin d
  have hq (i : Fin d) :
      (q i = (margin d : ℤ) ∨ q i = (cubeSide d : ℤ)-(margin d : ℤ)) ∧ q i ≠ v i := by
    dsimp [q]
    split_ifs <;> omega
  have hqc : InCube q := by intro i; have := hq i; dsimp; omega
  have hqv : q ≠ v := by intro he; exact (hq 0).2 (congrFun he 0)
  have path (x : Lattice d) (hx : Skeleton x) (hxv : x ≠ v) :
      FacePath (fun z => Skeleton z ∧ z ≠ v) x q := by
    obtain ⟨hxc,i,hi⟩ := hx
    obtain ⟨j,hji⟩ := exists_other (by omega : 2 ≤ d) i
    let y := Function.update q i (x i)
    have hyc : InCube y := inCube_update hqc i (x i) ⟨(hxc i).1,by have := (hxc i).2; dsimp at *; omega⟩
    have hyj : y j = q j := by simp [y,hji]
    have hyv : y ≠ v := by intro he; exact (hq j).2 (hyj.symm.trans (congrFun he j))
    have p1 := plane_punctured hd i (x i) ⟨(hxc i).1,by have := (hxc i).2; dsimp at *; omega⟩ v
      x ⟨⟨hxc,rfl⟩,hxv⟩ y ⟨⟨hyc,by simp [y]⟩,hyv⟩
    have p2 := plane_punctured hd j (q j) ⟨(hqc j).1,by have := (hqc j).2; dsimp at *; omega⟩ v
      y ⟨⟨hyc,hyj⟩,hyv⟩ q ⟨⟨hqc,rfl⟩,hqv⟩
    have p1' := p1.mono (fun z hz =>
      (show Skeleton z ∧ z ≠ v from ⟨⟨hz.1.1,i,by simpa [hz.1.2] using hi⟩,hz.2⟩))
    have p2' := p2.mono (fun z hz =>
      (show Skeleton z ∧ z ≠ v from ⟨⟨hz.1.1,j,by simpa [hz.1.2] using (hq j).1⟩,hz.2⟩))
    exact p1'.trans p2'
  intro x hx y hy
  exact (path x hx.1 hx.2).trans (path y hy.1 hy.2).reverse

end TranslationTiling.Rotations.General
