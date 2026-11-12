import TranslationTiling.Rotations.General.Skeleton

namespace TranslationTiling.Rotations.General
variable {d : ℕ} [NeZero d]

/-- A clear central line reaches an intact plane while avoiding one deleted voxel. -/
theorem clear_line_path {x v : Lattice d} (hx : x ∈ body) (hxv : x ≠ v)
    (i : Fin d) (hi : Central (d := d) (x i))
    (line : ∀ t : ℤ, (margin d : ℤ) ≤ t → t ≤ (cubeSide d : ℤ)-(margin d : ℤ) →
      Function.update x i t ∈ body) :
    ∃ y, Skeleton y ∧ y ≠ v ∧ FacePath (fun z => z ∈ body ∧ z ≠ v) x y := by
  dsimp [Central] at hi
  let a : ℤ := margin d
  let c : ℤ := (cubeSide d : ℤ)-(margin d : ℤ)
  let b : ℤ := if x i ≤ v i then a else c
  have hb : b = a ∨ b = c := by dsimp [b]; split_ifs <;> simp
  have hbr : a ≤ b ∧ b ≤ c := by dsimp [a,c] at *; omega
  have avoid (t : ℤ) (ht : min (x i) b ≤ t) (hu : t ≤ max (x i) b) :
      Function.update x i t ≠ v := by
    intro he
    have hti : t = v i := by simpa using congrFun he i
    have hsame : t = x i := by
      dsimp [b,a,c] at ht hu
      split_ifs at ht hu with hh
      · rw [min_eq_right (by omega : (margin d : ℤ) ≤ x i)] at ht
        rw [max_eq_left (by omega : (margin d : ℤ) ≤ x i)] at hu
        omega
      · rw [min_eq_left (by omega : x i ≤ (cubeSide d : ℤ)-(margin d : ℤ))] at ht
        rw [max_eq_right (by omega : x i ≤ (cubeSide d : ℤ)-(margin d : ℤ))] at hu
        omega
    rw [hsame,Function.update_eq_self] at he
    exact hxv he
  have path : FacePath (fun z => z ∈ body ∧ z ≠ v) x (Function.update x i b) := by
    apply FacePath.axis
    intro t ht hu
    have htr : a ≤ t ∧ t ≤ c := by
      have hxi : a ≤ x i ∧ x i ≤ c := by dsimp [a,c]; omega
      exact ⟨(le_min hxi.1 hbr.1).trans ht,hu.trans (max_le hxi.2 hbr.2)⟩
    exact ⟨line t htr.1 htr.2,avoid t ht hu⟩
  refine ⟨Function.update x i b,⟨(body_iff _).mp (line b hbr.1 hbr.2) |>.1,i,?_⟩,
    avoid b (min_le_right _ _) (le_max_right _ _),path⟩
  simpa only [Function.update_self] using hb

/-- If every coordinate is outer, two unchanged outer coordinates protect a
route to an intact plane. A third coordinate is why this argument needs d ≥ 3. -/
theorem outer_corner_path (hd : 3 ≤ d) {x v : Lattice d} (hx : x ∈ body) (hxv : x ≠ v)
    (outer : ∀ i, Outer (d := d) (x i)) :
    ∃ y, Skeleton y ∧ y ≠ v ∧ FacePath (fun z => z ∈ body ∧ z ≠ v) x y := by
  obtain ⟨j,hj⟩ : ∃ j, x j ≠ v j := by
    by_contra! hn
    exact hxv (funext hn)
  obtain ⟨i,hij⟩ := exists_other (by omega : 2 ≤ d) j
  obtain ⟨k,hki,hkj⟩ := exists_third hd i j
  have hp := margin_pos (d := d)
  have hL := margin_five_lt_cubeSide (d := d)
  let b : ℤ := if x i ≤ (margin d : ℤ) then margin d else (cubeSide d : ℤ)-(margin d : ℤ)
  have hb : b = (margin d : ℤ) ∨ b = (cubeSide d : ℤ)-(margin d : ℤ) := by
    dsimp [b]; split_ifs <;> simp
  have hbr : 0 ≤ b ∧ b < cubeSide d := by rcases hb with hb | hb <;> omega
  have hxc := ((body_iff x).mp hx).1
  have path : FacePath (fun z => z ∈ body ∧ z ≠ v) x (Function.update x i b) := by
    apply FacePath.axis
    intro t ht hu
    have htr : 0 ≤ t ∧ t < cubeSide d := by
      have hxi := hxc i
      dsimp at hxi
      exact ⟨(le_min hxi.1 hbr.1).trans ht,by
        have hh := hu.trans (max_le hxi.2 (by omega : b ≤ (cubeSide d : ℤ)-1)); omega⟩
    constructor
    · apply two_outer_body (inCube_update hxc i t htr) j k (Ne.symm hkj)
      · simpa [Ne.symm hij] using outer j
      · simpa [hki] using outer k
    · intro he
      exact hj (by simpa [Ne.symm hij] using congrFun he j)
  refine ⟨Function.update x i b,⟨inCube_update hxc i b hbr,i,?_⟩,?_,path⟩
  · simpa only [Function.update_self] using hb
  · intro he
    exact hj (by simpa [Ne.symm hij] using congrFun he j)

end TranslationTiling.Rotations.General
