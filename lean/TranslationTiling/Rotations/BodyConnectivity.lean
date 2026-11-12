import TranslationTiling.Rotations.PlanePaths

namespace TranslationTiling.Rotations.SixKeys

theorem skeleton_punctured (v : Point) : Connected {x | Skeleton x ∧ x ≠ v} := by
  let q : Point := fun i => if v i = 10 then 29 else 10
  have hq (i : Fin 3) : (q i = 10 ∨ q i = 29) ∧ q i ≠ v i := by
    dsimp [q]; split_ifs <;> omega
  have hqCube : InCube q := by intro i; have := hq i; omega
  have hqv : q ≠ v := by intro he; exact (hq 0).2 (congrFun he 0)
  have path (x : Point) (hx : Skeleton x) (hxv : x ≠ v) :
      FacePath (fun z => Skeleton z ∧ z ≠ v) x q := by
    obtain ⟨hxc, i, hi⟩ := hx
    let j : Fin 3 := if i = 0 then 1 else 0
    have hji : j ≠ i := by fin_cases i <;> decide
    let y := Function.update q i (x i)
    have hyCube : InCube y := inCube_update hqCube i (x i) (hxc i)
    have hyj : y j = q j := by simp [y, hji]
    have hyv : y ≠ v := by
      intro he
      exact (hq j).2 (hyj.symm.trans (congrFun he j))
    have h₁ := plane_punctured i (x i) (hxc i) v x ⟨⟨hxc, rfl⟩, hxv⟩
      y ⟨⟨hyCube, by simp [y]⟩, hyv⟩
    have h₂ := plane_punctured j (q j) (by have := hqCube j; exact this) v
      y ⟨⟨hyCube, hyj⟩, hyv⟩ q ⟨⟨hqCube, rfl⟩, hqv⟩
    have p₁ : FacePath (fun z => Skeleton z ∧ z ≠ v) x y := h₁.mono (by
      intro z hz
      exact ⟨⟨hz.1.1, i, by simpa [hz.1.2] using hi⟩, hz.2⟩)
    have p₂ : FacePath (fun z => Skeleton z ∧ z ≠ v) y q := h₂.mono (by
      intro z hz
      exact ⟨⟨hz.1.1, j, by simpa [hz.1.2] using (hq j).1⟩, hz.2⟩)
    exact p₁.trans p₂
  intro x hx y hy
  exact (path x hx.1 hx.2).trans (path y hy.1 hy.2).reverse

/-- A clear line gives two routes to the intact planes, so one avoids a
prescribed deleted voxel. -/
theorem clear_line_path {x v : Point} (hx : BodyPred x) (hxv : x ≠ v)
    (i : Fin 3) (hi : 10 < x i ∧ x i < 29)
    (line : ∀ t : ℤ, 10 ≤ t → t ≤ 29 → BodyPred (Function.update x i t)) :
    ∃ y, Skeleton y ∧ y ≠ v ∧ FacePath (fun z => BodyPred z ∧ z ≠ v) x y := by
  let b : ℤ := if x i ≤ v i then 10 else 29
  have hb : b = 10 ∨ b = 29 := by dsimp [b]; split_ifs <;> simp
  have hbRange : 10 ≤ b ∧ b ≤ 29 := by omega
  have avoid (t : ℤ) (ht : min (x i) b ≤ t) (hu : t ≤ max (x i) b) :
      Function.update x i t ≠ v := by
    intro he
    have hti : t = v i := by simpa using congrFun he i
    have hsame : t = x i := by
      dsimp [b] at ht hu
      split_ifs at ht hu with hh
      · rw [min_eq_right (by omega : 10 ≤ x i)] at ht
        rw [max_eq_left (by omega : 10 ≤ x i)] at hu
        omega
      · rw [min_eq_left (by omega : x i ≤ 29)] at ht
        rw [max_eq_right (by omega : x i ≤ 29)] at hu
        omega
    rw [hsame, Function.update_eq_self] at he
    exact hxv he
  have path : FacePath (fun z => BodyPred z ∧ z ≠ v) x (Function.update x i b) := by
    apply FacePath.axis
    intro t ht hu
    have htr : 10 ≤ t ∧ t ≤ 29 := by
      rcases hb with he | he <;> rw [he] at ht hu <;>
        simp [min_eq_left, max_eq_left, min_eq_right, max_eq_right] at ht hu <;> omega
    exact ⟨line t htr.1 htr.2, avoid t ht hu⟩
  refine ⟨Function.update x i b, ⟨(line b hbRange.1 hbRange.2).1, i, ?_⟩,
    avoid b (min_le_right _ _) (le_max_right _ _), path⟩
  simpa using hb

theorem outer_corner_path {x v : Point} (hx : BodyPred x) (hxv : x ≠ v)
    (outer : ∀ i, x i ≤ 10 ∨ 29 ≤ x i) :
    ∃ y, Skeleton y ∧ y ≠ v ∧ FacePath (fun z => BodyPred z ∧ z ≠ v) x y := by
  obtain ⟨j, hj⟩ : ∃ j, x j ≠ v j := by
    by_contra! hh; exact hxv (funext hh)
  let i : Fin 3 := if j = 0 then 1 else 0
  have hji : j ≠ i := by fin_cases j <;> decide
  let b : ℤ := if x i ≤ 10 then 10 else 29
  have hb : b = 10 ∨ b = 29 := by dsimp [b]; split_ifs <;> simp
  have hbr : 0 ≤ b ∧ b ≤ 39 := by omega
  have lines (a : Fin 3) (t : ℤ) (ht : 0 ≤ t ∧ t ≤ 39) : BodyPred (Function.update x a t) := by
    have hcube := inCube_update hx.1 a t ht
    have o0 := outer 0; have o1 := outer 1; have o2 := outer 2
    fin_cases a
    · apply two_outside_body hcube 1 2 (by decide)
      · simpa using o1
      · simpa using o2
    · apply two_outside_body hcube 0 2 (by decide)
      · simpa using o0
      · simpa using o2
    · apply two_outside_body hcube 0 1 (by decide)
      · simpa using o0
      · simpa using o1
  have line := lines i
  have path : FacePath (fun z => BodyPred z ∧ z ≠ v) x (Function.update x i b) := by
    apply FacePath.axis
    intro t ht hu
    have hxb := hx.1 i
    have htr : 0 ≤ t ∧ t ≤ 39 := by
      rcases le_total (x i) b with hh | hh
      · rw [min_eq_left hh] at ht; rw [max_eq_right hh] at hu; omega
      · rw [min_eq_right hh] at ht; rw [max_eq_left hh] at hu; omega
    exact ⟨line t htr, update_ne hji hj⟩
  refine ⟨Function.update x i b, ⟨(line b hbr).1, i, by simpa using hb⟩,
    update_ne hji hj, path⟩

theorem body_punctured (v : Point) : Connected ({x | x ∈ body} \ {v}) := by
  have reach (x : Point) (hx : BodyPred x) (hxv : x ≠ v) :
      ∃ y, Skeleton y ∧ y ≠ v ∧ FacePath (fun z => BodyPred z ∧ z ≠ v) x y := by
    by_cases central : ∃ i, 10 < x i ∧ x i < 29
    · obtain ⟨i, h₁, h₂, hl⟩ := clear_line hx central
      exact clear_line_path hx hxv i ⟨h₁, h₂⟩ hl
    · apply outer_corner_path hx hxv
      push_neg at central
      intro i
      have hh := central i
      omega
  intro x hx y hy
  obtain ⟨a, ha, hav, hxa⟩ := reach x ((mem_body_iff _).mp hx.1) hx.2
  obtain ⟨b, hb, hbv, hyb⟩ := reach y ((mem_body_iff _).mp hy.1) hy.2
  have hab : FacePath (fun z => BodyPred z ∧ z ≠ v) a b :=
    (skeleton_punctured v a ⟨ha, hav⟩ b ⟨hb, hbv⟩).mono
    (by intro z hz; exact ⟨skeleton_body hz.1, hz.2⟩)
  exact FacePath.mono ((hxa.trans hab).trans hyb.reverse)
    (by intro z hz; exact ⟨(mem_body_iff _).mpr hz.1, hz.2⟩)

end TranslationTiling.Rotations.SixKeys
