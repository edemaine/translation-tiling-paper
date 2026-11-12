import TranslationTiling.Rotations.General.Boxes

namespace TranslationTiling.Rotations.General
variable {d : ℕ}

/-- A rectangle with two nondegenerate coordinate intervals stays connected
when an arbitrary lattice point is removed. Other intervals may be singletons. -/
theorem box_punctured (lo hi : Lattice d) (v : Lattice d)
    (hb : ∀ i, lo i ≤ hi i) (a b : Fin d) (hab : a ≠ b)
    (ha : lo a < hi a) (hbb : lo b < hi b) : Connected (Box lo hi \ {v}) := by
  classical
  let q : Lattice d := fun i => if lo i = v i then hi i else lo i
  have hq (i : Fin d) : lo i ≤ q i ∧ q i ≤ hi i := by
    have := hb i
    dsimp [q]
    split_ifs <;> exact ⟨by omega,by omega⟩
  have hqa : q a ≠ v a := by dsimp [q]; split_ifs <;> omega
  have hqb : q b ≠ v b := by dsimp [q]; split_ifs <;> omega
  have path (x : Lattice d) (hx : x ∈ Box lo hi) (hxv : x ≠ v) :
      FacePath (· ∈ Box lo hi \ {v}) x q := by
    obtain ⟨j,hj⟩ : ∃ j, x j ≠ v j := by
      by_contra! hn
      exact hxv (funext hn)
    let i := if j = a then b else a
    have hij : j ≠ i := by dsimp [i]; split_ifs <;> simp_all
    have hqi : q i ≠ v i := by dsimp [i]; split_ifs <;> assumption
    let y := Function.update x i (q i)
    have hy : y ∈ Box lo hi := by
      intro k
      by_cases hk : k = i
      · subst k; simpa [y] using hq i
      · simpa [y,Function.update_of_ne hk] using hx k
    have p1 : FacePath (· ∈ Box lo hi \ {v}) x y := by
      apply FacePath.axis
      intro t ht hu
      constructor
      · intro k
        by_cases hk : k = i
        · subst k
          simp only [Function.update_self]
          exact ⟨(le_min (hx i).1 (hq i).1).trans ht,hu.trans (max_le (hx i).2 (hq i).2)⟩
        · simpa [Function.update_of_ne hk] using hx k
      · intro he
        exact hj (by simpa [Function.update_of_ne hij] using congrFun he j)
    let lo' := Function.update lo i (q i)
    let hi' := Function.update hi i (q i)
    have hys : y ∈ Box lo' hi' := by
      intro k
      by_cases hk : k = i
      · subst k; simp [y,lo',hi']
      · simpa [lo',hi',Function.update_of_ne hk] using hy k
    have hqs : q ∈ Box lo' hi' := by
      intro k
      by_cases hk : k = i
      · subst k; simp [lo',hi']
      · simpa [lo',hi',Function.update_of_ne hk] using hq k
    have p2 := box_path lo' hi' y q hys hqs
    apply p1.trans (p2.mono _)
    intro z hz
    have hzi : z i = q i := by have := hz i; simp [lo',hi'] at this; omega
    constructor
    · intro k
      by_cases hk : k = i
      · subst k; rw [hzi]; exact hq i
      · simpa [lo',hi',Function.update_of_ne hk] using hz k
    · intro he
      exact hqi (hzi.symm.trans (congrFun he i))
  intro x hx y hy
  exact (path x hx.1 hx.2).trans (path y hy.1 hy.2).reverse

end TranslationTiling.Rotations.General
