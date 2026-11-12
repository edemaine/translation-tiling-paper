import TranslationTiling.Rotations.General.Motions

namespace TranslationTiling.Rotations.General
variable {d : ℕ}

theorem Orientation.linear_faithful {r s : Orientation d}
    (h : ∀ x : Lattice d, r.linear x=s.linear x) : r=s := by
  have ha (i : Fin d) : r.axes i=s.axes i := by
    by_contra hn
    have hh := congrFun (h (Pi.single (r.axes i) 1)) i
    simp only [Orientation.linear_apply,Pi.single_eq_same,Pi.single_eq_of_ne (Ne.symm hn),mul_zero,mul_one] at hh
    unfold Orientation.sign at hh
    split_ifs at hh <;> norm_num at hh
  have hf (i : Fin d) : r.flip i=s.flip i := by
    have hh := congrFun (h (Pi.single (r.axes i) 1)) i
    simp only [Orientation.linear_apply,ha,Pi.single_eq_same,mul_one] at hh
    unfold Orientation.sign at hh
    cases h1 : r.flip i <;> cases h2 : s.flip i
    all_goals simp [h1,h2] at hh ⊢
  exact Orientation.ext (Equiv.ext ha) (funext hf)

theorem Motion.apply_faithful {m n : Motion d} (h : ∀ x, m.apply x=n.apply x) : m=n := by
  have ht : m.offset=n.offset := by simpa only [Motion.apply,map_zero,add_zero] using h 0
  have hr : m.orientation=n.orientation := Orientation.linear_faithful (by
    intro x
    have hh := h x
    simp only [Motion.apply,ht] at hh
    exact add_left_cancel hh)
  cases m
  cases n
  cases ht
  cases hr
  rfl

end TranslationTiling.Rotations.General
