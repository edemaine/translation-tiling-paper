import TranslationTiling.Rotations.General.KeyConnectivity

namespace TranslationTiling.Rotations.General
variable {d : ℕ} [NeZero d]

/-- Put the canonical face key in any prescribed local coordinate frame. -/
def placedKey (frame : Face d → Motion d) (f : Face d) : Set (Lattice d) :=
  (frame f).apply '' Key f

/-- Key recognition is independent of the choice of face coordinate frames. -/
theorem placed_key_rigid (hd : 2 ≤ d) (frame : Face d → Motion d)
    (f g : Face d) (m : Motion d)
    (he : m.apply '' placedKey frame f = placedKey frame g) :
    f = g ∧ ∀ x, m.apply x = x := by
  let n := (frame g).inverse.comp (m.comp (frame f))
  have hn : n.apply '' Key f = Key g := by
    calc
      _ = (frame g).inverse.apply '' (m.apply '' placedKey frame f) := by
        simp only [n,Motion.comp_apply,placedKey,Set.image_image,Function.comp_def]
      _ = (frame g).inverse.apply '' placedKey frame g := by rw [he]
      _ = Key g := by
        simp only [placedKey,Set.image_image,Function.comp_def,Motion.inverse_apply_apply,Set.image_id']
  obtain ⟨hfg,hr,ht⟩ := key_rigid hd f g n hn
  subst g
  refine ⟨rfl,?_⟩
  intro x
  have hi : n.apply ((frame f).inverse.apply x) = (frame f).inverse.apply x := by
    simp only [Motion.apply,hr,ht,Orientation.ident_apply,zero_add]
  have hi' := congrArg (frame f).apply hi
  simpa only [n,Motion.comp_apply,Motion.apply_inverse_apply] using hi'

end TranslationTiling.Rotations.General
