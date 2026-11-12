import TranslationTiling.Rotations.General.PlacedKeys

namespace TranslationTiling.Rotations.General
variable {d : ℕ} [NeZero d]

/-- Comparing keys in different source and target coordinate frames determines
the face label and the entire map between those frames. -/
theorem framed_key_rigid (hd : 2 ≤ d) (source target : Face d → Motion d)
    (f g : Face d) (m : Motion d)
    (he : m.apply '' placedKey source f = placedKey target g) :
    f = g ∧ ∀ x, m.apply ((source f).apply x) = (target f).apply x := by
  let n := (target g).inverse.comp (m.comp (source f))
  have hn : n.apply '' Key f = Key g := by
    calc
      _ = (target g).inverse.apply '' (m.apply '' placedKey source f) := by
        simp only [n,Motion.comp_apply,placedKey,Set.image_image,Function.comp_def]
      _ = (target g).inverse.apply '' placedKey target g := by rw [he]
      _ = Key g := by
        simp only [placedKey,Set.image_image,Function.comp_def,Motion.inverse_apply_apply,Set.image_id']
  obtain ⟨hfg,hr,ht⟩ := key_rigid hd f g n hn
  subst g
  refine ⟨rfl,fun x => ?_⟩
  have hi : n.apply x = x := by
    simp only [Motion.apply,hr,ht,Orientation.ident_apply,zero_add]
  have hi' := congrArg (target f).apply hi
  simpa only [n,Motion.comp_apply,Motion.apply_inverse_apply] using hi'

end TranslationTiling.Rotations.General
