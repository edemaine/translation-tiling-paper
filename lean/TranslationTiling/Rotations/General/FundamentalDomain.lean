import TranslationTiling.Rotations.General.Gadget
import TranslationTiling.Proofs.Basic

namespace TranslationTiling.Rotations.General
variable {d : ℕ} [NeZero d]

theorem scale_injective (L : ℕ) (hL : 0 < L) : Function.Injective (scale L : Lattice d → Lattice d) := by
  intro x y he
  ext i
  have hi := congrFun he i
  change (L : ℤ)*x i = (L : ℤ)*y i at hi
  exact mul_left_cancel₀ (by omega : (L : ℤ) ≠ 0) hi

theorem grid_unique {z w q r : Lattice d} (hq : q ∈ gadget) (hr : r ∈ gadget)
    (he : scale (cubeSide d) z+q = scale (cubeSide d) w+r) : z = w ∧ q = r := by
  obtain ⟨a,_,hu⟩ := gadget_exact (scale (cubeSide d) z+q)
  have hz : z = a := hu z ⟨q,hq,rfl⟩
  have hw : w = a := hu w ⟨r,hr,he.symm⟩
  have hzw := hz.trans hw.symm
  rw [← hzw] at he
  exact ⟨hzw,add_left_cancel he⟩

theorem fundamental_domain : ExactTiling (Set.range (scale (cubeSide d) : Lattice d → Lattice d))
    (↑(gadget : Finset (Lattice d)) : Set (Lattice d)) := by
  constructor
  · rintro ⟨a,q⟩ ⟨b,r⟩ he
    obtain ⟨z,hz⟩ := a.property
    obtain ⟨w,hw⟩ := b.property
    have he' : scale (cubeSide d) z+q.val = scale (cubeSide d) w+r.val := by
      simpa only [hz,hw] using he
    obtain ⟨hzw,hqr⟩ := grid_unique q.property r.property he'
    have hab : a.val = b.val := by rw [← hz,← hw,hzw]
    exact Prod.ext (Subtype.ext hab) (Subtype.ext hqr)
  · intro x
    obtain ⟨z,⟨q,hq,he⟩,_⟩ := gadget_exact x
    exact ⟨(⟨scale (cubeSide d) z,z,rfl⟩,⟨q,hq⟩),he⟩

end TranslationTiling.Rotations.General
