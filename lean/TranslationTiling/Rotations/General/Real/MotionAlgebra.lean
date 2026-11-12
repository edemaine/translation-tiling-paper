import TranslationTiling.Rotations.General.Real.Covers
import TranslationTiling.Rotations.General.Real.GridEmbedding

namespace TranslationTiling.Rotations.General.Real
variable {d : ℕ} [NeZero d]

noncomputable section
open Set MeasureTheory

def RigidMotion.ident : (RigidMotion d) := ⟨LinearIsometryEquiv.refl ℝ (EPoint d),0⟩
def RigidMotion.comp (m n : (RigidMotion d)) : (RigidMotion d) :=
  ⟨n.rotation.trans m.rotation, m.offset+m.rotation n.offset⟩

@[simp] theorem RigidMotion.ident_apply (x : (EPoint d)) : RigidMotion.ident.apply x = x := by
  simp [RigidMotion.ident, RigidMotion.apply]

@[simp] theorem RigidMotion.comp_apply (m n : (RigidMotion d)) (x : (EPoint d)) :
    (m.comp n).apply x = m.apply (n.apply x) := by
  simp [RigidMotion.comp, RigidMotion.apply, map_add, add_assoc]

theorem RigidMotion.ext_apply {m n : (RigidMotion d)} (h : ∀ x, m.apply x = n.apply x) : m = n := by
  have ht : m.offset = n.offset := by simpa [RigidMotion.apply] using h 0
  have hr : m.rotation = n.rotation := by
    apply LinearIsometryEquiv.ext
    intro x
    have hh := h x
    simp only [RigidMotion.apply, ht] at hh
    exact add_left_cancel hh
  cases m; cases n; simp_all

theorem RigidMotion.dist_apply (m : (RigidMotion d)) (x y : (EPoint d)) :
    dist (m.apply x) (m.apply y) = dist x y := by
  simp [RigidMotion.apply, dist_eq_norm, ← map_sub]

theorem embedMotion_inverse (m : (Motion d)) : embedMotion m.inverse = (embedMotion m).inverse := by
  apply RigidMotion.ext_apply
  intro x
  apply (embedMotion m).injective
  rw [RigidMotion.apply_inverse]
  ext i
  simp [embedMotion, RigidMotion.apply, Motion.inverse, Orientation.inverse,
    gridRotation, Orientation.linear, Orientation.sign]
  split_ifs <;> ring

theorem RigidMotion.normalize_cover {ι : Type*} {F : Finset (Lattice d)}
    (M : ι → (RigidMotion d)) (h : AECover (fun j => Placed F (M j))) (r : (RigidMotion d)) :
    AECover (fun j => Placed F (r.inverse.comp (M j))) := by
  have hae := r.measurePreserving.quasiMeasurePreserving.ae h
  filter_upwards [hae] with x hx
  have iffmem (j : ι) : r.apply x ∈ Placed F (M j) ↔
      x ∈ Placed F (r.inverse.comp (M j)) := by
    constructor
    · rintro ⟨y,hy,he⟩
      refine ⟨y,hy,?_⟩
      simp [RigidMotion.comp_apply,he]
    · rintro ⟨y,hy,he⟩
      refine ⟨y,hy,?_⟩
      have hh := congrArg r.apply he
      simpa only [RigidMotion.comp_apply,RigidMotion.apply_inverse] using hh
  obtain ⟨j,hj,hu⟩ := hx
  exact ⟨j,(iffmem j).mp hj,fun k hk => hu k ((iffmem k).mpr hk)⟩

end
end TranslationTiling.Rotations.General.Real
