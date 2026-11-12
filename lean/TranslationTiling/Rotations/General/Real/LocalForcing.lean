import TranslationTiling.Rotations.General.Real.LocalFilled
import TranslationTiling.Rotations.General.Real.DiscreteFinish

namespace TranslationTiling.Rotations.General.Real
variable {d : ℕ} [NeZero d]

noncomputable section
open Set

theorem embedMotion_comp (m n : (Motion d)) : embedMotion (m.comp n)=(embedMotion m).comp (embedMotion n) := by
  apply RigidMotion.ext_apply
  intro x
  rw [RigidMotion.comp_apply]
  ext i
  have hs : (m.orientation.comp n.orientation).sign i =
      m.orientation.sign i*n.orientation.sign (m.orientation.axes i) := by
    have sign_xor (a b : Bool) : (if xor a b then (-1:ℤ) else 1)=
        (if a then -1 else 1)*(if b then -1 else 1) := by
      cases a <;> cases b <;> decide
    exact sign_xor _ _
  simp only [embedMotion,RigidMotion.apply,Motion.comp,
    PiLp.add_apply,Pi.add_apply,castPoint_apply,gridRotation_apply,Orientation.linear_apply,
    Int.cast_add,Int.cast_mul,hs]
  change _ = _
  simp only [Orientation.comp,Equiv.trans_apply]
  push_cast
  ring

/-- The Euclidean one-entrance theorem. The other copies may start with any
orthogonal orientation and any real translation. -/
theorem euclidean_chamber_forces_neighbor (hd : 3 ≤ d) {ι : Type*} (M : ι → (RigidMotion d))
    (cover : AECover (fun j => Placed gadget (M j))) (host : ι)
    (hhost : M host=RigidMotion.ident) (i : (Face d)) :
    ∃ j, M j=embedMotion (⟨Orientation.ident,-shift i⟩ : (Motion d)) := by
  let e := embedMotion (frameMotion i)
  let N := fun j => e.inverse.comp (M j)
  have coverN : AECover (fun j => Placed gadget (N j)) :=
    RigidMotion.normalize_cover M cover e
  have nhost : N host=e.inverse := by
    apply RigidMotion.ext_apply
    intro x
    simp [N,hhost]
  have hhostN : Placed gadget (N host)=solid (localGadget i) := by
    rw [nhost]
    exact local_host_solid i
  obtain ⟨j,a,_,ha,filled,avoids⟩ := integral_fills_chamber hd N coverN host i hhostN
  let m := (frameMotion i).comp a
  have filledWorld : chamber i ⊆ Footprint m := by
    intro x hx
    have hxL : (frameMotion i).inverse.apply x ∈ localChamber i := by
      rw [mem_localChamber]
      obtain ⟨p,hp,rfl⟩ := hx
      simpa only [Motion.inverse_apply_apply] using hp
    obtain ⟨p,hp,he⟩ := filled hxL
    refine ⟨p,hp,?_⟩
    simp only [m,Motion.comp_apply,he,Motion.apply_inverse_apply]
  have avoidsWorld : Disjoint (Footprint m) (↑(body : Finset (Lattice d)) : Set (Lattice d)) := by
    apply Set.disjoint_left.mpr
    rintro x ⟨p,hp,rfl⟩ hxB
    have hL : a.apply p ∈ localBody i := by
      have hh : (frameMotion i).inverse.apply (m.apply p) ∈ localBody i :=
        Finset.mem_image_of_mem _ hxB
      simpa only [m,Motion.comp_apply,Motion.inverse_apply_apply] using hh
    exact Set.disjoint_left.mp avoids ⟨p,hp,rfl⟩ hL
  obtain ⟨hr,ht⟩ := filled_chamber_parameters hd m i filledWorld avoidsWorld
  have hmEq : m=(⟨Orientation.ident,-shift i⟩ : (Motion d)) := by
    change (⟨m.orientation,m.offset⟩ : (Motion d))=(⟨Orientation.ident,-shift i⟩ : (Motion d))
    rw [hr,ht]
  refine ⟨j,?_⟩
  have hj : M j=embedMotion m := by
    apply RigidMotion.ext_apply
    intro x
    have hh := congrArg (fun n : (RigidMotion d) => e.apply (n.apply x)) ha
    simp only [N,RigidMotion.comp_apply,RigidMotion.apply_inverse] at hh
    dsimp only [m]
    rw [embedMotion_comp,RigidMotion.comp_apply]
    exact hh
  rwa [hmEq] at hj

end
end TranslationTiling.Rotations.General.Real
